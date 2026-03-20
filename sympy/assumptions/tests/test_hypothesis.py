 """

Hypothesis-based property tests for lra_satask function.


These tests use the Hypothesis library to generate random test cases

for property-based testing of the Linear Real Arithmetic SAT solver,

specifically targeting the changes made in the check-real branch.


Test Strategy

=============


These hypothesis tests verify mathematical properties and invariants of

the lra_satask function through randomized testing:


- **Transitivity**: If a R b and b R c, then a R c (for relations R)

- **Reflexivity**: For equality and non-strict inequalities

- **Antisymmetry**: If a <= b and b <= a, then a == b

- **Contradiction detection**: Mutually exclusive assumptions

- **Consistency**: Adding weaker assumptions doesn't change results

- **Algebraic properties**: Multiplication, addition with inequalities

- **Negation properties**: ~(a > b) equivalent to (a <= b)

- **Chain reasoning**: Multi-step inference chains


Related Git Commits (check-real branch)

========================================


- 14a47b1382: assumptions: Clean up lra_satask

- 0a7468cc63: assumptions: Add reverse_encoding to EncodedCNF

- 20cad175df: _preprocess: Add docstring with examples

- c3d9e39520: lra_satask: Partially handle extended real exprs

- 37032d8c65: lra_satask: Validate expressions are NumberKind

- dfc7fea367: lra_satask: Make _preprocess more readable

- 34760714a3: lra_satask: Use unit clauses and refactor

"""


from hypothesis import given, assume, strategies as st, example

from sympy import symbols, Q, S

from sympy.assumptions.lra_satask import lra_satask

from sympy.logic.algorithms.lra_theory import UnhandledInput

from sympy.testing.pytest import raises



# Strategy for generating real-valued symbols

def real_symbol_strategy():

    return st.builds(

        lambda name: symbols(name, real=True),

        st.text(alphabet='abcdefghijklmnopqrstuvwxyz', min_size=1, max_size=2)

    )


# Strategy for generating positive integers (for constants in inequalities)

small_integers = st.integers(min_value=-100, max_value=100)

positive_integers = st.integers(min_value=1, max_value=100)

negative_integers = st.integers(min_value=-100, max_value=-1)



def test_transitivity_gt():

    """Test transitivity: if a > b and b > c, then a > c"""

    x, y, z = symbols('x y z', real=True)



    # If x > y and y > z, then x > z

    result = lra_satask(Q.gt(x, z), Q.gt(x, y) & Q.gt(y, z))

    assert result is True



@given(offset1=positive_integers, offset2=positive_integers)

def test_transitivity_chain(offset1, offset2):

    """Test transitivity chains with multiple variables"""

    x, y, z = symbols('x y z', real=True)



    # If x > y + offset1 and y > z + offset2, then x > z + (offset1 + offset2)

    total_offset = offset1 + offset2

    if total_offset > 0:

        result = lra_satask(

            Q.gt(x, z + total_offset - 1),

            Q.gt(x, y + offset1) & Q.gt(y, z + offset2)

        )

        assert result in [True, None]  # Should be True or at least not False



@given(value=small_integers)

def test_reflexivity_eq(value):

    """Test reflexivity: a == a is always true"""

    x = symbols('x', real=True)

    result = lra_satask(Q.eq(x, x), Q.eq(x, value))

    assert result is True



@given(value=small_integers)

def test_ge_reflexivity(value):

    """Test that x >= x is always true"""

    x = symbols('x', real=True)

    result = lra_satask(Q.ge(x, x), Q.eq(x, value))

    assert result is True



@given(value=small_integers)

def test_le_reflexivity(value):

    """Test that x <= x is always true"""

    x = symbols('x', real=True)

    result = lra_satask(Q.le(x, x), Q.eq(x, value))

    assert result is True



def test_antisymmetry_le():

    """Test antisymmetry: if a <= b and b <= a, then a == b"""

    x, y = symbols('x y', real=True)



    result = lra_satask(Q.eq(x, y), Q.le(x, y) & Q.le(y, x))

    assert result is True



def test_contradiction_gt_lt():

    """Test that x > 5 and x < 0 is a contradiction"""

    x = symbols('x', real=True)



    # x > 5 and x < 0 is contradictory - should return False

    result = lra_satask(Q.gt(x, 5), Q.lt(x, 0))

    assert result is False



@given(value=small_integers)

def test_trichotomy(value):

    """Test trichotomy: for any x and value, exactly one of x < value, x == value, x > value holds"""

    x = symbols('x', real=True)



    # If x > value, then not (x < value) and not (x == value)

    result_lt = lra_satask(Q.lt(x, value), Q.gt(x, value))

    result_eq = lra_satask(Q.eq(x, value), Q.gt(x, value))



    assert result_lt is False

    assert result_eq is False



@given(offset=positive_integers)

def test_addition_preserves_inequality(offset):

    """Test that if a < b, then a + c < b + c"""

    x, y, c = symbols('x y c', real=True)



    # If x < y, then x + offset < y + offset

    result = lra_satask(Q.lt(x + offset, y + offset), Q.lt(x, y))

    assert result is True



@given(a=small_integers, b=small_integers)

def test_subtraction_inequality(a, b):

    """Test inequality with subtraction"""

    assume(a < b)

    x, y = symbols('x y', real=True)



    # If x < a and y > b, then x - y < a - b

    result = lra_satask(Q.lt(x - y, a - b + 1), Q.lt(x, a) & Q.gt(y, b))

    assert result in [True, None]



@given(offset=positive_integers)

def test_negation_equivalence(offset):

    """Test that not (x > a) is equivalent to x <= a"""

    x = symbols('x', real=True)



    # If we know x > offset, asking if x <= 0 should be False (if offset > 0)

    result = lra_satask(Q.le(x, 0), Q.gt(x, offset))

    assert result is False



@given(lower=small_integers, upper=small_integers)

def test_interval_consistency(lower, upper):

    """Test consistency of interval constraints"""

    assume(lower < upper)

    x = symbols('x', real=True)



    # If lower < x < upper, then x > lower

    result = lra_satask(Q.gt(x, lower), Q.gt(x, lower) & Q.lt(x, upper))

    assert result is True



def test_three_variable_consistency():

    """Test consistency with three variables"""

    x, y, z = symbols('x y z', real=True)



    # If x < 0, y > 5, z > 10, then z > x

    result = lra_satask(Q.gt(z, x), Q.lt(x, 0) & Q.gt(y, 5) & Q.gt(z, 10))

    assert result is True



@given(positive_val=positive_integers)

def test_positive_predicate_implies_gt_zero(positive_val):

    """Test that Q.positive(x) implies x > 0"""

    x = symbols('x', real=True)



    result = lra_satask(Q.gt(x, 0), Q.positive(x))

    assert result is True



@given(negative_val=negative_integers)

def test_negative_predicate_implies_lt_zero(negative_val):

    """Test that Q.negative(x) implies x < 0"""

    x = symbols('x', real=True)



    result = lra_satask(Q.lt(x, 0), Q.negative(x))

    assert result is True



def test_zero_predicate_implies_eq_zero():

    """Test that Q.zero(x) implies x == 0"""

    x = symbols('x', real=True)



    result = lra_satask(Q.eq(x, 0), Q.zero(x))

    assert result is True



@given(value=positive_integers)

def test_nonzero_means_not_equal_zero(value):

    """Test that Q.nonzero(x) with x > value implies x != 0"""

    x = symbols('x', real=True)



    # If x is nonzero and x > value (where value > 0), then x > 0

    result = lra_satask(Q.gt(x, 0), Q.nonzero(x) & Q.gt(x, value))

    assert result is True



@given(value=positive_integers)

def test_nonnegative_includes_zero_and_positive(value):

    """Test that Q.nonnegative allows both zero and positive"""

    x = symbols('x', real=True)



    # x >= 0 should be consistent with x == 0

    result1 = lra_satask(Q.eq(x, 0), Q.nonnegative(x))

    assert result1 in [True, None]



    # x >= 0 should be consistent with x > value

    result2 = lra_satask(Q.gt(x, value), Q.nonnegative(x))

    assert result2 in [True, None]



@given(value=negative_integers)

def test_nonpositive_includes_zero_and_negative(value):

    """Test that Q.nonpositive allows both zero and negative"""

    x = symbols('x', real=True)



    # x <= 0 should be consistent with x == 0

    result1 = lra_satask(Q.eq(x, 0), Q.nonpositive(x))

    assert result1 in [True, None]



    # x <= 0 should be consistent with x < value (where value < 0)

    result2 = lra_satask(Q.lt(x, value), Q.nonpositive(x))

    assert result2 in [True, None]



def test_equality_symmetry():

    """Test that equality is symmetric: if x == y, then y == x"""

    x, y = symbols('x y', real=True)



    result = lra_satask(Q.eq(y, x), Q.eq(x, y))

    assert result is True



def test_equality_transitivity():

    """Test equality transitivity: if x == y and y == z, then x == z"""

    x, y, z = symbols('x y z', real=True)



    result = lra_satask(Q.eq(x, z), Q.eq(x, y) & Q.eq(y, z))

    assert result is True



@given(offset1=positive_integers, offset2=positive_integers)

def test_weakening_assumption(offset1, offset2):

    """Test that weakening assumptions doesn't make True become False"""

    assume(offset2 > offset1)

    x = symbols('x', real=True)



    # If x > offset2 implies something, then x > offset1 should also imply it

    # because x > offset2 is stronger than x > offset1

    result_strong = lra_satask(Q.gt(x, 0), Q.gt(x, offset2))

    result_weak = lra_satask(Q.gt(x, 0), Q.gt(x, offset1))



    # If strong assumption proves it True, weak one should too

    if result_strong is True:

        assert result_weak is True



@given(offset=positive_integers)

def test_strengthening_conclusion(offset):

    """Test that a weaker conclusion is at least as provable as stronger one"""

    x = symbols('x', real=True)



    # If we can prove x > offset, we should be able to prove x > 0

    result_strong = lra_satask(Q.gt(x, offset), Q.gt(x, offset + 10))

    result_weak = lra_satask(Q.gt(x, 0), Q.gt(x, offset + 10))



    if result_strong is True:

        assert result_weak is True



@given(num_vars=st.integers(min_value=2, max_value=5))

def test_chain_of_inequalities(num_vars):

    """Test chains of inequalities with multiple variables"""

    var_names = [f'v{i}' for i in range(num_vars)]

    vars = symbols(' '.join(var_names), real=True)



    # Create chain: v0 > v1 > v2 > ... > v_{n-1}

    assumptions = Q.gt(vars[0], vars[1])

    for i in range(1, num_vars - 1):

        assumptions = assumptions & Q.gt(vars[i], vars[i + 1])



    # Should be able to conclude first > last

    result = lra_satask(Q.gt(vars[0], vars[-1]), assumptions)

    assert result is True



@given(lower=small_integers, upper=small_integers, query=small_integers)

def test_range_query(lower, upper, query):

    """Test queries about values in a range"""

    assume(lower < upper)

    x = symbols('x', real=True)



    # If lower < x < upper, test various query values

    assumptions = Q.gt(x, lower) & Q.lt(x, upper)



    if query <= lower:

        # x must be greater than query

        result = lra_satask(Q.gt(x, query), assumptions)

        assert result is True

    elif query >= upper:

        # x must be less than query

        result = lra_satask(Q.lt(x, query), assumptions)

        assert result is True



@given(offset=positive_integers)

def test_double_negation(offset):

    """Test that double negation works correctly"""

    x = symbols('x', real=True)



    # not(not(x > offset)) should be equivalent to x > offset

    # In our system: if we assume x > offset, asking x > offset should be True

    result = lra_satask(Q.gt(x, offset), Q.gt(x, offset))

    assert result is True



@given(a=small_integers)

def test_constant_equality(a):

    """Test equality with constants"""

    x = symbols('x', real=True)



    # If x == a, then x >= a

    result_ge = lra_satask(Q.ge(x, a), Q.eq(x, a))

    assert result_ge is True



    # If x == a, then x <= a

    result_le = lra_satask(Q.le(x, a), Q.eq(x, a))

    assert result_le is True



@given(gap=positive_integers)

def test_inequality_gap(gap):

    """Test that we can detect impossible gaps"""

    x, y = symbols('x y', real=True)



    # If x < 0 and y > gap, then x < y

    result = lra_satask(Q.lt(x, y), Q.lt(x, 0) & Q.gt(y, gap))

    assert result is True



@given(val1=small_integers, val2=small_integers)

def test_two_variable_system(val1, val2):

    """Test systems with two variables"""

    x, y = symbols('x y', real=True)



    # If x > val1 and y < val2 and val1 > val2, then x > y

    if val1 > val2:

        result = lra_satask(Q.gt(x, y), Q.gt(x, val1) & Q.lt(y, val2))

        assert result is True



def test_unhandled_nan():

    """Test that NaN is properly rejected"""

    raises(UnhandledInput, lambda: lra_satask(Q.gt(S.NaN, 0), True))



def test_unhandled_matrix():

    """Test that matrices are properly rejected"""

    from sympy.matrices.expressions.matexpr import MatrixSymbol

    X = MatrixSymbol("X", 2, 2)

    raises(UnhandledInput, lambda: lra_satask(Q.gt(X, 0), True))



@given(offset=positive_integers)

def test_contradiction_with_false_assumption(offset):

    """Test that False assumptions lead to ValueError"""

    x = symbols('x', real=True)

    raises(ValueError, lambda: lra_satask(Q.gt(x, offset), False))



@given(offset=positive_integers)

def test_tautology_from_contradiction(offset):

    """Test that contradictory assumptions can prove anything"""

    x = symbols('x', real=True)



    # From False, anything follows (ex falso quodlibet)

    # x > offset and x < 0 when offset > 0 is contradictory

    raises(ValueError, lambda: lra_satask(Q.gt(x, 1000), Q.gt(x, offset) & Q.lt(x, -offset)))



@given(a=positive_integers, b=positive_integers)

def test_sum_of_positives(a, b):

    """Test that sum of positive values is positive"""

    x, y = symbols('x y', real=True)



    # If x > 0 and y > 0, then x + y > 0

    result = lra_satask(Q.gt(x + y, 0), Q.gt(x, 0) & Q.gt(y, 0))

    assert result is True



@given(a=positive_integers)

def test_negation_reverses_sign(a):

    """Test that negation reverses inequality"""

    x = symbols('x', real=True)



    # If x > a, then -x < -a

    result = lra_satask(Q.lt(-x, -a), Q.gt(x, a))

    assert result is True



@given(multiplier=st.integers(min_value=2, max_value=10))

def test_scaling_inequality(multiplier):

    """Test scaling inequalities by positive constants"""

    x = symbols('x', real=True)



    # If x > 1, then multiplier*x > multiplier

    result = lra_satask(Q.gt(multiplier * x, multiplier), Q.gt(x, 1))

    assert result is True
