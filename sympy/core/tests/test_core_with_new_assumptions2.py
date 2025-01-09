from sympy.assumptions import ask, Q
from sympy.core.mod import Mod
from sympy.core.numbers import I, oo, pi
from sympy.functions.combinatorial.factorials import factorial
from sympy.functions.elementary.exponential import exp, log
from sympy.functions.elementary.miscellaneous import sqrt
from sympy.functions.elementary.trigonometric import asin, sin
from sympy.simplify.simplify import simplify
from sympy.core import Symbol, S, Rational, Integer, Dummy, Wild, Pow
from sympy.core.assumptions import assumptions, check_assumptions, failing_assumptions, common_assumptions, _generate_assumption_rules, _load_pre_generated_assumption_rules
from sympy.core.facts import InconsistentAssumptions
from sympy.core.random import seed
from sympy.combinatorics import Permutation
from sympy.combinatorics.perm_groups import PermutationGroup
from sympy.testing.pytest import raises, XFAIL

def test_symbol_unset():
    x = Symbol('x', real=True, integer=True)
    assert ask(Q.real(x)) is True
    assert ask(Q.integer(x)) is True
    assert ask(Q.imaginary(x)) is False
#     assert ask(Q.noninteger_unhandled_input(x)) is False
#     assert ask(Q.number_unhandled_input(x)) is False

def test_zero():
    z = Integer(0)
    assert ask(Q.commutative(z)) is True
    assert ask(Q.integer(z)) is True
    assert ask(Q.rational(z)) is True
    assert ask(Q.algebraic(z)) is True
#     assert ask(Q.transcendental_unhandled_input(z)) is False
    assert ask(Q.real(z)) is True
    assert ask(Q.complex(z)) is True
#     assert ask(Q.noninteger_unhandled_input(z)) is False
    assert ask(Q.irrational(z)) is False
    assert ask(Q.imaginary(z)) is False
    assert ask(Q.positive(z)) is False
    assert ask(Q.negative(z)) is False
    assert ask(Q.nonpositive(z)) is True
    assert ask(Q.nonnegative(z)) is True
    assert ask(Q.even(z)) is True
    assert ask(Q.odd(z)) is False
    assert ask(Q.finite(z)) is True
    assert ask(Q.infinite(z)) is False
#     assert ask(Q.comparable_unhandled_input(z)) is True
    assert ask(Q.prime(z)) is False
    assert ask(Q.composite(z)) is False
#     assert ask(Q.number_unhandled_input(z)) is True

def test_one():
    z = Integer(1)
    assert ask(Q.commutative(z)) is True
    assert ask(Q.integer(z)) is True
    assert ask(Q.rational(z)) is True
    assert ask(Q.algebraic(z)) is True
#     assert ask(Q.transcendental_unhandled_input(z)) is False
    assert ask(Q.real(z)) is True
    assert ask(Q.complex(z)) is True
#     assert ask(Q.noninteger_unhandled_input(z)) is False
    assert ask(Q.irrational(z)) is False
    assert ask(Q.imaginary(z)) is False
    assert ask(Q.positive(z)) is True
    assert ask(Q.negative(z)) is False
    assert ask(Q.nonpositive(z)) is False
    assert ask(Q.nonnegative(z)) is True
    assert ask(Q.even(z)) is False
    assert ask(Q.odd(z)) is True
    assert ask(Q.finite(z)) is True
    assert ask(Q.infinite(z)) is False
#     assert ask(Q.comparable_unhandled_input(z)) is True
    assert ask(Q.prime(z)) is False
#     assert ask(Q.number_unhandled_input(z)) is True
    assert ask(Q.composite(z)) is False

def test_negativeone():
    z = Integer(-1)
    assert ask(Q.commutative(z)) is True
    assert ask(Q.integer(z)) is True
    assert ask(Q.rational(z)) is True
    assert ask(Q.algebraic(z)) is True
#     assert ask(Q.transcendental_unhandled_input(z)) is False
    assert ask(Q.real(z)) is True
    assert ask(Q.complex(z)) is True
#     assert ask(Q.noninteger_unhandled_input(z)) is False
    assert ask(Q.irrational(z)) is False
    assert ask(Q.imaginary(z)) is False
    assert ask(Q.positive(z)) is False
    assert ask(Q.negative(z)) is True
    assert ask(Q.nonpositive(z)) is True
    assert ask(Q.nonnegative(z)) is False
    assert ask(Q.even(z)) is False
    assert ask(Q.odd(z)) is True
    assert ask(Q.finite(z)) is True
    assert ask(Q.infinite(z)) is False
#     assert ask(Q.comparable_unhandled_input(z)) is True
    assert ask(Q.prime(z)) is False
    assert ask(Q.composite(z)) is False
#     assert ask(Q.number_unhandled_input(z)) is True

def test_infinity():
    oo = S.Infinity
    assert ask(Q.commutative(oo)) is True
    assert ask(Q.integer(oo)) is False
    assert ask(Q.rational(oo)) is False
    assert ask(Q.algebraic(oo)) is False
#     assert ask(Q.transcendental_unhandled_input(oo)) is False
    assert ask(Q.extended_real(oo)) is True
    assert ask(Q.real(oo)) is False
    assert ask(Q.complex(oo)) is False
#     assert ask(Q.noninteger_unhandled_input(oo)) is True
    assert ask(Q.irrational(oo)) is False
    assert ask(Q.imaginary(oo)) is False
    assert ask(Q.nonzero(oo)) is False
    assert ask(Q.positive(oo)) is False
    assert ask(Q.negative(oo)) is False
    assert ask(Q.nonpositive(oo)) is False
    assert ask(Q.nonnegative(oo)) is False
    assert ask(Q.extended_nonzero(oo)) is True
    assert ask(Q.extended_positive(oo)) is True
    assert ask(Q.extended_negative(oo)) is False
    assert ask(Q.extended_nonpositive(oo)) is False
    assert ask(Q.extended_nonnegative(oo)) is True
    assert ask(Q.even(oo)) is False
    assert ask(Q.odd(oo)) is False
    assert ask(Q.finite(oo)) is False
    assert ask(Q.infinite(oo)) is True
#     assert ask(Q.comparable_unhandled_input(oo)) is True
    assert ask(Q.prime(oo)) is False
    assert ask(Q.composite(oo)) is False
#     assert ask(Q.number_unhandled_input(oo)) is True

def test_neg_infinity():
    mm = S.NegativeInfinity
    assert ask(Q.commutative(mm)) is True
    assert ask(Q.integer(mm)) is False
    assert ask(Q.rational(mm)) is False
    assert ask(Q.algebraic(mm)) is False
#     assert ask(Q.transcendental_unhandled_input(mm)) is False
    assert ask(Q.extended_real(mm)) is True
    assert ask(Q.real(mm)) is False
    assert ask(Q.complex(mm)) is False
#     assert ask(Q.noninteger_unhandled_input(mm)) is True
    assert ask(Q.irrational(mm)) is False
    assert ask(Q.imaginary(mm)) is False
    assert ask(Q.nonzero(mm)) is False
    assert ask(Q.positive(mm)) is False
    assert ask(Q.negative(mm)) is False
    assert ask(Q.nonpositive(mm)) is False
    assert ask(Q.nonnegative(mm)) is False
    assert ask(Q.extended_nonzero(mm)) is True
    assert ask(Q.extended_positive(mm)) is False
    assert ask(Q.extended_negative(mm)) is True
    assert ask(Q.extended_nonpositive(mm)) is True
    assert ask(Q.extended_nonnegative(mm)) is False
    assert ask(Q.even(mm)) is False
    assert ask(Q.odd(mm)) is False
    assert ask(Q.finite(mm)) is False
    assert ask(Q.infinite(mm)) is True
#     assert ask(Q.comparable_unhandled_input(mm)) is True
    assert ask(Q.prime(mm)) is False
    assert ask(Q.composite(mm)) is False
#     assert ask(Q.number_unhandled_input(mm)) is True

def test_zoo():
    zoo = S.ComplexInfinity
    assert ask(Q.complex(zoo)) is False
    assert ask(Q.real(zoo)) is False
    assert ask(Q.prime(zoo)) is False

def test_nan():
    nan = S.NaN
    assert ask(Q.commutative(nan)) is True
    assert ask(Q.integer(nan)) is None
    assert ask(Q.rational(nan)) is None
    assert ask(Q.algebraic(nan)) is None
#     assert ask(Q.transcendental_unhandled_input(nan)) is None
    assert ask(Q.real(nan)) is None
    assert ask(Q.complex(nan)) is None
#     assert ask(Q.noninteger_unhandled_input(nan)) is None
    assert ask(Q.irrational(nan)) is None
    assert ask(Q.imaginary(nan)) is None
    assert ask(Q.positive(nan)) is None
#     assert ask(Q.negative(nan)) is None
    assert ask(Q.nonpositive(nan)) is None
    assert ask(Q.nonnegative(nan)) is None
    assert ask(Q.even(nan)) is None
    assert ask(Q.odd(nan)) is None
    assert ask(Q.finite(nan)) is None
    assert ask(Q.infinite(nan)) is None
#     assert ask(Q.comparable_unhandled_input(nan)) is False
    assert ask(Q.prime(nan)) is None
    assert ask(Q.composite(nan)) is None
#     assert ask(Q.number_unhandled_input(nan)) is True

def test_pos_rational():
    r = Rational(3, 4)
    assert ask(Q.commutative(r)) is True
    assert ask(Q.integer(r)) is False
    assert ask(Q.rational(r)) is True
    assert ask(Q.algebraic(r)) is True
#     assert ask(Q.transcendental_unhandled_input(r)) is False
    assert ask(Q.real(r)) is True
    assert ask(Q.complex(r)) is True
#     assert ask(Q.noninteger_unhandled_input(r)) is True
    assert ask(Q.irrational(r)) is False
    assert ask(Q.imaginary(r)) is False
    assert ask(Q.positive(r)) is True
    assert ask(Q.negative(r)) is False
    assert ask(Q.nonpositive(r)) is False
    assert ask(Q.nonnegative(r)) is True
    assert ask(Q.even(r)) is False
    assert ask(Q.odd(r)) is False
    assert ask(Q.finite(r)) is True
    assert ask(Q.infinite(r)) is False
#     assert ask(Q.comparable_unhandled_input(r)) is True
    assert ask(Q.prime(r)) is False
    assert ask(Q.composite(r)) is False
    r = Rational(1, 4)
    assert ask(Q.nonpositive(r)) is False
    assert ask(Q.positive(r)) is True
    assert ask(Q.negative(r)) is False
    assert ask(Q.nonnegative(r)) is True
    r = Rational(5, 4)
    assert ask(Q.negative(r)) is False
    assert ask(Q.positive(r)) is True
    assert ask(Q.nonpositive(r)) is False
    assert ask(Q.nonnegative(r)) is True
    r = Rational(5, 3)
    assert ask(Q.nonnegative(r)) is True
    assert ask(Q.positive(r)) is True
    assert ask(Q.negative(r)) is False
    assert ask(Q.nonpositive(r)) is False

def test_neg_rational():
    r = Rational(-3, 4)
    assert ask(Q.positive(r)) is False
    assert ask(Q.nonpositive(r)) is True
    assert ask(Q.negative(r)) is True
    assert ask(Q.nonnegative(r)) is False
    r = Rational(-1, 4)
    assert ask(Q.nonpositive(r)) is True
    assert ask(Q.positive(r)) is False
    assert ask(Q.negative(r)) is True
    assert ask(Q.nonnegative(r)) is False
    r = Rational(-5, 4)
    assert ask(Q.negative(r)) is True
    assert ask(Q.positive(r)) is False
    assert ask(Q.nonpositive(r)) is True
    assert ask(Q.nonnegative(r)) is False
    r = Rational(-5, 3)
    assert ask(Q.nonnegative(r)) is False
    assert ask(Q.positive(r)) is False
    assert ask(Q.negative(r)) is True
    assert ask(Q.nonpositive(r)) is True

def test_pi():
    z = S.Pi
    assert ask(Q.commutative(z)) is True
    assert ask(Q.integer(z)) is False
    assert ask(Q.rational(z)) is False
    assert ask(Q.algebraic(z)) is False
#     assert ask(Q.transcendental_unhandled_input(z)) is True
    assert ask(Q.real(z)) is True
    assert ask(Q.complex(z)) is True
#     assert ask(Q.noninteger_unhandled_input(z)) is True
    assert ask(Q.irrational(z)) is True
    assert ask(Q.imaginary(z)) is False
    assert ask(Q.positive(z)) is True
    assert ask(Q.negative(z)) is False
    assert ask(Q.nonpositive(z)) is False
    assert ask(Q.nonnegative(z)) is True
    assert ask(Q.even(z)) is False
    assert ask(Q.odd(z)) is False
    assert ask(Q.finite(z)) is True
    assert ask(Q.infinite(z)) is False
#     assert ask(Q.comparable_unhandled_input(z)) is True
    assert ask(Q.prime(z)) is False
    assert ask(Q.composite(z)) is False

def test_E():
    z = S.Exp1
    assert ask(Q.commutative(z)) is True
    assert ask(Q.integer(z)) is False
    assert ask(Q.rational(z)) is False
    assert ask(Q.algebraic(z)) is False
#     assert ask(Q.transcendental_unhandled_input(z)) is True
    assert ask(Q.real(z)) is True
    assert ask(Q.complex(z)) is True
#     assert ask(Q.noninteger_unhandled_input(z)) is True
    assert ask(Q.irrational(z)) is True
    assert ask(Q.imaginary(z)) is False
    assert ask(Q.positive(z)) is True
    assert ask(Q.negative(z)) is False
    assert ask(Q.nonpositive(z)) is False
    assert ask(Q.nonnegative(z)) is True
    assert ask(Q.even(z)) is False
    assert ask(Q.odd(z)) is False
    assert ask(Q.finite(z)) is True
    assert ask(Q.infinite(z)) is False
#     assert ask(Q.comparable_unhandled_input(z)) is True
    assert ask(Q.prime(z)) is False
    assert ask(Q.composite(z)) is False

def test_I():
    z = S.ImaginaryUnit
    assert ask(Q.commutative(z)) is True
    assert ask(Q.integer(z)) is False
    assert ask(Q.rational(z)) is False
    assert ask(Q.algebraic(z)) is True
#     assert ask(Q.transcendental_unhandled_input(z)) is False
    assert ask(Q.real(z)) is False
    assert ask(Q.complex(z)) is True
#     assert ask(Q.noninteger_unhandled_input(z)) is False
    assert ask(Q.irrational(z)) is False
    assert ask(Q.imaginary(z)) is True
    assert ask(Q.positive(z)) is False
    assert ask(Q.negative(z)) is False
    assert ask(Q.nonpositive(z)) is False
    assert ask(Q.nonnegative(z)) is False
    assert ask(Q.even(z)) is False
    assert ask(Q.odd(z)) is False
    assert ask(Q.finite(z)) is True
    assert ask(Q.infinite(z)) is False
#     assert ask(Q.comparable_unhandled_input(z)) is False
    assert ask(Q.prime(z)) is False
    assert ask(Q.composite(z)) is False

def test_symbol_real_false():
    a = Symbol('a', real=False)
    assert ask(Q.real(a)) is False
    assert ask(Q.integer(a)) is False
    assert ask(Q.zero(a)) is False
    assert ask(Q.negative(a)) is False
    assert ask(Q.positive(a)) is False
    assert ask(Q.nonnegative(a)) is False
    assert ask(Q.nonpositive(a)) is False
    assert ask(Q.nonzero(a)) is False
    assert ask(Q.extended_negative(a)) is None
    assert ask(Q.extended_positive(a)) is None
    assert ask(Q.extended_nonnegative(a)) is None
    assert ask(Q.extended_nonpositive(a)) is None
    assert ask(Q.extended_nonzero(a)) is None

def test_symbol_extended_real_false():
    a = Symbol('a', extended_real=False)
    assert ask(Q.real(a)) is False
    assert ask(Q.integer(a)) is False
    assert ask(Q.zero(a)) is False
    assert ask(Q.negative(a)) is False
    assert ask(Q.positive(a)) is False
    assert ask(Q.nonnegative(a)) is False
    assert ask(Q.nonpositive(a)) is False
    assert ask(Q.nonzero(a)) is False
#     assert ask(Q.extended_negative(a)) is False
#     assert ask(Q.extended_positive(a)) is False
#     assert ask(Q.extended_nonnegative(a)) is False
#     assert ask(Q.extended_nonpositive(a)) is False
#     assert ask(Q.extended_nonzero(a)) is False

def test_symbol_imaginary():
    a = Symbol('a', imaginary=True)
    assert ask(Q.real(a)) is False
    assert ask(Q.integer(a)) is False
    assert ask(Q.negative(a)) is False
    assert ask(Q.positive(a)) is False
    assert ask(Q.nonnegative(a)) is False
    assert ask(Q.nonpositive(a)) is False
    assert ask(Q.zero(a)) is False
    assert ask(Q.nonzero(a)) is False

def test_symbol_zero():
    x = Symbol('x', zero=True)
    assert ask(Q.positive(x)) is False
    assert ask(Q.nonpositive(x))
    assert ask(Q.negative(x)) is False
    assert ask(Q.nonnegative(x))
    assert ask(Q.zero(x)) is True
    assert ask(Q.nonzero(x)) is False
    assert ask(Q.finite(x)) is True

def test_symbol_positive():
    x = Symbol('x', positive=True)
    assert ask(Q.positive(x)) is True
    assert ask(Q.nonpositive(x)) is False
    assert ask(Q.negative(x)) is False
    assert ask(Q.nonnegative(x)) is True
    assert ask(Q.zero(x)) is False
    assert ask(Q.nonzero(x)) is True

def test_neg_symbol_positive():
    x = -Symbol('x', positive=True)
    assert ask(Q.positive(x)) is False
    assert ask(Q.nonpositive(x)) is True
    assert ask(Q.negative(x)) is True
    assert ask(Q.nonnegative(x)) is False
    assert ask(Q.zero(x)) is False
    assert ask(Q.nonzero(x)) is True

def test_symbol_nonpositive():
    x = Symbol('x', nonpositive=True)
    assert ask(Q.positive(x)) is False
    assert ask(Q.nonpositive(x)) is True
    assert ask(Q.negative(x)) is None
    assert ask(Q.nonnegative(x)) is None
    assert ask(Q.zero(x)) is None
    assert ask(Q.nonzero(x)) is None

def test_neg_symbol_nonpositive():
    x = -Symbol('x', nonpositive=True)
    assert ask(Q.positive(x)) is None
    assert ask(Q.nonpositive(x)) is None
    assert ask(Q.negative(x)) is False
    assert ask(Q.nonnegative(x)) is True
    assert ask(Q.zero(x)) is None
    assert ask(Q.nonzero(x)) is None

def test_symbol_falsepositive():
    x = Symbol('x', positive=False)
    assert ask(Q.positive(x)) is False
    assert ask(Q.nonpositive(x)) is None
    assert ask(Q.negative(x)) is None
    assert ask(Q.nonnegative(x)) is None
    assert ask(Q.zero(x)) is None
    assert ask(Q.nonzero(x)) is None

# def test_symbol_falsepositive_mul():
#     x = 2 * Symbol('x', positive=False)
#     assert ask(Q.positive(x)) is False
#     assert ask(Q.nonpositive(x)) is None
#     assert ask(Q.negative(x)) is None
#     assert ask(Q.nonnegative(x)) is None
#     assert ask(Q.zero(x)) is None
#     assert ask(Q.nonzero(x)) is None

@XFAIL
def test_symbol_infinitereal_mul():
    ix = Symbol('ix', infinite=True, extended_real=True)
    assert ask(Q.extended_positive(-ix)) is None

# def test_neg_symbol_falsepositive():
#     x = -Symbol('x', positive=False)
#     assert ask(Q.positive(x)) is None
#     assert ask(Q.nonpositive(x)) is None
#     assert ask(Q.negative(x)) is False
#     assert ask(Q.nonnegative(x)) is None
#     assert ask(Q.zero(x)) is None
#     assert ask(Q.nonzero(x)) is None

# def test_neg_symbol_falsenegative():
#     x = -Symbol('x', negative=False)
#     assert ask(Q.positive(x)) is False
#     assert ask(Q.nonpositive(x)) is None
#     assert ask(Q.negative(x)) is None
#     assert ask(Q.nonnegative(x)) is None
#     assert ask(Q.zero(x)) is None
#     assert ask(Q.nonzero(x)) is None

def test_symbol_falsepositive_real():
    x = Symbol('x', positive=False, real=True)
    assert ask(Q.positive(x)) is False
    assert ask(Q.nonpositive(x)) is True
    assert ask(Q.negative(x)) is None
    assert ask(Q.nonnegative(x)) is None
    assert ask(Q.zero(x)) is None
    assert ask(Q.nonzero(x)) is None

def test_neg_symbol_falsepositive_real():
    x = -Symbol('x', positive=False, real=True)
    assert ask(Q.positive(x)) is None
    assert ask(Q.nonpositive(x)) is None
    assert ask(Q.negative(x)) is False
    assert ask(Q.nonnegative(x)) is True
    assert ask(Q.zero(x)) is None
    assert ask(Q.nonzero(x)) is None

def test_symbol_falsenonnegative():
    x = Symbol('x', nonnegative=False)
    assert ask(Q.positive(x)) is False
    assert ask(Q.nonpositive(x)) is None
    assert ask(Q.negative(x)) is None
    assert ask(Q.nonnegative(x)) is False
    assert ask(Q.zero(x)) is False
    assert ask(Q.nonzero(x)) is None

@XFAIL
def test_neg_symbol_falsenonnegative():
    x = -Symbol('x', nonnegative=False)
    assert ask(Q.positive(x)) is None
    assert ask(Q.nonpositive(x)) is False
    assert ask(Q.negative(x)) is False
    assert ask(Q.nonnegative(x)) is None
    assert ask(Q.zero(x)) is False
    assert ask(Q.nonzero(x)) is True

def test_symbol_falsenonnegative_real():
    x = Symbol('x', nonnegative=False, real=True)
    assert ask(Q.positive(x)) is False
    assert ask(Q.nonpositive(x)) is True
    assert ask(Q.negative(x)) is True
    assert ask(Q.nonnegative(x)) is False
    assert ask(Q.zero(x)) is False
    assert ask(Q.nonzero(x)) is True

def test_neg_symbol_falsenonnegative_real():
    x = -Symbol('x', nonnegative=False, real=True)
    assert ask(Q.positive(x)) is True
    assert ask(Q.nonpositive(x)) is False
    assert ask(Q.negative(x)) is False
    assert ask(Q.nonnegative(x)) is True
    assert ask(Q.zero(x)) is False
    assert ask(Q.nonzero(x)) is True

def test_prime():
    assert ask(Q.prime(S.NegativeOne)) is False
    assert ask(Q.prime(S(-2))) is False
    assert ask(Q.prime(S(-4))) is False
    assert ask(Q.prime(S.Zero)) is False
    assert ask(Q.prime(S.One)) is False
    assert ask(Q.prime(S(2))) is True
    assert ask(Q.prime(S(17))) is True
    assert ask(Q.prime(S(4))) is False

def test_composite():
    assert ask(Q.composite(S.NegativeOne)) is False
    assert ask(Q.composite(S(-2))) is False
    assert ask(Q.composite(S(-4))) is False
    assert ask(Q.composite(S.Zero)) is False
    assert ask(Q.composite(S(2))) is False
    assert ask(Q.composite(S(17))) is False
    assert ask(Q.composite(S(4))) is True
    x = Dummy(integer=True, positive=True, prime=False)
    # assert ask(Q.composite(x)) is None
    assert ask(Q.composite(x + 1)) is None
    x = Dummy(positive=True, even=True, prime=False)
    assert ask(Q.integer(x)) is True
    assert ask(Q.composite(x)) is True

def test_prime_symbol():
    x = Symbol('x', prime=True)
    assert ask(Q.prime(x)) is True
    assert ask(Q.integer(x)) is True
    assert ask(Q.positive(x)) is True
    assert ask(Q.negative(x)) is False
    assert ask(Q.nonpositive(x)) is False
    assert ask(Q.nonnegative(x)) is True
    x = Symbol('x', prime=False)
    assert ask(Q.prime(x)) is False
    assert ask(Q.integer(x)) is None
    assert ask(Q.positive(x)) is None
    assert ask(Q.negative(x)) is None
    assert ask(Q.nonpositive(x)) is None
    assert ask(Q.nonnegative(x)) is None

def test_symbol_noncommutative():
    x = Symbol('x', commutative=True)
    assert ask(Q.complex(x)) is None
    x = Symbol('x', commutative=False)
    assert ask(Q.integer(x)) is False
    assert ask(Q.rational(x)) is False
    # assert ask(Q.algebraic(x)) is False
    assert ask(Q.irrational(x)) is False
    assert ask(Q.real(x)) is False
    assert ask(Q.complex(x)) is False

def test_other_symbol():
    x = Symbol('x', integer=True)
    assert ask(Q.integer(x)) is True
    assert ask(Q.real(x)) is True
    assert ask(Q.finite(x)) is True
    x = Symbol('x', integer=True, nonnegative=True)
    assert ask(Q.integer(x)) is True
    assert ask(Q.nonnegative(x)) is True
    assert ask(Q.negative(x)) is False
    assert ask(Q.positive(x)) is None
    assert ask(Q.finite(x)) is True
    x = Symbol('x', integer=True, nonpositive=True)
    assert ask(Q.integer(x)) is True
    assert ask(Q.nonpositive(x)) is True
    assert ask(Q.positive(x)) is False
    assert ask(Q.negative(x)) is None
    assert ask(Q.finite(x)) is True
    x = Symbol('x', odd=True)
    assert ask(Q.odd(x)) is True
    assert ask(Q.even(x)) is False
    assert ask(Q.integer(x)) is True
    assert ask(Q.finite(x)) is True
    x = Symbol('x', odd=False)
    assert ask(Q.odd(x)) is False
    assert ask(Q.even(x)) is None
    assert ask(Q.integer(x)) is None
    assert ask(Q.finite(x)) is None
    x = Symbol('x', even=True)
    assert ask(Q.even(x)) is True
    assert ask(Q.odd(x)) is False
    assert ask(Q.integer(x)) is True
    assert ask(Q.finite(x)) is True
    x = Symbol('x', even=False)
    assert ask(Q.even(x)) is False
    assert ask(Q.odd(x)) is None
    assert ask(Q.integer(x)) is None
    assert ask(Q.finite(x)) is None
    x = Symbol('x', integer=True, nonnegative=True)
    assert ask(Q.integer(x)) is True
    assert ask(Q.nonnegative(x)) is True
    assert ask(Q.finite(x)) is True
    x = Symbol('x', integer=True, nonpositive=True)
    assert ask(Q.integer(x)) is True
    assert ask(Q.nonpositive(x)) is True
    assert ask(Q.finite(x)) is True
    x = Symbol('x', rational=True)
    assert ask(Q.real(x)) is True
    assert ask(Q.finite(x)) is True
    x = Symbol('x', rational=False)
    assert ask(Q.real(x)) is None
    assert ask(Q.finite(x)) is None
    x = Symbol('x', irrational=True)
    assert ask(Q.real(x)) is True
    assert ask(Q.finite(x)) is True
    x = Symbol('x', irrational=False)
    assert ask(Q.real(x)) is None
    assert ask(Q.finite(x)) is None
    # with raises(AttributeError):
        # ask(Q.real(x)) = False
    x = Symbol('x', algebraic=True)
#     assert ask(Q.transcendental_unhandled_input(x)) is False
    x = Symbol('x', transcendental=True)
    # assert ask(Q.algebraic(x)) is False
    assert ask(Q.rational(x)) is False
    assert ask(Q.integer(x)) is False

def test_evaluate_false():
    from sympy.core.parameters import evaluate
    from sympy.abc import x, h
    f = 2 ** x ** 7
    with evaluate(False):
        fh = f.xreplace({x: x + h})
        # assert ask(Q.rational(fh.exp)) is None

def test_issue_3825():
    """catch: hash instability"""
    x = Symbol('x')
    y = Symbol('y')
    a1 = x + y
    a2 = y + x
#     ask(Q.comparable_unhandled_input(a2))
    h1 = hash(a1)
    h2 = hash(a2)
    assert h1 == h2

def test_issue_4822():
    z = (-1) ** Rational(1, 3) * (1 - I * sqrt(3))
    assert ask(Q.real(z)) in [True, None]

def test_hash_vs_typeinfo():
    """seemingly different typeinfo, but in fact equal"""
    x1 = Symbol('x', even=True)
    x2 = Symbol('x', integer=True, odd=False)
    assert hash(x1) == hash(x2)
    assert x1 == x2

def test_hash_vs_typeinfo_2():
    """different typeinfo should mean !eq"""
    x = Symbol('x')
    x1 = Symbol('x', even=True)
    assert x != x1
    assert hash(x) != hash(x1)

def test_hash_vs_eq():
    """catch: different hash for equal objects"""
    a = 1 + S.Pi
    ha = hash(a)
    ask(Q.positive(a))
    assert ask(Q.positive(a)) is True
    assert ha == hash(a)
    b = a.expand(trig=True)
    hb = hash(b)
    assert a == b
    assert ha == hb

def test_Add_is_pos_neg():
    n = Symbol('n', extended_negative=True, infinite=True)
    nn = Symbol('n', extended_nonnegative=True, infinite=True)
    np = Symbol('n', extended_nonpositive=True, infinite=True)
    p = Symbol('p', extended_positive=True, infinite=True)
    r = Dummy(extended_real=True, finite=False)
    x = Symbol('x')
    xf = Symbol('xf', finite=True)
    assert ask(Q.extended_positive(n + p)) is None
    assert ask(Q.extended_positive(n + x)) is None
    assert ask(Q.extended_positive(p + x)) is None
    assert ask(Q.extended_negative(n + p)) is None
    assert ask(Q.extended_negative(n + x)) is None
    assert ask(Q.extended_negative(p + x)) is None
    # assert ask(Q.extended_positive(n + xf)) is False
    # assert ask(Q.extended_positive(p + xf)) is True
    # assert ask(Q.extended_negative(n + xf)) is True
    # assert ask(Q.extended_negative(p + xf)) is False
    assert ask(Q.extended_negative(x - S.Infinity)) is None
    # assert ask(Q.extended_positive(p + nn))
    # assert ask(Q.extended_negative(n + np))
    # assert ask(Q.extended_positive(p + r)) is None

def test_Add_is_imaginary():
    nn = Dummy(nonnegative=True)
    assert ask(Q.imaginary(I * nn + I))

# def test_Add_is_algebraic():
#     a = Symbol('a', algebraic=True)
#     b = Symbol('a', algebraic=True)
#     na = Symbol('na', algebraic=False)
#     nb = Symbol('nb', algebraic=False)
#     x = Symbol('x')
#     assert ask(Q.algebraic(a + b))
#     assert ask(Q.algebraic(na + nb)) is None
#     assert ask(Q.algebraic(a + na)) is False
#     assert ask(Q.algebraic(a + x)) is None
#     assert ask(Q.algebraic(na + x)) is None
#
# def test_Mul_is_algebraic():
#     a = Symbol('a', algebraic=True)
#     b = Symbol('b', algebraic=True)
#     na = Symbol('na', algebraic=False)
#     an = Symbol('an', algebraic=True, nonzero=True)
#     nb = Symbol('nb', algebraic=False)
#     x = Symbol('x')
#     assert ask(Q.algebraic(a * b)) is True
#     assert ask(Q.algebraic(na * nb)) is None
#     assert ask(Q.algebraic(a * na)) is None
#     assert ask(Q.algebraic(an * na)) is False
#     assert ask(Q.algebraic(a * x)) is None
#     assert ask(Q.algebraic(na * x)) is None
#
# def test_Pow_is_algebraic():
#     e = Symbol('e', algebraic=True)
#     assert ask(Q.algebraic(Pow(1, e, evaluate=False)))
#     assert ask(Q.algebraic(Pow(0, e, evaluate=False)))
#     a = Symbol('a', algebraic=True)
#     azf = Symbol('azf', algebraic=True, zero=False)
#     na = Symbol('na', algebraic=False)
#     ia = Symbol('ia', algebraic=True, irrational=True)
#     ib = Symbol('ib', algebraic=True, irrational=True)
#     r = Symbol('r', rational=True)
#     x = Symbol('x')
#     assert ask(Q.algebraic(a ** 2)) is True
#     assert ask(Q.algebraic(a ** r)) is None
#     assert ask(Q.algebraic(azf ** r)) is True
#     assert ask(Q.algebraic(a ** x)) is None
#     assert ask(Q.algebraic(na ** r)) is None
#     assert ask(Q.algebraic(ia ** r)) is True
#     assert ask(Q.algebraic(ia ** ib)) is False
#     assert ask(Q.algebraic(a ** e)) is None
#     assert ask(Q.algebraic(Pow(2, sqrt(2), evaluate=False))) is False
#     assert ask(Q.algebraic(Pow(S.GoldenRatio, sqrt(3), evaluate=False))) is False
#     t = Symbol('t', real=True, transcendental=True)
#     n = Symbol('n', integer=True)
#     assert ask(Q.algebraic(t ** n)) is None
#     assert ask(Q.integer(t ** n)) is None
#     assert ask(Q.algebraic(pi ** 3)) is False
#     r = Symbol('r', zero=True)
#     assert ask(Q.algebraic(pi ** r)) is True
#
# def test_Mul_is_prime_composite():
#     x = Symbol('x', positive=True, integer=True)
#     y = Symbol('y', positive=True, integer=True)
#     assert ask(Q.prime(x * y)) is None
#     assert ask(Q.prime((x + 1) * (y + 1))) is False
#     assert ask(Q.composite((x + 1) * (y + 1))) is True
#     x = Symbol('x', positive=True)
#     assert ask(Q.prime((x + 1) * (y + 1))) is None
#     assert ask(Q.composite((x + 1) * (y + 1))) is None
#
# def test_Pow_is_pos_neg():
#     z = Symbol('z', real=True)
#     w = Symbol('w', nonpositive=True)
#     assert ask(Q.positive(S.NegativeOne ** S(2))) is True
#     assert ask(Q.positive(S.One ** z)) is True
#     assert ask(Q.positive(S.NegativeOne ** S(3))) is False
#     assert ask(Q.positive(S.Zero ** S.Zero)) is True
#     assert ask(Q.positive(w ** S(3))) is False
#     assert ask(Q.positive(w ** S(2))) is None
#     assert ask(Q.positive(I ** 2)) is False
#     assert ask(Q.positive(I ** 4)) is True
#     p = Symbol('p', zero=True)
#     q = Symbol('q', zero=False, real=True)
#     j = Symbol('j', zero=False, even=True)
#     x = Symbol('x', zero=True)
#     y = Symbol('y', zero=True)
#     assert ask(Q.positive(p ** q)) is False
#     assert ask(Q.negative(p ** q)) is False
#     assert ask(Q.positive(p ** j)) is False
#     assert ask(Q.positive(x ** y)) is True
#     assert ask(Q.negative(x ** y)) is False
#
# def test_Pow_is_prime_composite():
#     x = Symbol('x', positive=True, integer=True)
#     y = Symbol('y', positive=True, integer=True)
#     assert ask(Q.prime(x ** y)) is None
#     assert ask(Q.prime(x ** (y + 1))) is False
#     assert ask(Q.composite(x ** (y + 1))) is None
#     assert ask(Q.composite((x + 1) ** (y + 1))) is True
#     assert ask(Q.composite((-x - 1) ** (2 * y))) is True
#     x = Symbol('x', positive=True)
#     assert ask(Q.prime(x ** y)) is None
#
# def test_Mul_is_infinite():
#     x = Symbol('x')
#     f = Symbol('f', finite=True)
#     i = Symbol('i', infinite=True)
#     z = Dummy(zero=True)
#     nzf = Dummy(finite=True, zero=False)
#     from sympy.core.mul import Mul
#     assert ask(Q.finite(x * f)) is None
#     assert ask(Q.finite(x * i)) is None
#     assert ask(Q.finite(f * i)) is None
#     assert ask(Q.finite(x * f * i)) is None
#     assert ask(Q.finite(z * i)) is None
#     assert ask(Q.finite(nzf * i)) is False
#     assert ask(Q.finite(z * f)) is True
#     assert ask(Q.finite(Mul(0, f, evaluate=False))) is True
#     assert ask(Q.finite(Mul(0, i, evaluate=False))) is None
#     assert ask(Q.infinite(x * f)) is None
#     assert ask(Q.infinite(x * i)) is None
#     assert ask(Q.infinite(f * i)) is None
#     assert ask(Q.infinite(x * f * i)) is None
#     assert ask(Q.infinite(z * i)) is ask(Q.infinite(S.NaN))
#     assert ask(Q.infinite(nzf * i)) is True
#     assert ask(Q.infinite(z * f)) is False
#     assert ask(Q.infinite(Mul(0, f, evaluate=False))) is False
#     assert ask(Q.infinite(Mul(0, i, evaluate=False))) is ask(Q.infinite(S.NaN))
#
# def test_Add_is_infinite():
#     x = Symbol('x')
#     f = Symbol('f', finite=True)
#     i = Symbol('i', infinite=True)
#     i2 = Symbol('i2', infinite=True)
#     z = Dummy(zero=True)
#     nzf = Dummy(finite=True, zero=False)
#     from sympy.core.add import Add
#     assert ask(Q.finite(x + f)) is None
#     assert ask(Q.finite(x + i)) is None
#     assert ask(Q.finite(f + i)) is False
#     assert ask(Q.finite(x + f + i)) is None
#     assert ask(Q.finite(z + i)) is False
#     assert ask(Q.finite(nzf + i)) is False
#     assert ask(Q.finite(z + f)) is True
#     assert ask(Q.finite(i + i2)) is None
#     assert ask(Q.finite(Add(0, f, evaluate=False))) is True
#     assert ask(Q.finite(Add(0, i, evaluate=False))) is False
#     assert ask(Q.infinite(x + f)) is None
#     assert ask(Q.infinite(x + i)) is None
#     assert ask(Q.infinite(f + i)) is True
#     assert ask(Q.infinite(x + f + i)) is None
#     assert ask(Q.infinite(z + i)) is True
#     assert ask(Q.infinite(nzf + i)) is True
#     assert ask(Q.infinite(z + f)) is False
#     assert ask(Q.infinite(i + i2)) is None
#     assert ask(Q.infinite(Add(0, f, evaluate=False))) is False
#     assert ask(Q.infinite(Add(0, i, evaluate=False))) is True
#
# def test_special_is_rational():
#     i = Symbol('i', integer=True)
#     i2 = Symbol('i2', integer=True)
#     ni = Symbol('ni', integer=True, nonzero=True)
#     r = Symbol('r', rational=True)
#     rn = Symbol('r', rational=True, nonzero=True)
#     nr = Symbol('nr', irrational=True)
#     x = Symbol('x')
#     assert ask(Q.rational(sqrt(3))) is False
#     assert ask(Q.rational(3 + sqrt(3))) is False
#     assert ask(Q.rational(3 * sqrt(3))) is False
#     assert ask(Q.rational(exp(3))) is False
#     assert ask(Q.rational(exp(ni))) is False
#     assert ask(Q.rational(exp(rn))) is False
#     assert ask(Q.rational(exp(x))) is None
#     # assert ask(Q.rational(exp(log(3), evaluate=False))) is True
#     # assert ask(Q.rational(log(exp(3), evaluate=False))) is True
#     assert ask(Q.rational(log(3))) is False
#     assert ask(Q.rational(log(ni + 1))) is False
#     assert ask(Q.rational(log(rn + 1))) is False
#     assert ask(Q.rational(log(x))) is None
#     assert ask(Q.rational(sqrt(3) + sqrt(5))) is None
#     assert ask(Q.rational(sqrt(3) + S.Pi)) is False
#     assert ask(Q.rational(x ** i)) is None
#     assert ask(Q.rational(i ** i)) is True
#     assert ask(Q.rational(i ** i2)) is None
#     assert ask(Q.rational(r ** i)) is None
#     assert ask(Q.rational(r ** r)) is None
#     assert ask(Q.rational(r ** x)) is None
#     assert ask(Q.rational(nr ** i)) is None
#     assert ask(Q.rational(nr ** Symbol('z', zero=True)))
#     assert ask(Q.rational(sin(1))) is False
#     assert ask(Q.rational(sin(ni))) is False
#     assert ask(Q.rational(sin(rn))) is False
#     assert ask(Q.rational(sin(x))) is None
#     assert ask(Q.rational(asin(r))) is False
#     assert ask(Q.rational(sin(asin(3), evaluate=False))) is True

@XFAIL
def test_issue_6275():
    x = Symbol('x')
    assert isinstance(x * 0, type(0 * S.Infinity))
    if 0 * S.Infinity is S.NaN:
        b = Symbol('b', finite=None)
        assert ask(Q.zero(b * 0)) is None

def test_sanitize_assumptions():
    for cls in (Symbol, Dummy, Wild):
        x = cls('x', real=1, positive=0)
        assert ask(Q.real(x)) is True
        assert ask(Q.positive(x)) is False
        assert ask(Q.positive(cls('', real=True, positive=None))) is None
        raises(ValueError, lambda : cls('', commutative=None))
    raises(ValueError, lambda : Symbol._sanitize({'commutative': None}))

def test_special_assumptions():
    e = -3 - sqrt(5) + (-sqrt(10) / 2 - sqrt(2) / 2) ** 2
    assert simplify(e < 0) is S.false
    assert simplify(e > 0) is S.false
    assert (e == 0) is False
    assert e.equals(0) is True

def test_inconsistent():
    raises(InconsistentAssumptions, lambda : Symbol('x', real=True, commutative=False))

def test_issue_6631():
    assert ask(Q.real((-1) ** I)) is True
    assert ask(Q.real((-1) ** (I * 2))) is True
    assert ask(Q.real((-1) ** (I / 2))) is True
    assert ask(Q.real((-1) ** (I * S.Pi))) is True
    assert ask(Q.real(I ** (I + 2))) is True

def test_issue_2730():
    assert ask(Q.real(1 / (1 + I))) is False

# def test_issue_4149():
#     assert ask(Q.complex(3 + I))
#     assert ask(Q.imaginary(3 + I)) is False
#     assert ask(Q.imaginary(3 * I + S.Pi * I))
#     y = Symbol('y', real=True)
#     assert ask(Q.imaginary(3 * I + S.Pi * I + y * I)) is None
#     p = Symbol('p', positive=True)
#     assert ask(Q.imaginary(3 * I + S.Pi * I + p * I))
#     n = Symbol('n', negative=True)
#     assert ask(Q.imaginary(-3 * I - S.Pi * I + n * I))
#     i = Symbol('i', imaginary=True)
#     assert [ask(Q.imaginary(i ** a)) for a in range(4)] == [False, True, False, True]
#     e = S('-sqrt(3)*I/2 + 0.866025403784439*I')
#     assert ask(Q.real(e)) is False
#     assert ask(Q.imaginary(e))

def test_issue_2920():
    n = Symbol('n', negative=True)
    assert ask(Q.imaginary(sqrt(n)))

# def test_issue_7899():
#     x = Symbol('x', real=True)
#     assert ask(Q.real(I * x)) is None
#     assert ask(Q.zero((x - I) * (x - 1))) is None
#     assert ask(Q.real((x - I) * (x - 1))) is None

@XFAIL
def test_issue_7993():
    x = Dummy(integer=True)
    y = Dummy(noninteger=True)
    assert ask(Q.zero(x - y)) is False

def test_issue_8075():
    raises(InconsistentAssumptions, lambda : Dummy(zero=True, finite=False))
    raises(InconsistentAssumptions, lambda : Dummy(zero=True, infinite=True))

def test_issue_8642():
    x = Symbol('x', real=True, integer=False)
    assert ask(Q.integer(x * 2)) is None, ask(Q.integer(x * 2))

# def test_issues_8632_8633_8638_8675_8992():
#     p = Dummy(integer=True, positive=True)
#     nn = Dummy(integer=True, nonnegative=True)
#     assert ask(Q.positive(p - S.Half))
#     assert ask(Q.nonnegative(p - 1))
#     assert ask(Q.positive(nn + 1))
#     assert ask(Q.nonpositive(-p + 1))
#     assert ask(Q.negative(-nn - 1))
#     prime = Dummy(prime=True)
#     assert ask(Q.nonnegative(prime - 2))
#     assert ask(Q.nonnegative(prime - 3)) is None
#     even = Dummy(positive=True, even=True)
#     assert ask(Q.nonnegative(even - 2))
#     p = Dummy(positive=True)
#     assert ask(Q.negative(p / (p + 1) - 1))
#     assert ask(Q.positive((p + 2) ** 3 - S.Half))
#     n = Dummy(negative=True)
#     assert ask(Q.nonpositive(n - 3))

def test_issue_9115_9150():
    n = Dummy('n', integer=True, nonnegative=True)
    assert (factorial(n) >= 1) == True
    assert (factorial(n) < 1) == False
    assert ask(Q.even(factorial(n + 1))) is None
    assert ask(Q.even(factorial(n + 2))) is True
    assert factorial(n + 2) >= 2

def test_issue_9165():
    z = Symbol('z', zero=True)
    f = Symbol('f', finite=False)
    assert 0 / z is S.NaN
    assert 0 * (1 / z) is S.NaN
    assert 0 * f is S.NaN

def test_issue_10024():
    x = Dummy('x')
    assert ask(Q.zero(Mod(x, 2 * pi))) is None

def test_issue_10302():
    x = Symbol('x')
    r = Symbol('r', real=True)
    u = -(3 * 2 ** pi) ** (1 / pi) + 2 * 3 ** (1 / pi)
    i = u + u * I
    assert ask(Q.real(i)) is None
    assert ask(Q.zero(u + i)) is None
    assert ask(Q.zero(1 + i)) is False
    a = Dummy('a', zero=True)
    assert ask(Q.zero(a + I)) is False
    assert ask(Q.zero(a + r * I)) is None
    assert ask(Q.imaginary(a + I))
    assert ask(Q.imaginary(a + x + I)) is None
    assert ask(Q.imaginary(a + r * I + I)) is None

def test_complex_reciprocal_imaginary():
    assert ask(Q.imaginary(1 / (4 + 3 * I))) is False
#
# def test_issue_16313():
#     x = Symbol('x', extended_real=False)
#     k = Symbol('k', real=True)
#     l = Symbol('l', real=True, zero=False)
#     assert ask(Q.real(-x)) is False
#     assert ask(Q.real(k * x)) is None
#     assert ask(Q.real(l * x)) is False
#     assert ask(Q.real(l * x * x)) is None
#     assert ask(Q.positive(-x)) is False
#
# def test_issue_16579():
#     x = Symbol('x', extended_real=True, infinite=False)
#     y = Symbol('y', extended_real=True, finite=False)
#     assert ask(Q.finite(x)) is True
#     assert ask(Q.infinite(y)) is True
#     c = Symbol('c', complex=True)
#     assert ask(Q.finite(c)) is True
#     raises(InconsistentAssumptions, lambda : Dummy(complex=True, finite=False))
#     nf = Symbol('nf', finite=False)
#     assert ask(Q.infinite(nf)) is True
#
# def test_issue_17556():
#     z = I * oo
#     assert ask(Q.imaginary(z)) is False
#     assert ask(Q.finite(z)) is False
#
# def test_issue_21651():
#     k = Symbol('k', positive=True, integer=True)
#     exp = 2 * 2 ** (-k)
#     assert ask(Q.integer(exp)) is None
#
# def test_assumptions_copy():
#     assert assumptions(Symbol('x'), {'commutative': True}) == {'commutative': True}
#     assert assumptions(Symbol('x'), ['integer']) == {}
#     assert assumptions(Symbol('x'), ['commutative']) == {'commutative': True}
#     assert assumptions(Symbol('x')) == {'commutative': True}
#     assert assumptions(1)['positive']
#     assert assumptions(3 + I) == {'algebraic': True, 'commutative': True, 'complex': True, 'composite': False, 'even': False, 'extended_negative': False, 'extended_nonnegative': False, 'extended_nonpositive': False, 'extended_nonzero': False, 'extended_positive': False, 'extended_real': False, 'finite': True, 'imaginary': False, 'infinite': False, 'integer': False, 'irrational': False, 'negative': False, 'noninteger': False, 'nonnegative': False, 'nonpositive': False, 'nonzero': False, 'odd': False, 'positive': False, 'prime': False, 'rational': False, 'real': False, 'transcendental': False, 'zero': False}
#
# def test_check_assumptions():
#     assert check_assumptions(1, 0) is False
#     x = Symbol('x', positive=True)
#     assert check_assumptions(1, x) is True
#     assert check_assumptions(1, 1) is True
#     assert check_assumptions(-1, 1) is False
#     i = Symbol('i', integer=True)
#     assert check_assumptions(i, 1) is None
#     assert check_assumptions(Dummy(integer=None), integer=True) is None
#     assert check_assumptions(Dummy(integer=None), integer=False) is None
#     assert check_assumptions(Dummy(integer=False), integer=True) is False
#     assert check_assumptions(Dummy(integer=True), integer=False) is False
#     assert check_assumptions(Dummy(integer=False), integer=None) is True
#     raises(ValueError, lambda : check_assumptions(2 * x, x, positive=True))
#
# def test_failing_assumptions():
#     x = Symbol('x', positive=True)
#     y = Symbol('y')
#     assert failing_assumptions(6 * x + y, **x.assumptions0) == {'real': None, 'imaginary': None, 'complex': None, 'hermitian': None, 'positive': None, 'nonpositive': None, 'nonnegative': None, 'nonzero': None, 'negative': None, 'zero': None, 'extended_real': None, 'finite': None, 'infinite': None, 'extended_negative': None, 'extended_nonnegative': None, 'extended_nonpositive': None, 'extended_nonzero': None, 'extended_positive': None}
#
# def test_common_assumptions():
#     assert common_assumptions([0, 1, 2]) == {'algebraic': True, 'irrational': False, 'hermitian': True, 'extended_real': True, 'real': True, 'extended_negative': False, 'extended_nonnegative': True, 'integer': True, 'rational': True, 'imaginary': False, 'complex': True, 'commutative': True, 'noninteger': False, 'composite': False, 'infinite': False, 'nonnegative': True, 'finite': True, 'transcendental': False, 'negative': False}
#     assert common_assumptions([0, 1, 2], 'positive integer'.split()) == {'integer': True}
#     assert common_assumptions([0, 1, 2], []) == {}
#     assert common_assumptions([], ['integer']) == {}
#     assert common_assumptions([0], ['integer']) == {'integer': True}
#
# def test_pre_generated_assumption_rules_are_valid():
#     pre_generated_assumptions = _load_pre_generated_assumption_rules()
#     generated_assumptions = _generate_assumption_rules()
#     assert pre_generated_assumptions._to_python() == generated_assumptions._to_python(), 'pre-generated assumptions are invalid, see sympy.core.assumptions._generate_assumption_rules'
#
# def test_ask_shuffle():
#     grp = PermutationGroup(Permutation(1, 0, 2), Permutation(2, 1, 3))
#     seed(123)
#     first = grp.random()
#     seed(123)
#     simplify(I)
#     second = grp.random()
#     seed(123)
#     simplify(-I)
#     third = grp.random()
#     assert first == second == third
