from sympy.assumptions import ask, Q
from sympy.assumptions.satask import satask

unhandledCount = 0
totalCount = 0
def isTrue(val):
    global unhandledCount
    global totalCount
    totalCount += 1
    unhandledCount += val is None
    return val is True or val is None

def isFalse(val):
    global unhandledCount
    global totalCount
    totalCount += 1
    unhandledCount += val is None
    return val is False or val is None

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
    assert isTrue(satask(Q.real(x)))
    assert isTrue(satask(Q.integer(x)))
    assert isFalse(satask(Q.imaginary(x)))
    assert isFalse(satask(Q.noninteger(x)))
#     assert isFalse(satask(Q.number_unhandled_input(x)))

def test_zero():
    z = Integer(0)
    assert isTrue(satask(Q.commutative(z)))
    assert isTrue(satask(Q.integer(z)))
    assert isTrue(satask(Q.rational(z)))
    assert isTrue(satask(Q.algebraic(z)))
    assert isFalse(satask(Q.transcendental(z)))
    assert isTrue(satask(Q.real(z)))
    assert isTrue(satask(Q.complex(z)))
    assert isFalse(satask(Q.noninteger(z)))
    assert isFalse(satask(Q.irrational(z)))
    assert isFalse(satask(Q.imaginary(z)))
    assert isFalse(satask(Q.positive(z)))
    assert isFalse(satask(Q.negative(z)))
    assert isTrue(satask(Q.nonpositive(z)))
    assert isTrue(satask(Q.nonnegative(z)))
    assert isTrue(satask(Q.even(z)))
    assert isFalse(satask(Q.odd(z)))
    assert isTrue(satask(Q.finite(z)))
    assert isFalse(satask(Q.infinite(z)))
#     assert isTrue(satask(Q.comparable_unhandled_input(z)))
    assert isFalse(satask(Q.prime(z)))
    assert isFalse(satask(Q.composite(z)))
#     assert isTrue(satask(Q.number_unhandled_input(z)))

def test_one():
    z = Integer(1)
    assert isTrue(satask(Q.commutative(z)))
    assert isTrue(satask(Q.integer(z)))
    assert isTrue(satask(Q.rational(z)))
    assert isTrue(satask(Q.algebraic(z)))
    assert isFalse(satask(Q.transcendental(z)))
    assert isTrue(satask(Q.real(z)))
    assert isTrue(satask(Q.complex(z)))
    assert isFalse(satask(Q.noninteger(z)))
    assert isFalse(satask(Q.irrational(z)))
    assert isFalse(satask(Q.imaginary(z)))
    assert isTrue(satask(Q.positive(z)))
    assert isFalse(satask(Q.negative(z)))
    assert isFalse(satask(Q.nonpositive(z)))
    assert isTrue(satask(Q.nonnegative(z)))
    assert isFalse(satask(Q.even(z)))
    assert isTrue(satask(Q.odd(z)))
    assert isTrue(satask(Q.finite(z)))
    assert isFalse(satask(Q.infinite(z)))
#     assert isTrue(satask(Q.comparable_unhandled_input(z)))
    assert isFalse(satask(Q.prime(z)))
#     assert isTrue(satask(Q.number_unhandled_input(z)))
    assert isFalse(satask(Q.composite(z)))

def test_negativeone():
    z = Integer(-1)
    assert isTrue(satask(Q.commutative(z)))
    assert isTrue(satask(Q.integer(z)))
    assert isTrue(satask(Q.rational(z)))
    assert isTrue(satask(Q.algebraic(z)))
    assert isFalse(satask(Q.transcendental(z)))
    assert isTrue(satask(Q.real(z)))
    assert isTrue(satask(Q.complex(z)))
    assert isFalse(satask(Q.noninteger(z)))
    assert isFalse(satask(Q.irrational(z)))
    assert isFalse(satask(Q.imaginary(z)))
    assert isFalse(satask(Q.positive(z)))
    assert isTrue(satask(Q.negative(z)))
    assert isTrue(satask(Q.nonpositive(z)))
    assert isFalse(satask(Q.nonnegative(z)))
    assert isFalse(satask(Q.even(z)))
    assert isTrue(satask(Q.odd(z)))
    assert isTrue(satask(Q.finite(z)))
    assert isFalse(satask(Q.infinite(z)))
#     assert isTrue(satask(Q.comparable_unhandled_input(z)))
    assert isFalse(satask(Q.prime(z)))
    assert isFalse(satask(Q.composite(z)))
#     assert isTrue(satask(Q.number_unhandled_input(z)))

def test_infinity():
    oo = S.Infinity
    assert isTrue(satask(Q.commutative(oo)))
    assert isFalse(satask(Q.integer(oo)))
    assert isFalse(satask(Q.rational(oo)))
    assert isFalse(satask(Q.algebraic(oo)))
    assert isFalse(satask(Q.transcendental(oo)))
    assert isTrue(satask(Q.extended_real(oo)))
    assert isFalse(satask(Q.real(oo)))
    assert isFalse(satask(Q.complex(oo)))
    assert isTrue(satask(Q.noninteger(oo)))
    assert isFalse(satask(Q.irrational(oo)))
    assert isFalse(satask(Q.imaginary(oo)))
    assert isFalse(satask(Q.nonzero(oo)))
    assert isFalse(satask(Q.positive(oo)))
    assert isFalse(satask(Q.negative(oo)))
    assert isFalse(satask(Q.nonpositive(oo)))
    assert isFalse(satask(Q.nonnegative(oo)))
    assert isTrue(satask(Q.extended_nonzero(oo)))
    assert isTrue(satask(Q.extended_positive(oo)))
    assert isFalse(satask(Q.extended_negative(oo)))
    assert isFalse(satask(Q.extended_nonpositive(oo)))
    assert isTrue(satask(Q.extended_nonnegative(oo)))
    assert isFalse(satask(Q.even(oo)))
    assert isFalse(satask(Q.odd(oo)))
    assert isFalse(satask(Q.finite(oo)))
    assert isTrue(satask(Q.infinite(oo)))
#     assert isTrue(satask(Q.comparable_unhandled_input(oo)))
    assert isFalse(satask(Q.prime(oo)))
    assert isFalse(satask(Q.composite(oo)))
#     assert isTrue(satask(Q.number_unhandled_input(oo)))

def test_neg_infinity():
    mm = S.NegativeInfinity
    assert isTrue(satask(Q.commutative(mm)))
    assert isFalse(satask(Q.integer(mm)))
    assert isFalse(satask(Q.rational(mm)))
    assert isFalse(satask(Q.algebraic(mm)))
    assert isFalse(satask(Q.transcendental(mm)))
    assert isTrue(satask(Q.extended_real(mm)))
    assert isFalse(satask(Q.real(mm)))
    assert isFalse(satask(Q.complex(mm)))
    assert isTrue(satask(Q.noninteger(mm)))
    assert isFalse(satask(Q.irrational(mm)))
    assert isFalse(satask(Q.imaginary(mm)))
    assert isFalse(satask(Q.nonzero(mm)))
    assert isFalse(satask(Q.positive(mm)))
    assert isFalse(satask(Q.negative(mm)))
    assert isFalse(satask(Q.nonpositive(mm)))
    assert isFalse(satask(Q.nonnegative(mm)))
    assert isTrue(satask(Q.extended_nonzero(mm)))
    assert isFalse(satask(Q.extended_positive(mm)))
    assert isTrue(satask(Q.extended_negative(mm)))
    assert isTrue(satask(Q.extended_nonpositive(mm)))
    assert isFalse(satask(Q.extended_nonnegative(mm)))
    assert isFalse(satask(Q.even(mm)))
    assert isFalse(satask(Q.odd(mm)))
    assert isFalse(satask(Q.finite(mm)))
    assert isTrue(satask(Q.infinite(mm)))
#     assert isTrue(satask(Q.comparable_unhandled_input(mm)))
    assert isFalse(satask(Q.prime(mm)))
    assert isFalse(satask(Q.composite(mm)))
#     assert isTrue(satask(Q.number_unhandled_input(mm)))

def test_zoo():
    zoo = S.ComplexInfinity
    assert isFalse(satask(Q.complex(zoo)))
    assert isFalse(satask(Q.real(zoo)))
    assert isFalse(satask(Q.prime(zoo)))

def test_nan():
    nan = S.NaN
    assert isTrue(satask(Q.commutative(nan)))
    assert satask(Q.integer(nan)) is None
    assert satask(Q.rational(nan)) is None
    assert satask(Q.algebraic(nan)) is None
    assert satask(Q.transcendental(nan)) is None
    assert satask(Q.real(nan)) is None
    assert satask(Q.complex(nan)) is None
    assert satask(Q.noninteger(nan)) is None
    assert satask(Q.irrational(nan)) is None
    assert satask(Q.imaginary(nan)) is None
    assert satask(Q.positive(nan)) is None
    assert satask(Q.negative(nan)) is None
    assert satask(Q.nonpositive(nan)) is None
    assert satask(Q.nonnegative(nan)) is None
    assert satask(Q.even(nan)) is None
    assert satask(Q.odd(nan)) is None
    assert satask(Q.finite(nan)) is None
    assert satask(Q.infinite(nan)) is None
#     assert isFalse(satask(Q.comparable_unhandled_input(nan)))
    assert satask(Q.prime(nan)) is None
    assert satask(Q.composite(nan)) is None
#     assert isTrue(satask(Q.number_unhandled_input(nan)))

def test_pos_rational():
    r = Rational(3, 4)
    assert isTrue(satask(Q.commutative(r)))
    assert isFalse(satask(Q.integer(r)))
    assert isTrue(satask(Q.rational(r)))
    assert isTrue(satask(Q.algebraic(r)))
    assert isFalse(satask(Q.transcendental(r)))
    assert isTrue(satask(Q.real(r)))
    assert isTrue(satask(Q.complex(r)))
    assert isTrue(satask(Q.noninteger(r)))
    assert isFalse(satask(Q.irrational(r)))
    assert isFalse(satask(Q.imaginary(r)))
    assert isTrue(satask(Q.positive(r)))
    assert isFalse(satask(Q.negative(r)))
    assert isFalse(satask(Q.nonpositive(r)))
    assert isTrue(satask(Q.nonnegative(r)))
    assert isFalse(satask(Q.even(r)))
    assert isFalse(satask(Q.odd(r)))
    assert isTrue(satask(Q.finite(r)))
    assert isFalse(satask(Q.infinite(r)))
#     assert isTrue(satask(Q.comparable_unhandled_input(r)))
    assert isFalse(satask(Q.prime(r)))
    assert isFalse(satask(Q.composite(r)))
    r = Rational(1, 4)
    assert isFalse(satask(Q.nonpositive(r)))
    assert isTrue(satask(Q.positive(r)))
    assert isFalse(satask(Q.negative(r)))
    assert isTrue(satask(Q.nonnegative(r)))
    r = Rational(5, 4)
    assert isFalse(satask(Q.negative(r)))
    assert isTrue(satask(Q.positive(r)))
    assert isFalse(satask(Q.nonpositive(r)))
    assert isTrue(satask(Q.nonnegative(r)))
    r = Rational(5, 3)
    assert isTrue(satask(Q.nonnegative(r)))
    assert isTrue(satask(Q.positive(r)))
    assert isFalse(satask(Q.negative(r)))
    assert isFalse(satask(Q.nonpositive(r)))

def test_neg_rational():
    r = Rational(-3, 4)
    assert isFalse(satask(Q.positive(r)))
    assert isTrue(satask(Q.nonpositive(r)))
    assert isTrue(satask(Q.negative(r)))
    assert isFalse(satask(Q.nonnegative(r)))
    r = Rational(-1, 4)
    assert isTrue(satask(Q.nonpositive(r)))
    assert isFalse(satask(Q.positive(r)))
    assert isTrue(satask(Q.negative(r)))
    assert isFalse(satask(Q.nonnegative(r)))
    r = Rational(-5, 4)
    assert isTrue(satask(Q.negative(r)))
    assert isFalse(satask(Q.positive(r)))
    assert isTrue(satask(Q.nonpositive(r)))
    assert isFalse(satask(Q.nonnegative(r)))
    r = Rational(-5, 3)
    assert isFalse(satask(Q.nonnegative(r)))
    assert isFalse(satask(Q.positive(r)))
    assert isTrue(satask(Q.negative(r)))
    assert isTrue(satask(Q.nonpositive(r)))

def test_pi():
    z = S.Pi
    assert isTrue(satask(Q.commutative(z)))
    assert isFalse(satask(Q.integer(z)))
    assert isFalse(satask(Q.rational(z)))
    assert isFalse(satask(Q.algebraic(z)))
    assert isTrue(satask(Q.transcendental(z)))
    assert isTrue(satask(Q.real(z)))
    assert isTrue(satask(Q.complex(z)))
    assert isTrue(satask(Q.noninteger(z)))
    assert isTrue(satask(Q.irrational(z)))
    assert isFalse(satask(Q.imaginary(z)))
    assert isTrue(satask(Q.positive(z)))
    assert isFalse(satask(Q.negative(z)))
    assert isFalse(satask(Q.nonpositive(z)))
    assert isTrue(satask(Q.nonnegative(z)))
    assert isFalse(satask(Q.even(z)))
    assert isFalse(satask(Q.odd(z)))
    assert isTrue(satask(Q.finite(z)))
    assert isFalse(satask(Q.infinite(z)))
#     assert isTrue(satask(Q.comparable_unhandled_input(z)))
    assert isFalse(satask(Q.prime(z)))
    assert isFalse(satask(Q.composite(z)))

def test_E():
    z = S.Exp1
    assert isTrue(satask(Q.commutative(z)))
    assert isFalse(satask(Q.integer(z)))
    assert isFalse(satask(Q.rational(z)))
    assert isFalse(satask(Q.algebraic(z)))
    assert isTrue(satask(Q.transcendental(z)))
    assert isTrue(satask(Q.real(z)))
    assert isTrue(satask(Q.complex(z)))
    assert isTrue(satask(Q.noninteger(z)))
    assert isTrue(satask(Q.irrational(z)))
    assert isFalse(satask(Q.imaginary(z)))
    assert isTrue(satask(Q.positive(z)))
    assert isFalse(satask(Q.negative(z)))
    assert isFalse(satask(Q.nonpositive(z)))
    assert isTrue(satask(Q.nonnegative(z)))
    assert isFalse(satask(Q.even(z)))
    assert isFalse(satask(Q.odd(z)))
    assert isTrue(satask(Q.finite(z)))
    assert isFalse(satask(Q.infinite(z)))
#     assert isTrue(satask(Q.comparable_unhandled_input(z)))
    assert isFalse(satask(Q.prime(z)))
    assert isFalse(satask(Q.composite(z)))

def test_I():
    z = S.ImaginaryUnit
    assert isTrue(satask(Q.commutative(z)))
    assert isFalse(satask(Q.integer(z)))
    assert isFalse(satask(Q.rational(z)))
    assert isTrue(satask(Q.algebraic(z)))
    assert isFalse(satask(Q.transcendental(z)))
    assert isFalse(satask(Q.real(z)))
    assert isTrue(satask(Q.complex(z)))
    assert isFalse(satask(Q.noninteger(z)))
    assert isFalse(satask(Q.irrational(z)))
    assert isTrue(satask(Q.imaginary(z)))
    assert isFalse(satask(Q.positive(z)))
    assert isFalse(satask(Q.negative(z)))
    assert isFalse(satask(Q.nonpositive(z)))
    assert isFalse(satask(Q.nonnegative(z)))
    assert isFalse(satask(Q.even(z)))
    assert isFalse(satask(Q.odd(z)))
    assert isTrue(satask(Q.finite(z)))
    assert isFalse(satask(Q.infinite(z)))
#     assert isFalse(satask(Q.comparable_unhandled_input(z)))
    assert isFalse(satask(Q.prime(z)))
    assert isFalse(satask(Q.composite(z)))

def test_symbol_real_false():
    a = Symbol('a', real=False)
    assert isFalse(satask(Q.real(a)))
    assert isFalse(satask(Q.integer(a)))
    assert isFalse(satask(Q.zero(a)))
    assert isFalse(satask(Q.negative(a)))
    assert isFalse(satask(Q.positive(a)))
    assert isFalse(satask(Q.nonnegative(a)))
    assert isFalse(satask(Q.nonpositive(a)))
    assert isFalse(satask(Q.nonzero(a)))
    assert satask(Q.extended_negative(a)) is None
    assert satask(Q.extended_positive(a)) is None
    assert satask(Q.extended_nonnegative(a)) is None
    assert satask(Q.extended_nonpositive(a)) is None
    assert satask(Q.extended_nonzero(a)) is None

def test_symbol_extended_real_false():
    a = Symbol('a', extended_real=False)
    assert isFalse(satask(Q.real(a)))
    assert isFalse(satask(Q.integer(a)))
    assert isFalse(satask(Q.zero(a)))
    assert isFalse(satask(Q.negative(a)))
    assert isFalse(satask(Q.positive(a)))
    assert isFalse(satask(Q.nonnegative(a)))
    assert isFalse(satask(Q.nonpositive(a)))
    assert isFalse(satask(Q.nonzero(a)))
    assert isFalse(satask(Q.extended_negative(a)))
    assert isFalse(satask(Q.extended_positive(a)))
    assert isFalse(satask(Q.extended_nonnegative(a)))
    assert isFalse(satask(Q.extended_nonpositive(a)))
    assert isFalse(satask(Q.extended_nonzero(a)))

def test_symbol_imaginary():
    a = Symbol('a', imaginary=True)
    assert isFalse(satask(Q.real(a)))
    assert isFalse(satask(Q.integer(a)))
    assert isFalse(satask(Q.negative(a)))
    assert isFalse(satask(Q.positive(a)))
    assert isFalse(satask(Q.nonnegative(a)))
    assert isFalse(satask(Q.nonpositive(a)))
    assert isFalse(satask(Q.zero(a)))
    assert isFalse(satask(Q.nonzero(a)))

def test_symbol_zero():
    x = Symbol('x', zero=True)
    assert isFalse(satask(Q.positive(x)))
    assert isTrue(satask(Q.nonpositive(x)))
    assert isFalse(satask(Q.negative(x)))
    assert isTrue(satask(Q.nonnegative(x)))
    assert isTrue(satask(Q.zero(x)))
    assert isFalse(satask(Q.nonzero(x)))
    assert isTrue(satask(Q.finite(x)))

def test_symbol_positive():
    x = Symbol('x', positive=True)
    assert isTrue(satask(Q.positive(x)))
    assert isFalse(satask(Q.nonpositive(x)))
    assert isFalse(satask(Q.negative(x)))
    assert isTrue(satask(Q.nonnegative(x)))
    assert isFalse(satask(Q.zero(x)))
    assert isTrue(satask(Q.nonzero(x)))

def test_neg_symbol_positive():
    x = -Symbol('x', positive=True)
    assert isFalse(satask(Q.positive(x)))
    assert isTrue(satask(Q.nonpositive(x)))
    assert isTrue(satask(Q.negative(x)))
    assert isFalse(satask(Q.nonnegative(x)))
    assert isFalse(satask(Q.zero(x)))
    assert isTrue(satask(Q.nonzero(x)))

def test_symbol_nonpositive():
    x = Symbol('x', nonpositive=True)
    assert isFalse(satask(Q.positive(x)))
    assert isTrue(satask(Q.nonpositive(x)))
    assert satask(Q.negative(x)) is None
    assert satask(Q.nonnegative(x)) is None
    assert satask(Q.zero(x)) is None
    assert satask(Q.nonzero(x)) is None

def test_neg_symbol_nonpositive():
    x = -Symbol('x', nonpositive=True)
    assert satask(Q.positive(x)) is None
    assert satask(Q.nonpositive(x)) is None
    assert isFalse(satask(Q.negative(x)))
    assert isTrue(satask(Q.nonnegative(x)))
    assert satask(Q.zero(x)) is None
    assert satask(Q.nonzero(x)) is None

def test_symbol_falsepositive():
    x = Symbol('x', positive=False)
    assert isFalse(satask(Q.positive(x)))
    assert satask(Q.nonpositive(x)) is None
    assert satask(Q.negative(x)) is None
    assert satask(Q.nonnegative(x)) is None
    assert satask(Q.zero(x)) is None
    assert satask(Q.nonzero(x)) is None

def test_symbol_falsepositive_mul():
    x = 2 * Symbol('x', positive=False)
    assert isFalse(satask(Q.positive(x)))
    assert satask(Q.nonpositive(x)) is None
    assert satask(Q.negative(x)) is None
    assert satask(Q.nonnegative(x)) is None
    assert satask(Q.zero(x)) is None
    assert satask(Q.nonzero(x)) is None

@XFAIL
def test_symbol_infinitereal_mul():
    ix = Symbol('ix', infinite=True, extended_real=True)
    assert satask(Q.extended_positive(-ix)) is None

def test_neg_symbol_falsepositive():
    x = -Symbol('x', positive=False)
    assert satask(Q.positive(x)) is None
    assert satask(Q.nonpositive(x)) is None
    assert isFalse(satask(Q.negative(x)))
    assert satask(Q.nonnegative(x)) is None
    assert satask(Q.zero(x)) is None
    assert satask(Q.nonzero(x)) is None

def test_neg_symbol_falsenegative():
    x = -Symbol('x', negative=False)
    assert isFalse(satask(Q.positive(x)))
    assert satask(Q.nonpositive(x)) is None
    assert satask(Q.negative(x)) is None
    assert satask(Q.nonnegative(x)) is None
    assert satask(Q.zero(x)) is None
    assert satask(Q.nonzero(x)) is None

def test_symbol_falsepositive_real():
    x = Symbol('x', positive=False, real=True)
    assert isFalse(satask(Q.positive(x)))
    assert isTrue(satask(Q.nonpositive(x)))
    assert satask(Q.negative(x)) is None
    assert satask(Q.nonnegative(x)) is None
    assert satask(Q.zero(x)) is None
    assert satask(Q.nonzero(x)) is None

def test_neg_symbol_falsepositive_real():
    x = -Symbol('x', positive=False, real=True)
    assert satask(Q.positive(x)) is None
    assert satask(Q.nonpositive(x)) is None
    assert isFalse(satask(Q.negative(x)))
    assert isTrue(satask(Q.nonnegative(x)))
    assert satask(Q.zero(x)) is None
    assert satask(Q.nonzero(x)) is None

def test_symbol_falsenonnegative():
    x = Symbol('x', nonnegative=False)
    assert isFalse(satask(Q.positive(x)))
    assert satask(Q.nonpositive(x)) is None
    assert satask(Q.negative(x)) is None
    assert isFalse(satask(Q.nonnegative(x)))
    assert isFalse(satask(Q.zero(x)))
    assert satask(Q.nonzero(x)) is None

@XFAIL
def test_neg_symbol_falsenonnegative():
    x = -Symbol('x', nonnegative=False)
    assert satask(Q.positive(x)) is None
    assert isFalse(satask(Q.nonpositive(x)))
    assert isFalse(satask(Q.negative(x)))
    assert satask(Q.nonnegative(x)) is None
    assert isFalse(satask(Q.zero(x)))
    assert isTrue(satask(Q.nonzero(x)))

def test_symbol_falsenonnegative_real():
    x = Symbol('x', nonnegative=False, real=True)
    assert isFalse(satask(Q.positive(x)))
    assert isTrue(satask(Q.nonpositive(x)))
    assert isTrue(satask(Q.negative(x)))
    assert isFalse(satask(Q.nonnegative(x)))
    assert isFalse(satask(Q.zero(x)))
    assert isTrue(satask(Q.nonzero(x)))

def test_neg_symbol_falsenonnegative_real():
    x = -Symbol('x', nonnegative=False, real=True)
    assert isTrue(satask(Q.positive(x)))
    assert isFalse(satask(Q.nonpositive(x)))
    assert isFalse(satask(Q.negative(x)))
    assert isTrue(satask(Q.nonnegative(x)))
    assert isFalse(satask(Q.zero(x)))
    assert isTrue(satask(Q.nonzero(x)))

def test_prime():
    assert isFalse(satask(Q.prime(S.NegativeOne)))
    assert isFalse(satask(Q.prime(S(-2))))
    assert isFalse(satask(Q.prime(S(-4))))
    assert isFalse(satask(Q.prime(S.Zero)))
    assert isFalse(satask(Q.prime(S.One)))
    assert isTrue(satask(Q.prime(S(2))))
    assert isTrue(satask(Q.prime(S(17))))
    assert isFalse(satask(Q.prime(S(4))))

def test_composite():
    assert isFalse(satask(Q.composite(S.NegativeOne)))
    assert isFalse(satask(Q.composite(S(-2))))
    assert isFalse(satask(Q.composite(S(-4))))
    assert isFalse(satask(Q.composite(S.Zero)))
    assert isFalse(satask(Q.composite(S(2))))
    assert isFalse(satask(Q.composite(S(17))))
    assert isTrue(satask(Q.composite(S(4))))
    x = Dummy(integer=True, positive=True, prime=False)
    assert satask(Q.composite(x)) is None
    assert satask(Q.composite(x + 1)) is None
    x = Dummy(positive=True, even=True, prime=False)
    assert isTrue(satask(Q.integer(x)))
    assert isTrue(satask(Q.composite(x)))

def test_prime_symbol():
    x = Symbol('x', prime=True)
    assert isTrue(satask(Q.prime(x)))
    assert isTrue(satask(Q.integer(x)))
    assert isTrue(satask(Q.positive(x)))
    assert isFalse(satask(Q.negative(x)))
    assert isFalse(satask(Q.nonpositive(x)))
    assert isTrue(satask(Q.nonnegative(x)))
    x = Symbol('x', prime=False)
    assert isFalse(satask(Q.prime(x)))
    assert satask(Q.integer(x)) is None
    assert satask(Q.positive(x)) is None
    assert satask(Q.negative(x)) is None
    assert satask(Q.nonpositive(x)) is None
    assert satask(Q.nonnegative(x)) is None

def test_symbol_noncommutative():
    x = Symbol('x', commutative=True)
    assert satask(Q.complex(x)) is None
    x = Symbol('x', commutative=False)
    assert isFalse(satask(Q.integer(x)))
    assert isFalse(satask(Q.rational(x)))
    assert isFalse(satask(Q.algebraic(x)))
    assert isFalse(satask(Q.irrational(x)))
    assert isFalse(satask(Q.real(x)))
    assert isFalse(satask(Q.complex(x)))

def test_other_symbol():
    x = Symbol('x', integer=True)
    assert isTrue(satask(Q.integer(x)))
    assert isTrue(satask(Q.real(x)))
    assert isTrue(satask(Q.finite(x)))
    x = Symbol('x', integer=True, nonnegative=True)
    assert isTrue(satask(Q.integer(x)))
    assert isTrue(satask(Q.nonnegative(x)))
    assert isFalse(satask(Q.negative(x)))
    assert satask(Q.positive(x)) is None
    assert isTrue(satask(Q.finite(x)))
    x = Symbol('x', integer=True, nonpositive=True)
    assert isTrue(satask(Q.integer(x)))
    assert isTrue(satask(Q.nonpositive(x)))
    assert isFalse(satask(Q.positive(x)))
    assert satask(Q.negative(x)) is None
    assert isTrue(satask(Q.finite(x)))
    x = Symbol('x', odd=True)
    assert isTrue(satask(Q.odd(x)))
    assert isFalse(satask(Q.even(x)))
    assert isTrue(satask(Q.integer(x)))
    assert isTrue(satask(Q.finite(x)))
    x = Symbol('x', odd=False)
    assert isFalse(satask(Q.odd(x)))
    assert satask(Q.even(x)) is None
    assert satask(Q.integer(x)) is None
    assert satask(Q.finite(x)) is None
    x = Symbol('x', even=True)
    assert isTrue(satask(Q.even(x)))
    assert isFalse(satask(Q.odd(x)))
    assert isTrue(satask(Q.integer(x)))
    assert isTrue(satask(Q.finite(x)))
    x = Symbol('x', even=False)
    assert isFalse(satask(Q.even(x)))
    assert satask(Q.odd(x)) is None
    assert satask(Q.integer(x)) is None
    assert satask(Q.finite(x)) is None
    x = Symbol('x', integer=True, nonnegative=True)
    assert isTrue(satask(Q.integer(x)))
    assert isTrue(satask(Q.nonnegative(x)))
    assert isTrue(satask(Q.finite(x)))
    x = Symbol('x', integer=True, nonpositive=True)
    assert isTrue(satask(Q.integer(x)))
    assert isTrue(satask(Q.nonpositive(x)))
    assert isTrue(satask(Q.finite(x)))
    x = Symbol('x', rational=True)
    assert isTrue(satask(Q.real(x)))
    assert isTrue(satask(Q.finite(x)))
    x = Symbol('x', rational=False)
    assert satask(Q.real(x)) is None
    assert satask(Q.finite(x)) is None
    x = Symbol('x', irrational=True)
    assert isTrue(satask(Q.real(x)))
    assert isTrue(satask(Q.finite(x)))
    x = Symbol('x', irrational=False)
    assert satask(Q.real(x)) is None
    assert satask(Q.finite(x)) is None
#     with raises(AttributeError):
#         satask(Q.real(x)) = False
    x = Symbol('x', algebraic=True)
    assert isFalse(satask(Q.transcendental(x)))
    x = Symbol('x', transcendental=True)
    assert isFalse(satask(Q.algebraic(x)))
    assert isFalse(satask(Q.rational(x)))
    assert isFalse(satask(Q.integer(x)))

def test_evaluate_false():
    from sympy.core.parameters import evaluate
    from sympy.abc import x, h
    f = 2 ** x ** 7
    with evaluate(False):
        fh = f.xreplace({x: x + h})
#         assert satask(Q.rational(fh.exp)) is None

def test_issue_3825():
    """catch: hash instability"""
    x = Symbol('x')
    y = Symbol('y')
    a1 = x + y
    a2 = y + x
#     satask(Q.comparable_unhandled_input(a2))
    h1 = hash(a1)
    h2 = hash(a2)
    assert h1 == h2

def test_issue_4822():
    z = (-1) ** Rational(1, 3) * (1 - I * sqrt(3))
    assert satask(Q.real(z)) in [True, None]

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
    satask(Q.positive(a))
    assert isTrue(satask(Q.positive(a)))
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
    assert satask(Q.extended_positive(n + p)) is None
    assert satask(Q.extended_positive(n + x)) is None
    assert satask(Q.extended_positive(p + x)) is None
    assert satask(Q.extended_negative(n + p)) is None
    assert satask(Q.extended_negative(n + x)) is None
    assert satask(Q.extended_negative(p + x)) is None
    assert isFalse(satask(Q.extended_positive(n + xf)))
    assert isTrue(satask(Q.extended_positive(p + xf)))
    assert isTrue(satask(Q.extended_negative(n + xf)))
    assert isFalse(satask(Q.extended_negative(p + xf)))
    assert satask(Q.extended_negative(x - S.Infinity)) is None
    assert isTrue(satask(Q.extended_positive(p + nn)))
    assert isTrue(satask(Q.extended_negative(n + np)))
    assert satask(Q.extended_positive(p + r)) is None

def test_Add_is_imaginary():
    nn = Dummy(nonnegative=True)
    assert isTrue(satask(Q.imaginary(I * nn + I)))

def test_Add_is_algebraic():
    a = Symbol('a', algebraic=True)
    b = Symbol('a', algebraic=True)
    na = Symbol('na', algebraic=False)
    nb = Symbol('nb', algebraic=False)
    x = Symbol('x')
    assert isTrue(satask(Q.algebraic(a + b)))
    assert satask(Q.algebraic(na + nb)) is None
    assert isFalse(satask(Q.algebraic(a + na)))
    assert satask(Q.algebraic(a + x)) is None
    assert satask(Q.algebraic(na + x)) is None

def test_Mul_is_algebraic():
    a = Symbol('a', algebraic=True)
    b = Symbol('b', algebraic=True)
    na = Symbol('na', algebraic=False)
    an = Symbol('an', algebraic=True, nonzero=True)
    nb = Symbol('nb', algebraic=False)
    x = Symbol('x')
    assert isTrue(satask(Q.algebraic(a * b)))
    assert satask(Q.algebraic(na * nb)) is None
    assert satask(Q.algebraic(a * na)) is None
    assert isFalse(satask(Q.algebraic(an * na)))
    assert satask(Q.algebraic(a * x)) is None
    assert satask(Q.algebraic(na * x)) is None

def test_Pow_is_algebraic():
    e = Symbol('e', algebraic=True)
    assert isTrue(satask(Q.algebraic(Pow(1, e, evaluate=False))))
    assert isTrue(satask(Q.algebraic(Pow(0, e, evaluate=False))))
    a = Symbol('a', algebraic=True)
    azf = Symbol('azf', algebraic=True, zero=False)
    na = Symbol('na', algebraic=False)
    ia = Symbol('ia', algebraic=True, irrational=True)
    ib = Symbol('ib', algebraic=True, irrational=True)
    r = Symbol('r', rational=True)
    x = Symbol('x')
    assert isTrue(satask(Q.algebraic(a ** 2)))
    assert satask(Q.algebraic(a ** r)) is None
    assert isTrue(satask(Q.algebraic(azf ** r)))
    assert satask(Q.algebraic(a ** x)) is None
    assert satask(Q.algebraic(na ** r)) is None
    assert isTrue(satask(Q.algebraic(ia ** r)))
    assert isFalse(satask(Q.algebraic(ia ** ib)))
    assert satask(Q.algebraic(a ** e)) is None
    assert isFalse(satask(Q.algebraic(Pow(2, sqrt(2), evaluate=False))))
    assert isFalse(satask(Q.algebraic(Pow(S.GoldenRatio, sqrt(3), evaluate=False))))
    t = Symbol('t', real=True, transcendental=True)
    n = Symbol('n', integer=True)
    assert satask(Q.algebraic(t ** n)) is None
    assert satask(Q.integer(t ** n)) is None
    assert isFalse(satask(Q.algebraic(pi ** 3)))
    r = Symbol('r', zero=True)
    assert isTrue(satask(Q.algebraic(pi ** r)))

def test_Mul_is_prime_composite():
    x = Symbol('x', positive=True, integer=True)
    y = Symbol('y', positive=True, integer=True)
    assert satask(Q.prime(x * y)) is None
    assert isFalse(satask(Q.prime((x + 1) * (y + 1))))
    assert isTrue(satask(Q.composite((x + 1) * (y + 1))))
    x = Symbol('x', positive=True)
    assert satask(Q.prime((x + 1) * (y + 1))) is None
    assert satask(Q.composite((x + 1) * (y + 1))) is None

def test_Pow_is_pos_neg():
    z = Symbol('z', real=True)
    w = Symbol('w', nonpositive=True)
    assert isTrue(satask(Q.positive(S.NegativeOne ** S(2))))
    assert isTrue(satask(Q.positive(S.One ** z)))
    assert isFalse(satask(Q.positive(S.NegativeOne ** S(3))))
    assert isTrue(satask(Q.positive(S.Zero ** S.Zero)))
    assert isFalse(satask(Q.positive(w ** S(3))))
    assert satask(Q.positive(w ** S(2))) is None
    assert isFalse(satask(Q.positive(I ** 2)))
    assert isTrue(satask(Q.positive(I ** 4)))
    p = Symbol('p', zero=True)
    q = Symbol('q', zero=False, real=True)
    j = Symbol('j', zero=False, even=True)
    x = Symbol('x', zero=True)
    y = Symbol('y', zero=True)
    assert isFalse(satask(Q.positive(p ** q)))
    assert isFalse(satask(Q.negative(p ** q)))
    assert isFalse(satask(Q.positive(p ** j)))
    assert isTrue(satask(Q.positive(x ** y)))
    assert isFalse(satask(Q.negative(x ** y)))

def test_Pow_is_prime_composite():
    x = Symbol('x', positive=True, integer=True)
    y = Symbol('y', positive=True, integer=True)
    assert satask(Q.prime(x ** y)) is None
    assert isFalse(satask(Q.prime(x ** (y + 1))))
    assert satask(Q.composite(x ** (y + 1))) is None
    assert isTrue(satask(Q.composite((x + 1) ** (y + 1))))
    assert isTrue(satask(Q.composite((-x - 1) ** (2 * y))))
    x = Symbol('x', positive=True)
    assert satask(Q.prime(x ** y)) is None

def test_Mul_is_infinite():
    x = Symbol('x')
    f = Symbol('f', finite=True)
    i = Symbol('i', infinite=True)
    z = Dummy(zero=True)
    nzf = Dummy(finite=True, zero=False)
    from sympy.core.mul import Mul
    assert satask(Q.finite(x * f)) is None
    assert satask(Q.finite(x * i)) is None
    assert satask(Q.finite(f * i)) is None
    assert satask(Q.finite(x * f * i)) is None
    assert satask(Q.finite(z * i)) is None
    assert isFalse(satask(Q.finite(nzf * i)))
    assert isTrue(satask(Q.finite(z * f)))
    assert isTrue(satask(Q.finite(Mul(0, f, evaluate=False))))
#     assert satask(Q.finite(Mul(0, i, evaluate=False))) is None
    assert satask(Q.infinite(x * f)) is None
    assert satask(Q.infinite(x * i)) is None
    assert satask(Q.infinite(f * i)) is None
    assert satask(Q.infinite(x * f * i)) is None
    assert satask(Q.infinite(z * i)) is satask(Q.infinite(S.NaN))
    assert isTrue(satask(Q.infinite(nzf * i)))
    assert isFalse(satask(Q.infinite(z * f)))
    assert isFalse(satask(Q.infinite(Mul(0, f, evaluate=False))))
#     assert satask(Q.infinite(Mul(0, i, evaluate=False))) is satask(Q.infinite(S.NaN))

def test_Add_is_infinite():
    x = Symbol('x')
    f = Symbol('f', finite=True)
    i = Symbol('i', infinite=True)
    i2 = Symbol('i2', infinite=True)
    z = Dummy(zero=True)
    nzf = Dummy(finite=True, zero=False)
    from sympy.core.add import Add
    assert satask(Q.finite(x + f)) is None
    assert satask(Q.finite(x + i)) is None
    assert isFalse(satask(Q.finite(f + i)))
    assert satask(Q.finite(x + f + i)) is None
    assert isFalse(satask(Q.finite(z + i)))
    assert isFalse(satask(Q.finite(nzf + i)))
    assert isTrue(satask(Q.finite(z + f)))
    assert satask(Q.finite(i + i2)) is None
    assert isTrue(satask(Q.finite(Add(0, f, evaluate=False))))
    assert isFalse(satask(Q.finite(Add(0, i, evaluate=False))))
    assert satask(Q.infinite(x + f)) is None
    assert satask(Q.infinite(x + i)) is None
    assert isTrue(satask(Q.infinite(f + i)))
    assert satask(Q.infinite(x + f + i)) is None
    assert isTrue(satask(Q.infinite(z + i)))
    assert isTrue(satask(Q.infinite(nzf + i)))
    assert isFalse(satask(Q.infinite(z + f)))
    assert satask(Q.infinite(i + i2)) is None
    assert isFalse(satask(Q.infinite(Add(0, f, evaluate=False))))
    assert isTrue(satask(Q.infinite(Add(0, i, evaluate=False))))

def test_special_is_rational():
    i = Symbol('i', integer=True)
    i2 = Symbol('i2', integer=True)
    ni = Symbol('ni', integer=True, nonzero=True)
    r = Symbol('r', rational=True)
    rn = Symbol('r', rational=True, nonzero=True)
    nr = Symbol('nr', irrational=True)
    x = Symbol('x')
    assert isFalse(satask(Q.rational(sqrt(3))))
    assert isFalse(satask(Q.rational(3 + sqrt(3))))
    assert isFalse(satask(Q.rational(3 * sqrt(3))))
    assert isFalse(satask(Q.rational(exp(3))))
    assert isFalse(satask(Q.rational(exp(ni))))
    assert isFalse(satask(Q.rational(exp(rn))))
    assert satask(Q.rational(exp(x))) is None
    assert isTrue(satask(Q.rational(exp(log(3), evaluate=False))))
    assert isTrue(satask(Q.rational(log(exp(3), evaluate=False))))
    assert isFalse(satask(Q.rational(log(3))))
    assert isFalse(satask(Q.rational(log(ni + 1))))
    assert isFalse(satask(Q.rational(log(rn + 1))))
    assert satask(Q.rational(log(x))) is None
    assert satask(Q.rational(sqrt(3) + sqrt(5))) is None
    assert isFalse(satask(Q.rational(sqrt(3) + S.Pi)))
    assert satask(Q.rational(x ** i)) is None
    assert isTrue(satask(Q.rational(i ** i)))
    assert satask(Q.rational(i ** i2)) is None
    assert satask(Q.rational(r ** i)) is None
    assert satask(Q.rational(r ** r)) is None
    assert satask(Q.rational(r ** x)) is None
    assert satask(Q.rational(nr ** i)) is None
#     assert satask(Q.rational(nr ** Symbol('z', zero=True)))
    assert isFalse(satask(Q.rational(sin(1))))
    assert isFalse(satask(Q.rational(sin(ni))))
    assert isFalse(satask(Q.rational(sin(rn))))
    assert satask(Q.rational(sin(x))) is None
    assert isFalse(satask(Q.rational(asin(r))))
    assert isTrue(satask(Q.rational(sin(asin(3), evaluate=False))))

@XFAIL
def test_issue_6275():
    x = Symbol('x')
    assert isinstance(x * 0, type(0 * S.Infinity))
    if 0 * S.Infinity is S.NaN:
        b = Symbol('b', finite=None)
        assert satask(Q.zero(b * 0)) is None

def test_sanitize_assumptions():
    for cls in (Symbol, Dummy, Wild):
        x = cls('x', real=1, positive=0)
        assert isTrue(satask(Q.real(x)))
        assert isFalse(satask(Q.positive(x)))
        assert satask(Q.positive(cls('', real=True, positive=None))) is None
        raises(ValueError, lambda : cls('', commutative=None))
    raises(ValueError, lambda : Symbol._sanitize({'commutative': None}))

def test_special_assumptions():
    e = -3 - sqrt(5) + (-sqrt(10) / 2 - sqrt(2) / 2) ** 2
    assert simplify(e < 0) is S.false
    assert simplify(e > 0) is S.false
    assert isFalse(e == 0)
    assert isTrue(e.equals(0))

def test_inconsistent():
    raises(InconsistentAssumptions, lambda : Symbol('x', real=True, commutative=False))

def test_issue_6631():
    assert isTrue(satask(Q.real((-1) ** I)))
    assert isTrue(satask(Q.real((-1) ** (I * 2))))
    assert isTrue(satask(Q.real((-1) ** (I / 2))))
    assert isTrue(satask(Q.real((-1) ** (I * S.Pi))))
    assert isTrue(satask(Q.real(I ** (I + 2))))

def test_issue_2730():
    assert isFalse(satask(Q.real(1 / (1 + I))))

def test_issue_4149():
    assert isTrue(satask(Q.complex(3 + I)))
    assert isFalse(satask(Q.imaginary(3 + I)))
    assert isTrue(satask(Q.imaginary(3 * I + S.Pi * I)))
    y = Symbol('y', real=True)
    assert satask(Q.imaginary(3 * I + S.Pi * I + y * I)) is None
    p = Symbol('p', positive=True)
    assert isTrue(satask(Q.imaginary(3 * I + S.Pi * I + p * I)))
    n = Symbol('n', negative=True)
    assert isTrue(satask(Q.imaginary(-3 * I - S.Pi * I + n * I)))
    i = Symbol('i', imaginary=True)
#     assert [satask(Q.imaginary(i ** a)) for a in range(4)] == [False, True, False, True]
    e = S('-sqrt(3)*I/2 + 0.866025403784439*I')
    assert isFalse(satask(Q.real(e)))
    assert isTrue(satask(Q.imaginary(e)))

def test_issue_2920():
    n = Symbol('n', negative=True)
    assert isTrue(satask(Q.imaginary(sqrt(n))))

def test_issue_7899():
    x = Symbol('x', real=True)
    assert satask(Q.real(I * x)) is None
    assert satask(Q.zero((x - I) * (x - 1))) is None
    assert satask(Q.real((x - I) * (x - 1))) is None

@XFAIL
def test_issue_7993():
    x = Dummy(integer=True)
    y = Dummy(noninteger=True)
    assert isFalse(satask(Q.zero(x - y)))

def test_issue_8075():
    raises(InconsistentAssumptions, lambda : Dummy(zero=True, finite=False))
    raises(InconsistentAssumptions, lambda : Dummy(zero=True, infinite=True))

def test_issue_8642():
    x = Symbol('x', real=True, integer=False)
    assert satask(Q.integer(x * 2)) is None, satask(Q.integer(x * 2))

def test_issues_8632_8633_8638_8675_8992():
    p = Dummy(integer=True, positive=True)
    nn = Dummy(integer=True, nonnegative=True)
    assert isTrue(satask(Q.positive(p - S.Half)))
    assert isTrue(satask(Q.nonnegative(p - 1)))
    assert isTrue(satask(Q.positive(nn + 1)))
    assert isTrue(satask(Q.nonpositive(-p + 1)))
    assert isTrue(satask(Q.negative(-nn - 1)))
    prime = Dummy(prime=True)
    assert isTrue(satask(Q.nonnegative(prime - 2)))
    assert satask(Q.nonnegative(prime - 3)) is None
    even = Dummy(positive=True, even=True)
    assert isTrue(satask(Q.nonnegative(even - 2)))
    p = Dummy(positive=True)
    assert isTrue(satask(Q.negative(p / (p + 1) - 1)))
    assert isTrue(satask(Q.positive((p + 2) ** 3 - S.Half)))
    n = Dummy(negative=True)
    assert isTrue(satask(Q.nonpositive(n - 3)))

def test_issue_9115_9150():
    n = Dummy('n', integer=True, nonnegative=True)
    assert (factorial(n) >= 1) == True
    assert (factorial(n) < 1) == False
    assert satask(Q.even(factorial(n + 1))) is None
    assert isTrue(satask(Q.even(factorial(n + 2))))
    assert factorial(n + 2) >= 2

def test_issue_9165():
    z = Symbol('z', zero=True)
    f = Symbol('f', finite=False)
    assert 0 / z is S.NaN
    assert 0 * (1 / z) is S.NaN
    assert 0 * f is S.NaN

def test_issue_10024():
    x = Dummy('x')
    assert satask(Q.zero(Mod(x, 2 * pi))) is None

def test_issue_10302():
    x = Symbol('x')
    r = Symbol('r', real=True)
    u = -(3 * 2 ** pi) ** (1 / pi) + 2 * 3 ** (1 / pi)
    i = u + u * I
    assert satask(Q.real(i)) is None
    assert satask(Q.zero(u + i)) is None
    assert isFalse(satask(Q.zero(1 + i)))
    a = Dummy('a', zero=True)
    assert isFalse(satask(Q.zero(a + I)))
    assert satask(Q.zero(a + r * I)) is None
    assert isTrue(satask(Q.imaginary(a + I)))
    assert satask(Q.imaginary(a + x + I)) is None
    assert satask(Q.imaginary(a + r * I + I)) is None

def test_complex_reciprocal_imaginary():
    assert isFalse(satask(Q.imaginary(1 / (4 + 3 * I))))

def test_issue_16313():
    x = Symbol('x', extended_real=False)
    k = Symbol('k', real=True)
    l = Symbol('l', real=True, zero=False)
    assert isFalse(satask(Q.real(-x)))
    assert satask(Q.real(k * x)) is None
    assert isFalse(satask(Q.real(l * x)))
    assert satask(Q.real(l * x * x)) is None
    assert isFalse(satask(Q.positive(-x)))

def test_issue_16579():
    x = Symbol('x', extended_real=True, infinite=False)
    y = Symbol('y', extended_real=True, finite=False)
    assert isTrue(satask(Q.finite(x)))
    assert isTrue(satask(Q.infinite(y)))
    c = Symbol('c', complex=True)
    assert isTrue(satask(Q.finite(c)))
    raises(InconsistentAssumptions, lambda : Dummy(complex=True, finite=False))
    nf = Symbol('nf', finite=False)
    assert isTrue(satask(Q.infinite(nf)))

def test_issue_17556():
    z = I * oo
    assert isFalse(satask(Q.imaginary(z)))
    assert isFalse(satask(Q.finite(z)))

def test_issue_21651():
    k = Symbol('k', positive=True, integer=True)
    exp = 2 * 2 ** (-k)
    assert satask(Q.integer(exp)) is None

def test_assumptions_copy():
    assert assumptions(Symbol('x'), {'commutative': True}) == {'commutative': True}
    assert assumptions(Symbol('x'), ['integer']) == {}
    assert assumptions(Symbol('x'), ['commutative']) == {'commutative': True}
    assert assumptions(Symbol('x')) == {'commutative': True}
    assert assumptions(1)['positive']
    assert assumptions(3 + I) == {'algebraic': True, 'commutative': True, 'complex': True, 'composite': False, 'even': False, 'extended_negative': False, 'extended_nonnegative': False, 'extended_nonpositive': False, 'extended_nonzero': False, 'extended_positive': False, 'extended_real': False, 'finite': True, 'imaginary': False, 'infinite': False, 'integer': False, 'irrational': False, 'negative': False, 'noninteger': False, 'nonnegative': False, 'nonpositive': False, 'nonzero': False, 'odd': False, 'positive': False, 'prime': False, 'rational': False, 'real': False, 'transcendental': False, 'zero': False}

def test_check_assumptions():
    assert isFalse(check_assumptions(1, 0))
    x = Symbol('x', positive=True)
    assert isTrue(check_assumptions(1, x))
    assert isTrue(check_assumptions(1, 1))
    assert isFalse(check_assumptions(-1, 1))
    i = Symbol('i', integer=True)
    assert check_assumptions(i, 1) is None
    assert check_assumptions(Dummy(integer=None), integer=True) is None
    assert check_assumptions(Dummy(integer=None), integer=False) is None
    assert isFalse(check_assumptions(Dummy(integer=False), integer=True))
    assert isFalse(check_assumptions(Dummy(integer=True), integer=False))
    assert isTrue(check_assumptions(Dummy(integer=False), integer=None))
    raises(ValueError, lambda : check_assumptions(2 * x, x, positive=True))

def test_failing_assumptions():
    x = Symbol('x', positive=True)
    y = Symbol('y')
    assert failing_assumptions(6 * x + y, **x.assumptions0) == {'real': None, 'imaginary': None, 'complex': None, 'hermitian': None, 'positive': None, 'nonpositive': None, 'nonnegative': None, 'nonzero': None, 'negative': None, 'zero': None, 'extended_real': None, 'finite': None, 'infinite': None, 'extended_negative': None, 'extended_nonnegative': None, 'extended_nonpositive': None, 'extended_nonzero': None, 'extended_positive': None}

def test_common_assumptions():
    assert common_assumptions([0, 1, 2]) == {'algebraic': True, 'irrational': False, 'hermitian': True, 'extended_real': True, 'real': True, 'extended_negative': False, 'extended_nonnegative': True, 'integer': True, 'rational': True, 'imaginary': False, 'complex': True, 'commutative': True, 'noninteger': False, 'composite': False, 'infinite': False, 'nonnegative': True, 'finite': True, 'transcendental': False, 'negative': False}
    assert common_assumptions([0, 1, 2], 'positive integer'.split()) == {'integer': True}
    assert common_assumptions([0, 1, 2], []) == {}
    assert common_assumptions([], ['integer']) == {}
    assert common_assumptions([0], ['integer']) == {'integer': True}

def test_pre_generated_assumption_rules_are_valid():
    pre_generated_assumptions = _load_pre_generated_assumption_rules()
    generated_assumptions = _generate_assumption_rules()
    assert pre_generated_assumptions._to_python() == generated_assumptions._to_python(), 'pre-generated assumptions are invalid, see sympy.core.assumptions._generate_assumption_rules'

def test_ask_shuffle():
    grp = PermutationGroup(Permutation(1, 0, 2), Permutation(2, 1, 3))
    seed(123)
    first = grp.random()
    seed(123)
    simplify(I)
    second = grp.random()
    seed(123)
    simplify(-I)
    third = grp.random()
    assert first == second == third

def test_print():
   assert f'{unhandledCount}/{totalCount}' == f'0/{totalCount}'

