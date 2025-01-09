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
    assert isTrue(ask(Q.real(x)))
    assert isTrue(ask(Q.integer(x)))
    assert isFalse(ask(Q.imaginary(x)))
    assert isFalse(ask(Q.noninteger(x)))
#     assert isFalse(ask(Q.number_unhandled_input(x)))

def test_zero():
    z = Integer(0)
    assert isTrue(ask(Q.commutative(z)))
    assert isTrue(ask(Q.integer(z)))
    assert isTrue(ask(Q.rational(z)))
    assert isTrue(ask(Q.algebraic(z)))
    assert isFalse(ask(Q.transcendental(z)))
    assert isTrue(ask(Q.real(z)))
    assert isTrue(ask(Q.complex(z)))
    assert isFalse(ask(Q.noninteger(z)))
    assert isFalse(ask(Q.irrational(z)))
    assert isFalse(ask(Q.imaginary(z)))
    assert isFalse(ask(Q.positive(z)))
    assert isFalse(ask(Q.negative(z)))
    assert isTrue(ask(Q.nonpositive(z)))
    assert isTrue(ask(Q.nonnegative(z)))
    assert isTrue(ask(Q.even(z)))
    assert isFalse(ask(Q.odd(z)))
    assert isTrue(ask(Q.finite(z)))
    assert isFalse(ask(Q.infinite(z)))
#     assert isTrue(ask(Q.comparable_unhandled_input(z)))
    assert isFalse(ask(Q.prime(z)))
    assert isFalse(ask(Q.composite(z)))
#     assert isTrue(ask(Q.number_unhandled_input(z)))

def test_one():
    z = Integer(1)
    assert isTrue(ask(Q.commutative(z)))
    assert isTrue(ask(Q.integer(z)))
    assert isTrue(ask(Q.rational(z)))
    assert isTrue(ask(Q.algebraic(z)))
    assert isFalse(ask(Q.transcendental(z)))
    assert isTrue(ask(Q.real(z)))
    assert isTrue(ask(Q.complex(z)))
    assert isFalse(ask(Q.noninteger(z)))
    assert isFalse(ask(Q.irrational(z)))
    assert isFalse(ask(Q.imaginary(z)))
    assert isTrue(ask(Q.positive(z)))
    assert isFalse(ask(Q.negative(z)))
    assert isFalse(ask(Q.nonpositive(z)))
    assert isTrue(ask(Q.nonnegative(z)))
    assert isFalse(ask(Q.even(z)))
    assert isTrue(ask(Q.odd(z)))
    assert isTrue(ask(Q.finite(z)))
    assert isFalse(ask(Q.infinite(z)))
#     assert isTrue(ask(Q.comparable_unhandled_input(z)))
    assert isFalse(ask(Q.prime(z)))
#     assert isTrue(ask(Q.number_unhandled_input(z)))
    assert isFalse(ask(Q.composite(z)))

def test_negativeone():
    z = Integer(-1)
    assert isTrue(ask(Q.commutative(z)))
    assert isTrue(ask(Q.integer(z)))
    assert isTrue(ask(Q.rational(z)))
    assert isTrue(ask(Q.algebraic(z)))
    assert isFalse(ask(Q.transcendental(z)))
    assert isTrue(ask(Q.real(z)))
    assert isTrue(ask(Q.complex(z)))
    assert isFalse(ask(Q.noninteger(z)))
    assert isFalse(ask(Q.irrational(z)))
    assert isFalse(ask(Q.imaginary(z)))
    assert isFalse(ask(Q.positive(z)))
    assert isTrue(ask(Q.negative(z)))
    assert isTrue(ask(Q.nonpositive(z)))
    assert isFalse(ask(Q.nonnegative(z)))
    assert isFalse(ask(Q.even(z)))
    assert isTrue(ask(Q.odd(z)))
    assert isTrue(ask(Q.finite(z)))
    assert isFalse(ask(Q.infinite(z)))
#     assert isTrue(ask(Q.comparable_unhandled_input(z)))
    assert isFalse(ask(Q.prime(z)))
    assert isFalse(ask(Q.composite(z)))
#     assert isTrue(ask(Q.number_unhandled_input(z)))

def test_infinity():
    oo = S.Infinity
    assert isTrue(ask(Q.commutative(oo)))
    assert isFalse(ask(Q.integer(oo)))
    assert isFalse(ask(Q.rational(oo)))
    assert isFalse(ask(Q.algebraic(oo)))
    assert isFalse(ask(Q.transcendental(oo)))
    assert isTrue(ask(Q.extended_real(oo)))
    assert isFalse(ask(Q.real(oo)))
    assert isFalse(ask(Q.complex(oo)))
    assert isTrue(ask(Q.noninteger(oo)))
    assert isFalse(ask(Q.irrational(oo)))
    assert isFalse(ask(Q.imaginary(oo)))
    assert isFalse(ask(Q.nonzero(oo)))
    assert isFalse(ask(Q.positive(oo)))
    assert isFalse(ask(Q.negative(oo)))
    assert isFalse(ask(Q.nonpositive(oo)))
    assert isFalse(ask(Q.nonnegative(oo)))
    assert isTrue(ask(Q.extended_nonzero(oo)))
    assert isTrue(ask(Q.extended_positive(oo)))
    assert isFalse(ask(Q.extended_negative(oo)))
    assert isFalse(ask(Q.extended_nonpositive(oo)))
    assert isTrue(ask(Q.extended_nonnegative(oo)))
    assert isFalse(ask(Q.even(oo)))
    assert isFalse(ask(Q.odd(oo)))
    assert isFalse(ask(Q.finite(oo)))
    assert isTrue(ask(Q.infinite(oo)))
#     assert isTrue(ask(Q.comparable_unhandled_input(oo)))
    assert isFalse(ask(Q.prime(oo)))
    assert isFalse(ask(Q.composite(oo)))
#     assert isTrue(ask(Q.number_unhandled_input(oo)))

def test_neg_infinity():
    mm = S.NegativeInfinity
    assert isTrue(ask(Q.commutative(mm)))
    assert isFalse(ask(Q.integer(mm)))
    assert isFalse(ask(Q.rational(mm)))
    assert isFalse(ask(Q.algebraic(mm)))
    assert isFalse(ask(Q.transcendental(mm)))
    assert isTrue(ask(Q.extended_real(mm)))
    assert isFalse(ask(Q.real(mm)))
    assert isFalse(ask(Q.complex(mm)))
    assert isTrue(ask(Q.noninteger(mm)))
    assert isFalse(ask(Q.irrational(mm)))
    assert isFalse(ask(Q.imaginary(mm)))
    assert isFalse(ask(Q.nonzero(mm)))
    assert isFalse(ask(Q.positive(mm)))
    assert isFalse(ask(Q.negative(mm)))
    assert isFalse(ask(Q.nonpositive(mm)))
    assert isFalse(ask(Q.nonnegative(mm)))
    assert isTrue(ask(Q.extended_nonzero(mm)))
    assert isFalse(ask(Q.extended_positive(mm)))
    assert isTrue(ask(Q.extended_negative(mm)))
    assert isTrue(ask(Q.extended_nonpositive(mm)))
    assert isFalse(ask(Q.extended_nonnegative(mm)))
    assert isFalse(ask(Q.even(mm)))
    assert isFalse(ask(Q.odd(mm)))
    assert isFalse(ask(Q.finite(mm)))
    assert isTrue(ask(Q.infinite(mm)))
#     assert isTrue(ask(Q.comparable_unhandled_input(mm)))
    assert isFalse(ask(Q.prime(mm)))
    assert isFalse(ask(Q.composite(mm)))
#     assert isTrue(ask(Q.number_unhandled_input(mm)))

def test_zoo():
    zoo = S.ComplexInfinity
    assert isFalse(ask(Q.complex(zoo)))
    assert isFalse(ask(Q.real(zoo)))
    assert isFalse(ask(Q.prime(zoo)))

def test_nan():
    nan = S.NaN
    assert isTrue(ask(Q.commutative(nan)))
    assert ask(Q.integer(nan)) is None
    assert ask(Q.rational(nan)) is None
    assert ask(Q.algebraic(nan)) is None
    assert ask(Q.transcendental(nan)) is None
    assert ask(Q.real(nan)) is None
    assert ask(Q.complex(nan)) is None
    assert ask(Q.noninteger(nan)) is None
    assert ask(Q.irrational(nan)) is None
    assert ask(Q.imaginary(nan)) is None
    assert ask(Q.positive(nan)) is None
    assert ask(Q.negative(nan)) is None
    assert ask(Q.nonpositive(nan)) is None
    assert ask(Q.nonnegative(nan)) is None
    assert ask(Q.even(nan)) is None
    assert ask(Q.odd(nan)) is None
    assert ask(Q.finite(nan)) is None
    assert ask(Q.infinite(nan)) is None
#     assert isFalse(ask(Q.comparable_unhandled_input(nan)))
    assert ask(Q.prime(nan)) is None
    assert ask(Q.composite(nan)) is None
#     assert isTrue(ask(Q.number_unhandled_input(nan)))

def test_pos_rational():
    r = Rational(3, 4)
    assert isTrue(ask(Q.commutative(r)))
    assert isFalse(ask(Q.integer(r)))
    assert isTrue(ask(Q.rational(r)))
    assert isTrue(ask(Q.algebraic(r)))
    assert isFalse(ask(Q.transcendental(r)))
    assert isTrue(ask(Q.real(r)))
    assert isTrue(ask(Q.complex(r)))
    assert isTrue(ask(Q.noninteger(r)))
    assert isFalse(ask(Q.irrational(r)))
    assert isFalse(ask(Q.imaginary(r)))
    assert isTrue(ask(Q.positive(r)))
    assert isFalse(ask(Q.negative(r)))
    assert isFalse(ask(Q.nonpositive(r)))
    assert isTrue(ask(Q.nonnegative(r)))
    assert isFalse(ask(Q.even(r)))
    assert isFalse(ask(Q.odd(r)))
    assert isTrue(ask(Q.finite(r)))
    assert isFalse(ask(Q.infinite(r)))
#     assert isTrue(ask(Q.comparable_unhandled_input(r)))
    assert isFalse(ask(Q.prime(r)))
    assert isFalse(ask(Q.composite(r)))
    r = Rational(1, 4)
    assert isFalse(ask(Q.nonpositive(r)))
    assert isTrue(ask(Q.positive(r)))
    assert isFalse(ask(Q.negative(r)))
    assert isTrue(ask(Q.nonnegative(r)))
    r = Rational(5, 4)
    assert isFalse(ask(Q.negative(r)))
    assert isTrue(ask(Q.positive(r)))
    assert isFalse(ask(Q.nonpositive(r)))
    assert isTrue(ask(Q.nonnegative(r)))
    r = Rational(5, 3)
    assert isTrue(ask(Q.nonnegative(r)))
    assert isTrue(ask(Q.positive(r)))
    assert isFalse(ask(Q.negative(r)))
    assert isFalse(ask(Q.nonpositive(r)))

def test_neg_rational():
    r = Rational(-3, 4)
    assert isFalse(ask(Q.positive(r)))
    assert isTrue(ask(Q.nonpositive(r)))
    assert isTrue(ask(Q.negative(r)))
    assert isFalse(ask(Q.nonnegative(r)))
    r = Rational(-1, 4)
    assert isTrue(ask(Q.nonpositive(r)))
    assert isFalse(ask(Q.positive(r)))
    assert isTrue(ask(Q.negative(r)))
    assert isFalse(ask(Q.nonnegative(r)))
    r = Rational(-5, 4)
    assert isTrue(ask(Q.negative(r)))
    assert isFalse(ask(Q.positive(r)))
    assert isTrue(ask(Q.nonpositive(r)))
    assert isFalse(ask(Q.nonnegative(r)))
    r = Rational(-5, 3)
    assert isFalse(ask(Q.nonnegative(r)))
    assert isFalse(ask(Q.positive(r)))
    assert isTrue(ask(Q.negative(r)))
    assert isTrue(ask(Q.nonpositive(r)))

def test_pi():
    z = S.Pi
    assert isTrue(ask(Q.commutative(z)))
    assert isFalse(ask(Q.integer(z)))
    assert isFalse(ask(Q.rational(z)))
    assert isFalse(ask(Q.algebraic(z)))
    assert isTrue(ask(Q.transcendental(z)))
    assert isTrue(ask(Q.real(z)))
    assert isTrue(ask(Q.complex(z)))
    assert isTrue(ask(Q.noninteger(z)))
    assert isTrue(ask(Q.irrational(z)))
    assert isFalse(ask(Q.imaginary(z)))
    assert isTrue(ask(Q.positive(z)))
    assert isFalse(ask(Q.negative(z)))
    assert isFalse(ask(Q.nonpositive(z)))
    assert isTrue(ask(Q.nonnegative(z)))
    assert isFalse(ask(Q.even(z)))
    assert isFalse(ask(Q.odd(z)))
    assert isTrue(ask(Q.finite(z)))
    assert isFalse(ask(Q.infinite(z)))
#     assert isTrue(ask(Q.comparable_unhandled_input(z)))
    assert isFalse(ask(Q.prime(z)))
    assert isFalse(ask(Q.composite(z)))

def test_E():
    z = S.Exp1
    assert isTrue(ask(Q.commutative(z)))
    assert isFalse(ask(Q.integer(z)))
    assert isFalse(ask(Q.rational(z)))
    assert isFalse(ask(Q.algebraic(z)))
    assert isTrue(ask(Q.transcendental(z)))
    assert isTrue(ask(Q.real(z)))
    assert isTrue(ask(Q.complex(z)))
    assert isTrue(ask(Q.noninteger(z)))
    assert isTrue(ask(Q.irrational(z)))
    assert isFalse(ask(Q.imaginary(z)))
    assert isTrue(ask(Q.positive(z)))
    assert isFalse(ask(Q.negative(z)))
    assert isFalse(ask(Q.nonpositive(z)))
    assert isTrue(ask(Q.nonnegative(z)))
    assert isFalse(ask(Q.even(z)))
    assert isFalse(ask(Q.odd(z)))
    assert isTrue(ask(Q.finite(z)))
    assert isFalse(ask(Q.infinite(z)))
#     assert isTrue(ask(Q.comparable_unhandled_input(z)))
    assert isFalse(ask(Q.prime(z)))
    assert isFalse(ask(Q.composite(z)))

def test_I():
    z = S.ImaginaryUnit
    assert isTrue(ask(Q.commutative(z)))
    assert isFalse(ask(Q.integer(z)))
    assert isFalse(ask(Q.rational(z)))
    assert isTrue(ask(Q.algebraic(z)))
    assert isFalse(ask(Q.transcendental(z)))
    assert isFalse(ask(Q.real(z)))
    assert isTrue(ask(Q.complex(z)))
    assert isFalse(ask(Q.noninteger(z)))
    assert isFalse(ask(Q.irrational(z)))
    assert isTrue(ask(Q.imaginary(z)))
    assert isFalse(ask(Q.positive(z)))
    assert isFalse(ask(Q.negative(z)))
    assert isFalse(ask(Q.nonpositive(z)))
    assert isFalse(ask(Q.nonnegative(z)))
    assert isFalse(ask(Q.even(z)))
    assert isFalse(ask(Q.odd(z)))
    assert isTrue(ask(Q.finite(z)))
    assert isFalse(ask(Q.infinite(z)))
#     assert isFalse(ask(Q.comparable_unhandled_input(z)))
    assert isFalse(ask(Q.prime(z)))
    assert isFalse(ask(Q.composite(z)))

def test_symbol_real_false():
    a = Symbol('a', real=False)
    assert isFalse(ask(Q.real(a)))
    assert isFalse(ask(Q.integer(a)))
    assert isFalse(ask(Q.zero(a)))
    assert isFalse(ask(Q.negative(a)))
    assert isFalse(ask(Q.positive(a)))
    assert isFalse(ask(Q.nonnegative(a)))
    assert isFalse(ask(Q.nonpositive(a)))
    assert isFalse(ask(Q.nonzero(a)))
    assert ask(Q.extended_negative(a)) is None
    assert ask(Q.extended_positive(a)) is None
    assert ask(Q.extended_nonnegative(a)) is None
    assert ask(Q.extended_nonpositive(a)) is None
    assert ask(Q.extended_nonzero(a)) is None

def test_symbol_extended_real_false():
    a = Symbol('a', extended_real=False)
    assert isFalse(ask(Q.real(a)))
    assert isFalse(ask(Q.integer(a)))
    assert isFalse(ask(Q.zero(a)))
    assert isFalse(ask(Q.negative(a)))
    assert isFalse(ask(Q.positive(a)))
    assert isFalse(ask(Q.nonnegative(a)))
    assert isFalse(ask(Q.nonpositive(a)))
    assert isFalse(ask(Q.nonzero(a)))
    assert isFalse(ask(Q.extended_negative(a)))
    assert isFalse(ask(Q.extended_positive(a)))
    assert isFalse(ask(Q.extended_nonnegative(a)))
    assert isFalse(ask(Q.extended_nonpositive(a)))
    assert isFalse(ask(Q.extended_nonzero(a)))

def test_symbol_imaginary():
    a = Symbol('a', imaginary=True)
    assert isFalse(ask(Q.real(a)))
    assert isFalse(ask(Q.integer(a)))
    assert isFalse(ask(Q.negative(a)))
    assert isFalse(ask(Q.positive(a)))
    assert isFalse(ask(Q.nonnegative(a)))
    assert isFalse(ask(Q.nonpositive(a)))
    assert isFalse(ask(Q.zero(a)))
    assert isFalse(ask(Q.nonzero(a)))

def test_symbol_zero():
    x = Symbol('x', zero=True)
    assert isFalse(ask(Q.positive(x)))
    assert isTrue(ask(Q.nonpositive(x)))
    assert isFalse(ask(Q.negative(x)))
    assert isTrue(ask(Q.nonnegative(x)))
    assert isTrue(ask(Q.zero(x)))
    assert isFalse(ask(Q.nonzero(x)))
    assert isTrue(ask(Q.finite(x)))

def test_symbol_positive():
    x = Symbol('x', positive=True)
    assert isTrue(ask(Q.positive(x)))
    assert isFalse(ask(Q.nonpositive(x)))
    assert isFalse(ask(Q.negative(x)))
    assert isTrue(ask(Q.nonnegative(x)))
    assert isFalse(ask(Q.zero(x)))
    assert isTrue(ask(Q.nonzero(x)))

def test_neg_symbol_positive():
    x = -Symbol('x', positive=True)
    assert isFalse(ask(Q.positive(x)))
    assert isTrue(ask(Q.nonpositive(x)))
    assert isTrue(ask(Q.negative(x)))
    assert isFalse(ask(Q.nonnegative(x)))
    assert isFalse(ask(Q.zero(x)))
    assert isTrue(ask(Q.nonzero(x)))

def test_symbol_nonpositive():
    x = Symbol('x', nonpositive=True)
    assert isFalse(ask(Q.positive(x)))
    assert isTrue(ask(Q.nonpositive(x)))
    assert ask(Q.negative(x)) is None
    assert ask(Q.nonnegative(x)) is None
    assert ask(Q.zero(x)) is None
    assert ask(Q.nonzero(x)) is None

def test_neg_symbol_nonpositive():
    x = -Symbol('x', nonpositive=True)
    assert ask(Q.positive(x)) is None
    assert ask(Q.nonpositive(x)) is None
    assert isFalse(ask(Q.negative(x)))
    assert isTrue(ask(Q.nonnegative(x)))
    assert ask(Q.zero(x)) is None
    assert ask(Q.nonzero(x)) is None

def test_symbol_falsepositive():
    x = Symbol('x', positive=False)
    assert isFalse(ask(Q.positive(x)))
    assert ask(Q.nonpositive(x)) is None
    assert ask(Q.negative(x)) is None
    assert ask(Q.nonnegative(x)) is None
    assert ask(Q.zero(x)) is None
    assert ask(Q.nonzero(x)) is None

def test_symbol_falsepositive_mul():
    x = 2 * Symbol('x', positive=False)
    assert isFalse(ask(Q.positive(x)))
    assert ask(Q.nonpositive(x)) is None
    assert ask(Q.negative(x)) is None
    assert ask(Q.nonnegative(x)) is None
    assert ask(Q.zero(x)) is None
    assert ask(Q.nonzero(x)) is None

@XFAIL
def test_symbol_infinitereal_mul():
    ix = Symbol('ix', infinite=True, extended_real=True)
    assert ask(Q.extended_positive(-ix)) is None

def test_neg_symbol_falsepositive():
    x = -Symbol('x', positive=False)
    assert ask(Q.positive(x)) is None
    assert ask(Q.nonpositive(x)) is None
    assert isFalse(ask(Q.negative(x)))
    assert ask(Q.nonnegative(x)) is None
    assert ask(Q.zero(x)) is None
    assert ask(Q.nonzero(x)) is None

def test_neg_symbol_falsenegative():
    x = -Symbol('x', negative=False)
    assert isFalse(ask(Q.positive(x)))
    assert ask(Q.nonpositive(x)) is None
    assert ask(Q.negative(x)) is None
    assert ask(Q.nonnegative(x)) is None
    assert ask(Q.zero(x)) is None
    assert ask(Q.nonzero(x)) is None

def test_symbol_falsepositive_real():
    x = Symbol('x', positive=False, real=True)
    assert isFalse(ask(Q.positive(x)))
    assert isTrue(ask(Q.nonpositive(x)))
    assert ask(Q.negative(x)) is None
    assert ask(Q.nonnegative(x)) is None
    assert ask(Q.zero(x)) is None
    assert ask(Q.nonzero(x)) is None

def test_neg_symbol_falsepositive_real():
    x = -Symbol('x', positive=False, real=True)
    assert ask(Q.positive(x)) is None
    assert ask(Q.nonpositive(x)) is None
    assert isFalse(ask(Q.negative(x)))
    assert isTrue(ask(Q.nonnegative(x)))
    assert ask(Q.zero(x)) is None
    assert ask(Q.nonzero(x)) is None

def test_symbol_falsenonnegative():
    x = Symbol('x', nonnegative=False)
    assert isFalse(ask(Q.positive(x)))
    assert ask(Q.nonpositive(x)) is None
    assert ask(Q.negative(x)) is None
    assert isFalse(ask(Q.nonnegative(x)))
    assert isFalse(ask(Q.zero(x)))
    assert ask(Q.nonzero(x)) is None

@XFAIL
def test_neg_symbol_falsenonnegative():
    x = -Symbol('x', nonnegative=False)
    assert ask(Q.positive(x)) is None
    assert isFalse(ask(Q.nonpositive(x)))
    assert isFalse(ask(Q.negative(x)))
    assert ask(Q.nonnegative(x)) is None
    assert isFalse(ask(Q.zero(x)))
    assert isTrue(ask(Q.nonzero(x)))

def test_symbol_falsenonnegative_real():
    x = Symbol('x', nonnegative=False, real=True)
    assert isFalse(ask(Q.positive(x)))
    assert isTrue(ask(Q.nonpositive(x)))
    assert isTrue(ask(Q.negative(x)))
    assert isFalse(ask(Q.nonnegative(x)))
    assert isFalse(ask(Q.zero(x)))
    assert isTrue(ask(Q.nonzero(x)))

def test_neg_symbol_falsenonnegative_real():
    x = -Symbol('x', nonnegative=False, real=True)
    assert isTrue(ask(Q.positive(x)))
    assert isFalse(ask(Q.nonpositive(x)))
    assert isFalse(ask(Q.negative(x)))
    assert isTrue(ask(Q.nonnegative(x)))
    assert isFalse(ask(Q.zero(x)))
    assert isTrue(ask(Q.nonzero(x)))

def test_prime():
    assert isFalse(ask(Q.prime(S.NegativeOne)))
    assert isFalse(ask(Q.prime(S(-2))))
    assert isFalse(ask(Q.prime(S(-4))))
    assert isFalse(ask(Q.prime(S.Zero)))
    assert isFalse(ask(Q.prime(S.One)))
    assert isTrue(ask(Q.prime(S(2))))
    assert isTrue(ask(Q.prime(S(17))))
    assert isFalse(ask(Q.prime(S(4))))

def test_composite():
    assert isFalse(ask(Q.composite(S.NegativeOne)))
    assert isFalse(ask(Q.composite(S(-2))))
    assert isFalse(ask(Q.composite(S(-4))))
    assert isFalse(ask(Q.composite(S.Zero)))
    assert isFalse(ask(Q.composite(S(2))))
    assert isFalse(ask(Q.composite(S(17))))
    assert isTrue(ask(Q.composite(S(4))))
    x = Dummy(integer=True, positive=True, prime=False)
    assert ask(Q.composite(x)) is None
    assert ask(Q.composite(x + 1)) is None
    x = Dummy(positive=True, even=True, prime=False)
    assert isTrue(ask(Q.integer(x)))
    assert isTrue(ask(Q.composite(x)))

def test_prime_symbol():
    x = Symbol('x', prime=True)
    assert isTrue(ask(Q.prime(x)))
    assert isTrue(ask(Q.integer(x)))
    assert isTrue(ask(Q.positive(x)))
    assert isFalse(ask(Q.negative(x)))
    assert isFalse(ask(Q.nonpositive(x)))
    assert isTrue(ask(Q.nonnegative(x)))
    x = Symbol('x', prime=False)
    assert isFalse(ask(Q.prime(x)))
    assert ask(Q.integer(x)) is None
    assert ask(Q.positive(x)) is None
    assert ask(Q.negative(x)) is None
    assert ask(Q.nonpositive(x)) is None
    assert ask(Q.nonnegative(x)) is None

def test_symbol_noncommutative():
    x = Symbol('x', commutative=True)
    assert ask(Q.complex(x)) is None
    x = Symbol('x', commutative=False)
    assert isFalse(ask(Q.integer(x)))
    assert isFalse(ask(Q.rational(x)))
    assert isFalse(ask(Q.algebraic(x)))
    assert isFalse(ask(Q.irrational(x)))
    assert isFalse(ask(Q.real(x)))
    assert isFalse(ask(Q.complex(x)))

def test_other_symbol():
    x = Symbol('x', integer=True)
    assert isTrue(ask(Q.integer(x)))
    assert isTrue(ask(Q.real(x)))
    assert isTrue(ask(Q.finite(x)))
    x = Symbol('x', integer=True, nonnegative=True)
    assert isTrue(ask(Q.integer(x)))
    assert isTrue(ask(Q.nonnegative(x)))
    assert isFalse(ask(Q.negative(x)))
    assert ask(Q.positive(x)) is None
    assert isTrue(ask(Q.finite(x)))
    x = Symbol('x', integer=True, nonpositive=True)
    assert isTrue(ask(Q.integer(x)))
    assert isTrue(ask(Q.nonpositive(x)))
    assert isFalse(ask(Q.positive(x)))
    assert ask(Q.negative(x)) is None
    assert isTrue(ask(Q.finite(x)))
    x = Symbol('x', odd=True)
    assert isTrue(ask(Q.odd(x)))
    assert isFalse(ask(Q.even(x)))
    assert isTrue(ask(Q.integer(x)))
    assert isTrue(ask(Q.finite(x)))
    x = Symbol('x', odd=False)
    assert isFalse(ask(Q.odd(x)))
    assert ask(Q.even(x)) is None
    assert ask(Q.integer(x)) is None
    assert ask(Q.finite(x)) is None
    x = Symbol('x', even=True)
    assert isTrue(ask(Q.even(x)))
    assert isFalse(ask(Q.odd(x)))
    assert isTrue(ask(Q.integer(x)))
    assert isTrue(ask(Q.finite(x)))
    x = Symbol('x', even=False)
    assert isFalse(ask(Q.even(x)))
    assert ask(Q.odd(x)) is None
    assert ask(Q.integer(x)) is None
    assert ask(Q.finite(x)) is None
    x = Symbol('x', integer=True, nonnegative=True)
    assert isTrue(ask(Q.integer(x)))
    assert isTrue(ask(Q.nonnegative(x)))
    assert isTrue(ask(Q.finite(x)))
    x = Symbol('x', integer=True, nonpositive=True)
    assert isTrue(ask(Q.integer(x)))
    assert isTrue(ask(Q.nonpositive(x)))
    assert isTrue(ask(Q.finite(x)))
    x = Symbol('x', rational=True)
    assert isTrue(ask(Q.real(x)))
    assert isTrue(ask(Q.finite(x)))
    x = Symbol('x', rational=False)
    assert ask(Q.real(x)) is None
    assert ask(Q.finite(x)) is None
    x = Symbol('x', irrational=True)
    assert isTrue(ask(Q.real(x)))
    assert isTrue(ask(Q.finite(x)))
    x = Symbol('x', irrational=False)
    assert ask(Q.real(x)) is None
    assert ask(Q.finite(x)) is None
#     with raises(AttributeError):
#         ask(Q.real(x)) = False
    x = Symbol('x', algebraic=True)
    assert isFalse(ask(Q.transcendental(x)))
    x = Symbol('x', transcendental=True)
    assert isFalse(ask(Q.algebraic(x)))
    assert isFalse(ask(Q.rational(x)))
    assert isFalse(ask(Q.integer(x)))

def test_evaluate_false():
    from sympy.core.parameters import evaluate
    from sympy.abc import x, h
    f = 2 ** x ** 7
    with evaluate(False):
        fh = f.xreplace({x: x + h})
#         assert ask(Q.rational(fh.exp)) is None

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
    assert isTrue(ask(Q.positive(a)))
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
    assert isFalse(ask(Q.extended_positive(n + xf)))
    assert isTrue(ask(Q.extended_positive(p + xf)))
    assert isTrue(ask(Q.extended_negative(n + xf)))
    assert isFalse(ask(Q.extended_negative(p + xf)))
    assert ask(Q.extended_negative(x - S.Infinity)) is None
    assert isTrue(ask(Q.extended_positive(p + nn)))
    assert isTrue(ask(Q.extended_negative(n + np)))
    assert ask(Q.extended_positive(p + r)) is None

def test_Add_is_imaginary():
    nn = Dummy(nonnegative=True)
    assert isTrue(ask(Q.imaginary(I * nn + I)))

def test_Add_is_algebraic():
    a = Symbol('a', algebraic=True)
    b = Symbol('a', algebraic=True)
    na = Symbol('na', algebraic=False)
    nb = Symbol('nb', algebraic=False)
    x = Symbol('x')
    assert isTrue(ask(Q.algebraic(a + b)))
    assert ask(Q.algebraic(na + nb)) is None
    assert isFalse(ask(Q.algebraic(a + na)))
    assert ask(Q.algebraic(a + x)) is None
    assert ask(Q.algebraic(na + x)) is None

def test_Mul_is_algebraic():
    a = Symbol('a', algebraic=True)
    b = Symbol('b', algebraic=True)
    na = Symbol('na', algebraic=False)
    an = Symbol('an', algebraic=True, nonzero=True)
    nb = Symbol('nb', algebraic=False)
    x = Symbol('x')
    assert isTrue(ask(Q.algebraic(a * b)))
    assert ask(Q.algebraic(na * nb)) is None
    assert ask(Q.algebraic(a * na)) is None
    assert isFalse(ask(Q.algebraic(an * na)))
    assert ask(Q.algebraic(a * x)) is None
    assert ask(Q.algebraic(na * x)) is None

def test_Pow_is_algebraic():
    e = Symbol('e', algebraic=True)
    assert isTrue(ask(Q.algebraic(Pow(1, e, evaluate=False))))
    assert isTrue(ask(Q.algebraic(Pow(0, e, evaluate=False))))
    a = Symbol('a', algebraic=True)
    azf = Symbol('azf', algebraic=True, zero=False)
    na = Symbol('na', algebraic=False)
    ia = Symbol('ia', algebraic=True, irrational=True)
    ib = Symbol('ib', algebraic=True, irrational=True)
    r = Symbol('r', rational=True)
    x = Symbol('x')
    assert isTrue(ask(Q.algebraic(a ** 2)))
    assert ask(Q.algebraic(a ** r)) is None
    assert isTrue(ask(Q.algebraic(azf ** r)))
    assert ask(Q.algebraic(a ** x)) is None
    assert ask(Q.algebraic(na ** r)) is None
    assert isTrue(ask(Q.algebraic(ia ** r)))
    assert isFalse(ask(Q.algebraic(ia ** ib)))
    assert ask(Q.algebraic(a ** e)) is None
    assert isFalse(ask(Q.algebraic(Pow(2, sqrt(2), evaluate=False))))
    assert isFalse(ask(Q.algebraic(Pow(S.GoldenRatio, sqrt(3), evaluate=False))))
    t = Symbol('t', real=True, transcendental=True)
    n = Symbol('n', integer=True)
    assert ask(Q.algebraic(t ** n)) is None
    assert ask(Q.integer(t ** n)) is None
    assert isFalse(ask(Q.algebraic(pi ** 3)))
    r = Symbol('r', zero=True)
    assert isTrue(ask(Q.algebraic(pi ** r)))

def test_Mul_is_prime_composite():
    x = Symbol('x', positive=True, integer=True)
    y = Symbol('y', positive=True, integer=True)
    assert ask(Q.prime(x * y)) is None
    assert isFalse(ask(Q.prime((x + 1) * (y + 1))))
    assert isTrue(ask(Q.composite((x + 1) * (y + 1))))
    x = Symbol('x', positive=True)
    assert ask(Q.prime((x + 1) * (y + 1))) is None
    assert ask(Q.composite((x + 1) * (y + 1))) is None

def test_Pow_is_pos_neg():
    z = Symbol('z', real=True)
    w = Symbol('w', nonpositive=True)
    assert isTrue(ask(Q.positive(S.NegativeOne ** S(2))))
    assert isTrue(ask(Q.positive(S.One ** z)))
    assert isFalse(ask(Q.positive(S.NegativeOne ** S(3))))
    assert isTrue(ask(Q.positive(S.Zero ** S.Zero)))
    assert isFalse(ask(Q.positive(w ** S(3))))
    assert ask(Q.positive(w ** S(2))) is None
    assert isFalse(ask(Q.positive(I ** 2)))
    assert isTrue(ask(Q.positive(I ** 4)))
    p = Symbol('p', zero=True)
    q = Symbol('q', zero=False, real=True)
    j = Symbol('j', zero=False, even=True)
    x = Symbol('x', zero=True)
    y = Symbol('y', zero=True)
    assert isFalse(ask(Q.positive(p ** q)))
    assert isFalse(ask(Q.negative(p ** q)))
    assert isFalse(ask(Q.positive(p ** j)))
    assert isTrue(ask(Q.positive(x ** y)))
    assert isFalse(ask(Q.negative(x ** y)))

def test_Pow_is_prime_composite():
    x = Symbol('x', positive=True, integer=True)
    y = Symbol('y', positive=True, integer=True)
    assert ask(Q.prime(x ** y)) is None
    assert isFalse(ask(Q.prime(x ** (y + 1))))
    assert ask(Q.composite(x ** (y + 1))) is None
    assert isTrue(ask(Q.composite((x + 1) ** (y + 1))))
    assert isTrue(ask(Q.composite((-x - 1) ** (2 * y))))
    x = Symbol('x', positive=True)
    assert ask(Q.prime(x ** y)) is None

def test_Mul_is_infinite():
    x = Symbol('x')
    f = Symbol('f', finite=True)
    i = Symbol('i', infinite=True)
    z = Dummy(zero=True)
    nzf = Dummy(finite=True, zero=False)
    from sympy.core.mul import Mul
    assert ask(Q.finite(x * f)) is None
    assert ask(Q.finite(x * i)) is None
    assert ask(Q.finite(f * i)) is None
    assert ask(Q.finite(x * f * i)) is None
    assert ask(Q.finite(z * i)) is None
    assert isFalse(ask(Q.finite(nzf * i)))
    assert isTrue(ask(Q.finite(z * f)))
    assert isTrue(ask(Q.finite(Mul(0, f, evaluate=False))))
    assert ask(Q.finite(Mul(0, i, evaluate=False))) is None
    assert ask(Q.infinite(x * f)) is None
    assert ask(Q.infinite(x * i)) is None
    assert ask(Q.infinite(f * i)) is None
    assert ask(Q.infinite(x * f * i)) is None
    assert ask(Q.infinite(z * i)) is ask(Q.infinite(S.NaN))
    assert isTrue(ask(Q.infinite(nzf * i)))
    assert isFalse(ask(Q.infinite(z * f)))
    assert isFalse(ask(Q.infinite(Mul(0, f, evaluate=False))))
    assert ask(Q.infinite(Mul(0, i, evaluate=False))) is ask(Q.infinite(S.NaN))

def test_Add_is_infinite():
    x = Symbol('x')
    f = Symbol('f', finite=True)
    i = Symbol('i', infinite=True)
    i2 = Symbol('i2', infinite=True)
    z = Dummy(zero=True)
    nzf = Dummy(finite=True, zero=False)
    from sympy.core.add import Add
    assert ask(Q.finite(x + f)) is None
    assert ask(Q.finite(x + i)) is None
    assert isFalse(ask(Q.finite(f + i)))
    assert ask(Q.finite(x + f + i)) is None
    assert isFalse(ask(Q.finite(z + i)))
    assert isFalse(ask(Q.finite(nzf + i)))
    assert isTrue(ask(Q.finite(z + f)))
    assert ask(Q.finite(i + i2)) is None
    assert isTrue(ask(Q.finite(Add(0, f, evaluate=False))))
    assert isFalse(ask(Q.finite(Add(0, i, evaluate=False))))
    assert ask(Q.infinite(x + f)) is None
    assert ask(Q.infinite(x + i)) is None
    assert isTrue(ask(Q.infinite(f + i)))
    assert ask(Q.infinite(x + f + i)) is None
    assert isTrue(ask(Q.infinite(z + i)))
    assert isTrue(ask(Q.infinite(nzf + i)))
    assert isFalse(ask(Q.infinite(z + f)))
    assert ask(Q.infinite(i + i2)) is None
    assert isFalse(ask(Q.infinite(Add(0, f, evaluate=False))))
    assert isTrue(ask(Q.infinite(Add(0, i, evaluate=False))))

def test_special_is_rational():
    i = Symbol('i', integer=True)
    i2 = Symbol('i2', integer=True)
    ni = Symbol('ni', integer=True, nonzero=True)
    r = Symbol('r', rational=True)
    rn = Symbol('r', rational=True, nonzero=True)
    nr = Symbol('nr', irrational=True)
    x = Symbol('x')
    assert isFalse(ask(Q.rational(sqrt(3))))
    assert isFalse(ask(Q.rational(3 + sqrt(3))))
    assert isFalse(ask(Q.rational(3 * sqrt(3))))
    assert isFalse(ask(Q.rational(exp(3))))
    assert isFalse(ask(Q.rational(exp(ni))))
    assert isFalse(ask(Q.rational(exp(rn))))
    assert ask(Q.rational(exp(x))) is None
    assert isTrue(ask(Q.rational(exp(log(3), evaluate=False))))
    assert isTrue(ask(Q.rational(log(exp(3), evaluate=False))))
    assert isFalse(ask(Q.rational(log(3))))
    assert isFalse(ask(Q.rational(log(ni + 1))))
    assert isFalse(ask(Q.rational(log(rn + 1))))
    assert ask(Q.rational(log(x))) is None
    assert ask(Q.rational(sqrt(3) + sqrt(5))) is None
    assert isFalse(ask(Q.rational(sqrt(3) + S.Pi)))
    assert ask(Q.rational(x ** i)) is None
    assert isTrue(ask(Q.rational(i ** i)))
    assert ask(Q.rational(i ** i2)) is None
    assert ask(Q.rational(r ** i)) is None
    assert ask(Q.rational(r ** r)) is None
    assert ask(Q.rational(r ** x)) is None
    assert ask(Q.rational(nr ** i)) is None
#     assert ask(Q.rational(nr ** Symbol('z', zero=True)))
    assert isFalse(ask(Q.rational(sin(1))))
    assert isFalse(ask(Q.rational(sin(ni))))
    assert isFalse(ask(Q.rational(sin(rn))))
    assert ask(Q.rational(sin(x))) is None
    assert isFalse(ask(Q.rational(asin(r))))
    assert isTrue(ask(Q.rational(sin(asin(3), evaluate=False))))

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
        assert isTrue(ask(Q.real(x)))
        assert isFalse(ask(Q.positive(x)))
        assert ask(Q.positive(cls('', real=True, positive=None))) is None
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
    assert isTrue(ask(Q.real((-1) ** I)))
    assert isTrue(ask(Q.real((-1) ** (I * 2))))
    assert isTrue(ask(Q.real((-1) ** (I / 2))))
    assert isTrue(ask(Q.real((-1) ** (I * S.Pi))))
    assert isTrue(ask(Q.real(I ** (I + 2))))

def test_issue_2730():
    assert isFalse(ask(Q.real(1 / (1 + I))))

def test_issue_4149():
    assert isTrue(ask(Q.complex(3 + I)))
    assert isFalse(ask(Q.imaginary(3 + I)))
    assert isTrue(ask(Q.imaginary(3 * I + S.Pi * I)))
    y = Symbol('y', real=True)
    assert ask(Q.imaginary(3 * I + S.Pi * I + y * I)) is None
    p = Symbol('p', positive=True)
    assert isTrue(ask(Q.imaginary(3 * I + S.Pi * I + p * I)))
    n = Symbol('n', negative=True)
    assert isTrue(ask(Q.imaginary(-3 * I - S.Pi * I + n * I)))
    i = Symbol('i', imaginary=True)
    assert [ask(Q.imaginary(i ** a)) for a in range(4)] == [False, True, False, True]
    e = S('-sqrt(3)*I/2 + 0.866025403784439*I')
    assert isFalse(ask(Q.real(e)))
    assert isTrue(ask(Q.imaginary(e)))

def test_issue_2920():
    n = Symbol('n', negative=True)
    assert isTrue(ask(Q.imaginary(sqrt(n))))

def test_issue_7899():
    x = Symbol('x', real=True)
    assert ask(Q.real(I * x)) is None
    assert ask(Q.zero((x - I) * (x - 1))) is None
    assert ask(Q.real((x - I) * (x - 1))) is None

@XFAIL
def test_issue_7993():
    x = Dummy(integer=True)
    y = Dummy(noninteger=True)
    assert isFalse(ask(Q.zero(x - y)))

def test_issue_8075():
    raises(InconsistentAssumptions, lambda : Dummy(zero=True, finite=False))
    raises(InconsistentAssumptions, lambda : Dummy(zero=True, infinite=True))

def test_issue_8642():
    x = Symbol('x', real=True, integer=False)
    assert ask(Q.integer(x * 2)) is None, ask(Q.integer(x * 2))

def test_issues_8632_8633_8638_8675_8992():
    p = Dummy(integer=True, positive=True)
    nn = Dummy(integer=True, nonnegative=True)
    assert isTrue(ask(Q.positive(p - S.Half)))
    assert isTrue(ask(Q.nonnegative(p - 1)))
    assert isTrue(ask(Q.positive(nn + 1)))
    assert isTrue(ask(Q.nonpositive(-p + 1)))
    assert isTrue(ask(Q.negative(-nn - 1)))
    prime = Dummy(prime=True)
    assert isTrue(ask(Q.nonnegative(prime - 2)))
    assert ask(Q.nonnegative(prime - 3)) is None
    even = Dummy(positive=True, even=True)
    assert isTrue(ask(Q.nonnegative(even - 2)))
    p = Dummy(positive=True)
    assert isTrue(ask(Q.negative(p / (p + 1) - 1)))
    assert isTrue(ask(Q.positive((p + 2) ** 3 - S.Half)))
    n = Dummy(negative=True)
    assert isTrue(ask(Q.nonpositive(n - 3)))

def test_issue_9115_9150():
    n = Dummy('n', integer=True, nonnegative=True)
    assert (factorial(n) >= 1) == True
    assert (factorial(n) < 1) == False
    assert ask(Q.even(factorial(n + 1))) is None
    assert isTrue(ask(Q.even(factorial(n + 2))))
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
    assert isFalse(ask(Q.zero(1 + i)))
    a = Dummy('a', zero=True)
    assert isFalse(ask(Q.zero(a + I)))
    assert ask(Q.zero(a + r * I)) is None
    assert isTrue(ask(Q.imaginary(a + I)))
    assert ask(Q.imaginary(a + x + I)) is None
    assert ask(Q.imaginary(a + r * I + I)) is None

def test_complex_reciprocal_imaginary():
    assert isFalse(ask(Q.imaginary(1 / (4 + 3 * I))))

def test_issue_16313():
    x = Symbol('x', extended_real=False)
    k = Symbol('k', real=True)
    l = Symbol('l', real=True, zero=False)
    assert isFalse(ask(Q.real(-x)))
    assert ask(Q.real(k * x)) is None
    assert isFalse(ask(Q.real(l * x)))
    assert ask(Q.real(l * x * x)) is None
    assert isFalse(ask(Q.positive(-x)))

def test_issue_16579():
    x = Symbol('x', extended_real=True, infinite=False)
    y = Symbol('y', extended_real=True, finite=False)
    assert isTrue(ask(Q.finite(x)))
    assert isTrue(ask(Q.infinite(y)))
    c = Symbol('c', complex=True)
    assert isTrue(ask(Q.finite(c)))
    raises(InconsistentAssumptions, lambda : Dummy(complex=True, finite=False))
    nf = Symbol('nf', finite=False)
    assert isTrue(ask(Q.infinite(nf)))

def test_issue_17556():
    z = I * oo
    assert isFalse(ask(Q.imaginary(z)))
    assert isFalse(ask(Q.finite(z)))

def test_issue_21651():
    k = Symbol('k', positive=True, integer=True)
    exp = 2 * 2 ** (-k)
    assert ask(Q.integer(exp)) is None

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

