from sympy.testing.pytest import XFAIL
from sympy.assumptions.ask import ask, Q
from sympy.assumptions.assume import assuming
from sympy.assumptions.refine import refine
from sympy.logic.boolalg import Equivalent
from sympy.functions.elementary.miscellaneous import sqrt
from sympy.functions.special.delta_functions import Heaviside
from sympy.abc import a, b, c, w, x, y, z


@XFAIL
def test_inequalities():
    # Test equivalent ways of writing Q.positive, Q.zero, Q.negative
    assert ask(Equivalent(Q.gt(x, 0), Q.positive(x))) is True
    assert ask(Equivalent(Q.lt(x, 0), Q.negative(x))) is True
    assert ask(Equivalent(Q.eq(x, 0), Q.zero(x))) is True
    assert ask(Equivalent(Q.ge(x, 0), Q.positive(x) | Q.zero(x))) is True
    assert ask(Equivalent(Q.le(x, 0), Q.negative(x) | Q.zero(x))) is True

    # test more complex problems
    assert ask(x > z, (x > y) & (y > z)) is True
    assert ask(x > z,  (x > w) & (w > y) & (y > z)) is True
    assert ask(x > z, ((x > y) & (y > z)) | ((x > w) & (w > y) & (y > z))) is True

    # test assumptions that mix inequalities and non-inequality unary assumptions
    assert ask(x > 0, Q.positive(x) & Q.prime(y))

    #https://stackoverflow.com/questions/21958031/simplify-a-simple-inequity-with-sympy/21978199#21978199
    with assuming((x > y) & (x > 0) & (y > 0)):
        assert ask(x+y < 2*x) is True
        assert ask(x > 2*y) is None


def test_number_line_properties():
    # From:
    # https://en.wikipedia.org/wiki/Inequality_(mathematics)#Properties_on_the_number_line

    # Converse
    # a ≤ b and b ≥ a are equivalent.
    ask(Equivalent(a <= b, b >= a))

    # Transitivity
    # If a ≤ b and b ≤ c, then a ≤ c.
    assert ask(a <= c, (a <= b) & (b <= c)) is True
    # If a ≤ b and b < c, then a < c.
    assert ask(a < c, (a <= b) & (b < c)) is True
    # If a < b and b ≤ c, then a < c.
    assert ask(a < c, (a < b) & (b <= c)) is True

    # Addition and subtraction
    # If a ≤ b, then a + c ≤ b + c and a − c ≤ b − c.
    assert ask(a + c <= b + c, a <= b) is True
    assert ask(a - c <= b - c, a <= b) is True

    # Multiplication and division
    # If a ≤ b and c > 0, then ac ≤ bc and a/c ≤ b/c. (True for non-zero c)
    assert ask(a*c <= b*c, (a <= b) & (c > 0) & ~ Q.zero(c)) is True
    assert ask(a/c <= b/c, (a <= b) & (c > 0) & ~ Q.zero(c)) is True
    # If a ≤ b and c < 0, then ac ≥ bc and a/c ≥ b/c. (True for non-zero c)
    assert ask(a*c >= b*c, (a <= b) & (c < 0) & ~ Q.zero(c)) is True
    assert ask(a/c >= b/c, (a <= b) & (c < 0) & ~ Q.zero(c)) is True

    # Additive inverse
    # If a ≤ b, then −a ≥ −b.
    assert ask(-a >= -b, a <= b) is True

    # Multiplicative inverse
    # For a, b that are both negative or both positive:
    # If a ≤ b, then 1/a ≥ 1/b .
    assert ask(1/a >= 1/b, (a <= b) & Q.positive(x) & Q.positive(b)) is True
    assert ask(1/a >= 1/b, (a <= b) & Q.negative(x) & Q.negative(b)) is True


@XFAIL
def test_equality():
    # test substitution property of equality
    assert ask(Q.prime(x), Q.eq(x, y) & Q.prime(y)) is True
    assert ask(Q.real(x), Q.eq(x, y) & Q.real(y)) is True
    assert ask(Q.imaginary(x), Q.eq(x, y) & Q.imaginary(y)) is True


@XFAIL
def test_refine():
    # https://groups.google.com/g/sympy/c/tVo7iZx1ts0/m/qxRqBX0GAwAJ
    assert refine(z**2 + w**2 > 0, Q.positive(z) & Q.positive(w)) is True
    # inspired from https://stackoverflow.com/questions/19553652/sympy-limit-symbol-variable-to-interval/19579453#19579453
    assert refine(sqrt((x - 1) ** 2), x > 1) == x-1
    # https://stackoverflow.com/questions/67217022/simplify-expression-with-assumptions-involving-relations-between-variables-in-sy?rq=3
    assert refine(a+b-c, Q.eq(a+c, c)) == 0

    # test piecewise
    refine(Heaviside(x), x > 2) == 1
    refine(Heaviside(x-1), x > 2) == 1