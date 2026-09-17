from __future__ import annotations
from sympy import I, Q, S, sqrt, symbols
from sympy.assumptions.lra_atoms import LRAConstraint, UnhandledInput
from sympy.testing.pytest import raises


def test_LRAConstraint_frozen():
    x = symbols("x", real=True)
    c = LRAConstraint(Q.gt, 2*x + 2, 2)
    raises(AttributeError, lambda: setattr(c, "function", Q.lt))
    raises(AttributeError, lambda: setattr(c, "lhs", x))
    raises(AttributeError, lambda: setattr(c, "rhs", S.One))
    raises(AttributeError, lambda: setattr(c, "terms", ((x, S.One),)))
    raises(AttributeError, lambda: setattr(c, "var_coeff", -S.One))
    raises(AttributeError, lambda: setattr(c, "const", S.One))
    raises(AttributeError, lambda: setattr(c, "equality", True))
    raises(AttributeError, lambda: setattr(c, "strict", False))


def test_LRAConstraint_equality_and_hashing():
    x = symbols("x", real=True)
    y = symbols("x", real=True)
    c1 = LRAConstraint(Q.gt, 2*x + 2, 2)
    c2 = LRAConstraint(Q.gt, 2*y + 2, 2)
    assert c1 == c2
    assert hash(c1) == hash(c2)
    assert c1.terms == c2.terms
    assert c1.var_coeff == c2.var_coeff
    assert c1.const == c2.const
    assert c1.equality == c2.equality
    assert c1.strict == c2.strict

    h = hash(c1)
    table = {c1: "atom"}
    seen = {c1}
    assert hash(c1) == h
    assert table[c2] == "atom"
    assert c2 in seen
    assert len(seen) == 1

    c3 = LRAConstraint(Q.eq, 2*x + 2, 2)
    assert c1 != c3
    assert len({c1, c3}) == 2
    assert not c1 == "Q.gt(2*x + 2, 2)"


def test_LRAConstraint_rejects_nonreal_direction():
    x = symbols("x", real=True)
    raises(UnhandledInput, lambda: LRAConstraint(Q.gt, I*x, S.Zero))


def test_LRAConstraint_irrational_direction():
    x, y = symbols("x y", real=True)
    c = LRAConstraint(Q.gt, sqrt(2)*x, S.Zero)
    assert c.terms == ((x, S.One),)
    assert c.var_coeff == -sqrt(2)
    assert c.const == S.Zero
    assert not c.equality and c.strict
    raises(UnhandledInput,
           lambda: LRAConstraint(Q.gt, sqrt(2)*x + y, S.Zero))
