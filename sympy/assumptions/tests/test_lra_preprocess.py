from __future__ import annotations
from sympy import I, Q, S, sqrt, symbols
from sympy.assumptions.cnf import CNF, EncodedCNF
from sympy.assumptions.lra_preprocess import (
    LRAConstraint, UnhandledInput, pred_to_lra_atom, translate_lra_atoms)
from sympy.testing.pytest import raises


def test_LRAConstraint_frozen():
    x = symbols("x", real=True)
    c = LRAConstraint(Q.gt, 2*x + 2, 2)
    raises(AttributeError, lambda: setattr(c, "terms", ((x, S.One),)))
    raises(AttributeError, lambda: setattr(c, "relation", Q.le))
    raises(AttributeError, lambda: setattr(c, "bound", S.One))
    raises(AttributeError, lambda: delattr(c, "terms"))


def test_LRAConstraint_equality_and_hashing():
    x = symbols("x", real=True)
    y = symbols("x", real=True)
    c1 = LRAConstraint(Q.gt, 2*x + 2, 2)
    c2 = LRAConstraint(Q.gt, 2*y + 2, 2)
    assert c1 == c2
    assert hash(c1) == hash(c2)
    assert c1.terms == c2.terms
    assert c1.relation == c2.relation
    assert c1.bound == c2.bound

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


def test_LRAConstraint_upper_bounds():
    x, y = symbols("x y", real=True)
    for relation, normalized in ((Q.gt, Q.lt), (Q.ge, Q.le)):
        c = LRAConstraint(relation, 2*x, 4)
        assert c.terms == ((x, -S.One),)
        assert c.relation == normalized
        assert c.bound == -2
        equivalent = LRAConstraint(normalized, -x, -2)
        assert c == equivalent
        assert hash(c) == hash(equivalent)
    c = LRAConstraint(Q.ge, 2*x + 3*y, 4)
    assert dict(c.terms) == {x: -2, y: -3}
    assert c.relation == Q.le
    assert c.bound == -4


def test_LRAConstraint_irrational_direction():
    x, y = symbols("x y", real=True)
    c = LRAConstraint(Q.gt, sqrt(2)*x, S.Zero)
    assert c.terms == ((x, -S.One),)
    assert c.relation == Q.lt
    assert c.bound == S.Zero
    raises(UnhandledInput,
           lambda: LRAConstraint(Q.gt, sqrt(2)*x + y, S.Zero))
    raises(UnhandledInput,
           lambda: LRAConstraint(Q.lt, sqrt(2)*x, S.One))
    assert (LRAConstraint(Q.lt, sqrt(2)*x, sqrt(2))
            == LRAConstraint(Q.lt, x, S.One))


def test_translate_lra_atoms_raw_and_pretranslated():
    x, y = symbols("x y", real=True)
    enc = EncodedCNF()
    enc.from_cnf(CNF.from_prop(Q.gt(x, 0) | Q.gt(y, 1)))
    pretranslated = pred_to_lra_atom(Q.ge(x, 1))
    enc.encoding[pretranslated] = len(enc.encoding) + 1
    constraints, conflicts = translate_lra_atoms(enc)
    assert not conflicts
    assert constraints[len(enc.encoding)] == pretranslated
    assert len(constraints) == 3
    assert all(c.relation in (Q.le, Q.lt) for c in constraints.values())


def test_translate_lra_atoms_constants():
    x = symbols("x", real=True)
    enc = EncodedCNF()
    enc.from_cnf(CNF.from_prop(Q.gt(x, 0) & Q.gt(2, 1) & Q.gt(1, 2)))
    constraints, conflicts = translate_lra_atoms(enc, testing_mode=True)
    assert list(constraints.values()) == [LRAConstraint(Q.gt, x, 0)]
    true_id = enc.encoding[Q.gt(2, 1)]
    false_id = enc.encoding[Q.gt(1, 2)]
    assert sorted(conflicts) == [[-false_id], [true_id]]


def test_translate_lra_atoms_unsupported():
    x = symbols("x", real=True)
    enc = EncodedCNF()
    enc.from_cnf(CNF.from_prop(Q.gt(x, 0)))
    enc.encoding[x] = len(enc.encoding) + 1
    raises(ValueError, lambda: translate_lra_atoms(enc))


def test_translate_lra_atoms_nonlinear():
    x, y = symbols("x y", real=True)
    enc = EncodedCNF()
    enc.from_cnf(CNF.from_prop(Q.gt(x, 0) & Q.gt(x*y, 0)))
    raises(UnhandledInput, lambda: translate_lra_atoms(enc))
