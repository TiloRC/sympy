"""Interpretation of predicates as linear arithmetic atoms.

This module translates binary relation predicates into
:class:`LRAConstraint` objects, validates them, and guarantees that every
coefficient and constant is rational. It is the single place where the
input of the linear arithmetic solver in
:mod:`sympy.logic.algorithms.lra_theory` is interpreted; the solver itself
only assembles its tableau from the constraint objects defined here.

The module deliberately imports nothing from :mod:`sympy.logic` so that it
can be imported from anywhere in :mod:`sympy.assumptions`.
"""
from __future__ import annotations
from sympy.core.add import Add
from sympy.core.mul import Mul
from sympy.core.numbers import Rational, oo
from sympy.core.relational import Eq, Ge, Gt, Le, Lt
from sympy.core.singleton import S
from sympy.core.symbol import Dummy
from sympy.core.sympify import sympify
from sympy.assumptions import Predicate
from sympy.assumptions.assume import AppliedPredicate
from sympy.assumptions.ask import Q
from sympy.utilities.iterables import sift


class UnhandledInput(Exception):
    """
    Raised when the atoms of a formula cannot be interpreted as linear
    arithmetic constraints, e.g. because of non-linearity, non-rational
    numbers, or imaginary components.
    """

# predicates that LRASolver understands and makes use of
ALLOWED_PRED = {Q.eq: Eq, Q.gt: Gt, Q.lt: Lt, Q.le: Le, Q.ge: Ge}


class LRAConstraint:
    """
    An atom of linear real arithmetic: a comparison of a linear expression
    with zero.

    ``function`` is one of ``Q.eq``, ``Q.gt``, ``Q.lt``, ``Q.ge``, ``Q.le``
    and ``lhs``, ``rhs`` are the expressions it compares. The constructor
    normalizes the comparison and stores what the solver consumes:

    - ``terms`` is a tuple of ``(term, coefficient)`` pairs describing the
      variable part, oriented so that ``Q.gt``/``Q.ge`` give upper bounds,
    - ``var_coeff`` is the factor that was folded out of the variable part;
      its sign gives the bound direction of the constraint,
    - ``const`` is the normalized additive constant,
    - ``equality`` and ``strict`` tell whether the comparison is an
      equation and whether an inequality is strict.

    Every coefficient and ``const`` is a ``Rational``; construction raises
    ``UnhandledInput`` otherwise. Instances compare structurally by their
    predicate and can be used as keys of an ``EncodedCNF``.

    Example
    =======

    >>> from sympy.assumptions.lra_atoms import LRAConstraint
    >>> from sympy.assumptions.ask import Q
    >>> from sympy.abc import x
    >>> c = LRAConstraint(Q.gt, 2*x + 2, 2)
    >>> c
    Q.gt(2*x + 2, 2)
    >>> c.terms
    ((x, 1),)
    >>> c.var_coeff, c.const, c.equality, c.strict
    (-2, 0, False, True)
    """

    def __init__(self, function, lhs, rhs):
        assert function in ALLOWED_PRED
        self.function = function
        self.lhs = lhs
        self.rhs = rhs
        expr = lhs - rhs
        if function in (Q.ge, Q.gt):
            expr = -expr
        vars, const = _sep_const_terms(expr)
        vars, var_coeff = _sep_const_coeff(vars)
        const = const / var_coeff
        terms = []
        for term in Add.make_args(vars):
            term, coeff = _sep_const_coeff(term)
            assert len(term.free_symbols) > 0
            if not isinstance(coeff, Rational):
                raise UnhandledInput("Non-rational numbers are not handled")
            terms.append((term, coeff))
        assert var_coeff != 0
        if not isinstance(const, Rational):
            raise UnhandledInput("Non-rational numbers are not handled")
        self.terms = tuple(terms)
        self.var_coeff = var_coeff
        self.const = const
        self.equality = function == Q.eq
        self.strict = function in (Q.gt, Q.lt)

    def __repr__(self):
        return f"{self.function}({self.lhs}, {self.rhs})"

    def __eq__(self, other):
        if not isinstance(other, LRAConstraint):
            return NotImplemented
        return ((self.function, self.lhs, self.rhs)
            == (other.function, other.lhs, other.rhs))

    def __hash__(self):
        return hash((self.function, self.lhs, self.rhs))


def pred_to_lra_atom(pred):
    """
    Convert an applied binary relation predicate into an
    :class:`LRAConstraint`, or into ``S.true``/``S.false`` when the
    comparison simplifies to a constant.

    Predicates other than applied relations from ``ALLOWED_PRED`` are
    returned unchanged. Non-linear or non-rational comparisons raise
    ``UnhandledInput`` when they are converted, and comparisons involving
    nan raise ``ValueError``.

    Example
    =======

    >>> from sympy.assumptions.lra_atoms import pred_to_lra_atom
    >>> from sympy.assumptions.ask import Q
    >>> from sympy.abc import x
    >>> pred_to_lra_atom(Q.ge(x - 1, 0))
    Q.ge(x - 1, 0)
    >>> pred_to_lra_atom(Q.gt(2, 1))
    True
    """
    if not isinstance(pred, AppliedPredicate):
        return pred
    assert pred.function in ALLOWED_PRED
    if pred.lhs == S.NaN or pred.rhs == S.NaN:
        raise ValueError(f"{pred} contains nan")
    if pred.lhs.is_imaginary or pred.rhs.is_imaginary:
        raise UnhandledInput(f"{pred} contains an imaginary component")
    if pred.lhs == oo or pred.rhs == oo:
        raise UnhandledInput(f"{pred} contains infinity")

    expr = pred.lhs - pred.rhs
    value = ALLOWED_PRED[pred.function](expr, S.Zero)
    if value not in (True, False):
        if not expr.free_symbols:
            raise UnhandledInput(f"{pred} could not be simplified")
        return LRAConstraint(pred.function, pred.lhs, pred.rhs)
    return S.true if value == True else S.false


def translate_lra_atoms(encoded_cnf, testing_mode=False):
    """Validate the atoms of ``encoded_cnf`` and separate constant facts
    from arithmetic constraints.

    Return a mapping from atom IDs to :class:`LRAConstraint` objects and a
    list of unit clauses fixing constant atoms. Keys that are already
    :class:`LRAConstraint` objects pass through unchanged; applied
    predicates are interpreted by :func:`pred_to_lra_atom`. Symbols need
    not have real assumptions: they represent real variables here.

    Example
    =======

    >>> from sympy.assumptions.lra_atoms import translate_lra_atoms
    >>> from sympy.assumptions.cnf import CNF, EncodedCNF
    >>> from sympy.assumptions.ask import Q
    >>> from sympy.abc import x
    >>> enc = EncodedCNF()
    >>> enc.from_cnf(CNF.from_prop(Q.gt(x, 0) & Q.gt(2, 1)))
    >>> constraints, conflicts = translate_lra_atoms(enc)
    >>> sorted(map(str, constraints.values()))
    ['Q.gt(x, 0)']
    >>> len(conflicts)
    1
    """
    items = encoded_cnf.encoding.items()
    if testing_mode:
        items = sorted(items, key=lambda item: str(item))

    constraints = {}
    conflicts = []
    empty_var = Dummy()
    for prop, atom_id in items:
        if isinstance(prop, Predicate):
            prop = prop(empty_var)
        if isinstance(prop, (AppliedPredicate, LRAConstraint)):
            atom = pred_to_lra_atom(prop)
            if isinstance(atom, LRAConstraint):
                constraints[atom_id] = atom
                continue
            value = atom
        else:
            value = prop
            if value not in (True, False):
                raise ValueError(f"Unhandled Predicate: {prop}")

        conflicts.append([atom_id if value == True else -atom_id])

    variables = []
    for constraint in constraints.values():
        for term, _ in constraint.terms:
            if term not in variables:
                variables.append(term)
    fs = [v.free_symbols for v in variables]
    assert all(len(syms) > 0 for syms in fs)
    fs_count = sum(len(syms) for syms in fs)
    if len(fs) > 0 and len(set.union(*fs)) < fs_count:
        raise UnhandledInput("Nonlinearity is not handled")

    return constraints, conflicts


def _sep_const_coeff(expr):
    """
    Example
    =======

    >>> from sympy.assumptions.lra_atoms import _sep_const_coeff
    >>> from sympy.abc import x, y
    >>> _sep_const_coeff(2*x)
    (x, 2)
    >>> _sep_const_coeff(2*x + 3*y)
    (2*x + 3*y, 1)
    """
    if isinstance(expr, Add):
        return expr, sympify(1)
    const, var = sift(Mul.make_args(expr),
                      lambda c: len(sympify(c).free_symbols) == 0,
                      binary=True)
    return Mul(*var), Mul(*const)


def _sep_const_terms(expr):
    """
    Example
    =======

    >>> from sympy.assumptions.lra_atoms import _sep_const_terms
    >>> from sympy.abc import x, y
    >>> _sep_const_terms(2*x + 3*y + 2)
    (2*x + 3*y, 2)
    """
    const, var = sift(Add.make_args(expr),
                      lambda t: len(t.free_symbols) == 0,
                      binary=True)
    return Add(*var), Add(*const)
