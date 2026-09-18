"""Interpretation of predicates as linear arithmetic atoms and
preprocessing of LRA queries.

This module owns everything between a Boolean formula with arithmetic
predicates and the encoded CNFs handed to the linear arithmetic solver
in :mod:`sympy.logic.algorithms.lra_theory`: the constraint
representation (:class:`LRAConstraint`), predicate interpretation,
expression validation, assumption extraction, CNF rewriting and atom
translation. :func:`prepare_lra_queries` is the entry point used by
:mod:`sympy.assumptions.lra_satask`.

The module deliberately imports nothing from :mod:`sympy.logic` so that
it can be imported from anywhere in :mod:`sympy.assumptions`.
"""
from __future__ import annotations
from typing import Any, Iterable
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
from sympy.assumptions.cnf import CNF, EncodedCNF, Literal
from sympy.core.kind import NumberKind
from sympy.matrices.kind import MatrixKind
from sympy.utilities.iterables import sift


class UnhandledInput(Exception):
    """
    Raised when the atoms of a formula cannot be interpreted as linear
    arithmetic constraints, e.g. because of non-linearity, non-rational
    numbers, or imaginary components.
    """

# predicates that LRASolver understands and makes use of
ALLOWED_PRED = {Q.eq: Eq, Q.gt: Gt, Q.lt: Lt, Q.le: Le, Q.ge: Ge}


class LRAConstraint(tuple):
    """
    An immutable normalized linear real arithmetic atom.

    ``terms`` and ``bound`` represent ``sum(term*coefficient) <= bound``.
    ``relation`` is ``Q.le`` or ``Q.lt`` for inequalities and ``Q.eq`` for
    equalities. The tuple layout is ``(terms, relation, bound)``.

    Construction raises ``UnhandledInput`` unless the normalized bound and
    coefficients are rational and the direction coefficient is a nonzero
    real number. Instances are compact and can be used as keys of an
    ``EncodedCNF``.

    Example
    =======

    >>> from sympy.assumptions.lra_preprocess import LRAConstraint
    >>> from sympy.assumptions.ask import Q
    >>> from sympy.abc import x
    >>> c = LRAConstraint(Q.gt, 2*x + 2, 2)
    >>> c.terms
    ((x, -1),)
    >>> c.relation, c.bound
    (Q.lt, 0)
    """
    __slots__ = ()

    def __new__(cls, function: Any, lhs: Any, rhs: Any) -> LRAConstraint:
        assert function in ALLOWED_PRED
        expr = lhs - rhs
        if function in (Q.ge, Q.gt):
            expr = -expr
        vars, const = _sep_const_terms(expr)
        vars, var_coeff = _sep_const_coeff(vars)
        assert var_coeff != 0
        if var_coeff.is_real is not True:
            raise UnhandledInput(
                f"{var_coeff} is not a real direction coefficient")
        if var_coeff.is_negative is True:
            vars = -vars
            var_coeff = -var_coeff
        elif var_coeff.is_positive is not True:
            raise UnhandledInput(
                f"{var_coeff} has an undetermined direction")
        bound = -const / var_coeff
        if not isinstance(bound, Rational):
            raise UnhandledInput("Non-rational numbers are not handled")
        terms = []
        for term in Add.make_args(vars):
            term, coeff = _sep_const_coeff(term)
            assert len(term.free_symbols) > 0
            terms.append((term, coeff))
        if any(not isinstance(coeff, Rational) for _, coeff in terms):
            raise UnhandledInput("Non-rational numbers are not handled")
        relation = Q.eq if function == Q.eq else (Q.lt if function in (Q.gt, Q.lt)
                                                   else Q.le)
        return tuple.__new__(cls, (tuple(terms), relation, bound))

    @property
    def terms(self) -> tuple[Any, ...]:
        return self[0]

    @property
    def relation(self) -> Any:
        return self[1]

    @property
    def bound(self) -> Rational:
        return self[2]


def pred_to_lra_atom(pred: Any) -> Any:
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

    >>> from sympy.assumptions.lra_preprocess import pred_to_lra_atom
    >>> from sympy.assumptions.ask import Q
    >>> from sympy.abc import x
    >>> pred_to_lra_atom(Q.ge(x - 1, 0)).relation
    Q.le
    >>> pred_to_lra_atom(Q.gt(2, 1))
    True
    """
    if not isinstance(pred, AppliedPredicate):
        return pred
    apred: Any = pred
    assert apred.function in ALLOWED_PRED
    if apred.lhs == S.NaN or apred.rhs == S.NaN:
        raise ValueError(f"{apred} contains nan")
    if apred.lhs.is_imaginary or apred.rhs.is_imaginary:
        raise UnhandledInput(f"{apred} contains an imaginary component")
    if apred.lhs == oo or apred.rhs == oo:
        raise UnhandledInput(f"{apred} contains infinity")

    expr = apred.lhs - apred.rhs
    value = ALLOWED_PRED[apred.function](expr, S.Zero)
    if value not in (True, False):
        if not expr.free_symbols:
            raise UnhandledInput(f"{apred} could not be simplified")
        return LRAConstraint(apred.function, apred.lhs, apred.rhs)
    return S.true if value == True else S.false


def translate_lra_atoms(encoded_cnf: EncodedCNF,
                        testing_mode: bool = False
                        ) -> tuple[dict[int, LRAConstraint], list[list[int]]]:
    """Validate the atoms of ``encoded_cnf`` and separate constant facts
    from arithmetic constraints.

    Return a mapping from atom IDs to :class:`LRAConstraint` objects and a
    list of unit clauses fixing constant atoms. A bare ``Predicate`` key
    is first applied to a dummy variable, keys that are already
    :class:`LRAConstraint` objects pass through ``pred_to_lra_atom``
    unchanged, and every other atom must be a Boolean constant; anything
    else cannot be interpreted and raises ``ValueError``. Symbols need
    not have real assumptions: they represent real variables here.

    Example
    =======

    >>> from sympy.assumptions.lra_preprocess import translate_lra_atoms
    >>> from sympy.assumptions.cnf import CNF, EncodedCNF
    >>> from sympy.assumptions.ask import Q
    >>> from sympy.abc import x
    >>> enc = EncodedCNF()
    >>> enc.from_cnf(CNF.from_prop(Q.gt(x, 0) & Q.gt(2, 1)))
    >>> constraints, conflicts = translate_lra_atoms(enc)
    >>> len(constraints)
    1
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
            prop = pred_to_lra_atom(prop)
        if isinstance(prop, LRAConstraint):
            constraints[atom_id] = prop
        elif prop in (True, False):
            conflicts.append([atom_id if prop == True else -atom_id])
        else:
            raise ValueError(f"Unhandled Predicate: {prop}")

    variables = dict.fromkeys(term for constraint in constraints.values()
                              for term, _ in constraint.terms)
    fs = [v.free_symbols for v in variables]
    assert all(len(syms) > 0 for syms in fs)
    fs_count = sum(len(syms) for syms in fs)
    if len(fs) > 0 and len(set.union(*fs)) < fs_count:
        raise UnhandledInput("Nonlinearity is not handled")

    return constraints, conflicts


def _sep_const_coeff(expr: Any) -> tuple[Any, Any]:
    """
    Example
    =======

    >>> from sympy.assumptions.lra_preprocess import _sep_const_coeff
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


def _sep_const_terms(expr: Any) -> tuple[Any, Any]:
    """
    Example
    =======

    >>> from sympy.assumptions.lra_preprocess import _sep_const_terms
    >>> from sympy.abc import x, y
    >>> _sep_const_terms(2*x + 3*y + 2)
    (2*x + 3*y, 2)
    """
    const, var = sift(Add.make_args(expr),
                      lambda t: len(t.free_symbols) == 0,
                      binary=True)
    return Add(*var), Add(*const)


_SIGN_TO_BINREL = {
    Q.positive: Q.gt,
    Q.negative: Q.lt,
    Q.zero: Q.eq,
    Q.nonzero: Q.ne,
    Q.nonpositive: Q.le,
    Q.nonnegative: Q.ge,
    Q.extended_positive: Q.gt,
    Q.extended_negative: Q.lt,
    Q.extended_nonpositive: Q.le,
    Q.extended_nonzero: Q.ne,
}


def prepare_lra_queries(prop: CNF, negated_prop: CNF,
                        factbase: CNF) -> tuple[EncodedCNF, EncodedCNF]:
    """Rewrite and encode the CNFs of a query and its negation on top of
    a fact base for checking with the LRA theory solver.

    ``prop``, ``negated_prop`` and ``factbase`` are the CNFs of the
    queried proposition, its negation and the assumptions. Return the
    encoded CNFs ``(sat_true, sat_false)``, the fact base conjoined with
    the proposition and with its negation respectively. This module does
    not check satisfiability itself.
    """
    predicates = (prop.all_predicates() | negated_prop.all_predicates()
                  | factbase.all_predicates())
    replacements = {pred: _pred_to_binrel(pred) for pred in predicates}
    expressions = {arg for pred in predicates if isinstance(pred, AppliedPredicate)
                   for arg in pred.arguments}
    for expr in expressions:
        _validate_expression(expr)
    factbase = factbase.copy()
    for pred in extract_pred_from_old_assum(expressions):
        factbase.add(pred)
        replacements[pred] = _pred_to_binrel(pred)

    encoded = EncodedCNF()
    encoded.from_cnf(_preprocess(factbase, replacements))
    sat_true = encoded.copy()
    sat_false = encoded.copy()
    sat_true.add_from_cnf(_preprocess(prop, replacements))
    sat_false.add_from_cnf(_preprocess(negated_prop, replacements))
    return sat_true, sat_false


def _preprocess(cnf: CNF, replacements: dict[Any, Any]) -> CNF:
    """Rewrite CNF literals to LRA relations, simplifying constant literals.

    Clauses containing a true literal are dropped and false literals are
    removed from their clauses. A clause whose literals are all false
    becomes a false literal so that the contradiction survives encoding.
    """
    clauses = set()
    true = Literal(S.true)
    false = Literal(S.false)
    for clause in cnf.clauses:
        new_clause = {new_lit for lit in clause
                      for new_lit in _rewrite_literal(lit, replacements[lit.lit])}
        if true in new_clause:
            continue
        new_clause.discard(false)
        clauses.add(frozenset(new_clause or {false}))
    return CNF(clauses)


def _rewrite_literal(literal: Literal, pred: Any) -> tuple[Literal, ...]:
    """Return the disjunction representing a converted literal for LRA.

    An equality is kept as is, a disequality is replaced by its two strict
    comparisons, and any other comparison is kept unchanged; the rewritten
    comparisons carry positive polarity while any other literal keeps its
    polarity. One common conversion path turns the comparisons into
    ``LRAConstraint`` atoms or folds them to ``S.true``/``S.false``.
    Clause-level elimination of constant literals is left to
    ``_preprocess``.
    """
    negated = getattr(literal, "is_Not")
    comparisons: tuple[Any, ...]
    if isinstance(pred, AppliedPredicate) and pred.function in (Q.eq, Q.ne):
        if (pred.function == Q.ne) != negated:
            comparisons = (Q.gt(*pred.arguments), Q.lt(*pred.arguments))
        else:
            comparisons = (Q.eq(*pred.arguments),)
        negated = False
    else:
        comparisons = (pred,)
    return tuple(_comparison_literal(comparison, negated)
                 for comparison in comparisons)


def _comparison_literal(pred: Any, negated: bool) -> Literal:
    """Convert *pred* to an ``LRAConstraint`` atom literal with *negated* polarity."""
    if pred not in (True, False):
        pred = pred_to_lra_atom(pred)
    if pred in (True, False):
        return Literal(S.true if bool(pred) != negated else S.false)
    return Literal(pred, negated)


def _pred_to_binrel(pred: Any) -> Any:
    """Validate a predicate and convert it to a relation or Boolean constant."""
    if not isinstance(pred, AppliedPredicate):
        return pred
    function = pred.function
    if function in _SIGN_TO_BINREL:
        return _SIGN_TO_BINREL[function](pred.arguments[0], 0)
    if function in (Q.negative_infinite, Q.positive_infinite):
        return S.false
    if function in ALLOWED_PRED or function == Q.ne:
        return pred
    raise UnhandledInput(f"LRASolver: {pred} is an unhandled predicate")


def _validate_expression(expr: Any) -> None:
    """Reject domains and expressions that real arithmetic cannot represent."""
    if getattr(expr, "kind", None) == MatrixKind(NumberKind):
        raise UnhandledInput(f"LRASolver: {expr} is of MatrixKind")
    if expr == S.NaN:
        raise UnhandledInput("LRASolver: nan")
    if not getattr(expr, "free_symbols", None):
        return
    if expr.is_real is not True:
        raise UnhandledInput(f"LRASolver: {expr} must be real")
    if isinstance(expr, Mul) and not all(arg.is_real is True for arg in expr.args):
        raise UnhandledInput(f"LRASolver: {expr} must be real")
    if expr.is_integer == True and expr.is_zero != True:
        raise UnhandledInput(f"LRASolver: {expr} is an integer")
    if expr.is_integer == False:
        raise UnhandledInput(f"LRASolver: {expr} can't be an integer")
    if expr.is_rational == False:
        raise UnhandledInput(f"LRASolver: {expr} is irational")


def extract_pred_from_old_assum(all_exprs: Iterable[Any]) -> list[Any]:
    """
    Returns a list of relevant new assumption predicate
    based on any old assumptions.

    The expressions must already be validated for LRA by
    ``_validate_expression``.

    Ignored predicate:
    - commutative
    - complex
    - algebraic
    - transcendental
    - extended_real
    - real
    - all matrix predicate
    - rational
    - irrational

    Example
    =======
    >>> from sympy.assumptions.lra_preprocess import extract_pred_from_old_assum
    >>> from sympy import symbols
    >>> x, y = symbols("x y", positive=True)
    >>> extract_pred_from_old_assum([x, y, 2])
    [Q.positive(x), Q.positive(y)]
    """
    ret = []
    for expr in all_exprs:
        if not getattr(expr, "free_symbols", None):
            continue
        for name in ("zero", "positive", "negative", "nonzero", "nonpositive",
                     "nonnegative"):
            if getattr(expr, "is_" + name):
                ret.append(getattr(Q, name)(expr))
                break

    return ret
