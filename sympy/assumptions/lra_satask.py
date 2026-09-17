from __future__ import annotations
from sympy.assumptions.cnf import CNF, EncodedCNF, Literal
from sympy.assumptions.ask import Q
from sympy.logic.inference import satisfiable
from sympy.assumptions.lra_atoms import (ALLOWED_PRED, UnhandledInput,
                                         pred_to_lra_atom)
from sympy.matrices.kind import MatrixKind
from sympy.core.kind import NumberKind
from sympy.assumptions.assume import AppliedPredicate
from sympy.core.mul import Mul
from sympy.core.singleton import S


def lra_satask(proposition, assumptions=True):
    """
    Function to evaluate the proposition with assumptions using SAT algorithm
    in conjunction with an Linear Real Arithmetic theory solver.

    Used to handle inequalities. Should eventually be depreciated and combined
    into satask, but infinity handling and other things need to be implemented
    before that can happen.
    """
    return check_satisfiability(CNF.from_prop(proposition),
                                CNF.from_prop(~proposition),
                                CNF.from_prop(assumptions))


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


def check_satisfiability(prop, _prop, factbase):
    """Answer *prop* with the LRA theory solver, taking CNF inputs."""
    predicates = (prop.all_predicates() | _prop.all_predicates()
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
    sat_false.add_from_cnf(_preprocess(_prop, replacements))

    can_be_true = satisfiable(sat_true, use_lra_theory=True) is not False
    can_be_false = satisfiable(sat_false, use_lra_theory=True) is not False

    if can_be_true and can_be_false:
        return None
    if can_be_true and not can_be_false:
        return True
    if not can_be_true and can_be_false:
        return False
    raise ValueError("Inconsistent assumptions")


def _preprocess(cnf, replacements):
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


def _rewrite_literal(literal, pred):
    """Return the disjunction representing a converted literal for LRA.

    The converted literal wraps an ``LRAConstraint`` so that the encoded
    CNF carries interpreted atoms; predicates that simplify to a constant
    are folded to ``S.true``/``S.false`` with the polarity of the literal.
    """
    negated = literal.is_Not
    if isinstance(pred, AppliedPredicate) and pred.function in (Q.eq, Q.ne):
        if (pred.function == Q.ne) != negated:
            atoms = [pred_to_lra_atom(rel(*pred.arguments))
                     for rel in (Q.gt, Q.lt)]
            if any(atom is S.true for atom in atoms):
                return (Literal(S.true),)
            atoms = [atom for atom in atoms if atom is not S.false]
            if not atoms:
                return (Literal(S.false),)
            return tuple(Literal(atom) for atom in atoms)
        atom = pred_to_lra_atom(Q.eq(*pred.arguments))
        if atom in (True, False):
            return (Literal(S.true if bool(atom) else S.false),)
        return (Literal(atom),)
    if pred not in (True, False):
        pred = pred_to_lra_atom(pred)
    if pred in (True, False):
        return (Literal(S.true if bool(pred) != negated else S.false),)
    return (Literal(pred, negated),)


def _pred_to_binrel(pred):
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


def _validate_expression(expr):
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


def extract_pred_from_old_assum(all_exprs):
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
    >>> from sympy.assumptions.lra_satask import extract_pred_from_old_assum
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
