"""
Reasoning engine that answers questions about a propagated set of facts.
"""
from __future__ import annotations

from sympy.assumptions.assume import AppliedPredicate
from sympy.assumptions.cnf import CNF, EncodedCNF
from sympy.logic.algorithms.dpll2 import SATSolver, IpasirStatus


class ReasoningEngine:

    def __init__(self, factbase: EncodedCNF, prop: CNF, _prop: CNF) -> None:
        if {0} in factbase.data:
            raise ValueError("Inconsistent assumptions")

        self._factbase = factbase

        # TODO: Move solver initialization into `__init__` once the sat solver
        # can be given new variables after initialization.
        #
        # `_create_question` primarily exists because of features I would like to add when the sat solver
        # can be given new variables:
        # - Create/answer multiple questions in the same reasoning engine. This would improve
        #   performance when asking many related questions.
        # - Ask compound questions -- questions that are composed of the subquestions and
        #   optional additional assumptions.
        # Though, I think it also makes the code more readable.
        self.selector: int = self._create_question(prop, _prop)

    def _create_question(self, prop: CNF, _prop: CNF) -> int:
        guarded, selector = _encode_with_selector(prop, _prop, self._factbase)
        self._encoding = guarded.encoding
        self._solver = SATSolver(guarded.data, range(1, selector + 1),
                                 set(), guarded.symbols + [selector])

        if self._solver.propagate() == IpasirStatus.UNSATISFIABLE:
            raise ValueError("Inconsistent assumptions")

        return selector

    def lookup(self, pred: AppliedPredicate) -> bool | None:
        lit = self._encoding.get(pred)
        if lit is None:
            return None

        return self.fixed(lit)

    def fixed(self, lit: int) -> bool | None:
        return {1: True, -1: False, 0: None}[self._solver.fixed(lit)]

    def ask_question(self, selector: int) -> bool | None:
        # TODO: Run additional checks to see which combination of the
        # assumptions, global_assumptions, and relevant_facts are inconsistent.
        if self._solver.solve() == IpasirStatus.UNSATISFIABLE:
            raise ValueError("Inconsistent assumptions")

        # The selector literal will either be set to true or false in the model
        # that `solve()` found. True means `prop` is satisfiable, false means `_prop` is satisfiable.
        selector_state = self._solver.val(selector)
        assert selector_state in (1, -1)
        # Determine the satifsiability of the other state by assuming it and then solving.
        self._solver.assume(-selector_state)
        other_state_is_satisfiable = self._solver.solve() == IpasirStatus.SATISFIABLE

        if other_state_is_satisfiable:
            return None
        else:
            return selector_state > 0


def _add_guarded(encoded: EncodedCNF, cnf: CNF, active: int) -> None:
    # Add the clauses of `cnf` to `encoded`, each guarded by the literal
    # `active`, so that `cnf` holds when `active` is true and says nothing at
    # all when it is false. Dropping the 0 that encodes False leaves a clause
    # nothing can satisfy as the unit {-active}, which is what stops `active`
    # from being true.
    encoded.data += [(encoded.encode(clause) - {0}) | {-active}
                     for clause in cnf.clauses]


def _encode_with_selector(prop: CNF, _prop: CNF,
                          factbase: EncodedCNF) -> tuple[EncodedCNF, int]:
    """Return *factbase* with the clauses of prop and _prop added to it, and
    the selector variable that activates prop when true and _prop when false.
    """
    true_false_guarded = factbase.copy()

    # Number the predicates of both sides before choosing the selector. Doing
    # it after would give the selector a number that encoding the second side
    # still hands out to a predicate.
    for clause in (*prop.clauses, *_prop.clauses):
        true_false_guarded.encode(clause)

    # One past the last predicate, so the selector is a variable of its own.
    selector = len(true_false_guarded.encoding) + 1

    _add_guarded(true_false_guarded, prop, selector)
    _add_guarded(true_false_guarded, _prop, -selector)

    return true_false_guarded, selector
