from __future__ import annotations
from sympy.assumptions.cnf import CNF
from sympy.assumptions.lra_preprocess import prepare_lra_queries
from sympy.logic.inference import satisfiable


def lra_satask(proposition, assumptions=True):
    """
    Function to evaluate the proposition with assumptions using SAT algorithm
    in conjunction with an Linear Real Arithmetic theory solver.

    Used to handle inequalities. Should eventually be depreciated and combined
    into satask, but infinity handling and other things need to be implemented
    before that can happen.
    """
    sat_true, sat_false = prepare_lra_queries(
        CNF.from_prop(proposition), CNF.from_prop(~proposition),
        CNF.from_prop(assumptions))
    can_be_true = satisfiable(sat_true, use_lra_theory=True) is not False
    can_be_false = satisfiable(sat_false, use_lra_theory=True) is not False

    if can_be_true and can_be_false:
        return None
    if can_be_true and not can_be_false:
        return True
    if not can_be_true and can_be_false:
        return False
    raise ValueError("Inconsistent assumptions")
