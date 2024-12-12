from my_encoder import expressions, encoded_cnf_to_z3_solver2
from sympy.logic.algorithms.dpll2 import dpll_satisfiable
from sympy.logic.algorithms.z3_wrapper import encoded_cnf_to_z3_solver




from pyinstrument import Profiler



def default_solver():
    for expr in expressions:
        try:
            res = dpll_satisfiable(expr, all_models=False, use_lra_theory=True)
        except:
            print("ERROR")
            pass

def from_string_z3_parser():
    import z3
    for expr in expressions:
        encoded_cnf_to_z3_solver(expr, z3)

def from_string_z3_parser_internals():
    import z3
    for expr in expressions:
        smtlib_string, solver = encoded_cnf_to_z3_solver2(expr, z3)
        z3.z3core.Z3_solver_from_string(solver.ctx.ref(), solver.solver, smtlib_string)


def smt2_z3_parser():
    import z3
    for expr in expressions:
        encoded_cnf_to_z3_solver(expr, z3, parse_smt2=True)


smt2_z3_parser()
#
# profiler = Profiler()
# profiler.start()
# default_solver()
# profiler.stop()
# profiler.open_in_browser()
#
# profiler = Profiler()
# profiler.start()
# from_string_z3_parser()
# profiler.stop()
# profiler.open_in_browser()
#
# profiler = Profiler()
# profiler.start()
# from_string_z3_parser_internals()
# profiler.stop()
# profiler.open_in_browser()
#
# profiler = Profiler()
# profiler.start()
# smt2_z3_parser()
# profiler.stop()
# profiler.open_in_browser()
