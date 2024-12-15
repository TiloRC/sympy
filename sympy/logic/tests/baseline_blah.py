from my_encoder import expressions, expressions2, oneBigExpression, encoded_cnf_to_z3_solver2
from sympy.logic.algorithms.dpll2 import dpll_satisfiable
from sympy.logic.algorithms.z3_wrapper import encoded_cnf_to_z3_solver
import ctypes
import z3



from pyinstrument import Profiler



def default_solver():
    for expr in expressions:
        try:
            res = dpll_satisfiable(expr, all_models=False, use_lra_theory=True)
            print(res)
        except:
            print("ERROR")
            pass

def from_string_z3_parser():
    for expr in expressions:
        encoded_cnf_to_z3_solver(expr, z3)


def from_string_z3_parser_internals():
    for expr in [oneBigExpression]:
        smtlib_string, solver = encoded_cnf_to_z3_solver2(expr, z3)
        smtlib_string= ""
        z3.z3core.Z3_solver_from_string(solver.ctx.ref(), solver.solver, smtlib_string)

        def funcCall():
            z3.z3core.Z3_solver_from_string(solver.ctx.ref(), solver.solver, "")

        funcCall()


def from_string_z3_parser_internals_small():
    for expr in expressions:
        smtlib_string, solver = encoded_cnf_to_z3_solver2(expr, z3)
        z3.z3core_small.Z3_solver_from_string(solver.ctx.ref(), solver.solver, smtlib_string)


def from_file_z3_parser():
    for expr in expressions:
        smtlib_string, solver = encoded_cnf_to_z3_solver2(expr, z3)
        with open("temp.txt", "w") as f:
            f.write(smtlib_string)

        solver.from_file("temp.txt")


def smt2_z3_parser():
    for expr in expressions:
        encoded_cnf_to_z3_solver(expr, z3, parse_smt2=True)


def string_dup():
    for expr in expressions:
        smtlib_string, solver = encoded_cnf_to_z3_solver2(expr, z3)
        expr = smtlib_string
        expr = list(str(expr) + str(expr))
        print(expr)

def string_c_conversion():
    for expr in expressions:
        smtlib_string, solver = encoded_cnf_to_z3_solver2(expr, z3)
        expr = ctypes.c_char_p(smtlib_string.encode('latin1'))
        print(expr)
        print(int(smtlib_string.encode('latin1')))



profiler = Profiler()
profiler.start()
from_string_z3_parser_internals()
profiler.stop()
profiler.open_in_browser()



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
