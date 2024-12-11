from my_encoder import encoded_cnf_to_z3_solver2, expressions, z3
from sympy.logic.algorithms.z3_wrapper import encoded_cnf_to_z3_solver



# ADD THE FOLLOWING TO z3core.py
"""
The following line must be added to the __init__ of Elementaries:
_lib = get_lib()
"""

import z3.z3core

from pyinstrument import Profiler

strings = []

profiler = Profiler()
profiler.start()
for expr in expressions:
    smtlib_string, solver = encoded_cnf_to_z3_solver2(expr, z3)
    strings.append(smtlib_string)
    z3.z3core._str_to_bytes(smtlib_string)
    blah = z3.parse_smt2_string(smtlib_string)
    solver.add(blah)
    #z3.z3core.Z3_solver_from_string(solver.ctx.ref(), solver.solver, smtlib_string)

    #lib = solver.from_string(smtlib_string)
    #(self.ctx,  self.solver, s)
    #smtlib_string.encode(enc if enc != None else 'latin-1')

profiler.stop()
profiler.open_in_browser()

profiler = Profiler()
profiler.start()
for s in strings:
    with open("smtlib_strings.txt", "a") as f:
        f.write(s)
        f.write("\n\n\n")
profiler.stop()
profiler.open_in_browser()

print(strings)
