from my_encoder import encoded_cnf_to_z3_solver2, expressions, z3
from sympy.logic.algorithms.z3_wrapper import encoded_cnf_to_z3_solver



# ADD THE FOLLOWING TO z3core.py
"""
The following line must be added to the __init__ of Elementaries:
_lib = get_lib()
"""

import z3.z3core
_lib = z3.z3core.get_lib()
from z3.z3core import Elementaries, _str_to_bytes

from pyinstrument import Profiler

profiler = Profiler()
profiler.start()
for expr in expressions:
    smtlib_string, solver = encoded_cnf_to_z3_solver2(expr, z3)
    z3.z3core.Z3_solver_from_string(solver.ctx.ref(), solver.solver, smtlib_string)
    # Equivalently, call the following code
    smtlib_string, solver = encoded_cnf_to_z3_solver2(expr, z3)
    _elems = Elementaries(_lib.Z3_parser_context_from_string)
    a0, a1, a2_bytes = solver.ctx.ref(), solver.solver, _str_to_bytes(smtlib_string)
    _elems.f(a0, a1, a2_bytes)
    _elems.Check(a0)

    #lib = solver.from_string(smtlib_string)
    #(self.ctx,  self.solver, s)
    #smtlib_string.encode(enc if enc != None else 'latin-1')

profiler.stop()
profiler.open_in_browser()

