from my_encoder import encoded_cnf_to_z3_solver2, expressions, z3
from sympy.logic.algorithms.z3_wrapper import encoded_cnf_to_z3_solver




from pyinstrument import Profiler

profiler = Profiler()
# Run the profiler
profiler.start()
for expr in expressions:
    encoded_cnf_to_z3_solver(expr, z3)

    # lib = solver.from_string(smtlib_string)
    # #(self.ctx,  self.solver, s)
    # smtlib_string.encode(enc if enc != None else 'latin-1')

profiler.stop()
# Open the profiler report in a browser
profiler.open_in_browser()

from pyinstrument import Profiler
