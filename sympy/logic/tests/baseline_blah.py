from my_encoder import expressions
from sympy.logic.algorithms.dpll2 import dpll_satisfiable




from pyinstrument import Profiler



profiler = Profiler()
# Run the profiler
profiler.start()
for expr in expressions:
    try:
        res = dpll_satisfiable(expr, all_models=False, use_lra_theory=True)
        print(res)
    except:
        print("ERROR")
        pass
    # lib = solver.from_string(smtlib_string)
    # #(self.ctx,  self.solver, s)
    # smtlib_string.encode(enc if enc != None else 'latin-1')

profiler.stop()
# Open the profiler report in a browser
profiler.open_in_browser()

from pyinstrument import Profiler
