from sympy.logic.algorithms.z3_wrapper import *

def encoded_cnf_to_z3_solver2(enc_cnf, z3):
    def dummify_bool(pred):
        return False
        assert isinstance(pred, AppliedPredicate)

        if pred.function in [Q.positive, Q.negative, Q.zero]:
            return pred
        else:
            return False

    s = z3.Solver()

    declarations = [f"(declare-const d{var} Bool)" for var in enc_cnf.variables]
    assertions = [clause_to_assertion(clause) for clause in enc_cnf.data]

    symbols = set()
    for pred, enc in enc_cnf.encoding.items():
        if not isinstance(pred, AppliedPredicate):
            continue
        if pred.function not in (Q.gt, Q.lt, Q.ge, Q.le, Q.ne, Q.eq, Q.positive, Q.negative, Q.extended_negative, Q.extended_positive, Q.zero, Q.nonzero, Q.nonnegative, Q.nonpositive, Q.extended_nonzero, Q.extended_nonnegative, Q.extended_nonpositive):
            continue

        pred_str = smtlib_code(pred, auto_declare=False, auto_assert=False, known_functions=known_functions)

        symbols |= pred.free_symbols
        pred = pred_str
        clause = f"(implies d{enc} {pred})"
        assertion = "(assert " + clause + ")"
        assertions.append(assertion)

    for sym in symbols:
        declarations.append(f"(declare-const {sym} Real)")

    declarations = "\n".join(declarations)
    assertions = "\n".join(assertions)

    return declarations + "\n" + assertions, s





from sympy.core.symbol import symbols
x, y, z = symbols('x,y,z')

expressions = [
    (x ** 2 >= 4) & (x <= 2) & (x >= -2),
    (x ** 2 <= 1) & (x > -1) & (x < 1),
    (x + y > 3) & (x - y <= 5),
    (x * y < 2) & (x > 0) & (y < 1),
    (x ** 2 - y ** 2 > 0) & (x > y),
    (x ** 2 + y ** 2 <= 4) & (x > 0) & (y > 0),
    (x * y >= 1) & (x + y <= 5) & (x - y > 1),
    (x ** 3 - y * z > 2) & (y < 3) & (z >= 0),
    (x ** 2 + y ** 2 - z ** 2 <= 1) & (x > 0) & (z != y),
    (x + y + z > 10) & (x * y * z < 20) & (x != y),
    (x ** 2 - y ** 2 > 4) & (x + y < 5) & (z ** 3 >= 3) & (x - z < 2),
    (x ** 2 + y ** 2 - z ** 2 >= 0) & (x < 3) & (y > 1) & (z <= 2),
    (x ** 4 - y ** 3 > 1) & (x + z > 2) & (x < y) & (y - z >= 0),
    (x + y - z > 0) & (x * z < y) & (z ** 2 - y > 1) & (x ** 2 - z > 2),
    (x ** 2 - 2 * y ** 2 >= 5) & (x ** 3 - z <= 4) & (x * y * z > 1) & (z ** 2 < x + y),
]

def format_expr(expr):
    if not isinstance(expr, EncodedCNF):
        exprs = EncodedCNF()
        exprs.add_prop(expr)
        expr = exprs
    return expr

from pyinstrument import Profiler
expressions = [format_expr(expr) for expr in expressions]

"""
`asdasdasdasda asdasdads`

"""

import sys
enc = sys.getdefaultencoding()

z3 = import_module("z3")
if z3 is None:
    raise ImportError("z3 is not installed")


# import z3.z3core
# _lib = z3.z3core.get_lib()
#
# from z3.z3core import Elementaries
# _elems=Elementaries(_lib.Z3_parser_context_from_string)

#r = _elems.f(a0, a1, _str_to_bytes(a2))
#_elems.Check(a0)

z3.z3core.Z3_solver_from_string()
#z3.z3core.Z3_solver_from_string()
# Start the profiler
profiler = Profiler()
# Run the profiler
profiler.start()
for expr in expressions:
    smtlib_string, solver = encoded_cnf_to_z3_solver2(expr, z3)

    z3.z3core.Z3_solver_from_string()

    lib = solver.from_string(smtlib_string)
    #(self.ctx,  self.solver, s)
    smtlib_string.encode(enc if enc != None else 'latin-1')

profiler.stop()
# Open the profiler report in a browser
profiler.open_in_browser()
