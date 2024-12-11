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

expressions = [
    (x <= -2) & (x >= 2),
    (x >= 2) | (x <= -2) & (x <= 2) & (x >= -2),
    (-1 <= x) & (x <= 1) & (x > -1) & (x < 1),
    (x + y > 3) & (x - y <= 5),
    (x > 0) & (y < 1) & (x + y < 2),
    (x - y > 0) & (x > y),
    (x > 0) & (y > 0) & (x + y <= 2),
    (x + y <= 5) & (x - y > 1),
    (x > 0) & (y < 3) & (z >= 0),
    (x > 0) & (z != y),
    (x + y + z > 10) & (x * y * z < 20) & (x != y),
    (x + y < 5) & (z >= 1) & (x - z < 2),
    (x < 3) & (y > 1) & (z <= 2),
    (x + z > 2) & (x < y) & (y - z >= 0),
    (x + y - z > 0) & (x * z < y) & (z > 1) & (x > 2),
    (x > 0) & (y > 0) & (z > 1),
    (x > -5) & (x < 5) & (y >= -1),
    (x + 2 * y > 6) & (y - x < 2),
    (x >= 0) & (x < 4) & (y > 1),
    (x - 2 * y > 1) & (x + y < 5),
    (x >= 3) & (y <= 1),
    (x + y >= 4) & (x - y <= 3),
    (x - z >= 2) & (z + y < 3),
    (x > 0) & (y >= 0) & (z < 4),
    (x > 1) & (y + z > 6) & (x - y < 2),
    (x + y - z > 0) & (y < 3),
    (x + 2 * y + z > 8) & (z < 5),
    (x - y >= 0) & (y + z <= 10),
    (x >= 0) & (y + z > 3),
    (x + y - 3 * z > 1) & (x < 5),
    (2 * x + y - z < 10) & (z > 2),
    (x + z < 7) & (y >= 3) & (x - y <= 0),
    (x - y > -2) & (z >= 1),
    (x + y - z <= 6) & (x > 2),
    (x + y > z) & (x - y < 3),
    (x - z > 1) & (y + 2 * z < 8),
    (x >= 1) & (y + z <= 5),
    (x + y + z < 10) & (x - y > 1),
    (x > 2) & (y > 1) & (z < 5),
    (x + z > 5) & (y <= 3),
    (x - y < 6) & (z > 1),
    (x > 0) & (x + y < 4) & (z < 5),
    (x + y > 8) & (y - z < 3),
    (x >= 0) & (z < 10),
    (x + y + z > 20) & (x - z < 10),
    (x - y + z < 12) & (y > 2),
    (x > 3) & (y + z < 8),
    (x + y >= 6) & (z > 1),
    (x - z > 3) & (y + 2 * x < 10),
    (x + y < 10) & (z > 2),
    (x - y + z > 5) & (x > 0),
    (x + z <= 8) & (y - z < 2),
    (x + y + z > 15) & (x - z < 7),
    (x > 2) & (y > 1) & (z < 9),
    (x + y - z < 6) & (x - y > 0),
    (x > 0) & (y > 2) & (z < 6),
    (x - y >= 4) & (z + x < 10),
    (x + 2 * y - z > 5) & (z < 7),
    (x + y + z <= 12) & (x - z > 3),
    (x - y < 8) & (y > 0),
    (x + z > 10) & (y < 5),
    (x > 1) & (y + z > 6),
    (x + y + z > 18) & (x - z < 12),
    (x - y > 5) & (y + z <= 9),
    (x > 2) & (z > 4),
    (x + y < 9) & (x - z > 3),
    (x - y + z <= 15) & (y > 1),
    (x + 2 * y - z > 10) & (z < 8),
    (x + y > 12) & (z > 1),
    (x - z >= 5) & (y + x < 14),
    (x + z <= 20) & (y - z < 5),
    (x - y > 10) & (y < 3),
    (x + y + z < 25) & (x > 2),
    (x - z < 15) & (z > 0),
    (x + y >= 20) & (z < 6),
    (x - y + z <= 30) & (y > 4),
    (x + z >= 18) & (y - z < 8),
    (x + y - z > 25) & (x < 6),
    (x + z < 22) & (y > 5),
    (x - y > 15) & (y + z > 18),
    (x > 3) & (y < 4) & (z > 12),
    (x + y + z > 30) & (x - z < 18),
    (x + z >= 25) & (y - z < 10),
    (x - y + z < 20) & (x > 1),
    (x + z > 15) & (y + x < 20),
    (x + 2 * y + z > 35) & (z < 25),
    (x + y + z <= 40) & (x - z > 5),
    (x + y > 25) & (y - z > 10),
    (x - z <= 20) & (z > 5),
    (x - y + z >= 35) & (y > 2),
    (x + y - z <= 50) & (z > 10),
    (x > 4) & (y < 3) & (z > 15),
    (x + y + z > 45) & (x - z < 30),
    (x - z >= 20) & (y + x < 40),
    (x + y + z < 50) & (x - y > 10),
    (x - z < 30) & (z > 5),
    (x > 10) & (y > 15) & (z < 20),
]


expressions = [expressions[2*i] & expressions[2*i+1] for i in range(len(expressions)//2)]


def format_expr(expr):
    if not isinstance(expr, EncodedCNF):
        exprs = EncodedCNF()
        exprs.add_prop(expr)
        expr = exprs
    return expr

expressions = [format_expr(expr) for expr in expressions]


z3 = import_module("z3")
if z3 is None:
    raise ImportError("z3 is not installed")
