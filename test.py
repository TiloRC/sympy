

from sympy import symbols, refine, Max, Q
a, b, c, d = symbols("a b c d", real=True)

expr = Max(a, b, c, d)
refine(expr, Q.gt(a, c))

reals = 0
for arg in expr.args:
    if ask(Q.imaginary(arg), assumptions):
        pass
    elif ask(Q.real(arg), assumptions):
        reals += 1
    else:
        break

else:
    if reals == 0:
        return True
    if reals in (1, len(expr.args)):
        # two reals could sum 0 thus giving an imaginary
        return False

