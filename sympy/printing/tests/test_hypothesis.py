from __future__ import annotations

from hypothesis import given, settings, strategies as st

from sympy.core.add import Add
from sympy.core.mod import Mod
from sympy.core.mul import Mul
from sympy.core.numbers import Float, I, Rational, nan, oo, zoo
from sympy.core.power import Pow
from sympy.core.singleton import S
from sympy.core.symbol import symbols
from sympy.functions.elementary.complexes import Abs, sign
from sympy.functions.elementary.exponential import exp, log
from sympy.functions.elementary.integers import floor
from sympy.functions.elementary.miscellaneous import Max, Min, sqrt
from sympy.functions.elementary.trigonometric import sin
from sympy.printing.c import ccode
from sympy.printing.codeprinter import rust_code
from sympy.printing.cxx import cxxcode
from sympy.testing.check_printed_code import check_printed_code, compiling_enabled
from sympy.testing.pytest import XFAIL, skip


def _random_expressions():
    """A strategy for expressions in real x, y and integer i, j, such as
    Max(i, y) or sin(x)**2 + floor(j/2)."""
    x, y = symbols('x y', real=True)
    i, j = symbols('i j', integer=True)
    leaves = st.sampled_from([x, y, i, j, S(2), S(-3), Rational(1, 2), Float(-2.5)])
    binary = st.sampled_from([Add, Mul, Pow, Mod, Min, Max])
    unary = st.sampled_from([sin, exp, log, sqrt, Abs, floor, sign])

    def apply(function, *args):
        try:
            return function(*args)
        except (ValueError, TypeError, ZeroDivisionError):
            return nan  # e.g. Min of a complex number

    return st.recursive(
        leaves,
        lambda e: st.builds(apply, binary, e, e) | st.builds(apply, unary, e),
        max_leaves=5,
    ).filter(lambda e: e.free_symbols and not e.has(nan, zoo, oo, -oo, I))


# The printers must not raise, and @check_printed_code checks that what they
# print compiles. Compiling needs SYMPY_CHECK_PRINTED_CODE, and without it
# the tests are skipped.

@settings(derandomize=True, database=None, report_multiple_bugs=False)
@given(_random_expressions())
@check_printed_code
def test_ccode(expr):
    if not compiling_enabled():
        skip('SYMPY_CHECK_PRINTED_CODE is not set')
    ccode(expr)


@XFAIL  # cxxcode(Min(i, x)) calls std::min with an int and a double
@settings(derandomize=True, database=None, report_multiple_bugs=False)
@given(_random_expressions())
@check_printed_code
def test_cxxcode(expr):
    if not compiling_enabled():
        skip('SYMPY_CHECK_PRINTED_CODE is not set')
    cxxcode(expr)


@XFAIL  # rust_code(Mod(x, i)) calls recip on an i32
@settings(derandomize=True, database=None, report_multiple_bugs=False)
@given(_random_expressions())
@check_printed_code
def test_rust_code(expr):
    if not compiling_enabled():
        skip('SYMPY_CHECK_PRINTED_CODE is not set')
    rust_code(expr)
