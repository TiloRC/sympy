from __future__ import annotations

import os
from contextlib import contextmanager

from sympy.codegen.ast import float80, real
from sympy.core.relational import Gt
from sympy.core.symbol import Symbol, symbols
from sympy.functions.elementary.trigonometric import sin
from sympy.logic.boolalg import And
from sympy.matrices.expressions.matexpr import MatrixSymbol
from sympy.printing.c import C99CodePrinter, ccode
from sympy.printing.codeprinter import CodePrinter, rust_code
from sympy.printing.octave import octave_code
from sympy.printing.rust import RustCodePrinter
from sympy.testing.check_printed_code import (PrintedCodeError, check_code, check_compiles,
                                              check_printed_code, compiling_enabled,
                                              declare, wrap_in_function)
from sympy.testing.pytest import raises, skip

x = Symbol('x', real=True)
n = Symbol('n', integer=True)
b, z = symbols('b z')


def test_declare():
    assert declare(C99CodePrinter(), x, False) == ('x', 'real')
    assert declare(C99CodePrinter(), n, False) == ('n', 'int')
    assert declare(C99CodePrinter(), b, True) == ('b', 'bool')
    e = raises(PrintedCodeError, lambda: declare(C99CodePrinter(), z, False))
    assert str(e.value).startswith('The type of z is unknown')


def _problem(printer, expr, assign_to=None):
    """The message of the PrintedCodeError that check_code() raises, or None."""
    try:
        check_code(printer, expr, assign_to, printer.doprint(expr, assign_to))
    except PrintedCodeError as problem:
        return str(problem)
    return None


def test_check_code():
    with _environment('0'):
        assert _problem(C99CodePrinter(), sin(x) + n) is None
        assert _problem(RustCodePrinter(), And(b, Gt(x, 0)), Symbol('y')) is None
        assert _problem(C99CodePrinter(), x, 'x') is None
        assert _problem(C99CodePrinter(), z + x).startswith('The type of z is unknown')
        assert _problem(C99CodePrinter(), x, 'z').startswith('The type of z is unknown')
        assert 'since it uses arrays' in _problem(C99CodePrinter(), MatrixSymbol('A', 2, 2)[0, 1])
        assert 'since it uses arrays' in _problem(C99CodePrinter(), x, MatrixSymbol('A', 1, 1)[0, 0])
        assert 'setting user_functions' in _problem(
            C99CodePrinter({'user_functions': {'sin': 'mysin'}}), sin(x)).replace('\n', ' ')
        assert 'setting type_aliases' in _problem(
            C99CodePrinter({'type_aliases': {real: float80}}), x).replace('\n', ' ')


def test_wrap_in_function():
    assert wrap_in_function('C89CodePrinter', 'y = M_PI*x;', [('x', 'real')], ('y', 'real')) == (
        '#define _XOPEN_SOURCE 700\n#include <math.h>\n#include <stdlib.h>\n'
        '\nvoid f(double x)\n{\n    double y;\n    y = M_PI*x;\n}\n')
    assert wrap_in_function('RustCodePrinter', 'b && x > 0.0', [('b', 'bool'), ('x', 'real')], None
                  ).endswith('\npub fn f(b: bool, x: f64)\n{\n    let _ = {\n'
                             '        b && x > 0.0\n    };\n}\n')


def test_check_printed_code():
    doprint = CodePrinter.doprint

    @check_printed_code
    def test_declared():
        assert rust_code(sin(x) + n) == 'n as f64 + x.sin()'
        assert octave_code(z) == 'z'  # not checked
    test_declared()
    assert test_declared.__name__ == 'test_declared'

    @check_printed_code
    def test_undeclared():
        assert ccode(z + 1) == 'z + 1'
    e = raises(PrintedCodeError, test_undeclared)
    assert str(e.value).startswith('C99CodePrinter printed\n\n    z + 1\n\nThe type of z')

    @check_printed_code
    def test_fails():
        assert ccode(z + 1) == 'wrong'
    raises(AssertionError, test_fails)

    @check_printed_code
    def test_prints_nothing():
        pass
    raises(PrintedCodeError, test_prints_nothing)
    assert CodePrinter.doprint is doprint


def test_compiling_enabled():
    with _environment('0'):
        assert not compiling_enabled()
    with _environment('1'):
        assert compiling_enabled()


@contextmanager
def _environment(value):
    old = os.environ.get('SYMPY_CHECK_PRINTED_CODE')
    os.environ['SYMPY_CHECK_PRINTED_CODE'] = value
    try:
        yield
    finally:
        if old is None:
            del os.environ['SYMPY_CHECK_PRINTED_CODE']
        else:
            os.environ['SYMPY_CHECK_PRINTED_CODE'] = old


def test_check_compiles():
    # Compiling is slow, so only in the printed code CI job
    if not compiling_enabled():
        skip('SYMPY_CHECK_PRINTED_CODE is not set')
    e = raises(PrintedCodeError, lambda: check_compiles('RustCodePrinter', 'x + 42',
                                                        [('x', 'real')], None))
    assert str(e.value).startswith("This doesn't compile.") and 'cannot add' in str(e.value)
    check_compiles('RustCodePrinter', 'x + 42.0', [('x', 'real')], None)
    e = raises(PrintedCodeError, lambda: check_compiles('C99CodePrinter', 'x % x',
                                                        [('x', 'real')], None))
    assert 'invalid operands' in str(e.value)
    check_compiles('C99CodePrinter', 'fmod(x, x)', [('x', 'real')], None)
