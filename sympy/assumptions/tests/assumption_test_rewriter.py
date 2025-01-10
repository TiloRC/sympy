import inspect
from types import FunctionType

def replace_function_calls(target_function, replacement_function):
    """
    Replaces all calls to the target function with the replacement function in the global scope.

    Args:
        target_function (function): The function to be replaced.
        replacement_function (function): The function to replace with.

    Raises:
        ValueError: If either target_function or replacement_function is not a function.
    """
    if not isinstance(target_function, FunctionType):
        raise ValueError("The target_function must be a callable function.")

    if not isinstance(replacement_function, FunctionType):
        raise ValueError("The replacement_function must be a callable function.")

    target_name = target_function.__name__
    globals_dict = inspect.stack()[1].frame.f_globals

    for name, obj in globals_dict.items():
        if obj is target_function:
            globals_dict[name] = replacement_function
#
# # Example usage
# def original_function():
#     print("Original function called.")
#
# def new_function():
#     print("Replacement function called.")
#
# # Call the original function
# original_function()
#
# # Replace all calls to original_function with new_function
# replace_function_calls(original_function, new_function)
#
# # Call the "original" function again (will now call the replacement function)
# original_function()

def replace_old_assumptions_api(code: str) -> str:
    """
    Replace calls using the old assumptions API with the new API.
    """
    class OldAssumptionRewriter(ast.NodeTransformer):
        """
        AST Node Transformer to replace old assumption API with the new API.
        """
        UNHANDLED_ASSUMPTIONS = {"comparable", "number"}
        def visit_Attribute(self, node):
            """
            Visit attribute nodes and rewrite `.is_<assumption>` to `ask(Q.<assumption>(<variable>))`.
            """
            if node.attr.startswith("is_"):
                assumption = node.attr[3:]  # Strip 'is_'
                variable = node.value
                if assumption in self.UNHANDLED_ASSUMPTIONS:
                    assumption += "_unhandled_input"

                # Replace with ask(Q.<assumption>(<variable>))
                return ast.Call(
                    func=ast.Name(id="ask", ctx=ast.Load()),
                    args=[
                        ast.Call(
                            func=ast.Attribute(
                                value=ast.Name(id="Q", ctx=ast.Load()),
                                attr=assumption,
                                ctx=ast.Load(),
                            ),
                            args=[variable],
                            keywords=[],
                        )
                    ],
                    keywords=[],
                )
            return node


    tree = ast.parse(code)
    rewriter = OldAssumptionRewriter()
    transformed_tree = rewriter.visit(tree)
    transformed_code = ast.unparse(transformed_tree)
    return transformed_code

def add_implicit_is_True_to_assert_statements(code):
    """
    Modifies Python code to make assert statements explicitly check for `is True`.
    For example:
        - `assert x` becomes `assert x is True`
    """
    class AddIsTrueTransformer(ast.NodeTransformer):
        def visit_Assert(self, node):
            # Transform only if the test is not already a comparison or explicitly `is True`
            if not isinstance(node.test, (ast.Compare)):
                # Wrap the existing test in a comparison to `True`
                node.test = ast.Compare(
                    left=node.test,
                    ops=[ast.Is()],
                    comparators=[ast.Constant(value=True)]
                )
            return node
    tree = ast.parse(code)
    transformer = AddIsTrueTransformer()
    transformed_tree = transformer.visit(tree)
    return ast.unparse(transformed_tree)

import ast

def rewrite_is_comparisons(source_code):
    """
    Replaces `is True` and `is False` comparisons in the given source code
    with `isTrue` and `isFalse` function calls.
    """
    class IsComparisonRewriter(ast.NodeTransformer):
        """
        AST Node Transformer to replace `is True` and `is False` comparisons with `isTrue` and `isFalse` function calls.
        """
        def visit_Compare(self, node):
            """
            Transform:
            - `is True` to `isTrue(<value>)`
            - `is False` to `isFalse(<value>)`
            """
            # Ensure the left side of the comparison is transformed first
            self.generic_visit(node)

            # Check if the comparison is of the form `is True` or `is False`
            if len(node.ops) == 1 and isinstance(node.ops[0], ast.Is):
                comparator = node.comparators[0]
                if isinstance(comparator, ast.Constant) and comparator.value in {True, False}:
                    # Determine whether to use isTrue or isFalse
                    is_func_name = "isTrue" if comparator.value is True else "isFalse"

                    # Replace the comparison with a function call: `isTrue(left)` or `isFalse(left)`
                    return ast.Call(
                        func=ast.Name(id=is_func_name, ctx=ast.Load()),  # `isTrue` or `isFalse`
                        args=[node.left],  # Pass the left-hand side of the comparison
                        keywords=[],
                    )
            return node

    tree = ast.parse(source_code)
    rewriter = IsComparisonRewriter()
    transformed_tree = rewriter.visit(tree)
    transformed_code = ast.unparse(transformed_tree)
    return transformed_code


def _comment_out_bad_lines(input_string, bad_strings):
    """
    Comments out each line in the input string that contains at least one of the bad strings.

    :param input_string: The input string with multiple lines.
    :param bad_strings: A list of strings to check for in each line.
    :return: A new string with bad lines commented out.
    """
    lines = input_string.splitlines()
    commented_lines = []

    for line in lines:
        if any(bad_str in line for bad_str in bad_strings):
            commented_lines.append(f"# {line}")
        else:
            commented_lines.append(line)

    return "\n".join(commented_lines)

from sympy.core import sympify
from sympy.core.kind import BooleanKind
from sympy.assumptions.assume import (global_assumptions, Predicate,
        AppliedPredicate)

def preprocess_ask_input(proposition, assumptions):
    proposition = sympify(proposition)
    assumptions = sympify(assumptions)

    if isinstance(proposition, Predicate) or proposition.kind is not BooleanKind:
        raise TypeError("proposition must be a valid logical expression")

    if isinstance(assumptions, Predicate) or assumptions.kind is not BooleanKind:
        raise TypeError("assumptions must be a valid logical expression")

    return proposition, assumptions

from sympy.assumptions.satask import satask
def my_satask(proposition, assumptions = True, context = global_assumptions):
    proposition, assumptions = preprocess_ask_input(proposition, assumptions)
    return satask(proposition, assumptions, context)

from sympy.assumptions.ask import _ask_single_fact, _extract_all_facts, Q
from sympy.core.relational import Eq, Ne, Gt, Lt, Ge, Le
from sympy.assumptions.cnf import CNF, EncodedCNF, Literal

def my_ask_single_fact(proposition, assumptions = True, context = global_assumptions):
    proposition, assumptions = preprocess_ask_input(proposition, assumptions)
    binrelpreds = {Eq: Q.eq, Ne: Q.ne, Gt: Q.gt, Lt: Q.lt, Ge: Q.ge, Le: Q.le}
    if isinstance(proposition, AppliedPredicate):
        key, args = proposition.function, proposition.arguments
    elif proposition.func in binrelpreds:
        key, args = binrelpreds[type(proposition)], proposition.args
    else:
        key, args = Q.is_true, (proposition,)

    # convert local and global assumptions to CNF
    assump_cnf = CNF.from_prop(assumptions)
    assump_cnf.extend(context)

    # extract the relevant facts from assumptions with respect to args
    local_facts = _extract_all_facts(assump_cnf, args)

    return _ask_single_fact(key, local_facts)


unhandledCount = 0
totalCount = 0
def isTrue(val):
    global unhandledCount
    global totalCount
    totalCount += 1
    unhandledCount += val is None
    return val is True or val is None

def isFalse(val):
    global unhandledCount
    global totalCount
    totalCount += 1
    unhandledCount += val is None
    return val is False or val is None

# # Test input code
# test_code = """
# x = True
# if x is True:
#     print("x is True")
# elif x is False:
#     print("x is False")
# else:
#     print("x is neither True nor False")
# """
#
# # Run the transformation and print the output
# transformed_test_code = rewrite_is_comparisons(test_code)
# print(transformed_test_code)

print_test = """
def test_print():
    assert f'{unhandledCount}/{totalCount}' == f'0/{totalCount}'
"""


new_imports = """
from sympy.assumptions.tests.assumption_test_rewriter import replace_function_calls, my_satask, my_ask_single_fact
from sympy.assumptions.satask import satask
from sympy.assumptions import ask, Q

unhandledCount = 0
totalCount = 0
def isTrue(val):
    global unhandledCount
    global totalCount
    totalCount += 1
    unhandledCount += val is None
    return val is True or val is None

def isFalse(val):
    global unhandledCount
    global totalCount
    totalCount += 1
    unhandledCount += val is None
    return val is False or val is None


"""

def rewrite_file(input_files, output_file, transformations):
    source_code = ""
    for filename in input_files:
        with open(filename, 'r') as input_file:
            source_code += input_file.read()

    for func in transformations:
        source_code = func(source_code)

    source_code = new_imports + source_code + print_test

    print(output_file)
    with open(output_file, 'w') as output_file:
        output_file.write(source_code)


import os

bad2 = [
    "unhandled_input",
    "with raises(AttributeError):",
    "(Q.real(x)) = False",
    "(Q.rational(nr ** Symbol('z', zero=True)))",  # ask wrongly gives False
    "(Q.rational(fh.exp)) is None",  # not sure
]

# benign falures
# see https://github.com/sympy/sympy/issues/27448#issuecomment-2571768879
asserting_current_behavior = [
    "assert satask(Q.finite(Mul(0, i, evaluate=False))) is None",
    "assert satask(Q.infinite(Mul(0, i, evaluate=False))) is satask(Q.infinite(S.NaN))"
]
misc = [
    "assert [satask(Q.imaginary(i ** a)) for a in range(4)] == [False, True, False, True]"
]

if __name__ == '__main__':
    print(os.getcwd())
    file = "sympy/core/tests/test_assumptions.py"
    file = "../../../" + file
    files = [file]

    bad = [
    # bugs I think?
    "unhandled_input",
    "with raises(AttributeError):",
    "(Q.real(x)) = False",
    "(Q.rational(nr ** Symbol('z', zero=True)))",  # ask wrongly gives False
    "(Q.rational(fh.exp)) is None",  # not sure

    # benign falures
    # see https://github.com/sympy/sympy/issues/27448#issuecomment-2571768879
    "assert satask(Q.finite(Mul(0, i, evaluate=False))) is None",
    "assert satask(Q.infinite(Mul(0, i, evaluate=False))) is satask(Q.infinite(S.NaN))",

    # misc??
    "assert [satask(Q.imaginary(i ** a)) for a in range(4)] == [False, True, False, True]"
    ]
    comment_out = lambda text: _comment_out_bad_lines(text, bad)



    transformations = [rewrite_is_comparisons, replace_old_assumptions_api, comment_out]
    rewrite_file(files, "test_old_assumptions_tests.py", transformations)

    def create_replacement_transformation(target_function_name, replacement_function_name):
        s = f"replace_function_calls({target_function_name}, {replacement_function_name})"
        return lambda code: s + "\n\n" + code


    ask_to_satask = create_replacement_transformation("ask", "my_satask")

    ask_to__ask_single_fact = create_replacement_transformation("ask","my_ask_single_fact")

    transformations = [add_implicit_is_True_to_assert_statements, rewrite_is_comparisons, ask_to__ask_single_fact]
    rewrite_file(["test_query.py"], "test_query_ask_single_fact.py", transformations)

