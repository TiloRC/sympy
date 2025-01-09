import ast

class AssumptionRewriter(ast.NodeTransformer):
    """
    AST Node Transformer to replace old assumption API with the new API.
    """
    UNHANDLED_ASSUMPTIONS = {"comparable", "number"}#{"noninteger", "number", "comparable", "transcendental"}  # Add other unhandled assumptions as needed
    def __init__(self, func):
        self.func = func

    def visit_Attribute(self, node):
        """
        Visit attribute nodes and rewrite `.is_<assumption>` to `ask(Q.<assumption>(<variable>))`.
        If the assumption is in the unhandled list, comment out the line.
        """
        if node.attr.startswith("is_"):
            assumption = node.attr[3:]  # Strip 'is_'
            variable = node.value

            if assumption in self.UNHANDLED_ASSUMPTIONS:
                assumption += "_unhandled_input"


            # Replace with ask(Q.<assumption>(<variable>))
            return ast.Call(
                func=ast.Name(id=self.func, ctx=ast.Load()),
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

def convert_assertions_to_new_api(file_path, output_path, func="ask"):
    """
    Reads a Python file, replaces `.is_<assumption>` using old assumptions API
    with the new API using `ask` and `Q.<assumption>`, and writes to a new file.

    Args:
        file_path (str): Path to the input Python file.
        output_path (str): Path to save the modified Python file.
    """
    with open(file_path, 'r') as file:
        source_code = file.read()

    # Parse the source code into an AST
    tree = ast.parse(source_code)

    # Transform the AST
    rewriter = AssumptionRewriter(func)
    transformed_tree = rewriter.visit(tree)

    # Convert the AST back to source code using ast.unparse
    transformed_code = ast.unparse(transformed_tree)

    new_imports = "from sympy.assumptions import ask, Q\n"
    new_imports += "from sympy.assumptions.satask import satask\n"
    new_funcs = """
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

    new_print = "\n\nprint(f'{unhandledCount}/{totalCount}')"

    transformed_code = new_imports + new_funcs + "\n"+ transformed_code + new_print

    # Write the updated code back to a file
    with open(output_path, 'w') as output_file:
        output_file.write(transformed_code)

    print(f"Updated file written to {output_path}")


def comment_unhandled_lines(input_file, output_file=None):
    """
    Comments out lines containing 'unhandled_input' in the specified file.

    Args:
        input_file (str): The file to process.
        output_file (str, optional): The file to save the processed content.
                                     If None, overwrites the input file.
    """
    output_file = output_file or input_file

    bad2 = [
        "unhandled_input",
        "with raises(AttributeError):",
        "(Q.real(x)) = False",
        "(Q.rational(nr ** Symbol('z', zero=True)))", # ask wrongly gives False
        "(Q.rational(fh.exp)) is None", # not sure
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

    bad2 += asserting_current_behavior + misc

    with open(input_file, 'r') as infile:
        lines = infile.readlines()

    with open(output_file, 'w') as outfile:
        for line in lines:
            if any(bad in line for bad in bad2):
                outfile.write(f"# {line}")
            else:
                outfile.write(line)

convert_assertions_to_new_api("test_assumptions.py", "test_core_with_new_assumptions.py")
comment_unhandled_lines(input_file="test_core_with_new_assumptions.py")

convert_assertions_to_new_api("test_assumptions.py", "test_core_satask.py", func="satask")
comment_unhandled_lines(input_file="test_core_satask.py")
