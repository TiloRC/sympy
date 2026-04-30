from sympy.abc import A, B, C, D, E, F
from sympy.logic.algorithms.dpll2 import SATSolver
import sympy.logic.algorithms.dpll2 as dpll2
import subprocess
import os

# Enable full tracing
dpll2.TRACE = True
dpll2.TRACE_CLAUSES = True

def run_example(name, symbols, clauses, find_all=False):
    print(f"\n--- Running Example: {name} ---")
    variables = set(range(1, len(symbols) + 1))
    solver = SATSolver(clauses, variables, set(), symbols)
    
    if find_all:
        list(solver._find_model())
    else:
        try:
            next(solver._find_model())
        except StopIteration:
            pass

    print(f"Decisions: {solver.num_decisions}")
    print(f"Nodes: {len(solver.graph)}")

    dot_file = f"{name}.dot"
    png_file = f"{name}.png"
    with open(dot_file, "w") as f:
        f.write(solver.to_dot())
    
    try:
        subprocess.run(["dot", "-Tpng", dot_file, "-o", png_file], check=True)
        print(f"Visualization saved to {png_file}")
    except:
        print(f"Could not render {png_file}")

def gen_n_queens(n):
    clauses = []
    # Variables: x_rc = (r*n) + c + 1
    def x(r, c): return r * n + c + 1

    # 1. At least one queen per row
    for r in range(n):
        clauses.append([x(r, c) for c in range(n)])
    
    # 2. At most one queen per row
    for r in range(n):
        for c1 in range(n):
            for c2 in range(c1 + 1, n):
                clauses.append([-x(r, c1), -x(r, c2)])
    
    # 3. At most one queen per column
    for c in range(n):
        for r1 in range(n):
            for r2 in range(r1 + 1, n):
                clauses.append([-x(r1, c), -x(r2, c)])
    
    # 4. At most one queen per diagonal
    for r1 in range(n):
        for c1 in range(n):
            for r2 in range(r1 + 1, n):
                for c2 in range(n):
                    if abs(r1 - r2) == abs(c1 - c2):
                        clauses.append([-x(r1, c1), -x(r2, c2)])
    return clauses

def gen_pigeonhole(n, m):
    # n pigeons, m holes
    # x_ph = p*m + h + 1
    def x(p, h): return p * m + h + 1
    clauses = []
    # Each pigeon in at least one hole
    for p in range(n):
        clauses.append([x(p, h) for h in range(m)])
    # Each hole has at most one pigeon
    for h in range(m):
        for p1 in range(n):
            for p2 in range(p1 + 1, n):
                clauses.append([-x(p1, h), -x(p2, h)])
    return clauses

# Ensure directory exists
os.makedirs("sat_visualizations", exist_ok=True)

# 1. Implication Chain
symbols1 = [A, B, C, D, E]
clauses1 = [[-1, 2], [-2, 3], [-3, 4], [-4, 5], [1]]
run_example("sat_visualizations/implication_chain", symbols1, clauses1)

# 2. Triangle Graph Coloring (2 colors): UNSAT
symbols2 = [A, B, C, D, E, F] # A1, A2, B1, B2, C1, C2
clauses2 = [
    [1, 2], [3, 4], [5, 6], # Each node has a color
    [-1, -2], [-3, -4], [-5, -6], # At most one color
    [-1, -3], [-2, -4], # Edge A-B
    [-3, -5], [-4, -6], # Edge B-C
    [-1, -5], [-2, -6]  # Edge A-C
]
run_example("sat_visualizations/triangle_coloring", symbols2, clauses2)

# 3. Pigeonhole Principle (4 pigeons, 3 holes): UNSAT
clauses3 = gen_pigeonhole(4, 3)
symbols3 = [f"P{p}{h}" for p in range(4) for h in range(3)]
run_example("sat_visualizations/pigeonhole_4_3", symbols3, clauses3)

# 4. N-Queens (N=4): SAT
clauses4 = gen_n_queens(4)
symbols4 = [f"Q{r}{c}" for r in range(4) for c in range(4)]
run_example("sat_visualizations/n_queens_4", symbols4, clauses4)
