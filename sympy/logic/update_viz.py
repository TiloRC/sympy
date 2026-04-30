import sys
import os
# Ensure we import from the local source
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "../../")))

import sympy
import re
import subprocess
from sympy.abc import A, B, C, D, E, F
from sympy.logic.algorithms.dpll2 import SATSolver
from sympy.logic.algorithms.sat_trace import TraceGraph

def run_example(name, symbols, clauses):
    print(f"\n--- Running Example: {name} ---")
    variables = set(range(1, len(symbols) + 1))
    
    # 1. Start the trace
    tg = TraceGraph(trace_clauses=True)
    tg.start_trace()

    # 2. Instantiate and run the solver
    solver = SATSolver(clauses, variables, set(), symbols, trace_graph=tg)
    try:
        next(solver._find_model())
    except StopIteration:
        pass
    
    # 3. End the trace and get DOT directly
    dot_content = tg.end_trace()

    print(f"Decisions: {solver.num_decisions}")
    
    # Calculate node count from DOT
    node_ids = set(re.findall(r"node_[a-z0-9_]+", dot_content)) if dot_content else set()
    node_count = len(node_ids)
    print(f"Nodes: {node_count}")

    if dot_content and node_count > 0:
        # Ensure path exists
        dirname = os.path.dirname(name)
        if dirname:
            os.makedirs(dirname, exist_ok=True)
            
        dot_file = f"{name}.dot"
        png_file = f"{name}.png"
        with open(dot_file, "w") as f:
            f.write(dot_content)
        
        try:
            subprocess.run(["dot", "-Tpng", dot_file, "-o", png_file], check=True)
            print(f"Visualization saved to {png_file}")
        except:
            print(f"Could not render {png_file} (is Graphviz installed?)")

def gen_n_queens(n):
    clauses = []
    def x(r, c): return r * n + c + 1
    for r in range(n):
        clauses.append([x(r, c) for c in range(n)])
    for r in range(n):
        for c1 in range(n):
            for c2 in range(c1 + 1, n):
                clauses.append([-x(r, c1), -x(r, c2)])
    for c in range(n):
        for r1 in range(n):
            for r2 in range(r1 + 1, n):
                clauses.append([-x(r1, c), -x(r2, c)])
    for r1 in range(n):
        for c1 in range(n):
            for r2 in range(r1 + 1, n):
                for c2 in range(n):
                    if abs(r1 - r2) == abs(c1 - c2):
                        clauses.append([-x(r1, c1), -x(r2, c2)])
    return clauses

def gen_pigeonhole(n, m):
    def x(p, h): return p * m + h + 1
    clauses = []
    for p in range(n):
        clauses.append([x(p, h) for h in range(m)])
    for h in range(m):
        for p1 in range(n):
            for p2 in range(p1 + 1, n):
                clauses.append([-x(p1, h), -x(p2, h)])
    return clauses

# Ensure directory exists
os.makedirs("sat_visualizations", exist_ok=True)

# --- SIMPLE EXAMPLES ---

# 1. Basic Contradiction: A and -A
run_example("sat_visualizations/contradiction", [A], [[1], [-1]])

# 2. Simple SAT: (A or B)
run_example("sat_visualizations/simple_sat", [A, B], [[1, 2]])

# 3. Branching UNSAT: All combinations of A, B
run_example("sat_visualizations/branch_unsat", [A, B], [[1, 2], [-1, 2], [1, -2], [-1, -2]])

# --- COMPLEX EXAMPLES ---

# 4. Implication Chain
run_example("sat_visualizations/implication_chain", [A, B, C, D, E], [[-1, 2], [-2, 3], [-3, 4], [-4, 5], [1]])

# 5. Triangle Graph Coloring (2 colors): UNSAT
run_example("sat_visualizations/triangle_coloring", [A, B, C, D, E, F], [
    [1, 2], [3, 4], [5, 6],
    [-1, -2], [-3, -4], [-5, -6],
    [-1, -3], [-2, -4],
    [-3, -5], [-4, -6],
    [-1, -5], [-2, -6]
])

# 6. Pigeonhole Principle (4 pigeons, 3 holes): UNSAT
run_example("sat_visualizations/pigeonhole_4_3", [f"P{p}{h}" for p in range(4) for h in range(3)], gen_pigeonhole(4, 3))

# 7. N-Queens (N=4): SAT
run_example("sat_visualizations/n_queens_4", [f"Q{r}{c}" for r in range(4) for c in range(4)], gen_n_queens(4))
