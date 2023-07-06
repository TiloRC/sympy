"""Implementation of DPLL(T) algorithm

References:
  - https://resources.mpi-inf.mpg.de/departments/rg1/conferences/vtsa17/slides/reynolds-vtsa-part1.pdf

  - Dutertre, B., de Moura, L. (2006). A Fast Linear-Arithmetic Solver for DPLL(T).
  In: Ball, T., Jones, R.B. (eds) Computer Aided Verification. CAV 2006.
  Lecture Notes in Computer Science, vol 4144. Springer, Berlin, Heidelberg.
  https://doi.org/10.1007/11817963_11
"""


"""
naive algorith:

All you need is an off the shelf sat solver and a theory solver. For this implementation


"""



class TheorySolver():
    """
    Requirements
    ============

    Let M be a set of T-literals. Then a theory solver should satisfy the
    following requirements:

    - Should be solution-sound, refutation-sound, terminating
    - Should produce models when M is T-satisfiable
    - **Should produce T-conflicts of minimal size when M is T-unsatisfiable**
    - **Should be designed to work incrementally**
        - M is constantly being appended to/backtracked upon
    - Can be designed to check T-satisfiability either:
        + Eagerly: Check if M is T-satisfiable immediately when any literal is
         added to M
        + Lazily: Check if M is T-satisfiable only when M is complete
    - Should cooperate with other theory solvers when combining theories
    """

    def __init__(self):
        self.state = {} # the set of atoms asserted so far

    def assert_atom(self, atom):
        """
        Adds an atom to the current state. Returns either ok or unsat with a
        conflict clause.
        """
        pass

    def check(self):
        """
        Checks whether the current state is consitent. Returns either ok or
        unsat with a conflict clause.
        """
        pass

    def backtrack(self):
        """
        Backtracts to consitent state on top of stack.
        """
        pass

class QFLinearRealArithmatic(TheorySolver):
    pass

class QFEqualityAndUninterpretedFunctions(TheorySolver):
    pass

def dpll_t(sat_solver, theory_solvers):
 pass

