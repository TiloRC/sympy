import matplotlib.pyplot as plt
from sympy.logic.utilities import load_file
from sympy import symbols, And, satisfiable
import timeit
import os

input_path = os.path.dirname(__file__)
input_path += "/../../sympy_benchmarks/benchmarks"
theories = []
for test in [5 * i for i in range(2, 30)]:
    file_name = os.path.join(input_path, 'logic-inputs', '%s.cnf' % test)
    theory = load_file(file_name)
    theories.append(theory)



import z3
z3_times = []
dpll2_times = []
for theory in theories:
    z3_time = timeit.timeit(lambda: satisfiable(theory, algorithm="z3"), number=3)
    dpll2_time = timeit.timeit(lambda: satisfiable(theory, algorithm="dpll2"), number=3)
    z3_times.append(z3_time)
    dpll2_times.append(dpll2_time)

plt.plot(z3_times, label='z3')
plt.plot(dpll2_times, label='dpll2')
plt.legend()
plt.show()

plt.semilogy(z3_times, label='z3')  # Log scale for the y-axis
plt.semilogy(dpll2_times, label='dpll2')  # Log scale for the y-axis
plt.legend()
plt.savefig("benchmarks.png")
plt.show()
