

import os
from sympy.logic.utilities import load_file
input_path = os.path.dirname(__file__)

input_path += "/../../sympy_benchmarks/benchmarks"

theories = []
for test in [5 * i for i in range(2, 30)]:
    file_name = os.path.join(input_path, 'logic-inputs', '%s.cnf' % test)
    theory = load_file(file_name)
    theories.append(theory)


from sympy import symbols, And, satisfiable
import timeit
easy_cnf_10 = And(*symbols(f'var0:10'))
easy_cnf_1k = And(*symbols(f'var0:1000'))
easy_cnf_10k = And(*symbols(f'var0:10000'))

# print(timeit.timeit(lambda: satisfiable(easy_cnf_10, algorithm="dpll2"), number=3))
# print(timeit.timeit(lambda: satisfiable(easy_cnf_10k, algorithm="dpll2"), number=3))
# print(timeit.timeit(lambda: satisfiable(easy_cnf_10, algorithm="z3"), number=3))
# print(timeit.timeit(lambda: satisfiable(easy_cnf_10k, algorithm="z3"), number=3))

import z3
for theory in theories:
    z3_time = timeit.timeit(lambda: satisfiable(theory, algorithm="z3"), number=1)
    dpll2_time = timeit.timeit(lambda: satisfiable(theory, algorithm="dpll2"), number=1)
    print(f"z3:{z3_time}, dpll2:{dpll2_time}")


#
# easy_cnf_100 = And(*symbols(f'var0:10'))
# for _ in range(5):
#     print(timeit.timeit(lambda: satisfiable(easy_cnf_100, algorithm="z3"), number=1))
# print(timeit.timeit(lambda: satisfiable(easy_cnf_100, algorithm="z3"), number=1))
# print(timeit.timeit(lambda: satisfiable(easy_cnf_100, algorithm="z3"), number=1))
# print(timeit.timeit(lambda: satisfiable(easy_cnf_100, algorithm="z3"), number=1))
