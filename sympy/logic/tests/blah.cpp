#include "z3.h"
#include <iostream>

int main() {
    // Initialize a Z3 context
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    // Create a solver
    Z3_solver solver = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, solver);

    // SMT-LIB string to parse
    const char* smtlib2_str = "(declare-fun x () Int)\n"
                              "(declare-fun y () Int)\n"
                              "(assert (> x y))\n"
                              "(assert (> x 10))\n"
                              "(check-sat)";

    // Use Z3_solver_from_string to parse and load the SMT-LIB string into the solver
    Z3_solver_from_string(ctx, solver, smtlib2_str);

    // Check the satisfiability of the loaded problem
    Z3_lbool result = Z3_solver_check(ctx, solver);
    if (result == Z3_L_TRUE) {
        std::cout << "SAT" << std::endl;
    } else if (result == Z3_L_FALSE) {
        std::cout << "UNSAT" << std::endl;
    } else {
        std::cout << "UNKNOWN" << std::endl;
    }

    // Cleanup
    Z3_solver_dec_ref(ctx, solver);
    Z3_del_context(ctx);

    return 0;
}
