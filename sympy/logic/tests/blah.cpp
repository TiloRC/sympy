#include "z3.h"
#include <iostream>
#include <fstream>
#include <sstream>
#include <string>
#include <vector>
#include <gperftools/profiler.h>


// Function to split the file content into SMT-LIB strings
std::vector<std::string> split_smtlib_strings(const std::string& content) {
    std::vector<std::string> strings;
    std::string delimiter = "\n\n\n";
    size_t start = 0;
    size_t end = content.find(delimiter);
    while (end != std::string::npos) {
        strings.push_back(content.substr(start, end - start));
        start = end + delimiter.length();
        end = content.find(delimiter, start);
    }
    strings.push_back(content.substr(start));
    return strings;
}

int main() {
    // Read SMT-LIB strings from file
    std::ifstream infile("smtlib_strings.txt");
    if (!infile.is_open()) {
        std::cerr << "Failed to open smtlib_strings.txt" << std::endl;
        return 1;
    }

    std::stringstream buffer;
    buffer << infile.rdbuf();
    std::string file_content = buffer.str();
    infile.close();

    // Split the file content into individual SMT-LIB strings
    std::vector<std::string> smtlib_strings = split_smtlib_strings(file_content);


     ProfilerStart("profile.prof");

    // Initialize a Z3 context
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    // Iterate over SMT-LIB strings and check satisfiability
    for (const auto& smtlib2_str : smtlib_strings) {
        // Create a solver
        Z3_solver solver = Z3_mk_solver(ctx);
        Z3_solver_inc_ref(ctx, solver);

        // Use Z3_solver_from_string to parse and load the SMT-LIB string into the solver
        Z3_solver_from_string(ctx, solver, smtlib2_str.c_str());

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
    }

    Z3_del_context(ctx);

     ProfilerStop();

    return 0;
}
