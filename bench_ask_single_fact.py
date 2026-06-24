"""
Benchmark: old vs new _ask_single_fact

Caches are warmed before timing so only the inference logic is measured.
"""
import timeit
from sympy import Q
from sympy.assumptions.cnf import CNF
from sympy.assumptions.ask import _ask_single_fact, _get_known_facts_matrices
from sympy.assumptions.ask_generated import get_known_facts_dict


# --- old implementation, copied verbatim ---
def _ask_single_fact_old(key, local_facts):
    if not local_facts.clauses:
        return None

    known_facts_dict = get_known_facts_dict()
    get_facts = lambda k: known_facts_dict.get(k, (set(), set()))

    for clause in local_facts.clauses:
        if len(clause) != 1:
            continue
        (f,) = clause
        pred, negated = f.arg, f.is_Not

        key_req, _ = get_facts(key)
        if negated and pred in key_req:
            return False

        if not negated:
            req, rej = get_facts(pred)
            if key in req:
                return True
            if key in rej:
                return False

    return None


# --- warm all caches before timing ---
get_known_facts_dict()
_get_known_facts_matrices()

# --- test cases ---
CASES = {
    "empty clauses -> None": (
        Q.even,
        CNF(),
    ),
    "single positive unit, hit True (zero->even)": (
        Q.even,
        CNF.from_prop(Q.zero),
    ),
    "single positive unit, hit False (odd->!even)": (
        Q.even,
        CNF.from_prop(Q.odd),
    ),
    "single negative unit, hit False (~zero->!zero)": (
        Q.zero,
        CNF.from_prop(~Q.zero),
    ),
    "single negative unit, modus tollens (~even->!zero)": (
        Q.zero,
        CNF.from_prop(~Q.even),
    ),
    "single positive unit, no hit -> None": (
        Q.transcendental,
        CNF.from_prop(Q.positive),
    ),
    "chained: prime->algebraic (one hop in dict)": (
        Q.algebraic,
        CNF.from_prop(Q.prime),
    ),
    "2 units: zero & integer (key=rational)": (
        Q.rational,
        CNF.from_prop(Q.zero & Q.integer),
    ),
    "4 units: integer & positive & real & finite (key=algebraic)": (
        Q.algebraic,
        CNF.from_prop(Q.integer & Q.positive & Q.real & Q.finite),
    ),
    "8 units (all positive, key=prime)": (
        Q.prime,
        CNF.from_prop(
            Q.integer & Q.positive & Q.real & Q.finite &
            Q.rational & Q.algebraic & Q.hermitian & Q.commutative
        ),
    ),
    "8 units, last one hits False (key=even, has Q.odd)": (
        Q.even,
        CNF.from_prop(
            Q.integer & Q.positive & Q.real & Q.finite &
            Q.rational & Q.algebraic & Q.hermitian & Q.odd
        ),
    ),
}

N = 50_000
WIDTH = 55

print(f"{'Case':<{WIDTH}} {'old (us)':>10} {'new (us)':>10} {'speedup':>9}")
print("-" * (WIDTH + 33))

for label, (key, local_facts) in CASES.items():
    # verify both agree
    old_res = _ask_single_fact_old(key, local_facts)
    new_res = _ask_single_fact(key, local_facts)
    assert old_res == new_res, f"MISMATCH on '{label}': old={old_res} new={new_res}"

    t_old = timeit.timeit(lambda: _ask_single_fact_old(key, local_facts), number=N)
    t_new = timeit.timeit(lambda: _ask_single_fact(key, local_facts), number=N)

    us_old = t_old / N * 1e6
    us_new = t_new / N * 1e6
    speedup = us_old / us_new

    print(f"{label:<{WIDTH}} {us_old:>10.2f} {us_new:>10.2f} {speedup:>8.2f}x")
