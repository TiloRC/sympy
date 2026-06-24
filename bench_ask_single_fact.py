"""
Benchmark: five _ask_single_fact implementations

  old    : original dict-lookup with early exit
  current: BMLP-SMP bitset with @cacheit
  v12    : improvements 1+2 (module-level global, single-pass closure+rejection)
  v123   : improvements 1+2+3 (above + list of indices instead of bitvector)
  v1234  : improvements 1+2+3+4 (above + hybrid fast-path for single unit clause)

Caches/globals are all warmed before timing.
"""
import timeit
from sympy import Q
from sympy.assumptions.cnf import CNF
from sympy.assumptions.ask import _ask_single_fact, _get_known_facts_matrices
from sympy.assumptions.ask_generated import get_known_facts_dict


# ---------------------------------------------------------------------------
# old: original dict-lookup
# ---------------------------------------------------------------------------
def _ask_old(key, local_facts):
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


# ---------------------------------------------------------------------------
# Shared matrix build (module-level global, lazy init — improvement 1)
# ---------------------------------------------------------------------------
_MATRICES = None

def _get_matrices():
    global _MATRICES
    if _MATRICES is None:
        d = get_known_facts_dict()
        preds = sorted(d, key=lambda p: str(p))
        index = {p: i for i, p in enumerate(preds)}
        n = len(preds)
        IMP = [0] * n
        REJ = [0] * n
        for p, (imp, rej) in d.items():
            i = index[p]
            for q in imp: IMP[i] |= 1 << index[q]
            for q in rej: REJ[i] |= 1 << index[q]
        _MATRICES = (index, IMP, REJ)
    return _MATRICES


# ---------------------------------------------------------------------------
# v12: improvements 1+2
#   1. module-level global instead of @cacheit
#   2. single pass for closure+rejection (IMP already closed, REJ closed under implication)
#      still uses bitvector for pos/neg collection + bit-extraction loop
# ---------------------------------------------------------------------------
def _ask_v12(key, local_facts):
    if not local_facts.clauses:
        return None
    index, IMP, REJ = _get_matrices()
    if key not in index:
        return None
    kbit = 1 << index[key]

    pos = neg = 0
    for clause in local_facts.clauses:
        if len(clause) != 1:
            continue
        (f,) = clause
        i = index.get(f.arg)
        if i is None:
            continue
        if f.is_Not:
            neg |= 1 << i
        else:
            pos |= 1 << i

    # Single pass: closure and rejection together (improvement 2)
    closure = rejected = 0
    c = pos
    while c:
        b = c & -c
        idx = b.bit_length() - 1
        closure |= IMP[idx]
        rejected |= REJ[idx]
        c ^= b

    if closure & kbit:
        return True
    if rejected & kbit:
        return False
    if neg & IMP[index[key]]:
        return False
    return None


# ---------------------------------------------------------------------------
# v123: improvements 1+2+3
#   3. collect indices into a list; iterate the list directly (no bit extraction)
# ---------------------------------------------------------------------------
def _ask_v123(key, local_facts):
    if not local_facts.clauses:
        return None
    index, IMP, REJ = _get_matrices()
    if key not in index:
        return None
    kbit = 1 << index[key]

    pos_idx = []
    neg_idx = []
    for clause in local_facts.clauses:
        if len(clause) != 1:
            continue
        (f,) = clause
        i = index.get(f.arg)
        if i is None:
            continue
        if f.is_Not:
            neg_idx.append(i)
        else:
            pos_idx.append(i)

    # Single pass over list (improvement 3 replaces bit-extraction loop)
    closure = rejected = 0
    for i in pos_idx:
        closure |= IMP[i]
        rejected |= REJ[i]

    if closure & kbit:
        return True
    if rejected & kbit:
        return False

    ki = index[key]
    key_imp = IMP[ki]
    for i in neg_idx:
        if key_imp & (1 << i):
            return False
    return None


# ---------------------------------------------------------------------------
# v1234: improvements 1+2+3+4
#   4. hybrid fast-path for the common single-unit-clause case
# ---------------------------------------------------------------------------
def _ask_v1234(key, local_facts):
    if not local_facts.clauses:
        return None
    index, IMP, REJ = _get_matrices()
    if key not in index:
        return None
    kbit = 1 << index[key]

    pos_idx = []
    neg_idx = []
    for clause in local_facts.clauses:
        if len(clause) != 1:
            continue
        (f,) = clause
        i = index.get(f.arg)
        if i is None:
            continue
        if f.is_Not:
            neg_idx.append(i)
        else:
            pos_idx.append(i)

    # Fast-path: single positive unit clause (improvement 4)
    if len(pos_idx) == 1 and not neg_idx:
        row = IMP[pos_idx[0]]
        if row & kbit:
            return True
        if REJ[pos_idx[0]] & kbit:
            return False
        return None

    # Fast-path: single negative unit clause, no positives (improvement 4)
    if not pos_idx and len(neg_idx) == 1:
        if IMP[index[key]] & (1 << neg_idx[0]):
            return False
        return None

    # General case
    closure = rejected = 0
    for i in pos_idx:
        closure |= IMP[i]
        rejected |= REJ[i]

    if closure & kbit:
        return True
    if rejected & kbit:
        return False

    key_imp = IMP[index[key]]
    for i in neg_idx:
        if key_imp & (1 << i):
            return False
    return None


# ---------------------------------------------------------------------------
# Warm everything before timing
# ---------------------------------------------------------------------------
get_known_facts_dict()
_get_known_facts_matrices()
_get_matrices()

# ---------------------------------------------------------------------------
# Test cases
# ---------------------------------------------------------------------------
CASES = {
    "empty clauses -> None": (
        Q.even, CNF()),
    "1 pos unit, True  (zero->even)": (
        Q.even, CNF.from_prop(Q.zero)),
    "1 pos unit, False (odd->!even)": (
        Q.even, CNF.from_prop(Q.odd)),
    "1 neg unit, False (~zero->!zero)": (
        Q.zero, CNF.from_prop(~Q.zero)),
    "1 neg unit, False (~even, modus tollens)": (
        Q.zero, CNF.from_prop(~Q.even)),
    "1 pos unit, None  (positive->transcendental?)": (
        Q.transcendental, CNF.from_prop(Q.positive)),
    "2 pos units (zero & integer, key=rational)": (
        Q.rational, CNF.from_prop(Q.zero & Q.integer)),
    "4 pos units (key=algebraic)": (
        Q.algebraic, CNF.from_prop(Q.integer & Q.positive & Q.real & Q.finite)),
    "8 pos units, None (key=prime)": (
        Q.prime, CNF.from_prop(
            Q.integer & Q.positive & Q.real & Q.finite &
            Q.rational & Q.algebraic & Q.hermitian & Q.commutative)),
    "8 pos units, False (has Q.odd, key=even)": (
        Q.even, CNF.from_prop(
            Q.integer & Q.positive & Q.real & Q.finite &
            Q.rational & Q.algebraic & Q.hermitian & Q.odd)),
}

IMPLS = [
    ("old",    _ask_old),
    ("current",_ask_single_fact),
    ("v12",    _ask_v12),
    ("v123",   _ask_v123),
    ("v1234",  _ask_v1234),
]

# Verify all implementations agree
for label, (key, local_facts) in CASES.items():
    results = {name: fn(key, local_facts) for name, fn in IMPLS}
    for name, res in results.items():
        assert res == results["old"], \
            f"MISMATCH '{label}' {name}={res} old={results['old']}"

N = 30_000
W = 42
H = f"{'Case':<{W}}" + "".join(f"{name:>9}" for name, _ in IMPLS)
print(H)
print("-" * len(H))

for label, (key, local_facts) in CASES.items():
    times = [timeit.timeit(lambda fn=fn: fn(key, local_facts), number=N) / N * 1e6
             for _, fn in IMPLS]
    row = f"{label:<{W}}" + "".join(f"{t:>8.2f} " for t in times)
    print(row)
