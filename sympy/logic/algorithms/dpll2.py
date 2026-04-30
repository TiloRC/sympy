"""Implementation of DPLL algorithm

Features:
  - Clause learning
  - Watch literal scheme
  - VSIDS heuristic

References:
  - https://en.wikipedia.org/wiki/DPLL_algorithm
"""
from __future__ import annotations

from collections import defaultdict
from heapq import heappush, heappop

from sympy.core.sorting import ordered
from sympy.assumptions.cnf import EncodedCNF

from sympy.logic.algorithms.lra_theory import LRASolver


# Set to True to enable tracing of the solver's decisions and propagations
TRACE = False
# Set to True to include the state of all clauses in the visualization nodes
TRACE_CLAUSES = False


def dpll_satisfiable(expr, all_models=False, use_lra_theory=False):
    """
    Check satisfiability of a propositional sentence.
    It returns a model rather than True when it succeeds.
    Returns a generator of all models if all_models is True.

    Examples
    ========

    >>> from sympy.abc import A, B
    >>> from sympy.logic.algorithms.dpll2 import dpll_satisfiable
    >>> dpll_satisfiable(A & ~B)
    {A: True, B: False}
    >>> dpll_satisfiable(A & ~A)
    False

    """
    if not isinstance(expr, EncodedCNF):
        exprs = EncodedCNF()
        exprs.add_prop(expr)
        expr = exprs

    # Return UNSAT when False (encoded as 0) is present in the CNF
    if {0} in expr.data:
        if all_models:
            return (f for f in [False])
        return False

    if use_lra_theory:
        lra, immediate_conflicts = LRASolver.from_encoded_cnf(expr)
    else:
        lra = None
        immediate_conflicts = []
    solver = SATSolver(expr.data + immediate_conflicts, expr.variables, set(), expr.symbols, lra_theory=lra)
    models = solver._find_model()

    if all_models:
        return _all_models(models)

    try:
        return next(models)
    except StopIteration:
        return False

    # Uncomment to confirm the solution is valid (hitting set for the clauses)
    #else:
        #for cls in clauses_int_repr:
            #assert solver.var_settings.intersection(cls)


def _all_models(models):
    satisfiable = False
    try:
        while True:
            yield next(models)
            satisfiable = True
    except StopIteration:
        if not satisfiable:
            yield False


class TraceGraph:
    """
    Encapsulates the state and logic for generating a Graphviz visualization
    of the SAT solver's search process.
    """

    def __init__(self, solver):
        self.solver = solver
        self.nodes = []
        self.edges = []
        self.node_count = 0
        self.parent_stack = [("node_root", 0)] # (node_id, level)
        self.pending_trace = None

        start_label = "START"
        if TRACE_CLAUSES:
            start_label += f"\\n{solver.clauses}"
        self.nodes.append(("node_root", start_label))

    def flush(self):
        if self.pending_trace:
            node_id = f"node_{self.node_count}"
            self.node_count += 1
            
            p = self.pending_trace
            label = p['msg']
            if p['consequences']:
                consequences_str = ""
                for cause, lits in p['consequences'].items():
                    lits_str = ", ".join(lits)
                    if cause:
                        consequences_str += f"\\n{cause} -> {lits_str}"
                    else:
                        consequences_str += f"\\n-> {lits_str}"
                label += consequences_str
            if p['conflict']:
                label += f"\\n{p['conflict']}"
            if p['sat']:
                label += "\\nSATISFIABLE"
            
            if TRACE_CLAUSES:
                label += f"\\n{p['clause_state']}"
            
            label = label.replace('"', '\\"')
            self.nodes.append((node_id, label))

            # Parent is the last node in the stack with level < current level
            parent_id = "node_root"
            while len(self.parent_stack) > 1 and self.parent_stack[-1][1] >= p['level']:
                self.parent_stack.pop()
            
            if self.parent_stack:
                parent_id = self.parent_stack[-1][0]
            
            self.edges.append((parent_id, node_id))
            self.parent_stack.append((node_id, p['level']))
            self.pending_trace = None

    def trace(self, msg, level=None, cause=None):
        if not TRACE:
            return

        if level is None:
            level = len(self.solver.levels) - 1
        print("  " * level + f"Level {level}: {msg}")

        if "Unit Propagation" in msg:
            content = msg.split('(')[-1]
            lit = content.split(')')[0]
            reason = ""
            if " via " in content:
                reason = f" (via {content.split(' via ')[-1]})"
            
            entry = f"{lit}{reason}"

            if self.pending_trace:
                if cause not in self.pending_trace['consequences']:
                    self.pending_trace['consequences'][cause] = []
                self.pending_trace['consequences'][cause].append(entry)
            elif level == 0:
                # Append to START node
                node_id, label = self.nodes[0]
                prefix = f"\\n{cause} -> " if cause else "\\n-> "
                if prefix not in label:
                    label += f"{prefix}{entry}"
                else:
                    label += f"\\n{cause if cause else ''} -> {entry}"
                self.nodes[0] = (node_id, label)
            return

        if msg == "STATE":
            if self.pending_trace:
                self.pending_trace['clause_state'] = self.get_clause_state()
            elif level == 0:
                # Update START node state if not already done
                node_id, label = self.nodes[0]
                state = self.get_clause_state()
                if state not in label:
                    label += f"\\n{state}"
                    self.nodes[0] = (node_id, label)
            return

        # Check if this is a terminal outcome for a level
        if "CONFLICT" in msg or "SATISFIABLE" in msg:
            if self.pending_trace:
                if "CONFLICT" in msg:
                    # Don't overwrite detailed conflict with generic one
                    if self.pending_trace['conflict'] and "(" not in msg:
                        return
                    if "(" in msg:
                        parts = msg.split('(')[-1].split(')')[0].split(' and ')
                        self.pending_trace['conflict'] = f"CONFLICT: {parts[0]} vs {parts[1]}"
                    else:
                        self.pending_trace['conflict'] = "CONFLICT"
                else:
                    self.pending_trace['sat'] = True
                return
            elif level == 0:
                # Root level conflict
                node_id = f"node_{self.node_count}"
                self.node_count += 1
                label = msg
                if "(" in msg:
                    parts = msg.split('(')[-1].split(')')[0].split(' and ')
                    label = f"CONFLICT: {parts[0]} vs {parts[1]}"
                self.nodes.append((node_id, label))
                self.edges.append(("node_root", node_id))
                return

        # If it's a literal, it's a new decision/branch. Flush previous.
        try:
            int(msg)
            self.flush()
            self.pending_trace = {
                'msg': msg,
                'level': level,
                'consequences': {}, # Grouped by trigger literal
                'conflict': None,
                'sat': False,
                'clause_state': ""
            }
        except ValueError:
            pass

    def get_clause_state(self):
        simplified = []
        for clause in self.solver.clauses:
            is_satisfied = False
            new_clause = []
            for lit in clause:
                if lit in self.solver.var_settings:
                    is_satisfied = True
                    break
                if -lit not in self.solver.var_settings:
                    new_clause.append(lit)
            if not is_satisfied:
                simplified.append(new_clause)
        return str(simplified)

    def to_dot(self):
        self.flush()
        dot = ["digraph SATSearch {", "  graph [dpi=300];"]
        for node_id, label in self.nodes:
            dot.append(f'  {node_id} [label="{label}"];')
        for start, end in self.edges:
            dot.append(f"  {start} -> {end};")
        dot.append("}")
        return "\n".join(dot)

    def __len__(self):
        return len(self.nodes)


class SATSolver:
    """
    Class for representing a SAT solver capable of
     finding a model to a boolean theory in conjunctive
     normal form.
    """

    def __init__(self, clauses, variables, var_settings, symbols=None,
                heuristic='vsids', clause_learning='none', INTERVAL=500,
                 lra_theory = None):

        self.var_settings = var_settings
        self.heuristic = heuristic
        self.is_unsatisfied = False
        self._unit_prop_queue = []
        self.update_functions = []
        self.INTERVAL = INTERVAL

        if symbols is None:
            self.symbols = list(ordered(variables))
        else:
            self.symbols = symbols

        self._initialize_variables(variables)
        self._initialize_clauses(clauses)

        if 'vsids' == heuristic:
            self._vsids_init()
            self.heur_calculate = self._vsids_calculate
            self.heur_lit_assigned = self._vsids_lit_assigned
            self.heur_lit_unset = self._vsids_lit_unset
            self.heur_clause_added = self._vsids_clause_added

            # Note: Uncomment this if/when clause learning is enabled
            #self.update_functions.append(self._vsids_decay)

        else:
            raise NotImplementedError

        if 'simple' == clause_learning:
            self.add_learned_clause = self._simple_add_learned_clause
            self.compute_conflict = self._simple_compute_conflict
            self.update_functions.append(self._simple_clean_clauses)
        elif 'none' == clause_learning:
            self.add_learned_clause = lambda x: None
            self.compute_conflict = lambda: None
        else:
            raise NotImplementedError

        # Create the base level
        self.levels = [Level(0)]
        self._current_level.varsettings = var_settings

        # Keep stats
        self.num_decisions = 0
        self.num_learned_clauses = 0
        self.original_num_clauses = len(self.clauses)

        self.lra = lra_theory

        # For Graphviz visualization
        self.graph = TraceGraph(self)

    def _trace(self, *args, **kwargs):
        self.graph.trace(*args, **kwargs)

    def to_dot(self):
        return self.graph.to_dot()

    def _format_lit(self, lit):
        return str(lit)

    def _initialize_variables(self, variables):
        """Set up the variable data structures needed."""
        self.sentinels = defaultdict(set)
        self.occurrence_count = defaultdict(int)
        self.variable_set = [False] * (len(variables) + 1)

    def _initialize_clauses(self, clauses):
        """Set up the clause data structures needed.

        For each clause, the following changes are made:
        - Unit clauses are queued for propagation right away.
        - Non-unit clauses have their first and last literals set as sentinels.
        - The number of clauses a literal appears in is computed.
        """
        self.clauses = [list(clause) for clause in clauses]

        for i, clause in enumerate(self.clauses):

            # Handle the unit clauses
            if 1 == len(clause):
                self._unit_prop_queue.append((clause[0], i))
                continue

            self.sentinels[clause[0]].add(i)
            self.sentinels[clause[-1]].add(i)

            for lit in clause:
                self.occurrence_count[lit] += 1

    def _find_model(self):
        """
        Main DPLL loop. Returns a generator of models.

        Variables are chosen successively, and assigned to be either
        True or False. If a solution is not found with this setting,
        the opposite is chosen and the search continues. The solver
        halts when every variable has a setting.

        Examples
        ========

        >>> from sympy.logic.algorithms.dpll2 import SATSolver
        >>> l = SATSolver([{2, -3}, {1}, {3, -3}, {2, -2},
        ... {3, -2}], {1, 2, 3}, set())
        >>> list(l._find_model())
        [{1: True, 2: False, 3: False}, {1: True, 2: True, 3: True}]

        >>> from sympy.abc import A, B, C
        >>> l = SATSolver([{2, -3}, {1}, {3, -3}, {2, -2},
        ... {3, -2}], {1, 2, 3}, set(), [A, B, C])
        >>> list(l._find_model())
        [{A: True, B: False, C: False}, {A: True, B: True, C: True}]

        """

        # We use this variable to keep track of if we should flip a
        #  variable setting in successive rounds
        flip_var = False

        # Check if unit prop says the theory is unsat right off the bat
        self._simplify()
        if TRACE_CLAUSES:
            self._trace("STATE")
        if self.is_unsatisfied:
            self._trace("CONFLICT")
            return

        # While the theory still has clauses remaining
        while True:
            # Perform cleanup / fixup at regular intervals
            if self.num_decisions % self.INTERVAL == 0:
                for func in self.update_functions:
                    func()

            if flip_var:
                # We have just backtracked and we are trying to opposite literal
                flip_var = False
                lit = self._current_level.decision
                msg = self._format_lit(lit)

            else:
                # Pick a literal to set
                lit = self.heur_calculate()
                self.num_decisions += 1

                # Stopping condition for a satisfying theory
                if 0 == lit:

                    # check if assignment satisfies lra theory
                    if self.lra:
                        for enc_var in self.var_settings:
                            res = self.lra.assert_lit(enc_var)
                            if res is not None:
                                break
                        res = self.lra.check()
                        self.lra.reset_bounds()
                    else:
                        res = None
                    if res is None or res[0]:
                        self._trace("SATISFIABLE")
                        yield {self.symbols[abs(lit) - 1]:
                                    lit > 0 for lit in self.var_settings}
                    else:
                        self._simple_add_learned_clause(res[1])

                        # backtrack until we unassign one of the literals causing the conflict
                        while not any(-lit in res[1] for lit in self._current_level.var_settings):
                            self._undo()

                    while self._current_level.flipped:
                        self._undo()
                    if len(self.levels) == 1:
                        return
                    flip_lit = -self._current_level.decision
                    self._undo()
                    self.levels.append(Level(flip_lit, flipped=True))
                    flip_var = True
                    continue

                # Start the new decision level
                self.levels.append(Level(lit))
                msg = self._format_lit(lit)

            # Trace the literal BEFORE assignment and simplification
            self._trace(msg)

            # Assign the literal, updating the clauses it satisfies
            self._assign_literal(lit)

            # _simplify the theory
            self._simplify()
            
            # Trace the state AFTER simplification
            if TRACE_CLAUSES:
                self._trace("STATE")

            # Check if we've made the theory unsat
            if self.is_unsatisfied:

                self.is_unsatisfied = False
                self._trace("CONFLICT")

                # We unroll all of the decisions until we can flip a literal
                while self._current_level.flipped:
                    self._undo()

                    # If we've unrolled all the way, the theory is unsat
                    if 1 == len(self.levels):
                        return

                # Detect and add a learned clause
                self.add_learned_clause(self.compute_conflict())

                # Try the opposite setting of the most recent decision
                flip_lit = -self._current_level.decision
                self._undo()
                self.levels.append(Level(flip_lit, flipped=True))
                flip_var = True

    ########################
    #    Helper Methods    #
    ########################
    @property
    def _current_level(self):
        """The current decision level data structure

        Examples
        ========

        >>> from sympy.logic.algorithms.dpll2 import SATSolver
        >>> l = SATSolver([{1}, {2}], {1, 2}, set())
        >>> next(l._find_model())
        {1: True, 2: True}
        >>> l._current_level.decision
        0
        >>> l._current_level.flipped
        False
        >>> l._current_level.var_settings
        {1, 2}

        """
        return self.levels[-1]

    def _clause_sat(self, cls):
        """Check if a clause is satisfied by the current variable setting.

        Examples
        ========

        >>> from sympy.logic.algorithms.dpll2 import SATSolver
        >>> l = SATSolver([{1}, {-1}], {1}, set())
        >>> try:
        ...     next(l._find_model())
        ... except StopIteration:
        ...     pass
        >>> l._clause_sat(0)
        False
        >>> l._clause_sat(1)
        True

        """
        for lit in self.clauses[cls]:
            if lit in self.var_settings:
                return True
        return False

    def _is_sentinel(self, lit, cls):
        """Check if a literal is a sentinel of a given clause.

        Examples
        ========

        >>> from sympy.logic.algorithms.dpll2 import SATSolver
        >>> l = SATSolver([{2, -3}, {1}, {3, -3}, {2, -2},
        ... {3, -2}], {1, 2, 3}, set())
        >>> next(l._find_model())
        {1: True, 2: False, 3: False}
        >>> l._is_sentinel(2, 3)
        True
        >>> l._is_sentinel(-3, 1)
        False

        """
        return cls in self.sentinels[lit]

    def _assign_literal(self, lit):
        """Make a literal assignment.

        The literal assignment must be recorded as part of the current
        decision level. Additionally, if the literal is marked as a
        sentinel of any clause, then a new sentinel must be chosen. If
        this is not possible, then unit propagation is triggered and
        another literal is added to the queue to be set in the future.

        Examples
        ========

        >>> from sympy.logic.algorithms.dpll2 import SATSolver
        >>> l = SATSolver([{2, -3}, {1}, {3, -3}, {2, -2},
        ... {3, -2}], {1, 2, 3}, set())
        >>> next(l._find_model())
        {1: True, 2: False, 3: False}
        >>> l.var_settings
        {-3, -2, 1}

        >>> l = SATSolver([{2, -3}, {1}, {3, -3}, {2, -2},
        ... {3, -2}], {1, 2, 3}, set())
        >>> l._assign_literal(-1)
        >>> try:
        ...     next(l._find_model())
        ... except StopIteration:
        ...     pass
        >>> l.var_settings
        {-1}

        """
        self.var_settings.add(lit)
        self._current_level.var_settings.add(lit)
        self.variable_set[abs(lit)] = True
        self.heur_lit_assigned(lit)

        sentinel_list = list(self.sentinels[-lit])

        for cls in sentinel_list:
            if not self._clause_sat(cls):
                other_sentinel = None
                for newlit in self.clauses[cls]:
                    if newlit != -lit:
                        if self._is_sentinel(newlit, cls):
                            other_sentinel = newlit
                        elif not self.variable_set[abs(newlit)]:
                            self.sentinels[-lit].remove(cls)
                            self.sentinels[newlit].add(cls)
                            other_sentinel = None
                            break

                # Check if no sentinel update exists
                if other_sentinel:
                    self._unit_prop_queue.append((other_sentinel, cls, lit))

    def _undo(self):
        """
        _undo the changes of the most recent decision level.

        Examples
        ========

        >>> from sympy.logic.algorithms.dpll2 import SATSolver
        >>> l = SATSolver([{2, -3}, {1}, {3, -3}, {2, -2},
        ... {3, -2}], {1, 2, 3}, set())
        >>> next(l._find_model())
        {1: True, 2: False, 3: False}
        >>> level = l._current_level
        >>> level.decision, level.var_settings, level.flipped
        (-3, {-3, -2}, False)
        >>> l._undo()
        >>> level = l._current_level
        >>> level.decision, level.var_settings, level.flipped
        (0, {1}, False)

        """
        # Undo the variable settings
        for lit in self._current_level.var_settings:
            self.var_settings.remove(lit)
            self.heur_lit_unset(lit)
            self.variable_set[abs(lit)] = False

        # Pop the level off the stack
        self.levels.pop()

    #########################
    #      Propagation      #
    #########################
    """
    Propagation methods should attempt to soundly simplify the boolean
      theory, and return True if any simplification occurred and False
      otherwise.
    """
    def _simplify(self):
        """Iterate over the various forms of propagation to simplify the theory.

        Examples
        ========

        >>> from sympy.logic.algorithms.dpll2 import SATSolver
        >>> l = SATSolver([{2, -3}, {1}, {3, -3}, {2, -2},
        ... {3, -2}], {1, 2, 3}, set())
        >>> l.variable_set
        [False, False, False, False]
        >>> l.sentinels
        {-3: {0, 2}, -2: {3, 4}, 2: {0, 3}, 3: {2, 4}}

        >>> l._simplify()

        >>> l.variable_set
        [False, True, False, False]
        >>> l.sentinels
        {-3: {0, 2}, -2: {3, 4}, -1: set(), 2: {0, 3},
        ...3: {2, 4}}

        """
        changed = True
        while changed:
            changed = False
            changed |= self._unit_prop()
            changed |= self._pure_literal()

    def _unit_prop(self):
        """Perform unit propagation on the current theory."""
        result = len(self._unit_prop_queue) > 0
        while self._unit_prop_queue:
            next_item = self._unit_prop_queue.pop()
            if isinstance(next_item, tuple):
                if len(next_item) == 3:
                    next_lit, reason_cls, trigger_lit = next_item
                else:
                    next_lit, reason_cls, trigger_lit = next_item[0], next_item[1], None
            else:
                next_lit, reason_cls, trigger_lit = next_item, None, None

            if -next_lit in self.var_settings:
                self._trace(f"CONFLICT ({self._format_lit(next_lit)} and {self._format_lit(-next_lit)})")
                self.is_unsatisfied = True
                self._unit_prop_queue = []
                return False
            elif next_lit not in self.var_settings:
                reason_str = f" via {self.clauses[reason_cls]}" if reason_cls is not None else ""
                self._trace(f"Unit Propagation ({self._format_lit(next_lit)}){reason_str}", cause=trigger_lit)
                self._assign_literal(next_lit)

        return result

    def _pure_literal(self):
        """Look for pure literals and assign them when found."""
        return False

    #########################
    #      Heuristics       #
    #########################
    def _vsids_init(self):
        """Initialize the data structures needed for the VSIDS heuristic."""
        self.lit_heap = []
        self.lit_scores = {}

        for var in range(1, len(self.variable_set)):
            self.lit_scores[var] = float(-self.occurrence_count[var])
            self.lit_scores[-var] = float(-self.occurrence_count[-var])
            heappush(self.lit_heap, (self.lit_scores[var], var))
            heappush(self.lit_heap, (self.lit_scores[-var], -var))

    def _vsids_decay(self):
        """Decay the VSIDS scores for every literal.

        Examples
        ========

        >>> from sympy.logic.algorithms.dpll2 import SATSolver
        >>> l = SATSolver([{2, -3}, {1}, {3, -3}, {2, -2},
        ... {3, -2}], {1, 2, 3}, set())

        >>> l.lit_scores
        {-3: -2.0, -2: -2.0, -1: 0.0, 1: 0.0, 2: -2.0, 3: -2.0}

        >>> l._vsids_decay()

        >>> l.lit_scores
        {-3: -1.0, -2: -1.0, -1: 0.0, 1: 0.0, 2: -1.0, 3: -1.0}

        """
        # We divide every literal score by 2 for a decay factor
        #  Note: This doesn't change the heap property
        for lit in self.lit_scores.keys():
            self.lit_scores[lit] /= 2.0

    def _vsids_calculate(self):
        """
            VSIDS Heuristic Calculation

        Examples
        ========

        >>> from sympy.logic.algorithms.dpll2 import SATSolver
        >>> l = SATSolver([{2, -3}, {1}, {3, -3}, {2, -2},
        ... {3, -2}], {1, 2, 3}, set())

        >>> l.lit_heap
        [(-2.0, -3), (-2.0, 2), (-2.0, -2), (0.0, 1), (-2.0, 3), (0.0, -1)]

        >>> l._vsids_calculate()
        -3

        >>> l.lit_heap
        [(-2.0, -2), (-2.0, 2), (0.0, -1), (0.0, 1), (-2.0, 3)]

        """
        if len(self.lit_heap) == 0:
            return 0

        # Clean out the front of the heap as long the variables are set
        while self.variable_set[abs(self.lit_heap[0][1])]:
            heappop(self.lit_heap)
            if len(self.lit_heap) == 0:
                return 0

        return heappop(self.lit_heap)[1]

    def _vsids_lit_assigned(self, lit):
        """Handle the assignment of a literal for the VSIDS heuristic."""
        pass

    def _vsids_lit_unset(self, lit):
        """Handle the unsetting of a literal for the VSIDS heuristic.

        Examples
        ========

        >>> from sympy.logic.algorithms.dpll2 import SATSolver
        >>> l = SATSolver([{2, -3}, {1}, {3, -3}, {2, -2},
        ... {3, -2}], {1, 2, 3}, set())
        >>> l.lit_heap
        [(-2.0, -3), (-2.0, 2), (-2.0, -2), (0.0, 1), (-2.0, 3), (0.0, -1)]

        >>> l._vsids_lit_unset(2)

        >>> l.lit_heap
        [(-2.0, -3), (-2.0, -2), (-2.0, -2), (-2.0, 2), (-2.0, 3), (0.0, -1),
        ...(-2.0, 2), (0.0, 1)]

        """
        var = abs(lit)
        heappush(self.lit_heap, (self.lit_scores[var], var))
        heappush(self.lit_heap, (self.lit_scores[-var], -var))

    def _vsids_clause_added(self, cls):
        """Handle the addition of a new clause for the VSIDS heuristic.

        Examples
        ========

        >>> from sympy.logic.algorithms.dpll2 import SATSolver
        >>> l = SATSolver([{2, -3}, {1}, {3, -3}, {2, -2},
        ... {3, -2}], {1, 2, 3}, set())

        >>> l.num_learned_clauses
        0
        >>> l.lit_scores
        {-3: -2.0, -2: -2.0, -1: 0.0, 1: 0.0, 2: -2.0, 3: -2.0}

        >>> l._vsids_clause_added({2, -3})

        >>> l.num_learned_clauses
        1
        >>> l.lit_scores
        {-3: -1.0, -2: -2.0, -1: 0.0, 1: 0.0, 2: -1.0, 3: -2.0}

        """
        self.num_learned_clauses += 1
        for lit in cls:
            self.lit_scores[lit] += 1

    ########################
    #   Clause Learning    #
    ########################
    def _simple_add_learned_clause(self, cls):
        """Add a new clause to the theory.

        Examples
        ========

        >>> from sympy.logic.algorithms.dpll2 import SATSolver
        >>> l = SATSolver([{2, -3}, {1}, {3, -3}, {2, -2},
        ... {3, -2}], {1, 2, 3}, set())

        >>> l.num_learned_clauses
        0
        >>> l.clauses
        [[2, -3], [1], [3, -3], [2, -2], [3, -2]]
        >>> l.sentinels
        {-3: {0, 2}, -2: {3, 4}, 2: {0, 3}, 3: {2, 4}}

        >>> l._simple_add_learned_clause([3])

        >>> l.clauses
        [[2, -3], [1], [3, -3], [2, -2], [3, -2], [3]]
        >>> l.sentinels
        {-3: {0, 2}, -2: {3, 4}, 2: {0, 3}, 3: {2, 4, 5}}

        """
        self._trace(f"Learned clause: {[self._format_lit(lit) for lit in cls]}")
        cls_num = len(self.clauses)
        self.clauses.append(cls)

        for lit in cls:
            self.occurrence_count[lit] += 1

        self.sentinels[cls[0]].add(cls_num)
        self.sentinels[cls[-1]].add(cls_num)

        self.heur_clause_added(cls)

    def _simple_compute_conflict(self):
        """ Build a clause representing the fact that at least one decision made
        so far is wrong.

        Examples
        ========

        >>> from sympy.logic.algorithms.dpll2 import SATSolver
        >>> l = SATSolver([{2, -3}, {1}, {3, -3}, {2, -2},
        ... {3, -2}], {1, 2, 3}, set())
        >>> next(l._find_model())
        {1: True, 2: False, 3: False}
        >>> l._simple_compute_conflict()
        [3]

        """
        return [-(level.decision) for level in self.levels[1:]]

    def _simple_clean_clauses(self):
        """Clean up learned clauses."""
        pass


class Level:
    """
    Represents a single level in the DPLL algorithm, and contains
    enough information for a sound backtracking procedure.
    """

    def __init__(self, decision, flipped=False):
        self.decision = decision
        self.var_settings = set()
        self.flipped = flipped
