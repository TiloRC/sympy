FORCE_TRACE = True
_ACTIVE_TRACE = None

def get_active_trace():
    return _ACTIVE_TRACE

class TraceGraph:
    """
    Encapsulates the state and logic for generating a Graphviz visualization
    of the SAT solver's search process.
    """

    def __init__(self, trace_clauses=True):
        self.solver = None
        self.trace_clauses = trace_clauses
        self.nodes = []
        self.edges = []
        self.node_count = 0
        self.parent_stack = [("node_root", 0)]  # (node_id, level)
        self.pending_trace = None

    def start_trace(self):
        global _ACTIVE_TRACE
        _ACTIVE_TRACE = self

    def attach_solver(self, solver):
        self.solver = solver
        start_label = "START"
        if self.trace_clauses:
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

            if self.trace_clauses:
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
        if self.solver is None:
            return

        if level is None:
            level = len(self.solver.levels) - 1

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
                'consequences': {},  # Grouped by trigger literal
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

    def end_trace(self):
        global _ACTIVE_TRACE
        _ACTIVE_TRACE = None
        return self.to_dot()

    def __len__(self):
        return len(self.nodes)
