"""Emit SAT instances for full-netlist checks of the square projection circuit.

The negative query allows every point assignment and every assignment with at
most the specified number of lines. The positive query asks for an incident
pair missed by the output, with all other bits completely unrestricted.
"""

import argparse
from pathlib import Path

import square_projection_circuit as square


class CNF:
    def __init__(self, variables):
        self.variables = variables
        self.clauses = []

    def fresh(self):
        self.variables += 1
        return self.variables

    def gate(self, op, a, b, output):
        if op == "and":
            self.clauses.extend([[-output, a], [-output, b], [output, -a, -b]])
        else:
            assert op == "or"
            self.clauses.extend([[output, -a], [output, -b], [-output, a, b]])

    def at_most(self, inputs, bound):
        if bound == 0:
            self.clauses.extend([[-x] for x in inputs])
            return
        previous = []
        for x in inputs:
            current = [self.fresh() for _ in range(min(len(previous)+1, bound))]
            self.clauses.append([-x, current[0]])
            for j, old in enumerate(previous):
                self.clauses.append([-old, current[j]])
                if j+1 < bound:
                    self.clauses.append([-x, -old, current[j+1]])
                else:
                    self.clauses.append([-x, -old])
            previous = current

    def write(self, path):
        with path.open("w") as out:
            print("p cnf", self.variables, len(self.clauses), file=out)
            for clause in self.clauses:
                print(*clause, 0, file=out)


def output_terms(circuit):
    """The output is exactly the union of the returned wires."""
    pending = [circuit.output]
    terms = set()
    seen = set()
    while pending:
        wire = pending.pop()
        if wire in seen:
            continue
        seen.add(wire)
        if wire >= circuit.inputs and circuit.gates[wire-circuit.inputs][0] == "or":
            pending.extend(circuit.gates[wire-circuit.inputs][1:])
        else:
            terms.add(wire)
    return sorted(terms)


def line_order(field, t, circuit, term, n):
    order = list(range(n))
    op, a, _ = circuit.gates[term-circuit.inputs]
    if op != "and" or a >= field.q**2:
        return order
    # Only the order of inputs to the cardinality counter changes. Grouping
    # lines by a direction of agreement helps unit propagation in affine cases.
    x, z = divmod(a, field.q)
    directions = square.selected_directions(field.s, t)
    def key(w):
        if w >= field.q**2:
            return len(directions)+1
        slope, intercept = divmod(w, field.q)
        y = field.ordinate(slope, x, intercept)
        return next((j for j,d in enumerate(directions)
                     if field.project(d, y) == field.project(d, z)), len(directions))
    return sorted(order, key=key)


class ProjectionQueries:
    def __init__(self, base, t):
        library = square.circuit_library()
        self.field = square.SquareField(base, library)
        self.circuit = square.build(self.field, t, library)
        self.t = t
        self.masks = self.field.line_masks()
        self.n = len(self.masks)
        self.terms = output_terms(self.circuit)
        c = self.circuit
        gates = CNF(c.inputs+len(c.gates))
        for j, (op, a, b) in enumerate(c.gates):
            gates.gate(op, a+1, b+1, c.inputs+j+1)
        self.positive = CNF(gates.variables)
        self.negative = CNF(gates.variables)
        self.positive.clauses = gates.clauses.copy()
        self.negative.clauses = gates.clauses
        positive_terms = []
        for w, mask in enumerate(self.masks):
            line = self.n+w+1
            while mask:
                bit = mask & -mask
                point = bit.bit_length()
                mask ^= bit
                self.negative.clauses.append([-point, -line])
                term = self.positive.fresh()
                self.positive.gate("and", point, line, term)
                positive_terms.append(term)
        self.positive.clauses.extend([positive_terms, [-(c.output+1)]])

    def query(self, mode, budget, branch=None):
        if mode == "positive":
            if branch is not None:
                raise ValueError("branch selection applies only to the negative query")
            return self.positive
        if mode != "negative":
            raise ValueError("unknown miter")
        cnf = CNF(self.negative.variables)
        cnf.clauses = self.negative.clauses.copy()
        order = range(self.n)
        if branch is not None:
            if not 0 <= branch < len(self.terms):
                raise ValueError("branch index outside the output OR decomposition")
            term = self.terms[branch]
            order = line_order(self.field, self.t, self.circuit, term, self.n)
            assert sorted(order) == list(range(self.n))
            cnf.clauses.append([term+1])
        cnf.at_most([self.n+1+w for w in order], budget)
        cnf.clauses.append([self.circuit.output+1])
        return cnf


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("base", type=int)
    parser.add_argument("directions_minus_one", type=int)
    parser.add_argument("mode", choices=("positive", "negative"))
    parser.add_argument("destination", type=Path)
    parser.add_argument("--budget", type=int)
    parser.add_argument("--branch", type=int)
    args = parser.parse_args()
    budget = args.directions_minus_one if args.budget is None else args.budget
    if budget < 0:
        parser.error("the line budget must be nonnegative")
    cnf = ProjectionQueries(args.base, args.directions_minus_one).query(args.mode, budget, args.branch)
    cnf.write(args.destination)
    print(f"{cnf.variables} variables, {len(cnf.clauses)} clauses")


if __name__ == "__main__":
    main()
