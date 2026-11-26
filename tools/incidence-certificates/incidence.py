"""Exact output probes for monotone circuits computing bipartite edge incidence."""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass, field
from pathlib import Path


def mask(indices):
    result = 0
    for index in indices:
        result |= 1 << index
    return result


def indices(bits):
    while bits:
        bit = bits & -bits
        yield bit.bit_length() - 1
        bits ^= bit


@dataclass
class Graph:
    columns: int
    row_masks: list
    markers: dict = field(default_factory=dict)
    max_gates: int | None = None
    first_gate: list | None = None

    @property
    def inputs(self):
        return len(self.row_masks) + self.columns

    def __post_init__(self):
        if type(self.columns) is not int or self.columns < 0:
            raise ValueError("columns must be a nonnegative integer")
        if not isinstance(self.row_masks, list) or any(
            type(bits) is not int or bits < 0 or bits.bit_length() > self.columns
            for bits in self.row_masks
        ):
            raise ValueError("each row mask must fit the declared column count")
        if not isinstance(self.markers, dict) or "output" in self.markers:
            raise ValueError("markers must map auxiliary wire names to input indices")
        for name, chosen in self.markers.items():
            bad_name = not isinstance(name, str) or not name or name in ("inputs", "gates")
            if bad_name or not isinstance(chosen, list) or any(
                    type(i) is not int or not 0 <= i < self.inputs for i in chosen):
                raise ValueError(f"invalid markers for {name!r}")
        if self.max_gates is not None and (type(self.max_gates) is not int or self.max_gates < 0):
            raise ValueError("max_gates must be a nonnegative integer")
        if self.first_gate is not None:
            parse_gate(self.first_gate)

    def maximal_independent_inputs(self, deleted=0):
        """Enumerate maximal independent sets in the induced graph, using original bit positions."""
        rows = len(self.row_masks)
        active_rows = ((1 << rows) - 1) & ~deleted
        active_cols = ((1 << self.columns) - 1) & ~(deleted >> rows)
        # A maximal row support determines its column complement through its union of neighbors.
        # Equal unions give the same closed set. Keep just the distinct unions at each stage.
        unions = {0}
        for i in indices(active_rows):
            neighbors = self.row_masks[i] & active_cols
            unions.update({old | neighbors for old in unions})
        for blocked in sorted(unions):
            cols = active_cols ^ blocked
            left = mask(i for i in indices(active_rows) if not (self.row_masks[i] & cols))
            yield left | (cols << rows)

    def probes(self):
        """Return input masks mapped to the expected values of the wires constrained there."""
        rows = len(self.row_masks)
        probes = {}

        def expect(x, name, value):
            wires = probes.setdefault(x, {})
            if name in wires and wires[name] != value:
                raise RuntimeError("conflicting expectations")
            wires[name] = value

        for i, neighbors in enumerate(self.row_masks):
            for j in indices(neighbors):
                expect((1 << i) | (1 << (rows + j)), "output", True)
        for x in self.maximal_independent_inputs():
            expect(x, "output", False)
        for name, markers in self.markers.items():
            marked = mask(markers)
            for i in indices(marked):
                expect(1 << i, name, True)
            for x in self.maximal_independent_inputs(marked):
                expect(x, name, False)
        return probes


def projective_plane(order, punctured=False):
    if order == 2:
        modulus, differences = 7, {0, 1, 3}
    elif order == 3:
        modulus, differences = 13, {0, 1, 3, 9}
    else:
        raise ValueError("the presets cover orders two and three")
    if punctured and order != 3:
        raise ValueError("the punctured preset uses the order-three labeling")
    rows = [r for r in range(modulus) if not (punctured and r == 9)]
    cols = [c for c in range(modulus) if not (punctured and c == 0)]
    row_masks = [mask(j for j, c in enumerate(cols) if (r + c) % modulus in differences) for r in rows]
    if punctured:
        return Graph(len(cols), row_masks, {"a": [0, 1, 3], "b": [15, 16, 18]}, 58, ["or", 0, 1])
    return Graph(len(cols), row_masks, {})


def parse_gate(gate):
    if not isinstance(gate, list) or not 1 <= len(gate) <= 3:
        raise ValueError(f"expected an operation followed by zero, one or two inputs, got {gate!r}")
    op, *sources = gate
    if op not in ("and", "or") or not all(type(i) is int and i >= 0 for i in sources):
        raise ValueError(f"invalid monotone gate: {gate!r}")
    return op, sources


def check_circuit(graph, candidate, probes):
    if type(candidate["inputs"]) is not int or candidate["inputs"] != graph.inputs:
        raise ValueError(f"expected {graph.inputs} inputs")
    gates = candidate["gates"]
    if not isinstance(gates, list):
        raise ValueError("gates must be a list")
    outputs = {name: candidate[name] for name in ["output", *graph.markers]}
    if any(type(i) is not int or not 0 <= i < graph.inputs + len(gates) for i in outputs.values()):
        raise ValueError("output index outside the final wire list")
    tests = sorted(probes.items())
    values = [mask(t for t, (x, _) in enumerate(tests) if (x >> i) & 1) for i in range(graph.inputs)]
    ones = (1 << len(tests)) - 1
    for gate in gates:
        op, sources = parse_gate(gate)
        value = ones if op == "and" else 0
        # Circuit.wires uses getD false for forward and out-of-range input reads.
        for i in sources:
            source = values[i] if i < len(values) else 0
            value = value & source if op == "and" else value | source
        values.append(value)
    failures = 0
    first = None
    for t, (x, expected) in enumerate(tests):
        for wire, wanted in expected.items():
            actual = bool((values[outputs[wire]] >> t) & 1)
            if actual != wanted:
                failures += 1
                if first is None:
                    first = {"input": x, "wire": wire, "expected": wanted, "actual": actual}
    size_ok = graph.max_gates is None or len(gates) <= graph.max_gates
    prefix_ok = graph.first_gate is None or gates[:1] == [graph.first_gate]
    return {"gates": len(gates), "size_ok": size_ok, "first_gate_ok": prefix_ok,
            "failed_wire_checks": failures, "first_failure": first,
            "accepted": failures == 0 and size_ok and prefix_ok}


def summary(graph, probes):
    counts = {name: {"positive": 0, "negative": 0} for name in ["output", *graph.markers]}
    for expected in probes.values():
        for name, wanted in expected.items():
            counts[name]["positive" if wanted else "negative"] += 1
    return {"input_bits": graph.inputs, "distinct_probes": len(probes),
            "wire_checks": sum(len(w) for w in probes.values()), "per_wire": counts}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("graph", help="pg3, fano, punctured, or a graph JSON path")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--vectors", action="store_true", help="emit expected wire values as JSON lines")
    mode.add_argument("--circuit", type=Path, help="check a candidate circuit JSON file")
    args = parser.parse_args()
    try:
        if args.graph in ("pg3", "fano", "punctured"):
            graph = projective_plane(2 if args.graph == "fano" else 3, args.graph == "punctured")
        else:
            graph = Graph(**json.loads(Path(args.graph).read_text()))
        probes = graph.probes()
        if args.vectors:
            for x, expected in sorted(probes.items()):
                print(json.dumps({"input": x, "expected": expected}, sort_keys=True))
            return 0
        result = summary(graph, probes)
        if args.circuit:
            result.update(check_circuit(graph, json.loads(args.circuit.read_text()), probes))
        print(json.dumps(result, indent=2))
        return 0 if result.get("accepted", True) else 1
    except (OSError, ValueError, KeyError, TypeError) as exc:
        parser.exit(2, f"invalid input: {exc}\n")


if __name__ == "__main__":
    raise SystemExit(main())
