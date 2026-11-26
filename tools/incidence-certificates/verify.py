"""Independent finite checks for the certificate generator and the 60-gate control."""

import json
from copy import deepcopy
from pathlib import Path

from incidence import Graph, check_circuit, mask, projective_plane, summary


def brute_negatives(independent, banned, bits):
    allowed = {x for x in independent if not x & banned}
    return {x for x in allowed if all(x | (1 << i) not in allowed
                                     for i in range(bits) if not x & (1 << i))}


def check_small(rows, columns):
    bits = rows + columns
    for graph_bits in range(1 << (rows * columns)):
        edges = [(i, j) for i in range(rows) for j in range(columns)
                 if graph_bits & (1 << (i * columns + j))]
        graph = Graph(columns, [sum(1 << j for r, j in edges if r == i) for i in range(rows)])
        independent = {x for x in range(1 << bits)
                       if all(not (x & (1 << i) and x & (1 << (rows + j))) for i, j in edges)}
        edge_masks = {(1 << i) | (1 << (rows + j)) for i, j in edges}
        expected_main = {x: True for x in edge_masks}
        expected_main.update({x: False for x in brute_negatives(independent, 0, bits)})
        for banned in range(1 << bits):
            graph.markers = {"aux": [i for i in range(bits) if banned & (1 << i)]}
            probes = graph.probes()
            actual_main = {x: w["output"] for x, w in probes.items() if "output" in w}
            assert actual_main == expected_main, (rows, columns, graph_bits, banned)
            expected_aux = {1 << i: True for i in range(bits) if banned & (1 << i)}
            expected_aux.update({x: False for x in brute_negatives(independent, banned, bits)})
            actual_aux = {x: w["aux"] for x, w in probes.items() if "aux" in w}
            assert actual_aux == expected_aux, (rows, columns, graph_bits, banned)
    return (1 << (rows * columns)) * (1 << bits)


def plane_edges():
    # Direct transcription of the full-plane labels enumerated in increasing order.
    return {(i, j) for i, r in enumerate([*range(9), 10, 11, 12])
            for j, c in enumerate(range(1, 13)) if (r + c) % 13 in (0, 1, 3, 9)}


def projected_certificate(graph, edges, probes):
    # The previous rule first found maximal negatives in the whole graph, then cleared markers.
    row_neighbors = [{j for r, j in edges if r == i} for i in range(12)]
    rectangles = set()
    for selected in range(4096):
        rows = {i for i in range(12) if selected & (1 << i)}
        cols = {j for j in range(12) if all(j not in row_neighbors[i] for i in rows)}
        if all(row_neighbors[i] & cols for i in range(12) if i not in rows):
            rectangles.add(selected | (mask(cols) << 12))
    assert len(rectangles) == 420
    assert {x for x, wires in probes.items() if wires.get("output") is False} == rectangles
    old_inputs = rectangles | {(1 << i) | (1 << (12+j)) for i, j in edges}
    old_wire_checks = len(old_inputs)
    for name, chosen in graph.markers.items():
        cleared = {x & ~mask(chosen) for x in rectangles}
        maximal = {x for x in cleared if all(x == y or x & y != x for y in cleared)}
        assert maximal == {x for x, wires in probes.items() if wires.get(name) is False}
        assert (len(cleared), len(maximal)) == (420, 197)
        old_inputs.update(cleared)
        old_inputs.update(1 << i for i in chosen)
        old_wire_checks += len(cleared) + len(chosen)
    assert (len(old_inputs), old_wire_checks) == (1183, 1311)


def full_table(reference, edges):
    """Check every row/column support against the defining equation, independently of probes."""
    all_cols = (1 << 4096) - 1
    col_values = [sum(1 << y for y in range(4096) if y & (1 << j)) for j in range(12)]
    hits_by_row = [0] * 12
    for i, j in edges:
        hits_by_row[i] |= col_values[j]
    want_b = col_values[3] | col_values[4] | col_values[6]
    for rows in range(4096):
        want_main = 0
        for i, hit in enumerate(hits_by_row):
            if rows & (1 << i):
                want_main |= hit
        independent = all_cols ^ want_main
        want_a = all_cols if rows & 0b1011 else 0
        values = [all_cols if rows & (1 << i) else 0 for i in range(12)] + col_values
        for op, a, b in reference["gates"]:
            assert max(a, b) < len(values) and op in ("and", "or")
            values.append((values[a] & values[b]) if op == "and" else (values[a] | values[b]))
        assert values[reference["output"]] == want_main, rows
        assert (values[reference["a"]] ^ want_a) & independent == 0, rows
        assert (values[reference["b"]] ^ want_b) & independent == 0, rows


def verify_reference_shape(reference, edges):
    """Parse the main output back into separate star trees and count the remaining gates."""
    gates = reference["gates"]
    seen = set()
    stars = []

    def take(wire):
        assert 24 <= wire < 24 + len(gates) and wire not in seen
        seen.add(wire)
        return gates[wire - 24]

    def leaves(wire):
        if wire < 24:
            return [wire]
        op, a, b = take(wire)
        assert op == "or"
        return leaves(a) + leaves(b)

    def decode(wire):
        op, a, b = take(wire)
        if op == "or":
            decode(a)
            decode(b)
        else:
            assert op == "and" and a < 12
            columns = leaves(b)
            assert all(12 <= v < 24 for v in columns) and len(columns) == len(set(columns))
            stars.append({(a, v - 12) for v in columns})

    decode(reference["output"])
    assert set.union(*stars) == edges and sum(map(len, stars)) == len(edges)
    assert (len(stars), len(seen), len(gates) - len(seen)) == (12, 56, 4)
    assert reference["a"] not in seen and reference["b"] not in seen


def check_controls(graph, probes, reference):
    result = check_circuit(graph, reference, probes)
    assert result == {"gates": 60, "size_ok": False, "first_gate_ok": True,
                      "failed_wire_checks": 0, "first_failure": None, "accepted": False}
    for wire in ("output", "a", "b"):
        bad = dict(reference, **{wire: 0})
        result = check_circuit(graph, bad, probes)
        assert result["failed_wire_checks"] > 0 and result["first_failure"]["wire"] == wire
    bad = deepcopy(reference)
    bad["gates"][0] = ["or", 1, 0]
    result = check_circuit(graph, bad, probes)
    assert not result["first_gate_ok"] and result["failed_wire_checks"] == 0
    one_edge = Graph(1, [1], {"tag": [0]})
    small = {"inputs": 2, "gates": [["or", 0, 999], ["and", 1, 2]], "output": 3, "tag": 2}
    assert check_circuit(one_edge, small, one_edge.probes())["accepted"]
    constants = {"inputs": 2, "gates": [["and"], ["or"], ["or", 0, 3], ["and", 1],
                                         ["and", 4, 5], ["and", 6, 2]], "output": 7, "tag": 4}
    assert check_circuit(one_edge, constants, one_edge.probes())["accepted"]
    assert check_circuit(one_edge, dict(constants, output=2), one_edge.probes())["failed_wire_checks"] > 0
    assert check_circuit(one_edge, dict(constants, tag=3), one_edge.probes())["failed_wire_checks"] > 0
    for bad_gate in (["not", 0, 0], ["or", True, 1], ["and", 0, -1], ["and", 0, 0, 1], []):
        try:
            check_circuit(one_edge, dict(small, gates=[bad_gate, ["and", 1, 2]]), one_edge.probes())
        except ValueError:
            continue
        raise AssertionError(bad_gate)


def main():
    for order, expected in ((2, (21, 37)), (3, (52, 704))):
        graph = projective_plane(order)
        assert summary(graph, graph.probes())["per_wire"]["output"] == dict(zip(("positive", "negative"), expected))
    configs = check_small(3, 3)
    assert configs == 32768
    boundaries = sum(check_small(m, n) for m, n in [(0, 0), (0, 3), (3, 0), (2, 3), (3, 2)])
    print(f"Direct subset enumeration agrees on {configs:,} labeled 3-by-3 graph/marker pairs "
          f"and {boundaries:,} rectangular or empty-side pairs.")

    graph = projective_plane(3, punctured=True)
    edges = plane_edges()
    assert len(edges) == 45
    probes = graph.probes()
    projected_certificate(graph, edges, probes)
    result = summary(graph, probes)
    assert (result["distinct_probes"], result["wire_checks"]) == (737, 865)
    print("Projected vs. induced-graph tests: 1,183 vs. 737 input masks, 1,311 vs. 865 wire checks.")

    reference = json.loads(Path(__file__).with_name("plane-reference-60.json").read_text())
    check_controls(graph, probes, reference)
    verify_reference_shape(reference, edges)
    full_table(reference, edges)
    print("60-gate control: 12 stars, 56 main-formula gates, four auxiliary gates. "
          "All 16,777,216 inputs satisfy the output specification. The 58-gate cap rejects it.")
    print("Bad output selections, an altered prefix and malformed gates were detected. "
          "Constants, copies and a forward read agree with the desk's gate semantics.")


if __name__ == "__main__":
    main()
