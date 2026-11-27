"""Count leaking maximal inputs of the published prefix and its AND lower bounds."""

import importlib.util
from itertools import combinations
from math import comb
from pathlib import Path


def load_prefix():
    source = Path(__file__).resolve().parents[1] / "shared-low-merges" / "sparse_line_circuit.py"
    spec = importlib.util.spec_from_file_location("shared_low_merges", source)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def leaking_rows(circuit, lines, q):
    n = len(lines)
    # In the coordinate numbering of the prefix, (1,1) misses z=0 and z=x+1.
    point = q + 1
    witness = {0, q + 1}
    leaked = forced = tested = 0
    for count in range(q + 1):
        for selected in combinations(range(n), count):
            tested += 1
            union = 0
            line_inputs = [0] * n
            for w in selected:
                union |= lines[w]
                line_inputs[w] = 1
            point_inputs = [int((union & (1 << p)) == 0) for p in range(n)]
            answer = circuit.evaluate(point_inputs + line_inputs)
            leaked += answer
            if witness.issubset(selected) and point_inputs[point]:
                assert answer == 1
                forced += 1
    assert tested == sum(comb(n, j) for j in range(q + 1))
    assert forced == sum(comb(q*q - 2, j) for j in range(q - 1))
    return tested, leaked, forced


def main():
    if not __debug__:
        raise SystemExit("Run Python without -O so the assertions are active.")
    source = load_prefix()
    for k in (1, 2):
        q = 1 << k
        prefix, _ = source.one_line_circuit(k)
        lines = source.line_point_masks(k)
        total, leaked, forced = leaking_rows(prefix, lines, q)
        print(f"q={q} sparse line sets={total} leaking rows={leaked} "
              f"witness extensions={forced} downstream AND lower bound={(max(1, leaked)-1).bit_length()}")
    for q in (4, 8, 16, 32):
        n = q*q + q + 1
        forced = sum(comb(q*q - 2, j) for j in range(q - 1))
        total = sum(comb(n, j) for j in range(q + 1))
        print(f"q={q} forced clauses={forced} forced downstream ANDs={(forced-1).bit_length()} "
              f"whole-circuit AND lower bound={(total-1).bit_length()}")


if __name__ == "__main__":
    main()
