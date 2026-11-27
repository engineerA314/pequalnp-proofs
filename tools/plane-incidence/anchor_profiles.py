"""Replay the fixed and averaged gate budgets with exact integer arithmetic."""

from collections import Counter
from itertools import combinations
from math import comb
import random

import pair_witnesses as witnesses
import square_projection_circuit as square


def singleton_profiles(circuit, n):
    values = circuit.wires([0]*n + [1 << w for w in range(n)])
    return [values[i] | values[j] for op, i, j in circuit.gates if op == "and"]


def level(n, q, r):
    return (sum(comb(n-r, j) for j in range(q-r+1))-1).bit_length()


def report(name, circuit, n, q):
    profiles = singleton_profiles(circuit, n)
    sizes = Counter(bin(mask).count("1") for mask in profiles)
    rng = random.Random(q)
    for r in sorted({0, q//2, q-1}):
        required = level(n, q, r)
        anchors = comb(n, r)
        weight = sum(number*comb(n-size, r) for size, number in sizes.items())
        assert weight >= anchors*required
        if anchors <= 20000:
            checked = list(combinations(range(n), r))
        else:
            checked = [rng.sample(range(n), r) for _ in range(120)]
        total = 0
        for labels in checked:
            mask = sum(1 << u for u in labels)
            count = sum(not D & mask for D in profiles)
            assert count >= required
            total += count
        if len(checked) == anchors:
            assert total == weight
        # A gate whose footprint has this many labels or more survives
        # with probability at most required / (2 * number of AND gates).
        cut = next((d for d in range(n+1)
                    if 2*len(profiles)*comb(n-d, r) <= required*anchors), None)
        if cut is not None:
            assert 2*sum(k for d,k in sizes.items() if d < cut) >= required
        print(f"{name} q={q} r={r} binary ANDs={len(profiles)} required={required} "
              f"floor of mean surviving={weight//anchors} cutoff={cut} checked={len(checked)}")


def main():
    if not __debug__:
        raise SystemExit("Run without -O to keep all checks active.")
    lib = square.circuit_library()
    for k in (1,2,3,4):
        q = 2**k
        masks = lib.line_point_masks(k)
        report("direct", witnesses.direct(lib,masks), len(masks), q)
        if k >= 2:
            prefix,_ = lib.one_line_circuit(k)
            report("completed dyadic", lib.complete_sparse_prefix(prefix,masks), len(masks), q)


if __name__ == "__main__":
    main()
