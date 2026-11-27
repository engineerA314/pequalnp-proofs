"""Exact cofactor functions and structural gate charges on complete truth tables."""

import argparse
from itertools import combinations

import pair_witnesses as witnesses
import square_projection_circuit as square


def prime_masks(q):
    rows = []
    for a in range(q):
        for b in range(q):
            rows.append(sum(1 << (x*q + (a*x+b) % q) for x in range(q)) | (1 << (q*q+a)))
    rows += [sum(1 << (x*q+v) for v in range(q)) | (1 << (q*q+q)) for x in range(q)]
    rows.append(sum(1 << p for p in range(q*q,q*q+q+1)))
    return rows


def outside_tables(n, row, q):
    outside = [w for w in range(n) if not (row >> w) & 1]
    union = 1  # truth-table position zero
    tables = [union]
    for r in range(1,q+1):
        for group in combinations(outside,r):
            assignment = sum(1 << w for w in group)
            union |= 1 << assignment
        tables.append(union)
    return tables


def check(circuit, masks, q, name):
    n = len(masks)
    full = (1 << (1 << n))-1
    # Each bit position of a truth table is an entire line assignment.
    line_functions = [(full // ((1 << (1 << w))+1)) << (1 << w) for w in range(n)]
    totals = {(b,r):0 for b in range(1,q+1) for r in range(1,q+1)}
    shared = [0]*len(circuit.gates)
    for p in range(n):
        pencil = sum(1 << w for w,line in enumerate(masks) if (line >> p) & 1)
        assert bin(pencil).count("1") == q+1
        outside = outside_tables(n,pencil,q)
        points = [full if v==p else 0 for v in range(n)]
        values = circuit.wires(points+line_functions)
        assert not (values[circuit.output] & outside[q])
        assert all((values[circuit.output] >> (1 << w)) & 1 for w in range(n) if (pencil >> w)&1)
        seen = set(values[:2*n]) | {0,full}
        counts = dict.fromkeys(totals,0)
        for g,f in enumerate(values[2*n:]):
            if f in seen:
                continue
            seen.add(f)
            singles = sum(1 << w for w in range(n) if (f >> (1 << w)) & 1)
            degree = bin(singles).count("1")
            if degree < 2 or (singles & ~pencil) or f & 1:
                continue
            shared[g] += 1
            for r in range(1,q+1):
                if f & outside[r]:
                    break
                for b in range(1,min(degree,q+1)):
                    counts[b,r] += 1
        for (b,r),count in counts.items():
            assert count >= min(q//b,q//r), (name,p,b,r,count)
            totals[b,r] += count
    assert sum(shared) == totals[1,1]
    mass = sum(totals[b,1] for b in range(1,q+1))
    harmonic = n*sum(q//b for b in range(1,q+1))
    assert mass >= harmonic
    print(f"{name} q={q} gates={len(circuit.gates)} honest gate-point pairs={totals[1,1]} "
          f"required={n*q} maximum points on one gate={max(shared)} "
          f"incidence degree mass={mass} required mass={harmonic}",flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("orders",nargs="*",type=int,default=[2,3])
    args = parser.parse_args()
    if not __debug__:
        raise SystemExit("Run without -O so all assertions stay active.")
    library = square.circuit_library()
    for q in args.orders:
        if q not in (2,3,4):
            raise SystemExit("Full truth tables in this replay support q=2,3,4.")
        masks = prime_masks(3) if q==3 else library.line_point_masks(q.bit_length()-1)
        circuit = witnesses.direct(library,masks)
        check(circuit,masks,q,"direct")
        circuit.output = circuit.gate("and",circuit.output,circuit.output)
        check(circuit,masks,q,"repeated output")
        if q==4:
            prefix,_ = library.one_line_circuit(2)
            check(library.complete_sparse_prefix(prefix,masks),masks,q,"completed selector")
