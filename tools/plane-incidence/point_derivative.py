"""Replay reverse point flags and compare them with forward accepting parses."""

import argparse
from itertools import combinations
from random import Random

import honest_cofactors as honest
import line_derivative
import pair_witnesses as witnesses
import square_projection_circuit as square


def forward_once(circuit, edge_raw, n):
    # Two independent predicates: some parse with zero or at most one point.
    allowed = [(0 if i<n else v,v) for i,v in enumerate(edge_raw)]
    for op,a,b in circuit.gates:
        l0,l1 = allowed[a]
        r0,r1 = allowed[b]
        if op == "or":
            allowed.append((l0|r0,l1|r1))
        else:
            allowed.append((l0&r0,(l0&r1)|(l1&r0)))
    return allowed[circuit.output]


def negatives(circuit, masks, q):
    n = len(masks)
    rng = Random(121+q)
    tested = 0
    for p in range(n):
        off = [w for w,line in enumerate(masks) if not (line >> p) & 1]
        if q<=4:
            groups = (g for r in range(q+1) for g in combinations(off,r))
        else:
            groups = [()] + [(w,) for w in off] + [rng.sample(off,r)
                      for r in range(2,q+1) for _ in range(3)]
        raw = [0]*n
        count = 0
        for group in groups:
            for w in group:
                raw[w] |= 1<<count
            count += 1
        flags = line_derivative.adjoints(circuit,[0]*n+raw,(1<<count)-1)
        assert flags[p]==0
        tested += count
    return tested


def check(name,circuit,masks,q,with_neg=True):
    n = len(masks)
    flags = line_derivative.adjoints(circuit,[0]*n+[1<<w for w in range(n)],(1<<n)-1)[:n]
    raw,edges = witnesses.signatures(masks)
    zero,forward = forward_once(circuit,raw,n)
    assert zero==0
    packed = cursor = 0
    for w,line in enumerate(masks):
        for p in range(n):
            if (line >> p) & 1:
                packed |= ((flags[p] >> w) & 1) << cursor
                cursor += 1
            else:
                assert not (flags[p] >> w) & 1
    assert cursor==edges and packed==forward
    line = witnesses.bounded(circuit,raw,True)[1]
    def size(value):
        return bin(value).count("1")
    assert size(packed)<=5*len(circuit.gates)+n
    assert size(packed)+size(line)<=8*len(circuit.gates)+2*n
    tested = negatives(circuit,masks,q) if with_neg else 0
    print(f"{name} gates={len(circuit.gates)} edges={edges} point-once={size(packed)} "
          f"line-once={size(line)} either={size(packed|line)} outside tests={tested}",flush=True)


def repeat_lines(lib,masks):
    n = len(masks)
    c = lib.Circuit(2*n)
    stars = []
    for w,row in enumerate(masks):
        y = c.gate("and",n+w,n+w)
        x = c.fold("or",[p for p in range(n) if row >> p & 1])
        stars.append(c.gate("and",x,y))
    c.output = c.fold("or",stars)
    return c


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("orders",nargs="*",type=int,default=[2,3,4,8])
    args = parser.parse_args()
    if not __debug__:
        raise SystemExit("Run without -O so the replay assertions stay active.")
    lib = square.circuit_library()
    for q in args.orders:
        if q!=3 and (q<2 or q & (q-1)):
            raise SystemExit("Use order 3 or a power of 2.")
        masks = honest.prime_masks(3) if q==3 else lib.line_point_masks(q.bit_length()-1)
        direct = witnesses.direct(lib,masks)
        check(f"direct-q{q}",direct,masks,q)
        check(f"repeated-lines-q{q}",repeat_lines(lib,masks),masks,q)
        direct.output = direct.gate("and",direct.output,direct.output)
        check(f"repeated-output-q{q}",direct,masks,q)
        if q>=4 and q!=3:
            prefix,_ = lib.one_line_circuit(q.bit_length()-1)
            check(f"completed-dyadic-q{q}",lib.complete_sparse_prefix(prefix,masks),masks,q)
