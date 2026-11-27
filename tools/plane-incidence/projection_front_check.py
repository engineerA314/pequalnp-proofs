"""Verify gate counts, all projected singleton rows and their intersections."""

import argparse
from itertools import combinations

import square_projection_circuit as square


def check(s):
    lib = square.circuit_library()
    field = square.SquareField(s, lib)
    q = field.q
    n = q*q + q + 1
    # Bit i denotes the one-active-ordinary-line assignment with label i.
    raw = [0]*n + [1 << i for i in range(q*q)] + [0]*(q+1)
    ordinates = [[field.ordinate(a,x,b) for a in range(q) for b in range(q)]
                 for x in range(q)]
    all_rows = []
    cost = s**3*(s-1)
    directions = square.selected_directions(s,s)
    for h in directions:
        c = lib.Circuit(2*n)
        final = square.projected_wires(field,c,h,n)
        assert len(c.gates) == 3*cost and all(op == "or" for op,_,_ in c.gates)
        wires = c.wires(raw)
        first_values = set(wires[c.inputs:c.inputs+cost])
        project = [field.project(h,z) for z in range(q)]
        for a in range(q):
            buckets = [0]*s
            for b in range(q):
                buckets[project[b]] |= 1 << (a*q+b)
            assert all(row in first_values for row in buckets)
        for x, values in enumerate(ordinates):
            expected = [0]*s
            for i,z in enumerate(values):
                expected[project[z]] |= 1 << i
            c0, c1 = project[x], project[field.theta_times(x)]
            assert all(wires[final[c0,c1,j]] == expected[j] for j in range(s))
            all_rows.extend(expected)
    popcount = getattr(int,"bit_count",lambda mask: bin(mask).count("1"))
    assert all(popcount(row)==s**3 for row in all_rows)
    intersections = {}
    for a,b in combinations(all_rows,2):
        count = popcount(a & b)
        intersections[count] = intersections.get(count,0)+1
    assert set(intersections) == {0,s*s}
    groups = q*len(directions)
    assert intersections[0] == groups*s*(s-1)//2
    assert intersections[q] == groups*(groups-1)//2 * s*s
    lower = len(all_rows)*(s-1)
    assert lower == cost*len(directions)
    print(f"q={q} directions={len(directions)} outputs={len(all_rows)} "
          f"row intersection histogram={intersections} OR lower={lower} built={3*lower}",flush=True)


if __name__ == "__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("bases",type=int,nargs="*",default=[2,3,4,5,7])
    args=parser.parse_args()
    if not __debug__:
        raise SystemExit("Run without -O so all checks are active.")
    for s in args.bases:
        check(s)
