"""Measure shortest accepting parses on every actual incident singleton pair."""

import square_projection_circuit as square


def signatures(masks):
    n = len(masks)
    raw = [0]*(2*n)
    edges = 0
    for w, row in enumerate(masks):
        while row:
            pbit = row & -row
            row ^= pbit
            p = pbit.bit_length()-1
            raw[p] |= 1 << edges
            raw[n+w] |= 1 << edges
            edges += 1
    return raw, edges


def bounded(circuit, raw, free_points):
    n = len(raw)//2
    # Entry k is the set of assignments that have a parse of cost at most k.
    # Reusing a gate through both operands of an AND counts both occurrences.
    state = [(v if free_points and i<n else 0, v, v) for i,v in enumerate(raw)]
    for op, a, b in circuit.gates:
        left, right = state[a], state[b]
        if op == "or":
            state.append(tuple(x|y for x,y in zip(left,right)))
        else:
            state.append((left[0]&right[0], (left[0]&right[1]) | (left[1]&right[0]),
                          (left[0]&right[2]) | (left[1]&right[1]) | (left[2]&right[0])))
    return state[circuit.output]


def direct(library, masks):
    n = len(masks)
    c = library.Circuit(2*n)
    stars = []
    for w, mask in enumerate(masks):
        points = [p for p in range(n) if mask >> p & 1]
        stars.append(c.gate("and", n+w, c.fold("or", points)))
    c.output = c.fold("or", stars)
    return c


def report(name, circuit, masks):
    raw, edges = signatures(masks)
    full = (1 << edges)-1
    assert circuit.evaluate(raw) == full
    both = bounded(circuit, raw, False)
    line = bounded(circuit, raw, True)
    assert both[1] == line[0] == 0
    short = bin(both[2]).count("1")
    once = bin(line[1]).count("1")
    assert (both[2] & ~line[1]) == 0 and short <= len(circuit.gates)
    print(f"{name}: edges={edges} gates={len(circuit.gates)} two-leaf={short} "
          f"line-once={once} line-at-most-twice={bin(line[2]).count('1')}")
    return short, once


def main():
    if not __debug__:
        raise SystemExit("Run Python without -O so the replay assertions are active.")
    library = square.circuit_library()
    for k in (2,3,4):
        masks = library.line_point_masks(k)
        base, _ = library.one_line_circuit(k)
        report(f"dyadic-q{2**k}", base, masks)
        c = direct(library, masks)
        edges = sum(bin(x).count("1") for x in masks)
        assert report(f"direct-q{2**k}", c, masks) == (edges,edges)
        c.output = c.gate("and", c.output, c.output)
        assert report(f"duplicated-output-q{2**k}", c, masks) == (0,0)
    for s in (2,3,4,5):
        field = square.SquareField(s, library)
        masks = field.line_masks()
        for t in sorted({1,s}):
            report(f"projection-q{field.q}-t{t}", square.build(field,t,library), masks)


if __name__ == "__main__":
    main()
