"""Trace the shared gates for a row and recover a sparse negative witness."""

import square_projection_circuit as square


def indices(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length()-1
        mask ^= bit


def trace(circuit, wire, row, width, singleton):
    owned, boundary = set(), set()
    todo = [wire]
    while todo:
        i = todo.pop()
        if i in owned or i in boundary:
            continue
        mask = singleton[i]
        if i >= circuit.inputs and not mask & ~row and bin(mask).count("1") > width:
            owned.add(i)
            _,left,right = circuit.gates[i-circuit.inputs]
            todo.extend([left,right])
        else:
            boundary.add(i)
    assert len(boundary) <= len(owned)+1
    return owned, boundary


def recover(circuit, wire, row, boundary, singleton):
    selected = narrow = 0
    for i in boundary:
        outside = singleton[i] & ~row
        if outside:
            selected |= outside & -outside
        else:
            narrow |= singleton[i]
    remaining = singleton[wire] & ~narrow
    if not remaining:
        return None
    chosen = list(indices(selected))
    assert not (selected & row) and len(chosen) <= len(boundary)
    raw = [(selected >> w) & 1 for w in range(circuit.inputs)]
    assert circuit.wires(raw)[wire]
    return chosen


def run(q, masks, lib):
    n = len(masks)
    rows = [sum(1 << w for w,line in enumerate(masks) if (line >> p) & 1)
            for p in range(n)]
    direct = lib.Circuit(n)
    outs = [direct.fold("or",indices(row)) for row in rows]
    raw = [1 << w for w in range(n)]
    singleton = direct.wires(raw)
    used = set()
    for out,row in zip(outs,rows):
        assert singleton[out] == row
        owned,boundary = trace(direct,out,row,1,singleton)
        assert len(owned) == q and len(boundary) == q+1
        assert not (used & owned)
        used.update(owned)
        assert recover(direct,out,row,boundary,singleton) is None
    assert len(used) == len(direct.gates) == n*q

    # Two OR chains retain distinct outside labels at every intermediate
    # gate. Their conjunction has all required singleton hits for row zero.
    bad = lib.Circuit(n)
    row = rows[0]
    outside = list(indices(((1 << n)-1) ^ row))[:2]
    ends = []
    for first in outside:
        current = first
        for i in indices(row):
            current = bad.gate("or",current,i)
        ends.append(current)
    bad.output = bad.gate("and",*ends)
    singles = bad.wires(raw)
    assert singles[bad.output] == row
    charged, cut = trace(bad,bad.output,row,1,singles)
    found = recover(bad,bad.output,row,cut,singles)
    assert len(charged) == 1 and found == outside and len(found) <= q
    print(f"q={q} point outputs={n} direct gates={len(used)} "
          f"private gates per row={q} recovered outside lines={found}")


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run without -O to keep the verification assertions active.")
    library = square.circuit_library()
    for k in (1,2,3,4,5):
        run(2**k,library.line_point_masks(k),library)
    for s in (3,5):
        field = square.SquareField(s,library)
        run(field.q,field.line_masks(),library)
