"""Certify the OR preprocessing still usable by a single-AND-level repair."""

import boundary_cofactors as boundary
import square_projection_circuit as square


def members(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def residual_graph(q, anchors, masks):
    n = q*q + q + 1
    points = sum(1 << (x*q + z) for x in range(q) for z in range(q) if z not in anchors)
    neighbors = [0]*(2*n)
    for w in range(q, q*q):
        line = n+w
        neighbors[line] = masks[w] & points
        assert bin(neighbors[line]).count("1") == q-len(anchors)
        for p in members(neighbors[line]):
            neighbors[p] |= 1 << line
    assert all(bin(neighbors[p]).count("1") == q-1 for p in members(points))
    return neighbors


def fits_star(support, neighbors):
    vertices = members(support)
    u, v = next(vertices), next(vertices)
    possible = neighbors[u] & neighbors[v]
    assert possible & (possible-1) == 0
    return bool(possible) and support & ~neighbors[possible.bit_length()-1] == 0


def surviving_preparations(circuit, q, anchors, neighbors):
    # None is constant true. Zero denotes constant false. Every other integer
    # represents exactly the OR of the indicated unfixed primary variables.
    n = q*q + q + 1
    state = [1 << p if neighbors[p] else 0 for p in range(2*n)]
    for b in anchors:
        state[n+b] = None
    total = eligible = 0
    for i, (op, a, b) in enumerate(circuit.gates):
        left, right = state[a], state[b]
        if op == "and":
            if left == 0 or right == 0:
                value = 0
            elif left is None:
                value = right
            elif right is None or left == right:
                value = left
            else:
                raise AssertionError(("nonconstant AND survived", q, i, a, b))
        elif left is None or right is None:
            value = None
        else:
            value = left | right
            if value != left and value != right:
                total += 1
                eligible += fits_star(value, neighbors)
        state.append(value)
    assert len(state) == circuit.inputs + len(circuit.gates)
    return total, eligible


def report(name, circuit, q, anchors, masks):
    if len(anchors)+2 > q:
        return
    neighbors = residual_graph(q, anchors, masks)
    total, eligible = surviving_preparations(circuit, q, anchors, neighbors)
    optimum = q*q*(q-len(anchors))-1
    print(f"{name} q={q} anchors={len(anchors)} prefix gates={len(circuit.gates)} "
          f"residual ORs={total} eligible ORs={eligible} residual optimum={optimum} "
          f"single-level suffix gates>={optimum-eligible}")


def main():
    if not __debug__:
        raise SystemExit("Run Python without -O so replay assertions are active.")
    library = square.circuit_library()
    for k in range(2, 7):
        q = 2**k
        circuit, _ = library.one_line_circuit(k)
        report("one-line", circuit, q, {0, q-1}, library.line_point_masks(k))
    for s in (2, 3, 4, 5):
        field = square.SquareField(s, library)
        masks = field.line_masks()
        for t in range(1, s+1):
            circuit = square.build(field, t, library)
            report(f"projection-t{t}", circuit, field.q, boundary.square_anchors(field, t), masks)


if __name__ == "__main__":
    main()
