"""Compare every reverse line flag with the forward minimum-occurrence calculation."""

import pair_witnesses as witnesses
import square_projection_circuit as square


def adjoints(circuit, primary, full):
    values = circuit.wires(primary)
    reverse = [0]*len(values)
    reverse[circuit.output] = full
    for i in reversed(range(len(circuit.gates))):
        op, left, right = circuit.gates[i]
        context = reverse[circuit.inputs+i]
        if op == "or":
            reverse[left] |= context
            reverse[right] |= context
        else:
            reverse[left] |= context & values[right]
            reverse[right] |= context & values[left]
    return reverse[:circuit.inputs]


def check(name, circuit, masks):
    n = len(masks)
    raw = [1 << p for p in range(n)]
    for w, mask in enumerate(masks):
        outside = ((1 << n)-1) ^ mask
        while outside:
            bit = outside & -outside
            raw[bit.bit_length()-1] |= 1 << (n+w)
            outside ^= bit
    flags = adjoints(circuit, raw+[0]*n, (1 << (2*n))-1)[n:]
    edge_inputs, edges = witnesses.signatures(masks)
    forward = witnesses.bounded(circuit, edge_inputs, True)[1]
    packed = visits = 0
    for w, mask in enumerate(masks):
        assert flags[w] & (1 << (n+w)) == 0
        assert flags[w] & ((1 << n)-1) & ~mask == 0
        while mask:
            bit = mask & -mask
            mask ^= bit
            if flags[w] & bit:
                packed |= 1 << visits
            visits += 1
    assert packed == forward and visits == edges
    count = bin(packed).count("1")
    assert count <= 3*len(circuit.gates)+n
    print(f"{name} gates={len(circuit.gates)} incident pairs={edges} "
          f"line-once pairs={count} complement tests rejected={n}")


def main():
    if not __debug__:
        raise SystemExit("Run Python without -O so the replay assertions are active.")
    library = square.circuit_library()
    for k in (2,3,4):
        masks = library.line_point_masks(k)
        base, _ = library.one_line_circuit(k)
        check(f"dyadic-q{2**k}", base, masks)
        check(f"completed-dyadic-q{2**k}", library.complete_sparse_prefix(base, masks), masks)
        direct = witnesses.direct(library, masks)
        check(f"direct-q{2**k}", direct, masks)
        direct.output = direct.gate("and", direct.output, direct.output)
        check(f"duplicated-output-q{2**k}", direct, masks)
    for s in (2,3,4,5):
        field = square.SquareField(s, library)
        masks = field.line_masks()
        check(f"projection-q{field.q}", square.build(field,s,library), masks)


if __name__ == "__main__":
    main()
