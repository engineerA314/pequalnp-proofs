"""Compare shared incidence circuits before and after distributive factoring."""

import pair_witnesses as witnesses
import square_projection_circuit as square


def selectors(library, masks, k, factored):
    circuit = witnesses.direct(library, masks)
    n = len(masks)
    labels = list(range(n, n+k))
    if factored:
        circuit.output = circuit.gate("or", circuit.output, circuit.fold("and", labels))
    else:
        leaves = [circuit.gate("or", circuit.output, i) for i in labels]
        circuit.output = circuit.fold("and", leaves)
    return circuit


def events(circuit, raw, n):
    pair = circuit.wires(raw)
    base = circuit.wires(raw[:n] + [0]*n)
    distinct = total = 0
    for op, a, b in circuit.gates:
        if op == "and":
            hits = (pair[a] & ~base[a]) & (pair[b] & ~base[b])
            distinct |= hits
            total += bin(hits).count("1")
    assert not base[circuit.output]
    return distinct, total


def main():
    if not __debug__:
        raise SystemExit("Run without -O so the replay assertions are active.")
    library = square.circuit_library()
    for degree in range(1, 5):
        q = 2**degree
        masks = library.line_point_masks(degree)
        n = len(masks)
        raw, edges = witnesses.signatures(masks)
        full = (1 << edges)-1
        for factored in (False, True):
            circuit = selectors(library, masks, q+1, factored)
            distinct, total = events(circuit, raw, n)
            assert circuit.evaluate(raw) == full
            assert distinct == (0 if factored else full)
            assert total == (0 if factored else q*edges)
            once = witnesses.bounded(circuit, raw, True)[1]
            assert (full & ~distinct & ~once) == 0
            # Each omitted leaf has a simultaneous witness to its necessity.
            # With no points, select all but the named one of the q+1 lines.
            all_omissions = (1 << (q+1))-1
            negative = [0]*(2*n)
            for i in range(q+1):
                negative[n+i] = all_omissions ^ (1 << i)
            assert circuit.evaluate(negative) == 0
            print(f"q={q} factored={factored} gates={len(circuit.gates)} "
                  f"forked incidences={bin(distinct).count('1')} events={total}")


if __name__ == "__main__":
    main()
