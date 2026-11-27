"""Test the buffered block layout against the project's total Boolean semantics."""
from itertools import product
from random import Random


def evaluate(circuit, inputs):
    gates, output = circuit
    wires = list(inputs)
    for op, ports in gates:
        values = [wires[i] if i < len(wires) else False for i in ports]
        if op == "and":
            value = all(values)
        elif op == "or":
            value = any(values)
        else:
            value = not (values and values[0])
        wires.append(value)
    return wires[output] if output < len(wires) else False


def compose(n, sources, target):
    gates = []

    def append(circuit, ports):
        body, output = circuit
        start = n + len(gates)

        def rename(i):
            return ports[i] if i < len(ports) else start + i - len(ports)

        gates.extend((op, [rename(i) for i in xs]) for op, xs in body)
        result = n + len(gates)
        gates.append(("or", [rename(output)]))
        return result

    positions = [append(c, list(range(n))) for c in reversed(sources)]
    output = append(target, list(reversed(positions)))
    return gates, output


def random_circuit(rng, n):
    count = rng.randrange(7)
    return ([(rng.choice(("and", "or", "not")),
              [rng.randrange(n + count + 4) for _ in range(rng.randrange(3))])
             for _ in range(count)], rng.randrange(n + count + 4))


def check():
    rng = Random(348)
    inputs_tested = 0
    for _ in range(1200):
        n, m = rng.randrange(6), rng.randrange(6)
        sources = [random_circuit(rng, n) for _ in range(m)]
        target = random_circuit(rng, m)
        combined = compose(n, sources, target)
        assert len(combined[0]) == sum(len(c[0]) + 1 for c in sources) + len(target[0]) + 1
        for word in product((False, True), repeat=n):
            assert evaluate(combined, word) == evaluate(target, [evaluate(c, word) for c in sources])
            inputs_tested += 1
    # The two lengths have the same zero-padded bits and opposite answers.
    family = [([("and", [])], 0), ([], 0)]
    for w in ([], [False], [True]):
        decision = any(len(w) == j and evaluate(c, (w + [False] * j)[:j]) for j, c in enumerate(family))
        assert decision == (len(w) == 0 or w[0])
    print(f"1200 composed circuits, {inputs_tested} input evaluations, empty-output length gate passed")


if __name__ == "__main__":
    check()
