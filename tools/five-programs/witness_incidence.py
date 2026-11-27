"""Exact finite checks for the witness-scale and incidence inequalities."""
from fractions import Fraction
from random import Random


def balanced(first, size, lines):
    if size == 1:
        value = 1 << first
    else:
        left = size // 2
        value = balanced(first, left, lines) | balanced(first + left, size - left, lines)
    lines.append(value)
    return value


def check(size, lines):
    assert (1 << size) - 1 in lines
    frequency = [sum(row >> k & 1 for row in lines) for k in range(size)]
    assert sum(Fraction(1, 1 << total) for total in frequency) <= Fraction(1, 2)
    loads = [bin(row).count("1") for row in lines]
    for q in range(1, size + 1):
        assert size <= q * (1 + sum(load > q for load in loads))
    m = size.bit_length() - 1
    assert sum(frequency) >= (m + 3) * size - 2 ** (m + 1)
    return sum(frequency)


def main():
    rng = Random(349)
    for n in range(1, 129):
        lines = []
        balanced(0, n, lines)
        m = n.bit_length() - 1
        assert check(n, lines) == (m + 3) * n - 2 ** (m + 1)
    for _ in range(500):
        n = rng.randint(2, 32)
        lines = [1 << i for i in range(n)]
        for _ in range(4 * n):
            a, b = rng.choices(lines, k=2)
            # A sound step may discard any subset of its predecessors' failures.
            lines.append((a | b) & rng.getrandbits(n))
        root = 0
        for i in range(n):
            root |= (1 << i) | rng.choice(lines)
            lines.append(root)
        check(n, lines)
    for n in (40, 288):
        lines = []
        balanced(0, n, lines)
        print(f"{n} witnesses, {len(lines)} lines, {check(n, lines)} incidences")


if __name__ == "__main__":
    main()
