"""Construct and check a positive binary circuit for t-sparse plane incidence.

The general construction is over a quadratic extension of any finite field.
This replay implements prime and binary-extension base fields. As in the
earlier shared-merge experiment, distinct bits probe distinct assignments.
"""

import argparse
import importlib.util
import random
from itertools import combinations
from math import comb, isqrt
from pathlib import Path


def circuit_library():
    source = Path(__file__).resolve().parents[1] / "shared-low-merges" / "sparse_line_circuit.py"
    spec = importlib.util.spec_from_file_location("shared_low_merges", source)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class SquareField:
    """Represent a0 + a1 θ by a0 + s*a1 with θ² = u + vθ."""

    def __init__(self, s, library):
        if s < 2:
            raise ValueError("the base field must have at least two elements")
        self.s, self.q = s, s*s
        if all(s % divisor for divisor in range(2, isqrt(s) + 1)):
            plus = lambda a, b: (a + b) % s
            times = lambda a, b: (a * b) % s
        elif s & (s - 1) == 0:
            modulus = library.irreducible(s.bit_length() - 1)
            plus = lambda a, b: a ^ b
            times = lambda a, b: library.multiply(a, b, modulus)
        else:
            raise ValueError("this replay supports prime or power-of-two base orders")
        self.plus = [[plus(a, b) for b in range(s)] for a in range(s)]
        self.times = [[times(a, b) for b in range(s)] for a in range(s)]
        self.neg = [self.plus[a].index(0) for a in range(s)]
        self.u, self.v = next((u, v) for u in range(s) for v in range(s)
                              if all(times(x, x) != plus(u, times(v, x)) for x in range(s)))
        self.parts = [(z % s, z // s) for z in range(self.q)]

    def pair(self, a0, a1):
        return a0 + self.s*a1

    def difference(self, left, right):
        return self.plus[left][self.neg[right]]

    def project(self, direction, z):
        a0, a1 = self.parts[z]
        return a1 if direction is None else self.plus[a0][self.times[direction][a1]]

    def theta_times(self, x):
        a0, a1 = self.parts[x]
        return self.pair(self.times[self.u][a1], self.plus[a0][self.times[self.v][a1]])

    def ordinate(self, a, x, b):
        """Independent incidence oracle using the coefficients of two polynomials."""
        a0, a1 = self.parts[a]
        x0, x1 = self.parts[x]
        b0, b1 = self.parts[b]
        add, mul = self.plus, self.times
        quadratic = mul[a1][x1]
        constant = add[add[mul[a0][x0]][mul[self.u][quadratic]]][b0]
        linear = add[add[mul[a0][x1]][mul[a1][x0]]][add[mul[self.v][quadratic]][b1]]
        return self.pair(constant, linear)

    def line_masks(self):
        q = self.q
        masks = []
        for a in range(q):
            for b in range(q):
                pts = [x*q + self.ordinate(a, x, b) for x in range(q)] + [q*q+a]
                masks.append(sum(1 << p for p in pts))
        for x in range(q):
            masks.append(sum(1 << p for p in [x*q + z for z in range(q)] + [q*q+q]))
        masks.append(sum(1 << p for p in range(q*q, q*q+q+1)))
        assert all(bin(mask).count("1") == q+1 for mask in masks)
        assert all((left & right) and ((left & right) & ((left & right) - 1)) == 0
                   for left, right in combinations(masks, 2))
        return masks


def selected_directions(s, t):
    # Include the second-coordinate direction in every instance.
    if not 1 <= t <= s:
        raise ValueError("the construction requires 1 <= t <= s")
    return [None] + list(range(t))


def projected_wires(field, circuit, direction, n):
    s, q = field.s, field.q
    buckets = [[] for _ in range(s)]
    for b in range(q):
        buckets[field.project(direction, b)].append(b)
    assert all(len(bucket) == s for bucket in buckets)
    first = {(a0, a1, h): circuit.fold("or", (n + field.pair(a0, a1)*q + b for b in buckets[h]))
             for a0 in range(s) for a1 in range(s) for h in range(s)}
    second = {(a0, c1, h): circuit.fold("or", (first[a0, a1, field.difference(h, field.times[c1][a1])]
                                              for a1 in range(s)))
              for a0 in range(s) for c1 in range(s) for h in range(s)}
    return {(c0, c1, h): circuit.fold("or", (second[a0, c1, field.difference(h, field.times[c0][a0])]
                                            for a0 in range(s)))
            for c0 in range(s) for c1 in range(s) for h in range(s)}


def build(field, t, library):
    s, q = field.s, field.q
    n = q*q + q + 1
    circuit = library.Circuit(2*n)
    directions = selected_directions(s, t)
    tests = [[] for _ in range(q*q)]
    for direction in directions:
        last = projected_wires(field, circuit, direction, n)
        for x in range(q):
            c0 = field.project(direction, x)
            c1 = field.project(direction, field.theta_times(x))
            for z in range(q):
                tests[x*q+z].append(last[c0, c1, field.project(direction, z)])
    assert len(circuit.gates) == 3*(t+1)*s**3*(s-1)
    points = [circuit.gate("and", p, circuit.fold("and", row)) for p, row in enumerate(tests)]
    affine = circuit.fold("or", points)
    slopes = [circuit.fold("or", range(n+a*q, n+(a+1)*q)) for a in range(q)]
    directions_at_infinity = circuit.fold("or", (circuit.gate("and", q*q+a, slopes[a]) for a in range(q)))
    verticals = []
    for x in range(q):
        active_point = circuit.fold("or", list(range(x*q, (x+1)*q)) + [n-1])
        verticals.append(circuit.gate("and", n+q*q+x, active_point))
    vertical = circuit.fold("or", verticals)
    infinity = circuit.gate("and", 2*n-1, circuit.fold("or", range(q*q, n)))
    circuit.output = circuit.fold("or", [affine, directions_at_infinity, vertical, infinity])
    assert len(circuit.gates) == (4*t+7)*q*q - 3*(t+1)*s**3 + 4*q + 1
    return circuit


def verify_sets(circuit, masks, selected_sets, library):
    """For each Y, singletons and the largest independent X certify every X."""
    n = len(masks)
    positive_bits = (1 << (n + 1)) - 1
    checked = 0
    for selected in selected_sets:
        covered = 0
        lines = [0]*n
        for w in selected:
            covered |= masks[w]
            lines[w] = positive_bits
        points = library.singleton_probes(n, covered)
        assert circuit.evaluate(points + lines) == covered, selected
        checked += 1
    return checked


def verify_sharp(field, directions, circuit, masks):
    n = len(masks)
    # A horizontal line z=b has index b, and (x,z)=(0,0) has index zero.
    active = [field.pair(1, 0) if d is None else field.pair(field.neg[d], 1) for d in directions]
    assert len(set(active)) == len(directions)
    inputs = [0]*(2*n)
    inputs[0] = 1
    for w in active:
        assert not (masks[w] & 1)
        inputs[n+w] = 1
    assert circuit.evaluate(inputs) == 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bases", type=int, nargs="+", default=[2, 3, 4, 5])
    parser.add_argument("--exhaustive-limit", type=int, default=150000,
                        help="exhaust every allowed line set if their count is at most this limit")
    parser.add_argument("--samples", type=int, default=512)
    args = parser.parse_args()
    if not __debug__:
        raise SystemExit("Run Python without -O so replay assertions are active.")
    library = circuit_library()
    for s in args.bases:
        field = SquareField(s, library)
        masks = field.line_masks()
        for t in range(1, s+1):
            circuit = build(field, t, library)
            n = len(masks)
            total = sum(comb(n, j) for j in range(t+1))
            if total <= args.exhaustive_limit:
                tests = (subset for j in range(t+1) for subset in combinations(range(n), j))
                count = verify_sets(circuit, masks, tests, library)
                assert count == total
                mode = "exhaustive"
            else:
                rng = random.Random(10000*s+t)
                tests = (rng.sample(range(n), i % (t+1)) for i in range(args.samples))
                count = verify_sets(circuit, masks, tests, library)
                mode = "sampled"
            verify_sharp(field, selected_directions(s, t), circuit, masks)
            print(f"q={field.q} t={t} gates={len(circuit.gates)} {mode} line sets={count} "
                  f"false positive at {t+1} lines verified", flush=True)


if __name__ == "__main__":
    main()
