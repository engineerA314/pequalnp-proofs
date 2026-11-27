"""Exact CNF counting by cliques of simultaneously falsifiable clauses."""
from dataclasses import dataclass
from itertools import product
from random import Random
from typing import Optional

from three_colour_word import encode, parse


def popcount(bits):
    return bin(bits).count("1")


def graph(cubes):
    adjacent = [set() for _ in cubes]
    for i, (ones, zeros) in enumerate(cubes):
        for j in range(i):
            a, b = cubes[j]
            if not ((ones & b) or (zeros & a)):
                adjacent[i].add(j)
                adjacent[j].add(i)
    return adjacent


def peel(adjacent):
    remaining = {i: set(row) for i, row in enumerate(adjacent)}
    order = []
    width = 0
    while remaining:
        i = min(remaining, key=lambda j: (len(remaining[j]), j))
        row = remaining.pop(i)
        width = max(width, len(row))
        for j in row:
            remaining[j].remove(i)
        order.append(i)
    return order, width


def terms(cubes, adjacent, order):
    yield 0, 0, 1
    rank = {v: i for i, v in enumerate(order)}
    for i in order:
        a, b = cubes[i]
        later = [j for j in adjacent[i] if rank[i] < rank[j]]
        stack = [(a, b, -1, sorted(later, key=rank.get))]
        while stack:
            ones, zeros, sign, candidates = stack.pop()
            yield ones, zeros, sign
            for k, j in enumerate(candidates):
                u, v = cubes[j]
                rest = [h for h in candidates[k+1:] if h in adjacent[j]]
                stack.append((ones | u, zeros | v, -sign, rest))


@dataclass
class Result:
    count: int
    model: Optional[dict]
    degeneracy: int
    cliques: int


def solve(formula):
    names = sorted({v for clause in formula for v, _ in clause})
    bits = {v: 1 << i for i, v in enumerate(names)}
    cubes = set()
    for clause in formula:
        ones = zeros = 0
        for v, literal_sign in clause:
            if literal_sign:
                zeros |= bits[v]
            else:
                ones |= bits[v]
        if ones & zeros:
            continue
        if not (ones or zeros):
            return Result(0, None, 0, 0)
        cubes.add((ones, zeros))
    cubes = sorted(cubes)
    adjacent = graph(cubes)
    order, width = peel(adjacent)
    parts = list(terms(cubes, adjacent, order))
    assert len(parts) <= 1 + len(cubes)*(1 << width)

    def restricted(ones, zeros):
        value = 0
        for a, b, sign in parts:
            if (a & zeros) or (b & ones):
                continue
            free = len(names) - popcount(ones | zeros | a | b)
            value += sign * (1 << free)
        return value

    total = restricted(0, 0)
    if total == 0:
        return Result(0, None, width, len(parts))
    ones = zeros = 0
    for v in names:
        bit = bits[v]
        if restricted(ones, zeros | bit) > 0:
            zeros |= bit
        else:
            ones |= bit
    model = {v: bool(ones & bits[v]) for v in names}
    return Result(total, model, width, len(parts))


def solve_word(word):
    formula = parse(word)
    return None if formula is None else solve(formula)


def valid(formula, model):
    return all(any(model[v] == s for v, s in c) for c in formula)


def check():
    rng = Random(20261127)
    for _ in range(900):
        n = rng.randint(1, 8)
        formula = [[(rng.randrange(n), bool(rng.randrange(2)))
                    for _ in range(rng.randrange(1, 7))] for _ in range(rng.randrange(11))]
        names = sorted({v for c in formula for v, _ in c})
        actual = sum(valid(formula, dict(zip(names, a))) for a in product((False, True), repeat=len(names)))
        result = solve_word(encode(formula))
        assert result.count == actual and (result.model is None) == (actual == 0)
        if result.model is not None:
            assert valid(formula, result.model)
    assert solve_word(bytes([1])) is None and solve([[]]).count == 0
    assert solve([[(777, True), (777, False)]]).count == 2
    n = 48
    formula = [[(i, not bool(j & (1 << i))) for i in range(n)] for j in range(256)]
    result = solve(formula)
    assert result.count == 2**n-256 and result.degeneracy == 0 and result.cliques == 257
    assert valid(formula, result.model)
    print(f"48 variables, 256 full-width clauses: {result.cliques} terms, {result.count} models")
    wide = solve([[(i, True) for i in range(1024)]])
    assert wide.count == 2**1024 - 1 and wide.cliques == 2
    print("1024-variable single clause: two terms; 900 random model-count and witness checks passed")


if __name__ == "__main__":
    check()
