"""Replay an ordinary PHP resolution certificate and locate its first matching obstruction."""
from itertools import combinations, permutations
from math import comb
from random import Random


def matching(clause, edges):
    """Return a locally injective falsifier, or None when every such matching satisfies the clause."""
    allowed = {p: set(edges[p]) for p, _, _ in clause}
    for p, h, positive in clause:
        if positive:
            allowed[p].discard(h)
        else:
            allowed[p].intersection_update({h})
    owner = {}

    def augment(p, seen):
        for h in sorted(allowed[p]):
            if h in seen:
                continue
            seen.add(h)
            if h not in owner or augment(owner[h], seen):
                owner[h] = p
                return True
        return False

    for p in sorted(allowed, key=lambda p: len(allowed[p])):
        if not augment(p, set()):
            return None
    return {p: h for h, p in owner.items()}


def hall_trace(n):
    holes = tuple(range(n))
    lines = []
    steps = []

    def append(clause, step):
        lines.append(frozenset(clause))
        steps.append(step)
        return len(lines) - 1

    def resolve(left, right, p, h):
        plus, minus = (p, h, True), (p, h, False)
        assert plus in lines[left] and minus in lines[right]
        return append((lines[left] - {plus}) | (lines[right] - {minus}), (left, right, p, h))

    rows = [append(((p, j, True) for j in holes), None) for p in range(n + 1)]
    clash = {(p, q, j): append(((p, j, False), (q, j, False)), None)
             for p, q in combinations(range(n + 1), 2) for j in holes}
    hall = {frozenset(): rows[0]}
    for k in range(1, n + 1):
        for group in combinations(holes, k):
            chosen = frozenset(group)
            proof = rows[k]
            for h in group:
                line = hall[chosen - {h}]
                for p in range(k):
                    line = resolve(line, clash[p, k, h], p, h)
                proof = resolve(proof, line, k, h)
            hall[chosen] = proof
            assert lines[proof] == {(p, h, True) for p in range(k + 1) for h in holes if h not in chosen}
    return lines, steps


def replay(n):
    lines, steps = hall_trace(n)
    holes = set(range(n))
    edges = [holes for _ in range(n + 1)]
    first = None
    for idx, (clause, step) in enumerate(zip(lines, steps)):
        if step is None:
            if all(s for _, _, s in clause):
                p = next(iter(clause))[0]
                assert clause == {(p, j, True) for j in holes}
            else:
                (p, j, s), (q, h, t) = clause
                assert p != q and j == h and not s and not t
        else:
            left, right, p, h = step
            assert left < idx and right < idx and (p, h, True) in lines[left] and (p, h, False) in lines[right]
            assert clause == (lines[left] - {(p, h, True)}) | (lines[right] - {(p, h, False)})
        if first is None:
            witness = matching(clause, edges)
            if witness is not None:
                assert step is not None and p not in witness and set(witness.values()) == holes
                assert len(witness) == n and all((witness[q] == j) != s for q, j, s in clause)
                first = idx
    assert lines[-1] == frozenset() and first is not None
    assert len(lines) == n + 1 + n*comb(n + 1, 2) + sum(comb(n,k)*k*(k + 1) for k in range(1, n + 1))
    return len(lines), first + 1


def check():
    rng = Random(238)
    for _ in range(650):
        m, n = rng.randint(1, 5), rng.randint(1, 5)
        edges = [{j for j in range(n) if rng.randrange(4)} for _ in range(m)]
        clause = {(rng.randrange(m), rng.randrange(n), bool(rng.randrange(2))) for _ in range(rng.randrange(10))}
        pigeons = sorted({p for p, _, _ in clause})
        def false_under(values):
            f = dict(zip(pigeons, values))
            return all(f[p] in edges[p] for p in pigeons) and all((f[p] == j) != s for p,j,s in clause)
        exists = any(false_under(v) for v in permutations(range(n), len(pigeons)))
        assert (matching(clause, edges) is not None) == exists
    print("650 matching decisions agree with exhaustive partial injections")
    for n in range(1, 9):
        count, first = replay(n)
        print(f"{n} holes: {count} lines, first locally falsifiable line {first}, matching size {n}")


if __name__ == "__main__":
    check()
