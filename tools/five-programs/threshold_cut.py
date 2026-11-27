"""Count a signed two-level threshold circuit using only crossing-gate patterns."""
from collections import Counter
from itertools import product
from math import comb
from random import Random
from threshold_count import dominance


def half_histogram(width, local, cross):
    """Use a Gray walk to update only gates touching the changed variable."""
    changes = [[] for _ in range(width)]
    for gid, (coefficients, _, _) in enumerate(local + cross):
        for i, w in enumerate(coefficients):
            if w:
                changes[i].append((gid, w))
    scores = [0] * (len(local) + len(cross))
    top = sum(weight for _, threshold, weight in local if threshold <= 0)
    hist = Counter()
    previous = 0
    for t in range(1 << width):
        gray = t ^ (t >> 1)
        if t:
            mask = previous ^ gray
            column = mask.bit_length() - 1
            sign = 1 if gray & mask else -1
            for gid, w in changes[column]:
                new = scores[gid] + sign*w
                if gid < len(local):
                    _, cut, value = local[gid]
                    top += value * (int(new >= cut) - int(scores[gid] >= cut))
                scores[gid] = new
        hist[(tuple(scores[len(local):]), top)] += 1
        previous = gray
    return hist


def cut_count(n, cut, gates, top):
    if not 0 <= cut <= n:
        raise ValueError("cut must be between zero and the declared input count")
    left, right, lcross, rcross = [], [], [], []
    for weights, threshold, value in gates:
        lhs, rhs = weights[:cut], weights[cut:n]
        if not any(rhs):
            left.append((lhs, threshold, value))
        elif not any(lhs):
            right.append((rhs, threshold, value))
        else:
            lcross.append((lhs, threshold, value))
            rcross.append((rhs, threshold, value))
    A = half_histogram(cut, left, lcross)
    B = half_histogram(n-cut, right, rcross)
    count = 0
    for bits in product((False, True), repeat=len(lcross)):
        cross_total = sum(weight for bit, (_, _, weight) in zip(bits, lcross) if bit)
        points = [(tuple(-x if bit else x for x, bit in zip(score, bits)) + (-local,), ways)
                  for (score, local), ways in A.items()]
        queries = [(tuple(y - threshold if bit else threshold - 1 - y
                          for y, bit, (_, threshold, _) in zip(score, bits, rcross))
                    + (local + cross_total - top,), ways) for (score, local), ways in B.items()]
        count += dominance(points, queries, len(bits) + 1)
    return count, len(lcross)


def brute(n, gates, top):
    return sum(sum(weight for row, threshold, weight in gates
                   if sum(x*w for x, w in zip(bits, row)) >= threshold) >= top
               for bits in product((0,1), repeat=n))


def check():
    rng = Random(2402)
    for _ in range(700):
        n = rng.randrange(10)
        cut = rng.randrange(n+1)
        gates = []
        for _ in range(rng.randrange(14)):
            row = [rng.randint(-3,3) for _ in range(rng.randrange(n+4))]
            side = rng.randrange(4)
            if side == 0:
                row = row[:cut]
            elif side == 1:
                row = [w if i >= cut else 0 for i,w in enumerate(row)]
            gates.append((row, rng.randint(-5,5), rng.randint(-6,6)))
        top = rng.randint(-8,8)
        assert cut_count(n,cut,gates,top)[0] == brute(n,gates,top)
    print("700 signed circuits with all cut positions, short and trailing weights match exhaustive counts")
    n = 36
    gates = []
    for i in range(n):
        row = [0]*n
        row[i] = 1
        for value in (3,-2,2,-3,1):
            gates.append((row,1,value))
    gates += [([1]*n,20,-3), ([1]*18+[-1]*18,0,2)]
    expected = sum(comb(18,a)*comb(18,b) for a in range(19) for b in range(19)
                   if a+b-3*(a+b>=20)+2*(a>=b)>=18)
    counted, crossing = cut_count(n,18,gates,18)
    assert counted == expected and crossing == 2
    print(f"{n} inputs, {len(gates)} bottom gates, {crossing} crossing gates, exact count {counted}")


if __name__ == "__main__":
    check()
