"""Exact signed-column compression for the project's ragged two-layer integer threshold circuits."""
from itertools import product
from math import comb, prod
from random import Random
from threshold_count import direct


def model_count(gates, top):
    inputs = max((len(weights) for weights, _, _ in gates), default=0)
    groups = {}
    zeros = 0
    for i in range(inputs):
        col = tuple(row[i] if i < len(row) else 0 for row, _, _ in gates)
        first = next((v for v in col if v), 0)
        if first == 0:
            zeros += 1
            continue
        sign = first < 0
        representative = tuple(-v for v in col) if sign else col
        m, negatives = groups.get(representative, (0, 0))
        groups[representative] = (m + 1, negatives + int(sign))
    grouped = list(groups.items())
    base = [-sum(negatives * col[i] for col, (_, negatives) in grouped) for i in range(len(gates))]
    coefficients = [tuple(comb(m, k) for k in range(m+1)) for _, (m, _) in grouped]
    patterns = prod(len(a) for a in coefficients)
    total = 0
    for counts in product(*(range(len(a)) for a in coefficients)):
        scores = base.copy()
        for k, (col, _) in zip(counts, grouped):
            scores = [s + k*v for s, v in zip(scores, col)]
        if sum(w for s, (_, threshold, w) in zip(scores, gates) if s >= threshold) >= top:
            total += prod(a[k] for a, k in zip(coefficients, counts))
    return total << zeros, patterns


if __name__ == '__main__':
    rng = Random(270676)
    for t in range(600):
        h, n = rng.randrange(9), rng.randrange(10)
        pool = [tuple(rng.randrange(-3, 4) for _ in range(h)) for _ in range(rng.randrange(1, 5))]
        cols = [tuple(s*v for v in rng.choice(pool)) if s else (0,)*h for s in (rng.choice((-1, 0, 1)) for _ in range(n))]
        gates = [([c[j] for c in cols][:rng.randrange(n+1)], rng.randrange(-9, 10), rng.randrange(-6, 7)) for j in range(h)]
        top = rng.randrange(-8, 9)
        count, states = model_count(gates, top)
        assert count == direct(gates, top) and 1 <= states <= 2**n
    # 257 distinct thresholds on a single signed statistic D = positives selected minus negatives selected.
    # The top gate is a majority of nested threshold events D >= -128,...,128, equivalently D >= 0.
    m = 240
    row = [1]*m + [-1]*m + [0]*32
    gates = [(row, t, 1) for t in range(-128, 129)]
    result, states = model_count(gates, 129)
    expected = ((2**(2*m)+comb(2*m,m))//2) << 32
    assert result == expected and states == 481
    # Arbitrarily long coefficients and integer ties.
    weight = 2**2048+3
    assert model_count([([weight,-weight,weight], weight, 1)], 1)[0] == 4
    print('600 exhaustive-oracle checks passed. 512 inputs, 257 gates,', states, 'count vectors.')
    print('512-input count:', result)
