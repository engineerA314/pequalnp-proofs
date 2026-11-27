"""Integer-arithmetic checks of the Hermitian square-sum and maximal contact examples."""
from itertools import product
from math import factorial, prod
from random import Random


def add(x, y):
    return x[0] + y[0], x[1] + y[1]


def multiply(x, y):
    return x[0]*y[0] - x[1]*y[1], x[0]*y[1] + x[1]*y[0]


def conjugate(x):
    return x[0], -x[1]


def squared(x):
    return x[0]**2 + x[1]**2


def coefficients(rows, d):
    table = {(0,)*d: (1, 0)}
    for row in rows:
        following = dict(table)
        for alpha, coefficient in table.items():
            for i, entry in enumerate(row):
                key = alpha[:i] + (alpha[i]+1,) + alpha[i+1:]
                following[key] = add(following.get(key, (0, 0)), multiply(coefficient, entry))
        table = {k: v for k, v in following.items() if v != (0, 0)}
    return table


def direct(rows, weights):
    matrix = []
    for u in rows:
        result_row = []
        for v in rows:
            entry = (1, 0)
            for weight, left, right in zip(weights, u, v):
                entry = add(entry, multiply((weight, 0), multiply(left, conjugate(right))))
            result_row.append(entry)
        matrix.append(result_row)
    dp = [(0, 0)] * (1 << len(rows))
    dp[0] = (1, 0)
    for mask in range(1, len(dp)):
        row = bin(mask).count("1") - 1
        for col, entry in enumerate(matrix[row]):
            if mask & (1 << col):
                dp[mask] = add(dp[mask], multiply(entry, dp[mask ^ (1 << col)]))
    return dp[-1]


def verify(rows, weights):
    n = len(rows)
    coeffs = coefficients(rows, len(weights))
    square_sum = sum(factorial(n-sum(a)) * prod(factorial(k) for k in a) * squared(c) *
                     prod(t**k for t, k in zip(weights, a)) for a, c in coeffs.items())
    assert direct(rows, weights) == (square_sum, 0)
    if all(t >= 0 for t in weights):
        active = any(t and z != (0, 0) for row in rows for t, z in zip(weights, row))
        assert (square_sum > factorial(n)) == active
        assert square_sum >= factorial(n)
    return square_sum


if __name__ == '__main__':
    rng = Random(2708)
    probes = 0
    for n, d in product(range(7), range(4)):
        for trial in range(10):
            rows = [[(rng.randrange(-2, 3), rng.randrange(-2, 3)) for _ in range(d)] for _ in range(n)]
            if trial == 0:
                rows = [[(0, 0)]*d for _ in range(n)]
            choices = [[1]*d, [rng.randrange(4) for _ in range(d)], [rng.randrange(-2, 3) for _ in range(d)]]
            for weights in choices:
                verify(rows, weights)
                probes += 1
    for n, entries in [(1, [(1, 0)]), (2, [(1, 0), (-1, 0)]), (4, [(1, 0), (0, 1), (-1, 0), (0, -1)])]:
        for t in range(-5, 6):
            assert verify([[z] for z in entries], [t]) == factorial(n)*(1+t**n)
    print(probes, 'Gaussian-integer square sums and 33 maximal-contact evaluations verified.')
