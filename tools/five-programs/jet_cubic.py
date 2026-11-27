"""Compute permanents over Z[sqrt(d)] directly by subset DP."""
from math import factorial


def permanent(matrix, d):
    n = len(matrix)
    dp = {0: (1, 0)}
    for row in matrix:
        nxt = {}
        for mask, (r, s) in dp.items():
            for j, (u, v) in enumerate(row):
                new = mask | (1 << j)
                if new == mask:
                    continue
                x, y = nxt.get(new, (0, 0))
                nxt[new] = x + r*u + d*s*v, y + r*v + s*u
        dp = nxt
    return dp[(1 << n) - 1]


def check():
    tested = 0
    for n in range(3, 13):
        a = [1, 1, -2] + [0] * (n - 3)
        u = [1, -1] + [0] * (n - 2)
        d = n * (n - 1) // 2
        for m in range(-2, 4):
            matrix = [[(2 + m*a[i], m*u[i]*a[j]) for j in range(n)] for i in range(n)]
            assert permanent(matrix, d) == (2**n * factorial(n) * (1 - m**3), 0)
            tested += 1
    print(f"{tested} exact scaled permanents, sizes 3 through 12")


if __name__ == "__main__":
    check()
