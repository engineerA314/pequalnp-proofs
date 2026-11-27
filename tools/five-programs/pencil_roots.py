"""Check negative integer samples in sparse two-generator power sums."""
from random import Random


def evaluate(p, x):
    return sum(c * x**e for e, c in p.items())


def roots(a, b, terms, degree, samples):
    answer = []
    for x in samples:
        u, v = evaluate(a, x), evaluate(b, x)
        if sum(c * (s*u + t*v)**degree for c, s, t in terms) == 0:
            answer.append(x)
    return answer


def check():
    rng = Random(103)
    tests = 0
    for _ in range(500):
        exponents = range(12)
        a = {n: rng.choice((-3, -2, -1, 1, 2, 3))
             for n in rng.sample(exponents, rng.randint(1, 5))}
        b = {n: rng.choice((-3, -2, -1, 1, 2, 3))
             for n in rng.sample(exponents, rng.randint(1, 5))}
        degree = rng.randint(1, 6)
        terms = [(rng.choice((-1, 1)), rng.randint(-3, 3), rng.randint(-3, 3))
                 for _ in range(rng.randint(1, 12))]
        # A polynomial of degree at most degree*11 vanishes identically if it
        # vanishes at this many distinct points. Exclude precisely that case.
        probes = range(11*degree + 1)
        if len(roots(a, b, terms, degree, probes)) == len(probes):
            continue
        found = roots(a, b, terms, degree, range(-30, 0))
        assert len(found) <= degree*(len(a.keys() | b.keys())-1)
        tests += 1
    for degree, terms in [(3, [(1,2,4),(-1,1,3),(-1,1,1)]),
                          (4, [(1,4,10),(-5,2,6),(-5,2,4),(4,0,2)])]:
        found = roots({1: 1}, {0: 1}, terms, degree, range(-30, 0))
        assert found == list(range(-degree, 0))
        print(f"degree {degree}, consecutive roots {found}")
    print(f"{tests} nonzero random families")


if __name__ == "__main__":
    check()
