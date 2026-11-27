"""Exact #SAT and model reconstruction with a supplied variable order."""
from dataclasses import dataclass
from itertools import product
from random import Random


@dataclass
class Table:
    scope: tuple
    counts: list

    def access(self, mask, positions):
        index = sum(((mask >> source) & 1) << dest for dest, source in enumerate(positions))
        return self.counts[index]


def satisfies(formula, assignment):
    return all(any(assignment[v] == b for v, b in clause) for clause in formula)


def solve(formula, order=None):
    """Return (#SAT, one model or None, maximum number of later neighbours in a bucket)."""
    names = {v for clause in formula for v, _ in clause}
    if order is None:
        order = sorted(names)
    else:
        order = list(order)
    if set(order) != names or len(order) != len(names):
        raise ValueError('The order must contain each variable of the input exactly once.')
    rank = {v: i for i, v in enumerate(order)}
    buckets = [[] for _ in order]
    constant = 1
    width = 0
    trace = []

    def route(table):
        nonlocal constant
        if table.scope:
            buckets[rank[table.scope[0]]].append(table)
        else:
            constant *= table.counts[0]

    for clause in formula:
        local = tuple(sorted({v for v, _ in clause}, key=rank.__getitem__))
        offsets = {v: i for i, v in enumerate(local)}
        entries = [int(any(((mask >> offsets[v]) & 1) == b for v, b in clause))
                   for mask in range(1 << len(local))]
        route(Table(local, entries))

    for i, pivot in enumerate(order):
        factors = buckets[i]
        remaining = {v for f in factors for v in f.scope if v != pivot}
        rest = tuple(sorted(remaining, key=rank.__getitem__))
        width = max(width, len(rest))
        offsets = {v: j for j, v in enumerate((pivot, *rest))}
        indexed = [(f, tuple(offsets[v] for v in f.scope)) for f in factors]
        projected = []
        choose_true = []
        for mask in range(1 << len(rest)):
            count = [1, 1]
            for table, positions in indexed:
                for bit in (0, 1):
                    count[bit] *= table.access((mask << 1) | bit, positions)
            projected.append(count[0] + count[1])
            choose_true.append(count[0] == 0 and count[1] > 0)
        trace.append((pivot, rest, choose_true))
        route(Table(rest, projected))
        buckets[i] = []

    if constant == 0:
        return 0, None, width
    assignment = {}
    for pivot, later, choices in reversed(trace):
        mask = sum(int(assignment[v]) << j for j, v in enumerate(later))
        assignment[pivot] = choices[mask]
    assert satisfies(formula, assignment)
    return constant, assignment, width


def check(formula, order):
    names = sorted({v for clause in formula for v, _ in clause})
    direct = sum(satisfies(formula, dict(zip(names, bits))) for bits in product((False, True), repeat=len(names)))
    count, model, _ = solve(formula, order)
    assert count == direct and (model is not None) == (direct > 0)
    if model is not None:
        assert set(model) == set(names) and satisfies(formula, model)


if __name__ == '__main__':
    # All subsets of the nine normalized clauses on two possible variables, including the empty clause.
    clauses = [[(v, bit) for v, bit in enumerate(pattern) if bit is not None]
               for pattern in product((None, False, True), repeat=2)]
    runs = 0
    for flags in product((False, True), repeat=len(clauses)):
        formula = [c for flag, c in zip(flags, clauses) if flag]
        names = sorted({v for c in formula for v, _ in c})
        check(formula, names)
        check(formula, list(reversed(names)))
        runs += 2
    rng = Random(120246)
    for _ in range(400):
        population = [2**(17*i)+i for i in range(rng.randrange(1, 9))]
        formula = [[(rng.choice(population), bool(rng.randrange(2))) for _ in range(rng.randrange(6))]
                   for _ in range(rng.randrange(20))]
        names = sorted({v for c in formula for v, _ in c})
        rng.shuffle(names)
        check(formula, names)
        runs += 1
    chain = [[(i, False), (i+1, True)] for i in range(255)]
    assert solve(chain, range(256))[::2] == (257, 1)
    chain += [[(0, True)], [(255, False)]]
    assert solve(chain, range(256)) == (0, None, 1)
    star = [[(0, False), (i, True)] for i in range(1, 12)]
    middle_first = solve(star, range(12))
    leaves_first = solve(star, [*range(1, 12), 0])
    assert middle_first[0] == leaves_first[0] == 2049
    assert (middle_first[2], leaves_first[2]) == (11, 1)
    print(runs, 'exhaustive-oracle comparisons passed. 256-variable chain and 12-variable star passed.')
