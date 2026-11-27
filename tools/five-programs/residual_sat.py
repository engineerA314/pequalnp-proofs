"""Exact raw CNF count and model by merging normalized residual clause sets."""
from itertools import product
from random import Random

from three_colour_word import encode, parse


def normalize(clauses):
    proper = set()
    for clause in clauses:
        c = frozenset(clause)
        if not c:
            return frozenset({c})
        if not any((v, not s) in c for v, s in c):
            proper.add(c)
    keep = []
    for c in sorted(proper, key=len):
        if not any(d <= c for d in keep):
            keep.append(c)
    return frozenset(keep)


def branch(formula, name, bit):
    return normalize(c - {(name, not bit)} for c in formula if (name, bit) not in c)


def solve(formula, order=None):
    """Return the count, a model over every original variable, and the peak state count."""
    names = {v for c in formula for v, _ in c}
    order = sorted(names) if order is None else list(order)
    if set(order) != names or len(order) != len(names):
        raise ValueError("the order must contain each original variable exactly once")
    states = {normalize(formula): (1, 0)}
    peak = 1
    for i, name in enumerate(order):
        updated = {}
        for state, (mass, example) in states.items():
            for bit in (False, True):
                child = branch(state, name, bit)
                if child in updated:
                    total, prior = updated[child]
                    updated[child] = (total + mass, prior)
                else:
                    updated[child] = (mass, example | (int(bit) << i))
        states = updated
        peak = max(peak, len(states))
    count, bits = states.get(frozenset(), (0, 0))
    model = {v: bool((bits >> i) & 1) for i, v in enumerate(order)} if count else None
    return count, model, peak


def solve_word(word, order=None):
    formula = parse(word)
    return (0, None, 0) if formula is None else solve(formula, order)


def satisfies(formula, x):
    return all(any(x[v] == b for v,b in c) for c in formula)


def check():
    rng = Random(27001)
    for _ in range(800):
        names = [1009*i+3 for i in range(rng.randrange(1,10))]
        formula = [[(rng.choice(names),bool(rng.randrange(2))) for _ in range(rng.randrange(6))]
                   for _ in range(rng.randrange(15))]
        order = list(dict.fromkeys(v for c in formula for v,_ in c))
        rng.shuffle(order)
        count, model, _ = solve_word(encode(formula),order)
        direct = sum(satisfies(formula,dict(zip(order,bits))) for bits in product((False,True),repeat=len(order)))
        assert count == direct
        assert (model is not None) == bool(count)
        if model is not None:
            assert set(model) == set(order) and satisfies(formula,model)
    assert solve_word(bytes([1])) == (0,None,0)
    assert solve_word(bytes([0,1])) == (0,None,0)
    k, b = 72, 60
    formula = [[(i,True)] + [(j,True) for j in range(k,k+b)] for i in range(k)]
    count, model, peak = solve_word(encode(formula),range(k+b))
    assert count == 2**(k+b)-2**k+1 and peak == 2 and satisfies(formula,model)
    print(f"800 random counts and witnesses verified; malformed words rejected")
    print(f"{k+b} variables, {k} clauses, {2**k} prefix masks, peak {peak} residual states, count {count}")


if __name__ == "__main__":
    check()
