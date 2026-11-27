"""Replay the critical assignments for bit pigeonhole and the tight ordinary-resolution family."""
from itertools import combinations
from math import comb


def bit_pigeonhole(holes):
    sources = [(i, j, a) for i, j in combinations(range(holes + 1), 2) for a in range(holes)]
    for left, right, target in sources:
        remaining = iter(h for h in range(holes) if h != target)
        model = [target if p in (left, right) else next(remaining) for p in range(holes + 1)]
        false_sources = [(i, j, a) for i, j, a in sources if model[i] == model[j] == a]
        assert false_sources == [(left, right, target)]
    assert len(sources) == holes * comb(holes + 1, 2)
    return len(sources)


def implication_chain(links):
    pos = lambda i: frozenset({(i, True)})
    neg = lambda i: frozenset({(i, False)})
    edges = [neg(i) | pos(i + 1) for i in range(links)]
    inputs = [pos(0), *edges, neg(links)]
    for omitted in range(len(inputs)):
        model = [i < omitted for i in range(links + 1)]
        unsatisfied = [j for j, clause in enumerate(inputs)
                       if not any(model[v] == polarity for v, polarity in clause)]
        assert unsatisfied == [omitted]
    proof = [pos(0)]
    for i, edge in enumerate([*edges, neg(links)]):
        unit = proof[-1]
        assert unit == pos(i) and neg(i) <= edge
        proof.extend([edge, (unit - pos(i)) | (edge - neg(i))])
    assert proof[-1] == frozenset() and len(proof) == 2 * len(inputs) - 1


if __name__ == '__main__':
    holes_to_axioms = {h: bit_pigeonhole(h) for h in (2, 4, 8, 16)}
    for n in range(65):
        implication_chain(n)
    print('Critical assignments checked by hole count:', holes_to_axioms)
    print('65 exact-length ordinary-resolution proofs verified')
