"""Project-format binary 3-SAT to the row-major graph predicate, with sparse variable IDs."""
from itertools import product
from math import isqrt
from random import Random
from three_colour import reduce_formula, solve_graph


def encode(formula):
    word = bytearray()
    for clause in formula:
        for var, sign in clause:
            if var < 0:
                raise ValueError('Variables are natural numbers.')
            word.extend((1, int(sign)))
            while var:
                word.extend((1, var & 1))
                var >>= 1
            word.extend((0, 1))
        word.extend((0, 0))
    return bytes(word)


def parse(word):
    if len(word) % 2:
        return None
    formula, clause, digits = [], [], []
    for flag, bit in zip(word[::2], word[1::2]):
        if bit not in (0, 1) or flag not in (0, 1):
            return None
        if flag:
            digits.append(bit)
        elif bit:
            if not digits or (len(digits) > 1 and digits[-1] == 0):
                return None
            var = sum(d << i for i, d in enumerate(digits[1:]))
            clause.append((var, bool(digits[0])))
            digits.clear()
        else:
            if digits:
                return None
            formula.append(clause)
            clause = []
    return None if digits or clause else formula


def reduce_word(word):
    formula = parse(word)
    if formula is None or any(len(c) not in (1, 2, 3) for c in formula):
        return bytes([1])
    occurrences = [v for c in formula for v, _ in c]
    names = list(reversed(dict.fromkeys(reversed(occurrences))))
    code = {v: i for i, v in enumerate(names)}
    triples = [[(code[v], b) for v, b in c + [c[-1]]*(3-len(c))] for c in formula]
    return reduce_formula(len(names)+1, triples)


def graph_accepts(word):
    side = isqrt(len(word))
    if side * side != len(word) or any(word[i*side+i] for i in range(side)):
        return False
    return solve_graph(word, side) is not None


def brute(formula):
    names = sorted({v for c in formula for v, _ in c})
    for bits in product((False, True), repeat=len(names)):
        assignment = dict(zip(names, bits))
        if all(any(assignment[v] == b for v, b in clause) for clause in formula):
            return True
    return False


if __name__ == '__main__':
    nwords = valid = 0
    for length in range(15):
        for bits in product((0, 1), repeat=length):
            word = bytes(bits)
            formula = parse(word)
            if formula is not None:
                valid += 1
                assert encode(formula) == word
            expected = formula is not None and all(len(c) <= 3 for c in formula) and brute(formula)
            graph = reduce_word(word)
            assert len(graph) <= (5 + 4*length)**2 and graph_accepts(graph) == expected
            nwords += 1

    empty, noncanonical, partial, odd = bytes(), bytes([1,1,1,0,0,1,0,0]), bytes([1,1,0,1]), bytes([0])
    assert [parse(x) for x in (empty, noncanonical, partial, odd)] == [[], None, None, None]
    big = (1 << 2048) + 37
    sample = [[(big, True)], [(big+1, True), (big, False)]]
    output = reduce_word(encode(sample))
    assert len(output) == 25**2 and graph_accepts(output)
    rng = Random(728101)
    for trial in range(250):
        names = [0, 1, big, big+1]
        formula = [[(rng.choice(names), bool(rng.randrange(2))) for _ in range(rng.randrange(5))]
                   for _ in range(rng.randrange(7))]
        word = encode(formula)
        assert parse(word) == formula
        assert graph_accepts(reduce_word(word)) == (all(len(c) <= 3 for c in formula) and brute(formula))
    print(nwords, 'raw words checked,', valid, 'canonical. 250 generated formulas and a 2,049-bit ID checked.')
