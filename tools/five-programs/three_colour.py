"""Row-major 3-SAT to 3-colouring reduction and independent round-trip tests."""

from itertools import product
from random import Random


def reduce_formula(n, clauses):
    """Literal (i,b) is true at an assignment exactly when assignment[i] equals b."""
    m = len(clauses)
    size = 3+2*n+8*m
    matrix = [bytearray(size) for _ in range(size)]

    def edge(i,j):
        assert i!=j
        matrix[i][j] = matrix[j][i] = 1

    def literal(var,polarity):
        return 3+2*var+int(polarity)

    def triangle(ids,feeds=None):
        for a,b in ((0,1),(0,2),(1,2)):
            edge(ids[a],ids[b])
        if feeds is not None:
            for i,f in zip(ids,feeds):
                edge(i,f)

    triangle([0,1,2])
    for var in range(n+m):
        edge(literal(var,False),2)
        edge(literal(var,True),2)
        edge(literal(var,True),literal(var,False))
    for i,clause in enumerate(clauses):
        if len(clause)!=3 or any(v<0 or v>=n for v,_ in clause):
            raise ValueError("Every clause needs three signed input variables in range.")
        a,b,c = [literal(v,sign) for v,sign in clause]
        first = 3+2*(n+m)+6*i
        triangle(range(first,first+3),[a,b,literal(n+i,True)])
        triangle(range(first+3,first+6),[literal(n+i,False),c,0])
    return b"".join(matrix)


def solve_graph(word,side):
    """Exact backtracking chooses the vertex with fewest remaining colours."""
    assert len(word)==side*side
    neighbors = [[j for j in range(side) if word[i*side+j]] for i in range(side)]
    colors = [-1]*side
    # Fix the three palettes to eliminate six equivalent permutations.
    colors[:3] = range(3)
    def visit(vertices):
        if not vertices:
            return True
        first = min(vertices)
        component = {first}
        stack = [first]
        while stack:
            for w in neighbors[stack.pop()]:
                if w in vertices and w not in component:
                    component.add(w)
                    stack.append(w)
        if len(component)<len(vertices):
            return visit(component) and visit(vertices-component)
        best = None
        for v in vertices:
            options = set(range(3))-set(colors[w] for w in neighbors[v])
            if not options:
                return False
            candidate = (len(options),2 not in neighbors[v],-len(neighbors[v]),v,sorted(options))
            if best is None or candidate<best:
                best = candidate
        _,_,_,v,options = best
        baseline = colors[:]
        for c in options:
            colors[v] = c
            if visit(vertices-{v}):
                return True
            colors[:] = baseline
        return False
    if not visit(set(range(3,side))):
        return None
    assert all(colors[i]!=colors[j] for i in range(side) for j in neighbors[i])
    return colors


def check(n, clauses):
    def satisfies(a):
        return all(any(a[i]==sign for i,sign in c) for c in clauses)
    expected = any(satisfies(a) for a in product((False,True),repeat=n))
    side = 3+2*n+8*len(clauses)
    word = reduce_formula(n,clauses)
    assignment = solve_graph(word,side)
    assert (assignment is not None)==expected
    if assignment is not None:
        assert satisfies([assignment[3+2*i+1]==assignment[1] for i in range(n)])
    return int(expected)


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run without -O so the checks remain active.")
    cases = sat = 0
    for n in range(3):
        literals = list(product(range(n),(False,True)))
        triples = list(product(literals,repeat=3))
        for length in range(3):
            for clauses in product(triples,repeat=length):
                sat += check(n,clauses)
                cases += 1
    rng = Random(314)
    for _ in range(110):
        n = rng.randrange(1,7)
        clauses = [[(rng.randrange(n),bool(rng.getrandbits(1))) for _ in range(3)]
                   for _ in range(rng.randrange(2,13))]
        sat += check(n,clauses)
        cases += 1
    # Every assignment to three bits violates exactly one of these eight clauses.
    blocker = [list(enumerate(bits)) for bits in product((False,True),repeat=3)]
    assert not check(3,blocker)
    assert all(check(3,blocker[:i]+blocker[i+1:]) for i in range(8))
    print(f"{cases+9} graph/formula round trips, {sat+8} satisfiable and {cases+1-sat} unsatisfiable")
