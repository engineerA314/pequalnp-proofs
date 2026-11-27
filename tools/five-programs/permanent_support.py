"""Exact coefficient support and integer witnesses for rank-one permanent families."""

from collections import defaultdict
from itertools import product
from math import factorial
from random import Random


def linear_product(rows, d):
    """Multiply the n affine row factors over the integers."""
    terms = {(0,)*d:1}
    for row in rows:
        if len(row)!=d:
            raise ValueError("Wrong number of row coordinates.")
        new = defaultdict(int,terms)
        for key,value in terms.items():
            for i,coefficient in enumerate(row):
                if coefficient:
                    exp = key[:i]+(key[i]+1,)+key[i+1:]
                    new[exp] += value*coefficient
        terms = {exp:v for exp,v in new.items() if v}
    return terms


def difference_terms(left,right,d):
    if len(left)!=len(right):
        raise ValueError("The permanent requires equally many rows and columns.")
    n = len(left)
    a,b = linear_product(left,d),linear_product(right,d)
    terms = {}
    for exp in a.keys() & b.keys():
        if not any(exp):
            continue
        factor = factorial(n-sum(exp))
        for e in exp:
            factor *= factorial(e)
        terms[exp] = factor*a[exp]*b[exp]
    return terms


def witness(terms,n,d):
    """Preserve a nonzero coefficient after each integer substitution."""
    if not terms:
        return None
    parameters = []
    for _ in range(d):
        for c in range(n+1):
            special = defaultdict(int)
            for (e,*rest),v in terms.items():
                special[tuple(rest)] += v*c**e
            special = {k:v for k,v in special.items() if v}
            if special:
                parameters.append(c)
                terms = special
                break
        else:
            raise AssertionError("Finite hitting grid lost a nonzero polynomial.")
    return tuple(parameters),terms[()]


def direct(left,right,parameters):
    n = len(left)
    matrix = [[1+sum(c*x*y for c,x,y in zip(parameters,u,v)) for v in right] for u in left]
    # Subset dynamic programming for the permanent, independent of the support formula.
    dp = [0]*(1<<n)
    dp[0] = 1
    for mask in range(1,1<<n):
        row = bin(mask).count("1")-1
        available = mask
        while available:
            bit = available & -available
            available -= bit
            dp[mask] += matrix[row][bit.bit_length()-1]*dp[mask-bit]
    return dp[-1]


def check(left,right,d,complete):
    n = len(left)
    terms = difference_terms(left,right,d)
    found = witness(terms,n,d)
    if found:
        c,t = found
        assert t and direct(left,right,c)-factorial(n)==t
    if complete:
        outcome = False
        for c in product(range(n+1),repeat=d):
            symbolic = sum(v*monomial(c,a) for a,v in terms.items())
            assert symbolic==direct(left,right,c)-factorial(n)
            outcome |= bool(symbolic)
        assert outcome==(found is not None)
    return found


def monomial(c,exp):
    v = 1
    for x,k in zip(c,exp):
        v *= x**k
    return v


if __name__=="__main__":
    if not __debug__:
        raise SystemExit("Run without -O so assertions stay active.")
    rng = Random(3127)
    cases = yes = grids = 0
    for n in range(7):
        for d in range(4):
            for trial in range(7):
                left = [[rng.choice((-1,0,1)) for _ in range(d)] for _ in range(n)]
                right = left if trial==0 else [[rng.choice((-1,0,1)) for _ in range(d)] for _ in range(n)]
                complete = (n<=4 or d<=2)
                result = check(left,right,d,complete)
                yes += result is not None
                cases += 1
                grids += (n+1)**d if complete else 0
                if trial==0 and any(any(row) for row in left):
                    assert result is not None
    # Both coordinate axes are level. The mixed coefficient finds the first failure.
    for n in range(2,13):
        left = [[int(j==i) for i in range(2)] for j in range(n)]
        right = [[int(j==0)-int(j==1)]*2 for j in range(n)]
        found = check(left,right,2,n<=4)
        assert found==((1,1),-2*factorial(n-2))
        assert direct(left,right,(1,0))==direct(left,right,(0,1))==factorial(n)
    print(f"{cases} deterministic families, {yes} nonconstant; {grids} grid evaluations cross-checked")
    print("Two individually level directions have a mixed obstruction at (1,1) for n=2 through 12.")
