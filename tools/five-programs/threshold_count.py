"""Exact #SAT for a depth-two integer threshold circuit by counting dominance pairs."""

from collections import Counter
from itertools import product
from random import Random


def scores(gates,start,stop):
    """Histogram of score vectors for all assignments to this half."""
    states = Counter({(0,)*len(gates):1})
    for pos in range(start,stop):
        column = tuple(row[pos] if pos<len(row) else 0 for row,_,_ in gates)
        nxt = states.copy()
        for key,count in states.items():
            nxt[tuple(x+w for x,w in zip(key,column))] += count
        states = nxt
    return states


def dominance(points, queries, dimensions):
    """Count multiplicities of point <= query, with inclusive integer thresholds."""
    if not points or not queries:
        return 0
    if dimensions==0:
        return sum(w for _,w in points)*sum(w for _,w in queries)
    idx = dimensions-1
    # At a tie all points precede all queries. This also handles a split inside equal keys.
    events = sorted([(v[idx],0,v,w) for v,w in points]+[(v[idx],1,v,w) for v,w in queries])
    if dimensions==1:
        mass = answer = 0
        for _,kind,_,weight in events:
            if kind:
                answer += mass*weight
            else:
                mass += weight
        return answer
    def visit(es):
        if len(es)<=1:
            return 0
        mid = len(es)//2
        low,high = es[:mid],es[mid:]
        lp = [(v,w) for _,k,v,w in low if k==0]
        hq = [(v,w) for _,k,v,w in high if k==1]
        left = visit(low) if lp and len(lp)<len(low) else 0
        right = visit(high) if hq and len(hq)<len(high) else 0
        return left+right+dominance(lp,hq,dimensions-1)
    return visit(events)


def count(gates,top):
    n = max((len(row) for row,_,_ in gates),default=0)
    cut = n//2
    lhs,rhs = scores(gates,0,cut),scores(gates,cut,n)
    answer = 0
    for mask in product((False,True),repeat=len(gates)):
        if sum(weight for on,(_,_,weight) in zip(mask,gates) if on)<top:
            continue
        points = [(tuple(-x if on else x for x,on in zip(xs,mask)),k) for xs,k in lhs.items()]
        queries = [(tuple(y-threshold if on else threshold-1-y
                          for y,on,(_,threshold,_) in zip(ys,mask,gates)),k) for ys,k in rhs.items()]
        answer += dominance(points,queries,len(gates))
    return answer


def direct(gates,top):
    n = max((len(row) for row,_,_ in gates),default=0)
    out = 0
    for x in product((0,1),repeat=n):
        total = sum(weight for row,bound,weight in gates
                    if sum(a*b for a,b in zip(x,row))>=bound)
        out += total>=top
    return out


if __name__=="__main__":
    if not __debug__:
        raise SystemExit("Run without -O so the comparisons remain active.")
    rng = Random(2033)
    tests = 0
    for gates in range(6):
        for n in range(10):
            for _ in range(4):
                c = [([rng.randrange(-4,5) for _ in range(rng.randrange(n+1))],
                      rng.randrange(-5,6),rng.randrange(-4,5)) for _ in range(gates)]
                top = rng.randrange(-6,7)
                assert count(c,top)==direct(c,top)
                tests += 1
    for d in range(6):
        for _ in range(30):
            p = [(tuple(rng.randrange(4) for _ in range(d)),rng.randrange(1,5)) for _ in range(14)]
            q = [(tuple(rng.randrange(4) for _ in range(d)),rng.randrange(1,5)) for _ in range(11)]
            expected = sum(a*b for x,a in p for y,b in q if all(i<=j for i,j in zip(x,y)))
            assert dominance(p,q,d)==expected
    # Forty inputs, with negative, positive and identical bottom columns.
    c = [([1]*40,20,3),([1,-1]*20,0,-2),([-1]*20, -6,2)]
    from math import comb
    check = 0
    for a,b,g,h in product(range(11),repeat=4):
        j = a+b+g+h
        active = 3*(j>=20)-2*(a-b+g-h>=0)+2*(a+b<=6)
        if active>=2:
            check += comb(10,a)*comb(10,b)*comb(10,g)*comb(10,h)
    assert count(c,2)==check
    print(f"{tests} circuits matched exhaustive search, 180 weighted dominance cases matched direct counts")
    print(f"40-input exact count {check} of {2**40}, checked by a separate binomial count")
