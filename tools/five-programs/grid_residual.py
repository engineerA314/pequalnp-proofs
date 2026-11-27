"""Extract and test distinguishable residuals for any variable order on an even square grid."""
from itertools import combinations, permutations
from random import Random
from residual_sat import normalize


def neighbors(a,b):
    return abs(a[0]-b[0])+abs(a[1]-b[1])==1


def edges(m):
    return [((i,j),(i+di,j+dj)) for i in range(m) for j in range(m)
            for di,dj in ((1,0),(0,1)) if i+di<m and j+dj<m]


def certificate(m,order):
    if m<2 or m%2:
        raise ValueError("the grid side must be positive and even")
    if len(order)!=m*m or set(order)!={(i,j) for i in range(m) for j in range(m)}:
        raise ValueError("supply every grid vertex exactly once")
    time = {v:t for t,v in enumerate(order)}
    finishes = [max(time[i,j] for j in range(m)) for i in range(m)]
    cut = min(finishes)
    row = finishes.index(cut)
    before = set(order[:cut+1])
    untouched = any(all((i,j) not in before for j in range(m)) for i in range(m))
    selected = range(0 if untouched else 1-row%2,m,2)
    pairs = []
    for i in selected:
        line = [(j,i) if untouched else (i,j) for j in range(m)]
        u,v = next((u,v) for u,v in zip(line,line[1:]) if (u in before)!=(v in before))
        pairs.append((u,v) if u in before else (v,u))
    ends = [v for pair in pairs for v in pair]
    assert len(set(ends))==m and all(u in before and v not in before for u,v in pairs)
    assert sum(neighbors(a,b) for a,b in combinations(ends,2)) == m//2
    return before,pairs


def check():
    rng = Random(345634)
    tests = 0
    for m in (2,4,6,8,16,32):
        vertices = [(i,j) for i in range(m) for j in range(m)]
        samples = permutations(vertices) if m==2 else [vertices,list(reversed(vertices))]+[rng.sample(vertices,len(vertices)) for _ in range(40)]
        for order in samples:
            before,pairs = certificate(m,list(order))
            graph = edges(m)
            if m<=8:
                forms = set()
                for mask in range(1<<len(pairs)):
                    zero = {u for i,(u,_) in enumerate(pairs) if mask>>i&1}
                    remaining = []
                    for e in graph:
                        if any(v in before-zero for v in e):
                            continue
                        remaining.append([(v,True) for v in e if v not in before])
                    form = normalize(remaining)
                    assert form not in forms
                    forms.add(form)
                    for i,(_,v) in enumerate(pairs):
                        assert all(any(name!=v for name,_ in clause) for clause in form) == (not bool(mask>>i&1))
            tests += 1
    rectangles = 0
    for r in range(1,13):
        for c in range(1,13):
            order = [(i,j) for i in range(r) for j in range(c)]
            rng.shuffle(order)
            side = 2*(min(r,c)//2)
            if side:
                restriction = [v for v in order if v[0]<side and v[1]<side]
                before,pairs = certificate(side,restriction)
                stop = order.index(restriction[len(before)-1])+1
                full_prefix = set(order[:stop])
                assert len(pairs)==min(r,c)//2
                assert all(u in full_prefix and v not in full_prefix for u,v in pairs)
            rectangles += 1
    print(f"certificates checked for {tests} square orders and {rectangles} rectangular orders")
    print("the square cases include all 24 variable orders on the 2 by 2 grid")
    print("every selected residual and singleton suffix verified directly on grids through 8 by 8")


if __name__ == "__main__":
    check()
