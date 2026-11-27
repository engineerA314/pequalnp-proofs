"""Exact rank screening and integer probes for a span of Gaussian-rational matrices."""
from fractions import Fraction
from functools import reduce
from math import factorial, gcd, lcm


def reduce_rows(rows, columns):
    m = [[Fraction(x) for x in row] for row in rows]
    pivots = []
    for c in range(columns):
        active = len(pivots)
        pos = next((j for j in range(active,len(m)) if m[j][c]),None)
        if pos is None:
            continue
        m[active], m[pos] = m[pos], m[active]
        a = m[active][c]
        m[active] = [x/a for x in m[active]]
        for j,row in enumerate(m):
            if j != active and row[c]:
                scale = row[c]
                m[j] = [y-scale*x for y,x in zip(row,m[active])]
        pivots.append(c)
    return m,pivots


def nullspace(rows, cols):
    form, pivots = reduce_rows(rows,cols)
    for c in range(cols):
        if c not in pivots:
            x = [Fraction(0)]*cols
            x[c] = 1
            for i,p in enumerate(pivots):
                x[p] = -form[i][c]
            yield x


def apply(rows,x):
    return [sum(a*b for a,b in zip(r,x)) for r in rows]


def permanent(n,flat):
    states = {0:1}
    for i in range(n):
        updated = {}
        for mask,score in states.items():
            for j in range(n):
                if not mask & (1<<j):
                    bit = mask | (1<<j)
                    updated[bit] = updated.get(bit,0)+score*flat[i*n+j]
        states = updated
    return states[(1<<n)-1]


def certificate(n,generators):
    if n<2 or any(len(v)!=n*n for v in generators):
        raise ValueError("expected square matrices with n at least two")
    # Coefficients are ordered as the real parts of all parameters, then the imaginary parts.
    d = len(generators)
    re,im = [],[]
    for j in range(n*n):
        r = [Fraction(v[j][0]) for v in generators]
        s = [Fraction(v[j][1]) for v in generators]
        re.append(r+[-x for x in s])
        im.append(s+r)
    ambient_rank = len(reduce_rows(re+im,2*d)[1])
    dimension, rem = divmod(ambient_rank,2)
    assert rem == 0
    joined = len(reduce_rows(re,2*d)[1])
    core = 2*dimension-joined
    if core <= 2*n-2:
        return dimension, joined, None
    found = None
    for x in nullspace(im,2*d):
        t = apply(re,x)
        if sum(t):
            found = x,t,"linear"
            break
    if found is None:
        sums = [[sum(re[i*n+j][c] for j in range(n)) for c in range(2*d)] for i in range(n)]
        sums += [[sum(re[i*n+j][c] for i in range(n)) for c in range(2*d)] for j in range(n)]
        for x in nullspace(im+sums,2*d):
            t = apply(re,x)
            if any(t):
                found = x,t,"quadratic"
                break
    assert found is not None
    x,t,kind = found
    scale = reduce(lcm,(v.denominator for v in t),1)
    entries = [int(scale*v) for v in t]
    div = reduce(gcd,map(abs,entries),0)
    t = [v//div for v in entries]
    x = [Fraction(scale,div)*v for v in x]
    assert apply(re,x)==t and not any(apply(im,x))
    if kind == "quadratic":
        assert all(sum(t[i*n:(i+1)*n]) == 0 for i in range(n))
        assert all(sum(t[i*n+j] for i in range(n)) == 0 for j in range(n))
    for s in range(1,n+1):
        value = permanent(n,[1+s*v for v in t])
        if value != factorial(n):
            return dimension, joined, (kind,x,t,s,value)
    raise AssertionError("the finite probe theorem guarantees a different value")


def example(n,centered_total,extra):
    """Real differences plus an unpaired complex direction, allowing redundant generators."""
    size = n*n
    def direction(j,phase):
        v = [(0,0)]*size
        v[j] = phase
        if centered_total:
            v[-1] = tuple(-x for x in phase)
        return v
    generators = [direction(j,(0,1) if j%2 else (1,1)) for j in range(2*n-1)]
    if extra and 2*n < size-1:
        a,b = direction(2*n-1,(1,0)), direction(2*n,(0,1))
        generators.append([(x+u,y+v) for (x,y),(u,v) in zip(a,b)])
    return generators+[generators[0]]


def check():
    for n in range(2,8):
        for zeros in (True,False):
            dim, joined, out = certificate(n,example(n,zeros,True))
            assert out is not None and 2*dim-joined>2*n-2
            assert out[0] == ("quadratic" if zeros else "linear")
        assert certificate(n,[])[2] is None
    d,r,(kind,_,t,s,v) = certificate(4,example(4,True,True))
    print(f"12 rank failures and 6 empty spans checked, dimension={d}, joined rank={r}, kind={kind}")
    print(f"4 by 4 integer direction {t}, probe {s}, permanent {v} versus {factorial(4)}")


if __name__ == "__main__":
    check()
