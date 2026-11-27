"""Check the two-parent feasibility criterion using exhaustive color assignments."""
from itertools import combinations, product


def check():
    n = 4
    ids = set(range(n))
    subsets = [set(s) for r in range(n+1) for s in combinations(sorted(ids),r)]
    feasible = 0
    for h in range(1,n+1):
        for R in subsets:
            if len(R)>h:
                continue
            fixed = dict(zip(sorted(R),range(len(R))))
            remaining = sorted(ids-R)
            # Every injective assignment on R is equivalent under a permutation of holes.
            choices = []
            for rest in product(range(h),repeat=len(remaining)):
                g = {**fixed, **dict(zip(remaining, rest))}
                choices.append({i for i,S in enumerate(subsets) if len({g[p] for p in S})==len(S)})
            for a,A in enumerate(subsets):
                for b,B in enumerate(subsets):
                    K = (A & B) | (R & (A | B))
                    expected = max(len(A),len(B),len(K)) <= h
                    actual = any(a in good and b in good for good in choices)
                    assert actual == expected
                    feasible += 1
    for holes in range(1,301):
        n = holes + 1
        blocks = [set(range(i,n,3)) for i in range(3)]
        scopes = [set(range(n))-B for B in blocks]
        assert max(map(len,scopes)) == (2*n+2)//3
        assert all(any(p in S and q in S for S in scopes) for p,q in combinations(range(n),2))
    print(f"{feasible} exact overlap-capacity tests; balanced width constructions checked through 300 holes")


if __name__ == "__main__":
    check()
