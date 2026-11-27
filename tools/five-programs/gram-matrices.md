# Positive semidefinite directions and the order of contact

Let $J$ be the all-ones matrix and $A$ any $n\times n$ complex Hermitian positive semidefinite matrix. For every real $t>0$,

$$\operatorname{per}(J+tA)=n! \ \Longleftrightarrow\ A=0.$$

For $A\ne0$ the permanent is real and strictly larger than $n!$. In particular any complex linear space on which the permanent stays equal to $n!$ at $J$ contains no nonzero positive semidefinite matrix, of any rank. The probe $t=1$ alone detects all such matrices. This restricts a concrete class of potential members of the project's permanent-level spaces. Their remaining indefinite and non-Hermitian directions still require analysis. [Theorem for mathlib's matrix positivity predicate](GramMatrixLevel.lean) · [Project coefficient identity](../../lean/PEqualNP/Gct/L099.lean)

More generally, let $u_i\in\mathbb C^n$ and attach nonnegative weights $t_i$. The permanent of $J+\sum_i t_i u_i u_i^*$ exceeds $n!$ exactly when at least one positive weight multiplies a nonzero vector. If all these vectors vanish, the matrix equals $J$. The statement allows zero weights, repeated directions and arbitrary dependencies among the columns. [Weighted criterion](GramWeights.lean)

Write $P(z)=\prod_j(1+\sum_i u_i(j)z_i)$. The project’s coefficient formula and complex conjugation give the exact expansion

$$\operatorname{per}\!\left(J+\sum_i t_i u_i u_i^*\right)=\sum_\alpha (n-|\alpha|)!\,\alpha!\,\left|[z^\alpha]P\right|^2\,t^\alpha.$$

Each summand is nonnegative when the weights are nonnegative, and the constant summand is $n!$. For positive weights, a nonzero entry in a generator makes $P$ nonconstant because a single-coordinate substitution can make one of its factors vanish. Factoring an arbitrary positive semidefinite matrix as $X^*X$ transfers this to the whole cone. [Sum of squares and strictness](GramPermanent.lean)

## Why derivatives of low order can miss such a direction

For every $n\ge1$, choose a primitive $n$th root of unity $\zeta$ and $u_j=\zeta^j$ for $0\le j<n$. Then, for **every complex** $t$,

$$\operatorname{per}(J+tuu^*)=n!(1+t^n).$$

Thus at a nonzero rank-one positive semidefinite direction all derivatives through order $n-1$ can agree with a constant, while a single positive evaluation separates it. The project already has the rank-one minor formula and the elementary symmetric sums of roots of unity. Combining them leaves exactly the constant and degree-$n$ terms. The construction attains the largest order of contact possible for a nonconstant permanent along a line. [All-order example](GramContact.lean) · [Project rank-one formula](../../lean/PEqualNP/Gct/Helpers/RankOne.lean) · [Project roots-of-unity identity](../../lean/PEqualNP/Gct/Helpers/Rung/RootsEsymm.lean)

## Replay

The Gaussian-integer checker compares the square-sum expression with a separate subset permanent algorithm on 840 probes, including negative and zero weights. It also tests 33 evaluations of the exact contact examples at orders 1, 2 and 4. Run `python3 tools/five-programs/gram_permanent.py`. [Exact checker](gram_permanent.py)

Rebuild the [permanent support modules](permanent-support.md) first. From the repository's `lean/` directory run

```sh
lake build PEqualNP.Gct.Helpers.RankOne PEqualNP.Gct.Helpers.MincExpansion PEqualNP.Gct.Helpers.Rung.RootsEsymm
for module in GramPermanent GramMatrixLevel GramWeights GramContact; do
  lake env lean -R ../tools/five-programs -o ".lake/build/lib/lean/$module.olean" "../tools/five-programs/$module.lean" && lake env leanchecker -v "$module" || exit 1
done
```
