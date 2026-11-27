# The cubic and quartic DIV targets on a two-dimensional span

Let $g_i$ be integer polynomials with at most $T$ nonzero coefficients each. Suppose their real span has dimension at most two. If the nonzero polynomial $F=\sum_i s_i g_i^d$, $d\ge1$, is divisible by $(X+1)\cdots(X+N)$, then
$$N\le d(2T-1).$$
There is no bound on the number of summands, their degrees, or their integer weights. In rank two, choose two original generators $A,B$ forming a basis and let $U$ be the union of their exponent supports. The stronger bound $d(|U|-1)$ holds for every finite set of distinct negative real zeros. In rank one the bound is $T-1$. The Lean interfaces accept the two basis polynomials and coefficient coordinates, or a single generator in rank one. [Integer divisibility bridge](SparsePencilDIV.lean) · [Rank one and exponent inequalities](SparsePencilCases.lean)

For L-gct-103 on this class, $N^{25}\le T^{27}$ once $T\ge6^{13}$. For L-gct-104, $N^5\le T^6$ once $T\ge8^5$. Both formal implications use the stronger linear bound. Any counterexample to either target beyond those thresholds therefore needs at least three independent input polynomials. [Cubic target](https://pequalnp.com/lemma#L-gct-103) · [Quartic target](https://pequalnp.com/lemma#L-gct-104)

Write $g_i=a_i A+b_i B$. At a point with $B(x)\ne0$, the ratio $A(x)/B(x)$ is a root of the nonzero univariate polynomial $P(z)=\sum_i s_i(a_i z+b_i)^d$. Its degree is at most $d$. Each ratio gives the sparse fibre $A-rB$, with at most $|U|-1$ negative roots by Descartes' rule of signs. If $\deg P<d$, the possible extra fibre $B=0$ fits within the $d$ available fibres. If $\deg P=d$, a zero with $B(x)=0$ has $A(x)=0$ as well. Such a point belongs to every finite fibre, with the case of no real root of $P$ handled separately. [Projective counting argument](SparsePencilRoots.lean) · [Polynomial chart and leading coefficient](SparsePencilChart.lean) · [Formal sparse root bound](SparseNegativeRoots.lean) · [Mathlib's Descartes theorem](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Polynomial/RuleOfSigns.html)

The support-sensitive constant is attained on consecutive negative integers, using just $A=X,B=1$ and signed powers of affine polynomials. For instance $(2X+4)^3-(X+3)^3-(X+1)^3=6(X+1)(X+2)(X+3)$. A signed quartic example has exactly the roots $-1,-2,-3,-4$. Its integer weights expand as repeated signed summands. Both identities are kernel-checked. An exact Python check also covers 495 nonzero random families across degrees one to six. [Examples](pencil_roots.py)

From `lean/` run

```sh
for m in SparseNegativeRoots SparsePencilChart SparsePencilRoots SparsePencilDIV SparsePencilCases
do
  lake env lean -R ../tools/five-programs -o ".lake/build/lib/lean/$m.olean" "../tools/five-programs/$m.lean" && lake env leanchecker -v "$m" || exit 1
done
python3 ../tools/five-programs/pencil_roots.py
```
