# Conjugation and the first two derivatives of the permanent

Let $J$ be the $n$-by-$n$ all-ones matrix and let $L$ be a complex linear space with $\operatorname{per}(J+t)=n!$ for all $t\in L$. For every $n\ge1$,
$$\dim_{\mathbb C}(L\cap\overline L)\le 2n-2.$$
In particular, this gives a linear bound for conjugation-stable level spaces. If $L$ is spanned by this intersection and at most $r$ more directions, then $\dim L\le2n-2+r$. Relative to the full complex target, any excess dimension requires at least as many independent exceptional directions. The argument gives no universal bound on their number. [Dimension and exceptional directions](PermanentConjugateBound.lean) · [Project L-gct-086](https://pequalnp.com/lemma#L-gct-086)

The first derivative forces the sum of all entries to vanish. The second forces the sum of products on ordered pairs in different rows and columns to vanish. These implications are proved directly from the project's permanent polynomial using permutation counts. On doubly centered matrices the quadratic form is the sum of the squared entries. Polarization makes the bilinear dot product zero on the doubly centered part of $L$. For $t\in L\cap\overline L$, taking the other argument to be $\overline t$ produces $\sum|t_{ij}|^2=0$ when $t$ is doubly centered. The first $n-1$ row sums and the first $n-1$ column sums therefore determine every member of the intersection. The rectangular version uses $p+q-2$ coordinates and both moment hypotheses. [Derivatives at J](PermanentJetOnes.lean) · [Conjugation and positivity](ConjugateMatrixCore.lean) · [Previous real-matrix bound](https://pequalnp.com/lemma#L-gct-158)

**The two derivative conditions alone allow dimension exactly $2n-2$ for every $n\ge3$.** Take $u=\sqrt{n(n-1)/2}(1,-1,0,\ldots)$ and $v=\sqrt{n(n-1)/6}(1,1,-2,0,\ldots)$. Let $a,b$ vary independently over the sum-zero vectors. The array $T_{ij}=a_i+b_j+u_i a_j+v_i b_j$ has row sums $n a_i$ and column sums $n b_j$, so it determines the two parameters. The equal squared lengths and orthogonality of $u,v$ force the quadratic condition. The image is complex-linear and stable under conjugation. [Frame identity](JetIsotropicFrame.lean) · [Coefficients](JetFrameCoefficients.lean) · [Exact dimension](JetMaximalExample.lean)

A single explicit direction exhibits the missing cubic information at every size. Take $a=(1,1,-2,0,\ldots)$ and $b=0$. The permanent along this line is exactly
$$\operatorname{per}(J+xT)=n!\,(1-8x^3) \qquad (x\in\mathbb C).$$
At $x=1/2$ it is zero. Thus the first two derivatives miss a counterexample even in a maximal-dimensional conjugation-stable space. The exact identity follows by averaging the two exceptional rows over distinct column positions. An independent subset-DP calculation checks 60 exact values for sizes 3 through 12. [Pair average](PermutationPairAverage.lean) · [All-size cubic identity](JetCubicEscape.lean) · [Exact-arithmetic check](jet_cubic.py)

Replay from `lean/` in this branch.

```sh
lake build PEqualNP.Gct.Helpers.PermHessian PEqualNP.Gct.Helpers.OrderConditions PEqualNP.Gct.Helpers.RealLevel PEqualNP.Gct.Helpers.LevelLow
for m in PermanentJetOnes ConjugateMatrixCore PermanentConjugateBound JetIsotropicFrame JetFrameCoefficients JetMaximalExample PermutationPairAverage JetCubicEscape
do
  lake env lean -R ../tools/five-programs -o ".lake/build/lib/lean/$m.olean" "../tools/five-programs/$m.lean" && lake env leanchecker -v "$m" || exit 1
done
python3 ../tools/five-programs/jet_cubic.py
```
