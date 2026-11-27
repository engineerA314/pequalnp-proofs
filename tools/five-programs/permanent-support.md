# Deciding when a rank-one-generated space keeps the permanent constant

Let $u_i,w_i\in\mathbb C^n$ for $1\le i\le d$. Consider the entire affine space of matrices $J+\sum_i c_i u_i w_i^{\mathsf T}$, where $J$ is the all-ones matrix. Form the two polynomials

$$A(z)=\prod_{j=1}^n\left(1+\sum_i u_i(j)z_i\right),\qquad B(z)=\prod_{j=1}^n\left(1+\sum_i w_i(j)z_i\right).$$

The permanent equals $n!$ for every parameter vector $c$ **if and only if** $A$ and $B$ have no common nonconstant monomial with nonzero coefficients. Moreover, when the criterion fails, there is a witness with **every parameter an integer between zero and $n$**, including for complex vectors. In particular, a permanent-level linear space at $J$ contains no nonzero symmetric rank-one direction $uu^{\mathsf T}$. This rules out a class of candidate generators at every order; a symmetric space can still have only higher-rank nonzero matrices. [Converse theorem](PermanentSupport.lean) · [Finite grid](PermanentGrid.lean) · [Symmetric directions](PermanentSymmetric.lean)

The starting point is the project's checked coefficient identity, L-gct-099. The coefficient of the parameter monomial $c^\alpha$ is $(n-|\alpha|)!\,\alpha!\,[z^\alpha]A\,[z^\alpha]B$. Over the complex numbers the factorials are nonzero and equality at every point forces equality of polynomials. That proves necessity. The project already had sufficiency. Each coordinate degree is at most $n$, so a grid of $n+1$ values in every coordinate detects every nonzero difference from $n!$. For $u_i=w_i$ the products coincide. If some $u_i(j)$ is nonzero, setting $z_i=-1/u_i(j)$ and every other coordinate to zero makes a factor vanish. Thus $A$ is nonconstant and its support overlaps itself. [Project coefficient identity](../../lean/PEqualNP/Gct/L099.lean) · [Existing sufficiency proof](../../lean/PEqualNP/Gct/Helpers/SupportCriterion.lean) · [Project's symmetric four-by-four probe](https://pequalnp.com/lemma#L-gct-231)

For integer data the executable constructs $A,B$ exactly. For a nonzero difference polynomial it tries $0,\ldots,n$ in the first unassigned coordinate and keeps a value that leaves some coefficient nonzero. Repeating this makes at most $d(n+1)$ polynomial specializations, even though the full grid has $(n+1)^d$ elements. Building or storing the sparse polynomials can still be exponential in the number of generators. The final witness is verified by an independent subset dynamic program on the numerical matrix. [Exact checker and witness extractor](permanent_support.py)

For example, take $u_1=e_1,u_2=e_2,w_1=w_2=e_1-e_2$ at any $n\ge2$. Each generator alone keeps the permanent constant. Together the difference is $-2(n-2)!c_1c_2$, and $(1,1)$ witnesses failure. Checking only a basis one direction at a time can miss the obstruction. The replay tests 196 families, including 109 nonconstant ones, and cross-checks 2,800 full-grid values using direct permanent computation. It also verifies this two-direction example for orders 2 through 12.

From the repository root run `python3 tools/five-programs/permanent_support.py`. From `lean/` run

```sh
lake build PEqualNP.Gct.Helpers.SupportCriterion
for mod in PermanentSupport PermanentGrid PermanentSymmetric; do
  lake env lean -R ../tools/five-programs -o ".lake/build/lib/lean/$mod.olean" "../tools/five-programs/$mod.lean" && lake env leanchecker -v "$mod" || exit 1
done
```
