# Counting threshold circuits by signed input columns

Read each input position as its column of bottom-gate weights, padding short gate rows with zeroes. Group nonzero columns that are identical up to a common sign. If there are $z$ all-zero columns and $d$ nonzero groups with multiplicities $m_1,\ldots,m_d$, the exact number of score vectors that the algorithm visits, with multiplicities kept separately, is bounded by

$$Q=\prod_{j=1}^{d}(m_j+1).$$

The algorithm enumerates exactly $Q$ count vectors; different count vectors can still give the same score. It works for arbitrarily many bottom gates, large signed weights and ties at either level. For polynomial-size circuit encodings it uses $Q\,\mathrm{poly}(n,|C|)$ bit operations. When $n-d=\omega(\log n)$ this is a superpolynomial saving over $2^n$. When $d=o(n)$ it is $2^{o(n)}$. These conditions concern the input weights and need to be shown for any proposed application of the counting-to-lower-bounds method. [Exact theorem on the project circuit](ProfileThreshold.lean) · [Unrestricted project target](https://pequalnp.com/lemma#L-clb-024)

In a group with representative column $v_j$, flip the input bits with negative orientation. If $k_j$ bits are true in the resulting group and the original group had $a_j$ negative columns, its contribution to the bottom-score vector is $(k_j-a_j)v_j$. Exactly $\binom{m_j}{k_j}$ assignments give this group count. Evaluate the top gate once for each combination, sum products of the binomial multiplicities for the accepting ones, and multiply by $2^z$. The formal proof constructs a bijection on actual assignments, accounts for padded weight lists and counts each fiber. [Binomial fiber sizes](ProfileMass.lean) · [Executable algorithm](profile_count.py)

For $m\ge1$, $(m+1)/2^m\le(3/4)^{m-1}$. Multiplying and accounting for zero columns gives $Q/2^n\le(3/4)^{n-d}$. Also $Q\le(1+(n-z)/d)^d$ for $d>0$ by arithmetic–geometric mean, which gives the subexponential regime. With $d=0$, the circuit is evaluated once. For comparison, the [split-and-list implementation](threshold-count.md) uses the number of bottom gates as its parameter. General subquadratic-gate results have different hypotheses. [General depth-two counting study](https://eccc.weizmann.ac.il/report/2016/100/)

The executable passed 600 exhaustive-enumeration checks. For 512 inputs and 257 distinct thresholds on a signed score, it visits 481 count vectors. The accepted count agrees with an independent symmetry calculation, $2^{32}(2^{480}+\binom{480}{240})/2$. It also tests 2,049-bit weights with an exact threshold equality. Run `python3 tools/five-programs/profile_count.py`.

Rebuild [ThresholdSplit](threshold-count.md) first, then from the repository's `lean/` directory run

```sh
for module in ProfileMass ProfileThreshold; do
  lake env lean -R ../tools/five-programs -o ".lake/build/lib/lean/$module.olean" "../tools/five-programs/$module.lean" && lake env leanchecker -v "$module" || exit 1
done
```
