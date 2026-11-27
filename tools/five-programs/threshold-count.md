# Exact counting for a depth-two threshold circuit with few bottom gates

Let $n$ be the number of inputs of the project's integer threshold circuit and $h$ its number of bottom gates. Splitting an input into halves gives an exact count of its satisfying assignments with

$$2^{\lceil n/2\rceil}\,2^{O(h)}(n+1)^{h+O(1)}$$

arithmetic comparisons and operations, up to polynomial factors in $h$ and the bit length of the encoded circuit. In particular, for $h=o(n/\log(n+2))$ this is $2^{n/2+o(n)}$ for circuits of polynomial encoding length. Negative weights, ties, empty gates and unequal weight-list lengths use the project's precise conventions. The formal identity below covers **all** circuits; the running-time improvement uses the bound on $h$. [Lean theorem on ThrCircuit.satCount](ThresholdSplit.lean) · [Project's general counting target](https://pequalnp.com/lemma#L-clb-024)

This is an implementation and formal specialization of the split-and-list approach. Impagliazzo, Paturi and Schneider used vector domination to obtain depth-two threshold SAT algorithms. Later work gives deterministic exact counting for subquadratically many threshold or symmetric gates with a different time bound. The open project target quantifies over every polynomial encoding bound and uses an explicit machine clock. The Lean proof here establishes the exact counting identity and the recurrence used by the implementation. [Impagliazzo, Paturi and Schneider](https://cseweb.ucsd.edu/~paturi/myPapers/pubs/ImpagliazzoPaturiSchneider_2013_focs.pdf) · [Subquadratic-gate counting algorithm](https://link.springer.com/chapter/10.1007/978-981-96-0668-9_20)

## The two half assignments

For each bottom gate $i$, write $u_i$ for the left score, $v_i$ for the right score and $t_i$ for its threshold. Enumerate the Boolean bottom patterns accepted by the top gate, at most $2^h$. For each such pattern build one point coordinate and one query coordinate per gate.

| Expected output | Point | Query | Condition |
| --- | --- | --- | --- |
| True | $-u_i$ | $v_i-t_i$ | $u_i+v_i\ge t_i$ |
| False | $u_i$ | $t_i-1-v_i$ | $u_i+v_i<t_i$ |

The pattern holds exactly when the point is at most the query in every coordinate. Different patterns cover disjoint full assignments. Repeated half-score vectors may be grouped by multiplicity. Each dominating pair contributes the product of its two multiplicities.

To count pairs in $h$ dimensions, sort by the last coordinate, placing all points before queries at equal values. Split that order in half. Count pairs entirely on either side in $h$ dimensions. Count low-point, high-query pairs in $h-1$ dimensions. A high point cannot be dominated by a low query. In one dimension a prefix sum counts all pairs. For $M$ input events the split tree has at most $\lceil\log_2 M\rceil$ levels and at each level the cross subproblems use at most $M$ events in aggregate. Induction gives $2^{O(h)}M(1+\log M)^{h+O(1)}$ operations, including sorting; here $M\le 2^{\lfloor n/2\rfloor}+2^{\lceil n/2\rceil}$. Intermediate scores and multiplicities have polynomial bit length. [Weighted split lemma](DominancePairs.lean) · [Executable counting algorithm](threshold_count.py)

## Replay

The implementation matched exhaustive enumeration on 240 small circuits and a direct double loop on 180 weighted dominance inputs, including ties. For a 40-input circuit with signed top and bottom weights it found **294,436,232,113** satisfying assignments out of $2^{40}$; an independent sum of binomial coefficients gives the same integer. Run `python3 tools/five-programs/threshold_count.py` from the repository root. From `lean/` run

```sh
lake build PEqualNP.Defs.CircuitLowerBounds
for mod in ThresholdSplit DominancePairs; do
  lake env lean -R ../tools/five-programs -o ".lake/build/lib/lean/$mod.olean" "../tools/five-programs/$mod.lean" && lake env leanchecker -v "$mod" || exit 1
done
```
