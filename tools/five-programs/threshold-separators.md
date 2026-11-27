# Exact threshold counting with a supplied input cut

Partition the $n$ inputs of a signed integer depth-two threshold circuit into sets of sizes $a,b$. Let $c$ count bottom gates having a nonzero coefficient on both sides. All other gates may be arbitrarily numerous. There is an exact count using $2^c$ weighted dominance calls in $c+1$ dimensions on at most $N=2^a+2^b$ records per call. The project's padded and truncated weight lists, negative top weights, and equality at thresholds are covered by the formal identity. [Score decomposition](ThresholdCutScores.lean) · [Exact project count and computable classification](ThresholdCutCount.lean)

On a balanced cut and polynomial-size encodings, $c=o(n)$ gives $2^{n/2+o(n)}$ bit operations. In particular, this includes every family with sublinearly many total bottom gates and families with any polynomial number of one-sided gates. For $c\le n/16$, the entropy bound below gives at most $2^{0.846n+o(n)}$. A suitable supplied variable order or a verified permutation of the input columns suffices. The method is conditional on the cut and gives no counting speedup for every circuit in L-clb-024. [Project target](https://pequalnp.com/lemma#L-clb-024)

For a fixed pattern $m$ of the crossing gates, compute the total top weight $W_m$ of its active gates. On each half assignment also compute the sum of top contributions $L$ or $R$ of the one-sided gates. Append the coordinate test $-L\le R+W_m-\theta$ to the $c$ crossing-gate tests, where $\theta$ is the top threshold. Each accepting assignment meets precisely one pattern. Arbitrary binary-encoded top weights cost a single ordered comparison, independently of their range. [Earlier all-gate split](threshold-count.md) · [Vector domination for threshold circuits, Impagliazzo, Paturi and Schneider](https://cseweb.ucsd.edu/~paturi/myPapers/pubs/ImpagliazzoPaturiSchneider_2013_focs.pdf)

Here is the accounting for dimension growing with $n$. Set $s=\lceil\log_2 N\rceil$ and $d=c+1$. A median partition sends disjoint halves down two same-dimension branches whose depth budget drops by one. A third branch receives at most $N$ records and drops one dimension. Charge one unit per record per call. If $V(0,d)=V(s,0)=1$ and $V(s,d)=1+V(s-1,d)+V(s,d-1)$ for positive indices, induction gives $V(s,d)=2\binom{s+d}{d}-1$. The total charge is at most $N V(s,d)$. Sorting, copying and arithmetic add polynomial overhead. For $c=o(n)$ the binomial costs $2^{o(n)}$. For $c/n=\alpha$ the resulting exponent is at most $1/2+\alpha+(1/2+\alpha)H_2(\alpha/(1/2+\alpha))$ up to lower-order terms. [Kernel-checked recurrence and record charge](DominanceVisitBound.lean)

The implementation uses a Gray walk on each half, updating only the gates touched by the flipped bit. It agreed with exhaustive enumeration on 700 signed instances. A 36-input example with 182 bottom gates, two crossing gates and distinct input columns has exactly 45,110,816,882 satisfying inputs. A separate binomial summation supplies the reference count. [Executable checker](threshold_cut.py)

First replay the modules in [signed column groups](signed-columns.md) and [the split proof](threshold-count.md). Then run in `lean/`.

```sh
for m in ThresholdCutScores ThresholdCutCount DominanceVisitBound
do
  lake env lean -R ../tools/five-programs -o ".lake/build/lib/lean/$m.olean" "../tools/five-programs/$m.lean" && lake env leanchecker -v "$m" || exit 1
done
python3 ../tools/five-programs/threshold_cut.py
```
