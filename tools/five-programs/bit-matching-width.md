# A two-premise matching bound for bit pigeonhole proofs

For $h=2^\ell$ holes with $\ell\ge1$, every project Res$(\oplus)$ refutation and every syntactic integer R(lin) refutation of the bit pigeonhole formula contains a line mentioning at least
$$\left\lceil\frac{2(h+1)}{3}\right\rceil$$
distinct pigeons. A parity equation mentions a pigeon if it uses one of its bit variables. An integer equation mentions it if a coefficient on one of its bits is nonzero. A disjunction uses the union across its equations. The bound gives 4, 6, 12 and 22 pigeons for 4, 8, 16 and 32 holes. This is a width bound. A single dense equation can have large support and rank one. The superpolynomial proof-length and bit-size targets remain open under this analysis. [Both project-model theorems](BitMatchingBound.lean) · [Parity project target](https://pequalnp.com/lemma#L-pcx-023) · [Integer project target](https://pequalnp.com/lemma#L-alg-006)

A line is locally valid if every placement injective on its mentioned pigeons makes it true. The collision axioms have this property and the empty line fails it. Given two parent supports $A,B$, conclusion support $R$, and a placement injective on $R$, when can we extend its values on $R$ to an assignment injective separately on both $A$ and $B$? The exact answer is
$$|A|, |B|, |K|\le h,\qquad K=(A\cap B)\cup(R\cap(A\cup B)).$$
Any two members of $K$ occur together in at least one of the three sets, so they must get different holes. Conversely one extends to $K$ first, then extends independently to $A$ and $B$ while preserving the shared values. No injectivity requirement is imposed between their private parts. [Extension construction](MatchingTwoParents.lean) · [Necessary and sufficient conditions](MatchingOverlapCriterion.lean)

Every pigeon in $K$ occurs at least twice, giving $2|K|\le|A|+|B|+|R|$. If all three widths are strictly below $\lceil 2(h+1)/3\rceil$, extensions exist. Semantic soundness therefore preserves local validity down the whole proof, a contradiction. The argument includes unary weakening and axioms with zero parents. A complementary first-failure certificate shows that the union of the parents alone exceeds $h$. [Width induction](ProofTwoThirds.lean) · [First failure](ProofMatchingBottleneck.lean) · [Parity locality](ParityMatchingWidth.lean) · [Integer locality](IntegerMatchingWidth.lean)

The constant is sharp for the abstract argument based only on supports, local injectivity and binary semantic inference. Partition $h+1$ pigeons as evenly as possible into three blocks. Let the three scopes each omit one block. Every pair of pigeons occurs together in a scope, and the largest scope has exactly $\lceil 2(h+1)/3\rceil$ members. Injectivity on the first two scopes entails noninjectivity on the third, since joint injectivity on all three would embed $h+1$ pigeons into $h$ holes. Choosing the third scope to omit a largest block makes the conclusion locally falsifiable. This witnesses the failure of the extension argument at the stated width. Implementing these semantic predicates in a restricted syntactic proof system is a separate issue. [Three-block rule](MatchingThreeBlocks.lean) · [12,032 exhaustive extension checks and 300 balanced examples](matching_overlap.py)

Follow the prerequisite builds in [the ordinary matching calculation](matching-boundary.md), [binary proof budgets](proof-dag-budget.md) and [syntactic integer budgets](integer-pigeonhole.md). Then run in `lean/`.

```sh
for m in MatchingExtension ProofMatchingBottleneck ParityMatchingWidth IntegerMatchingWidth MatchingTwoParents MatchingOverlapCriterion ProofTwoThirds BitMatchingBound MatchingThreeBlocks
do
  lake env lean -R ../tools/five-programs -o ".lake/build/lib/lean/$m.olean" "../tools/five-programs/$m.lean" && lake env leanchecker -v "$m" || exit 1
done
python3 ../tools/five-programs/matching_overlap.py
```
