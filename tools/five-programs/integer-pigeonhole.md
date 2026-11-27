# A proof-size floor for the syntactic integer system

Let $H=2^\ell$ with $\ell>0$, and let $K=H\binom{H+1}{2}$. Any syntactic integer R(lin) refutation of the project's binary pigeonhole formula with $H+1$ pigeons and $H$ holes has weighted size at least

$$(4\ell+2)K-1.$$

The statement uses the exact derivation rules and the coefficient-bit cost from the P = NP algorithm search program. For example, the floor is 399 at four holes and 4,031 at eight holes. This floor has order $H^3\log H$. The superpolynomial target in L-alg-006 remains open. [Lean proof](IntegerPigeonProof.lean) · [Target statement](https://pequalnp.com/lemma#L-alg-006) · [Project rule definitions](../../lean/PEqualNP/Defs/SearchQSyn.lean)

There are exactly $K$ distinct source lines after forgetting the order and repetition of equations. Deleting any one admits a satisfying assignment. One can collide exactly the two named pigeons at their named hole and assign the others bijectively to the remaining holes. Every written source contains $2\ell$ distinct literal equations. Each contributes at least two units of coefficient cost, and the line has one unit of overhead. A source therefore costs at least $4\ell+1$. [Source count, injectivity and literal cost](IntegerPigeonAxioms.lean)

Convert each written line to its set of equations. Integer linear combinations are sound binary inferences. Syntactic weakening and deletion of a false constant equation are sound unary inferences, and the Boolean line for a variable is true without premises. The general binary-DAG bound forces $K-1$ additional non-source lines, each costing at least one. This accounting works with arbitrary coefficient sizes, line reordering, duplicates, and unrestricted reuse of earlier lines. [General proof-DAG bound](proof-dag-budget.md)

Resolution over linear equations has polynomial-size proofs for several standard counting principles, including an ordinary pigeonhole encoding. Translating such upper bounds to this specific binary input formula and the project's syntax would require an explicit simulation and its size. A useful comparison for stronger results is the total cost already forced by writing the essential input lines. [Raz and Tzameret](https://arxiv.org/abs/0708.1529)

Replay the three modules for the [parity proof budget](proof-dag-budget.md) first. From the repository's `lean/` directory run

```sh
lake build PEqualNP.Defs.SearchQSyn PEqualNP.Search.Helpers.ResLinQ
for module in IntegerPigeonAxioms IntegerPigeonProof; do
  lake env lean -R ../tools/five-programs -o ".lake/build/lib/lean/$module.olean" "../tools/five-programs/$module.lean" && lake env leanchecker -v "$module" || exit 1
done
```
