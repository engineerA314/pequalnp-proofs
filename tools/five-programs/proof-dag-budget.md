# Counting shared inference steps in minimally unsatisfiable proofs

For a finite set of (K) essential input lines, every refutation in a sound proof system with at most two premises per inference contains at least (K-1) occurrences of lines outside the input set and at least (2K-1) line occurrences altogether. A line may be reused arbitrarily. The theorem includes nullary valid axioms, unary consequences, duplicated input lines, and proofs with unused material. It requires a falsifiable omission for *each* input line: deleting that line permits an assignment satisfying all the others. [General Lean theorem](ProofDagBudget.lean)

For the project's bit pigeonhole formulas, write (H=2^\ell), with (\ell>0), and (K=H\binom{H+1}{2}). Each unordered pair of pigeons and each hole specify one essential axiom. In the project's dag-like parity resolution with semantic weakening, every refutation uses at least **(2K-1) lines**. The checked baseline L-pcx-023 was (K+1). For four holes this raises 41 to 79, and for eight holes it raises 289 to 575. This bound grows cubically in the number of holes. [Project baseline](../../lean/PEqualNP/ProofComplexity/L023.lean) · [Instantiation and exact count](ParityProofBudget.lean)

The proof maintains a finite set of target lines while moving backwards through the actual derivation. A target that is a source contributes one input occurrence. An inference replaces one target by at most two earlier premises, so the frontier grows by at most one per non-source occurrence. The final source set entails the contradiction. Essentiality forces it to contain every input. This argument charges a shared inference once, even when later steps both depend on it.

The coefficient two is sharp for the general statement, already in ordinary resolution. For (k\ge0), take (x_0), the (k) implications (x_i\to x_{i+1}), and (\neg x_k). The (k+2) clauses are minimally unsatisfiable. The project’s resolution rules admit a proof of exactly (2k+3) lines, and every proof is at least that long. Proving a larger bound on bit pigeonhole therefore requires additional structure of that family or proof system. [All-length construction and matching lower bound](ResolutionChain.lean)

From the repository's `lean/` directory:

```sh
lake build PEqualNP.ProofComplexity.Helpers.SizeBound PEqualNP.ProofComplexity.Helpers.Resolution
for module in ProofDagBudget ParityProofBudget ResolutionChain; do
  lake env lean -R ../tools/five-programs -o ".lake/build/lib/lean/$module.olean" "../tools/five-programs/$module.lean" && lake env leanchecker -v "$module" || exit 1
done
```
