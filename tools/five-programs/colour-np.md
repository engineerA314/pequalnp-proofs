# A TM2 verifier for the exact 3-colourability language

The library's row-major graph language belongs to **PEqualNP.Library.NP**, including on arbitrary malformed words, directed adjacency matrices, loops and the zero-by-zero matrix. This proves the NP-membership part of L-lib-349 in the project's formal machine model. [Machine and NP theorem](ColourNP.lean) · [Project target](https://pequalnp.com/lemma#L-lib-349)

The certificate encodes two bit lists $a,b$ with the project's pairing function. The first list supplies the proposed side length $n=|a|$. At vertex $i$, the first bit selects colour zero; when that bit is false, the second bit selects colour one or two. The verifier checks that the graph has exactly $n^2$ entries, visits each ordered pair $i,j<n$ and rejects any edge whose endpoints have the same colour. A proper colouring yields a certificate of length $3n+1\le3|w|+1$. Soundness also holds for any irregular witness since every pair of bit lists still defines a colouring. [Certificate construction and both directions](ColourCertificate.lean)

The proof composes the project's actual polynomial-time machines for binary access, comparisons, pairing and bounded loops. It yields a polynomially clocked TM2 machine returning one Boolean output symbol on the tagged input–witness pair. The earlier [binary reduction](three-colour-words.md) supplies a separate correctness result from 3-SAT. A polynomial-time machine for a hardness reduction is the remaining obligation for full NP-completeness. [Bounded-loop and bit-access lemmas](WordMachine.lean) · [Formal NP definition](../../lean/PEqualNP/Defs/Base.lean)

Rebuild the graph modules from [the matrix construction](three-colour.md) first. From `lean/` run

```sh
lake build PEqualNP.Library.SearchHelpers.TableauStepWLoop PEqualNP.Library.SearchHelpers.SatVerifierCPT PEqualNP.Library.L032
for module in WordMachine ColourCertificate ColourNP; do
  lake env lean -R ../tools/five-programs -o ".lake/build/lib/lean/$module.olean" "../tools/five-programs/$module.lean" && lake env leanchecker -v "$module" || exit 1
done
```
