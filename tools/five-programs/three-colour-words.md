# A reduction on every input word from project 3-SAT to matrix 3-colourability

There is a total function $g$ on bit strings such that for **every word** $w$,

$$w\in\mathrm{KSAT}(3)\quad\Longleftrightarrow\quad g(w)\text{ is accepted by the row-major graph language in L-lib-349}.$$

The Lean proof also bounds $|g(w)|\le(5+4|w|)^2$. A variable with a large binary identifier receives a compact local index. This matters even for a single-literal clause since the numerical identifier can be exponential in the length of its spelling. [Language equivalence and output bound](ThreeColourWord.lean) · [Original gadget theorem](three-colour.md)

The executable parser is a left-to-right scan of tagged bit pairs. The Lean version re-encodes the parsed formula to check canonical spelling. It returns a formula $F$ exactly when the project's `encodeCNF F` equals the input. In particular, incomplete items, odd-length words and redundant most-significant zeroes are rejected. The empty word represents the empty conjunction. [Parser and both directions of its specification](CNFReader.lean)

At width at most three, a clause with one or two literals is padded by repeating its last literal. An empty clause makes the formula unsatisfiable, and a width above three puts the word outside the source language. Those cases and malformed encodings map to a one-vertex graph with a loop. All other formulas use the graph constructor with one extra dummy variable for total indexing. The number of graph vertices is $5+2v+8m$ for $v$ distinct identifiers and $m$ clauses. There are at least four input bits per literal and two per clause. [Compaction and padding proof](PackedThreeSAT.lean)

For a 2,049-bit variable identifier and its successor in a two-clause test, the output has 25 vertices and 625 bits. The independent replay tests the language equivalence on all 32,767 words of length at most 14 (222 canonical encodings), then 250 generated formulas with larger names. The accepting side runs a graph-colouring search and the source side enumerates truth assignments. Run `python3 tools/five-programs/three_colour_word.py`. [Executable reduction](three_colour_word.py)

The library already proves the exact source language NP-complete. The present result supplies a total computable map, a correctness theorem, and an explicit quadratic output-length bound. Transferring NP-hardness in the project's formal model also requires its polynomial-time TM2 computation theorem. Membership of the graph language in NP is a separate obligation. [Project 3-SAT completeness](../../lean/PEqualNP/Library/L032.lean) · [Reduction transfer theorem](../../lean/PEqualNP/Library/L020.lean)

Rebuild the [two graph modules](three-colour.md), then from the repository's `lean/` directory run

```sh
lake build PEqualNP.Defs.Search
for module in CNFReader PackedThreeSAT ThreeColourWord; do
  lake env lean -R ../tools/five-programs -o ".lake/build/lib/lean/$module.olean" "../tools/five-programs/$module.lean" && lake env leanchecker -v "$module" || exit 1
done
```
