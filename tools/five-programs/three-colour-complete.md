# NP-completeness of the project's binary three-colourability language

For the exact square, row-major adjacency language in L-lib-349, a polynomially clocked TM2 machine maps a raw 3-SAT word to a graph word with the same answer. Combined with the earlier verifier and the project's 3-SAT completeness theorem, this establishes full NP-completeness. It also proves the implication in L-lib-347 that polynomial-time decidability of this graph language would imply $P=NP$. [Formal reduction, complete theorem and corollary](GraphMatrixComplete.lean) · [Library statement](https://pequalnp.com/lemma#L-lib-349)

The input has $N$ bits. A successful syntax and width check produces a $(13(N+1))$-vertex graph. All other inputs produce the one-bit matrix with a loop. Output length is at most $169(N+1)^2$ on every word. Each variable is addressed by the first occurrence of its binary name. Increasing a sparse identifier affects the construction through its encoded length. The scan handles empty clauses separately from unused clause slots. One extra variable forced to false does both jobs. [Clause and variable scanning](GraphStreamWords.lean) · [Padding semantics](GraphStreamForm.lean) · [Assignment equivalence](GraphStreamCorrect.lean)

A fixed list of 13 roles and $N+1$ slots per role gives simple loops for emitting the adjacency matrix bit by bit. All palette copies project to the same three palette vertices. Every gadget vertex has a representative. Pulling a colouring back along the projection and restricting to representatives establish both directions. Equality, sign, wire and triangle tests are composed from the project's actual polynomial-time transducers. [Vertex projection](GraphStreamRoles.lean) · [Wire computation](GraphStreamCPT.lean) · [Adjacency machine](GraphCellMachine.lean) · [Row-major loops](GraphMatrixLoops.lean)

For a clean replay from this branch, run the following in the `lean/` directory with the pinned toolchain and the project's cached Mathlib. The earlier [word-level result](three-colour-words.md) uses a distinct, smaller graph construction.

```sh
lake build PEqualNP.Library.L032 PEqualNP.Library.L018 PEqualNP.Library.SearchHelpers.TableauStepWLoop PEqualNP.Library.SearchHelpers.SatVerifierCPT
for m in ThreeColourGadgets ThreeColourMatrix CNFReader PackedThreeSAT ThreeColourWord WordMachine ColourCertificate ColourNP GraphStreamWords GraphStreamForm GraphStreamCorrect GraphStreamCPT GraphStreamRoles GraphCellMachine GraphMatrixLoops GraphMatrixComplete
do
  lake env lean -R ../tools/five-programs -o ".lake/build/lib/lean/$m.olean" "../tools/five-programs/$m.lean" && lake env leanchecker -v "$m" || exit 1
done
```

This is a contributor-fork formalization of a classical complexity result. The project desk reported that L-lib-349 was closed to submissions when this was checked. It gives no polynomial-time algorithm for unrestricted three-colourability.
