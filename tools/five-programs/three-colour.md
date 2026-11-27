# A row-major graph word for 3-SAT

The library's 3-colourability language reads the length of its input as the square of an integer, uses row-major adjacency and allows arbitrary bit strings. For every formula with $n$ variable names and $m$ ordered triples of signed literals, the Lean construction produces a symmetric row-major adjacency word with side $3+2n+8m$. The input formula is satisfiable exactly when this word belongs to the **literal matrix language** in the project. Variables and clauses may repeat. The proof covers zero clauses. [Matrix theorem and explicit vertex numbering](ThreeColourMatrix.lean) · [Project's NP-completeness target](https://pequalnp.com/lemma#L-lib-349)

Three palette vertices are joined in a triangle. A variable has two opposite literal vertices, both adjacent to the third palette colour. For each clause with truth values $a,b,c$, add one Boolean variable $z$ and two triangles enforcing that the two triples $(a,b,z)$ and $(\neg z,c,\mathrm{false})$ each contain both truth values. The triangle vertices are attached individually to the corresponding literal colours. When the input clause is true, $z=\neg(a\lor b)$ works. Conversely, fitting the three different colours on either triangle forces its attached Boolean triple to be nonconstant. Every proper colouring can be normalized by the palette's permutation and decoded as a satisfying assignment. [Uniform gadget proof](ThreeColourGadgets.lean)

The translation is a classical reduction. The checked contribution supplies the all-instance gadget, vertex numbering, serialized output and equivalence for this project's exact target language. A complete proof of L-lib-349 additionally needs the bit-string input parser, the reduction from arbitrary NP languages and the polynomial-time machine in the project's time model. The executable directly fills the matrix in $O((3+2n+8m)^2+n+m)$ operations after reading the triples. [Original graph-colourability NP-completeness result, Garey, Johnson and Stockmeyer](https://www.math.ucdavis.edu/~deloera/MISC/LA-BIBLIO/trunk/JohnsonDavid2.pdf)

The independent graph-colouring replay tests all ordered formulas with up to two variables and two clauses, fixed-seed larger instances, and a minimally unsatisfiable 3-variable example and its eight clause deletions. It checks both the graph answer and the recovered input assignment. There are 4,354 test instances, of which 20 are unsatisfiable. From the repository root run `python3 tools/five-programs/three_colour.py`. From `lean/` run

```sh
for mod in ThreeColourGadgets ThreeColourMatrix; do
  lake env lean -R ../tools/five-programs -o ".lake/build/lib/lean/$mod.olean" "../tools/five-programs/$mod.lean" && lake env leanchecker -v "$mod" || exit 1
done
```
