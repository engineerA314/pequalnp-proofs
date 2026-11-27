# A grid CNF defeats every global variable order for residual-state search

Place one Boolean variable at each vertex of an $r$-by-$c$ grid. Add a positive two-literal clause $x_u\lor x_v$ for each pair of adjacent vertices. For **every** variable order, some prefix leaves at least
$$2^{\lfloor\min(r,c)/2\rfloor}$$
pairwise inequivalent residual Boolean functions. Any state from which every suffix decision can be answered must distinguish this many prefix assignments. On the $m$-by-$m$ family there are $N=m^2$ variables, $2m(m-1)$ clauses and at most four occurrences per variable. The bound $2^{\lfloor\sqrt N/2\rfloor}$ is superpolynomial in the formula's binary encoding length, even with a best choice of order. It excludes a general polynomial-time guarantee for [the residual-state enumeration algorithm](residual-sat.md). This concerns exact representations that support every suffix query along one global variable order. Grid instances themselves are satisfiable, for example by the all-true assignment. [All rectangles](GridRectangleLower.lean) · [State lower bound for every ordered split](GridResidualLower.lean)

For a square of side $2k$, stop as soon as its first row is completely read. If some row is still untouched, every column is mixed. Choose every other column. Otherwise all rows except the completed row are mixed. Choose the $k$ rows of the opposite parity to that row. Each chosen row or column contains an edge crossing the prefix. Skipping a strip between any two choices makes these $k$ edges an induced matching. A rectangle contains an induced even square of side $2\lfloor\min(r,c)/2\rfloor$ and inherits the selected prefix from its order. [First completed row](GridOrderCut.lean) · [Separated strips](GridStripMatching.lean)

For each subset of matching edges, set precisely its prefix endpoints to false and all other prefix variables to true. To test membership of a particular edge, set just its suffix endpoint to false. The resulting assignment violates the formula exactly when that edge was selected. Distinct subsets therefore require distinct residual states even under perfect semantic deduplication. This supplies a concrete counterfamily to the polynomial-state hypothesis for the preceding algorithm. It uses the established connection between ordered decision diagrams and structural width. [Matching decoder and exact CNF semantics](ResidualInducedMatching.lean) · [Amarilli et al., Connecting Width and Structure in Knowledge Compilation](https://pierre.senellart.com/publications/amarilli2018connecting_long.pdf)

The executable checked 234 square-grid orders, including every ordering of the $2$-by-$2$ grid, and 144 rectangle orders. For squares through $8$-by-$8$ it built each of the selected residual clause sets and checked the response to each singleton suffix. The proofs quantify over every order without enumeration. [Independent checker](grid_residual.py)

First build `ResidualAntichain` using [the residual SAT replay](residual-sat.md). Then run in `lean/`.

```sh
for m in ResidualInducedMatching GridStripMatching GridOrderCut GridResidualLower GridRectangleLower
do
  lake env lean -R ../tools/five-programs -o ".lake/build/lib/lean/$m.olean" "../tools/five-programs/$m.lean" && lake env leanchecker -v "$m" || exit 1
done
python3 ../tools/five-programs/grid_residual.py
```
