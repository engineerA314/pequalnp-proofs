# The cost of adding one AND level after a shared plane circuit

Consider either the [dyadic one-line circuit](../shared-low-merges/sparse_line_circuit.py) or the [square-order projection circuit](square-projections.md). A completion may read every primary input and every gate in the original circuit. Suppose each path **inside the added circuit** contains at most one binary AND. A completion satisfying the plane conjecture's tests needs at least $(1-o(1))q^3$ additional gates along each of the two growing families. Here $N=q^2+q+1$, so the lower bound is also $(1-o(1))Nq$. The proof concerns these two specified prefixes. Arbitrary additional AND depth remains open. [Project target](https://pequalnp.com/lemma#L-meta-1629)

## One AND level in a graph with no four-cycle

Let $G$ be a finite simple graph with at least one edge and with at most one common neighbor per pair of distinct vertices. A positive fan-in-two circuit accepts each edge and rejects every singleton and every nonedge pair. Among circuits with at most one binary AND on every input-output path, the exact minimum size is

$$|E(G)|+\tau(G)-1,$$

where $\tau(G)$ is the vertex cover number. Only these one- and two-variable tests are necessary. A minimum vertex cover realizes the upper bound by assigning each edge to one of its covered endpoints, collecting its neighbors with binary ORs, taking one AND per center and ORing the results.

For the lower bound, propagate constants and copies, discard dead wires and retain the $m$ contributing binary AND gates. Each has two disjunctions of input variables as operands. Any live path from a variable to the output consisting only of ORs would accept a singleton, so the output is the OR of the $m$ products. Joining these $m$ distinct gates into one output takes at least $m-1$ binary ORs, including when a later OR is reused. These gates are disjoint from the OR preparations feeding the products.

Let $A,B$ be the variable sets in one product. They are disjoint, since a shared variable would accept a singleton. Every crossing pair in $A\times B$ must be an edge. Two elements on each side would give a four-cycle. Thus one side is a single center $c$ and the other is a nonempty subset of its neighbors. The centers of the products cover $E$, giving $m\ge\tau(G)$.

For a fixed center $c$, let $m_c$ be its number of products. Take all their other operands as roots in the shared OR preparation. Their union can contain at most $m_c+g_c$ variables, where $g_c$ counts preparatory ORs whose support contains at least two variables and lies inside the neighborhood of $c$. To see this, trace the distinct roots backwards. Dropping a singleton root accounts for at most one variable. Replacing the latest large root by its two parents increases the number of roots by at most one and spends its gate exactly once. Parents remain inside the same neighborhood. A gate with two different variables can count for at most one center, since two centers have at most one common neighbor. Every edge occurs in some star. Summing over centers gives $|E|\le m+\sum_c g_c$. Adding the output ORs proves the lower bound. [Shared OR accounting](SharedOrStars.lean) · [Star and cover bound](SingleLevelStars.lean)

This argument uses the single-level model studied by Amano–Maruoka and Jukna. Jukna explicitly credits Amano–Maruoka with the $|E|$ lower bound for four-cycle-free graphs. The accounting above keeps the cover term, allows the plane's partial specification and measures the reusable part of a fixed prefix. [Amano and Maruoka](https://doi.org/10.1007/s00453-006-0073-0) · [Jukna, Section 3](https://web.vu.lt/mif/s.jukna/ftp/single1.pdf)

## Restricting the plane and retaining every prefix wire

Fix horizontal lines with intercepts in a nonempty set $B$ to one, and set all other horizontals, vertical lines, lines at infinity and direction points to zero. Keep the points $(x,z)$ with $z\notin B$ and ordinary lines of nonzero slope as variables. Write $r=|B|$ and assume $r+2\le q$. Every one- or two-variable assignment in the restriction has at most $q$ active lines in the original circuit. Activating an incident point-line pair must be accepted by monotonicity. On a singleton or nonedge pair there is no incidence, including with the fixed horizontals. These are precisely the tests used above.

The residual graph is four-cycle-free, has $q(q-r)$ points, and each point has $q-1$ neighbors. Its vertex cover number is exactly $q(q-r)$. All retained points form a cover. For the matching lower bound, fix $b_0\in B$ and assign to $(x,z)$ the incident line of slope $z-b_0$ and intercept $z-(z-b_0)x$. Different ordinates give different slopes. At a fixed ordinate, the nonzero slope gives different intercepts for different abscissas. Thus the restricted one-level optimum is exactly $q^2(q-r)-1$. [Lean proof over any finite field](AffineStarBound.lean)

For the dyadic prefix, use the two horizontal intercepts $0$ and the all-ones field word. Each intercept address bit has both rails permanently true, and every slope bit has its zero rail true. Each dual-rail XOR product then has a constant operand and leaves both address rails true. The point multiplexers become OR trees. All boundary ANDs have constant operands on the restriction. For the projection prefix, use $s$ horizontal intercepts for a proper set of directions, or $2s-1$ intercepts for all directions, with $q=s^2$. Every final projection test is then permanently true, and every point product becomes a copy. The projective boundary again folds to ORs and copies. These arguments account for intermediate gates, including ones the suffix may read directly. [Anchor construction and minimum size](projection-anchors.md)

Consequently the restricted prefix plus the new gates is single-level. Subtracting the entire original prefix size gives the all-order lower bound $q^2(q-r)-1-|\mathrm{prefix}|$ for the suffix. The dyadic prefix has at most $30q^2$ gates and $r=2$. The square-order prefixes have $O(q^2\sqrt q)$ gates uniformly in the chosen direction count, and $r\le2\sqrt q-1$.

For an individual netlist one can subtract only **eligible prefix ORs**. Compute the exact variable support of every wire after restriction. A union equal to either operand is a copy. Any remaining prefix OR used in a product's preparation must have its entire support inside one neighborhood, since ORs preserve each operand's support. An ineligible OR cannot feed a productive star arm or reach the output through ORs alone. Thus $q^2(q-r)-1-u$ added gates are necessary if the original circuit has $u$ eligible residual ORs.

| Prefix | $q$ | Fixed horizontals | Original gates | Eligible prefix ORs | Additional gates required |
| --- | ---: | ---: | ---: | ---: | ---: |
| Dyadic | 8 | 2 | 653 | 36 | 347 |
| Dyadic | 16 | 2 | 2,449 | 196 | 3,387 |
| Dyadic | 64 | 2 | 32,361 | 3,844 | 250,107 |
| Square, all five directions | 16 | 7 | 4,993 | 0 | 2,303 |
| Square, all six directions | 25 | 9 | 14,726 | 3 | 9,996 |

The Lean theorems cover the shared OR network, normalized parallel products and affine geometry. The reductions from a single-level gate DAG and from each all-order prefix construction are given above. The executable certificate propagates a Boolean constant or an exact OR support at every generated prefix wire and rejects any surviving nontrivial AND. It then checks whether each OR support fits a star in an independently generated incidence graph. [Prefix checker](single_level_repair.py)

From the repository root run `python3 tools/plane-incidence/single_level_repair.py`. From `lean/`, run

```sh
lake build PEqualNP.MetaComplexity.Helpers.Support
for mod in SharedOrStars SingleLevelStars AffineStarBound; do
  lake env lean -R ../tools/plane-incidence -o ".lake/build/lib/lean/$mod.olean" "../tools/plane-incidence/$mod.lean" && lake env leanchecker -v "$mod" || exit 1
done
```
