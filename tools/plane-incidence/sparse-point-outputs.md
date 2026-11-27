# Exact front-end cost for all point answers under sparse line tests

Suppose a binary monotone circuit reads the $N=q^2+q+1$ line selectors of an order-$q$ projective plane. It must provide one wire $h_p$ for every point $p$. It may share any internal gates between these wires, use ANDs and ORs at any depth, and return arbitrary monotone answers on line sets larger than $q$.

If $h_p$ accepts every singleton line through $p$ and rejects every set of at most $q$ lines missing $p$, the shared circuit needs **at least $Nq$ distinct gates**. This minimum is exact. For each point independently, use $q$ binary ORs to combine its $q+1$ incident lines. More generally, imposing negative tests only up to $t\le q$ forces at least $Nt$ front-end gates. Any implementation that first produces all point answers and then combines them with the point selectors pays this cost in its front end. The original single-output conjecture allows mixing point and line variables much earlier. [Lean theorem on projective planes](SparsePlanes.lean) · [Project target](https://pequalnp.com/lemma#L-meta-1629)

## Charging a shared gate once

For a wire $g$, let $S_g$ consist of the line labels whose singleton input makes $g$ true. For target point $p$, let $R_p$ be its $q+1$ incident lines. Mark $g$ if it is false at the empty input, $S_g\subseteq R_p$, and $|S_g|\ge2$. A physical gate can be marked for at most one point because two pencils share exactly one line.

Trace backwards from $h_p$, traversing marked gates and stopping on other wires. If the trace visits $c$ marked gates, its stopping set $F$ contains at most $c+1$ distinct wires. This counts a shared subgate once in the trace. It also works with repeated operands. Monotonicity gives the following implication. If the stopping wires that are true on input $X$ are all true on input $Y$, then $h_p(X)=1$ implies $h_p(Y)=1$. [Shared-frontier proof](SparseFrontier.lean)

A stopping wire either can be made true with at most one outside line, or is true on at most one singleton. In the latter case it is false at the empty input and on all outside singletons, and stopped precisely because its singleton support was small. For each wire of the first kind, choose one outside witness, allowing the empty set, and take their union $Y$. All these wires are true on $Y$. If $|F|\le q$, some incident singleton $w$ avoids the singleton supports of every wire of the second kind. The stopping wires true on $\{w\}$ are therefore all true on $Y$. The output accepts $Y$, even though $|Y|\le q$ and every line in $Y$ misses $p$. Hence $|F|\ge q+1$ and $c\ge q$. Summing over points gives the claim. [Sparse witness construction](SparseRows.lean)

For $q=16$, for example, a front end answering all 273 point queries needs at least 4,368 gates before the point bits are combined. The lower bound holds even if the front end may fail on large independent line sets. The executable replay traces a matching circuit and also constructs an actual two-outsider false positive in an intentionally insufficient candidate. [Reproducible frontier check](sparse_frontier.py)

## Partial outputs and projections

The argument also works if row sets meet in at most $b\ge1$ labels and output $i$ recognizes only $a_i$ singleton labels. Stop whenever a wire that rejects all one-label outside witnesses recognizes at most $b$ singletons. If the row must reject outside sets of size up to $t$, there are disjoint gate charges $c_i$, with total at most the circuit size, such that

$$c_i<t \quad\Longrightarrow\quad a_i\le b(c_i+1).$$

This gives at least $\min(t,\max(0,\lceil a_i/b\rceil-1))$ gates per row. In the square-order projection construction the $ds^3$ rows have $s^3$ labels and meet pairwise in at most $s^2$. Already **$s-1$ active outside lines** as the soundness budget force $ds^3(s-1)$ total gates. In contrast, the bound specifically on binary ORs uses the full row-complement negative. [Sparse projection corollary](SparsePlanes.lean) · [OR count with complement tests](projection-front-cost.md)

The exact Boolean-sum bounds without any input promise are classical. The statement here explicitly weakens each output's negative tests to sparse outside sets. The project's honest-factor lemma also uses outside witnesses, for an AND-list of factors. The arbitrary shared frontier and its summed row-gate budget are proved here. [Mehlhorn on exact Boolean sums](https://citeseerx.ist.psu.edu/document?doi=e3379453f082008ccb0af8ad2343089fcc298c6a&repid=rep1&type=pdf) · [Project's honest-factor argument](../../lean/PEqualNP/MetaComplexity/Helpers/Deg2Cover.lean)

## Replay

From the repository root run `python3 tools/plane-incidence/sparse_frontier.py`. Build the dependencies listed in the [projection-front-end note](projection-front-cost.md) and [anchor-budget note](anchor-budget.md). From `lean/` run

```sh
for mod in SparseFrontier SparseRows SparsePlanes; do
  lake env lean -R ../tools/plane-incidence -o ".lake/build/lib/lean/$mod.olean" "../tools/plane-incidence/$mod.lean" && lake env leanchecker -v "$mod" || exit 1
done
```
