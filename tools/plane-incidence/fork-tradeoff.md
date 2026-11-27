# Simultaneous rises at a shared AND

Fix an incident point–line pair $(p,w)$. Evaluate every wire twice, first with just $p$ active and then with both $p$ and $w$ active. Say a binary AND has a simultaneous rise at $(p,w)$ when both of its operand values change from zero to one. Write $B$ for the number of distinct incident pairs with at least one such gate somewhere in the circuit. On every order-$q$ plane satisfying the hypotheses of L-meta-1629, a circuit of $s$ gates satisfies

$$Nq\le 3s+B\le 3s+\sum_{g\text{ binary AND}} |\{(p,w):\text{both operands of }g\text{ rise}\}|.$$

Fan-out, repeated operands and depth are unrestricted. The first term counts shared gates only once. The first error term also charges each exceptional incidence only once, even if many gates experience the same change. [Lean theorem on the project circuit](PlaneForkBound.lean)

To see the dichotomy, fix a pair for which no AND has a simultaneous rise. Inductively, each wire that is true on the larger input is already true on the smaller input or admits a parse using the newly enabled line exactly once. At a true OR one can choose any true child. At a true binary AND, at least one operand was already true. Its line-free parse can be paired with the other operand's parse. The project rejects the smaller input and accepts the incident pair, so the output admits a parse with one occurrence of the line. The shared reverse-circuit bound charges all such pairs by $3s+N$. Subtracting $N$ from the plane's $N(q+1)$ incidences proves the inequality. [Wire induction and reverse flag](LineForks.lean) · [Reverse-circuit bound](line-once.md)

For example, assume the two operand cones of each binary AND use disjoint sets of line inputs. Turning on one line cannot change both operands. The bound becomes $Nq\le 3s$ with arbitrary reuse of point inputs at ANDs and arbitrary sharing at ORs. More generally, a total of at most $97s$ simultaneous-rise events would suffice for the project's $Nq\le100s$ target. Bounding those events, or avoiding repeated charges more effectively, requires additional structure.

## Replay

Build the dependencies in [the one-line-occurrence replay](line-once.md), then run from `lean/`.

```sh
for mod in LineForks PlaneForkBound; do
  lake env lean -R ../tools/plane-incidence -o ".lake/build/lib/lean/$mod.olean" "../tools/plane-incidence/$mod.lean" && lake env leanchecker -v "$mod" || exit 1
done
```
