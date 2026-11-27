# The AND gates that survive fixed line selections

Let $D_g$ be the set of line labels $w$ for which at least one input of binary AND $g$ is true when the sole active primary variable is $y_w$. This counts what the operands can actually do on singleton inputs even if their cones contain many more line variables. Let $N=q^2+q+1$. For every circuit on the original project promise and each $0\le r\le q$, put

$$L_r=\left\lceil\log_2\sum_{j=0}^{q-r}\binom{N-r}{j}\right\rceil.$$

For every $r$-line set $R$, at least $L_r$ distinct binary ANDs satisfy $D_g\cap R=\varnothing$. Consequently the same original circuit satisfies the following weighted inequalities simultaneously for all choices of $r$.

$$\binom Nr L_r\ \le\sum_{g\ \mathrm{binary\ AND}}\binom{N-|D_g|}{r}.$$

Each gate contributes once, regardless of fan-out. At $r=0$ this recovers the binary AND count. Larger $r$ discounts ANDs that become copies under many line selections. [Lean proof with the original circuit and plane hypotheses](PlaneAnchorBudget.lean)

## Fixed anchors and averaging

Fix the lines of $R$ to one and leave all other inputs variable. If $w\in R\cap D_g$, monotonicity keeps the corresponding operand true on all extensions. Replace the gate by a copy of the other operand. The rewrite keeps wire numbering, including repeated operands and the project's missing-wire convention. It also replaces a binary OR with a true constant if some anchored singleton turns on an operand. It produces exactly the same value at every wire on this subcube. [Gate rewrite and exact budget accounting](AnchorPruning.lean)

For each line set $Y$ containing $R$ with $|Y|\le q$, take the negative input consisting of all points outside $\bigcup Y$ and the lines of $Y$. Two distinct such rows cover a positive input. Choose a line $w$ in one set but absent from the other. At most $q$ of the $q+1$ points on $w$ are covered by the other set. Take an uncovered point $p$ on $w$, and activate that point and the lines $R\cup\{w\}$. This positive input lies in the subcube of the rewrite. The AND transcript must distinguish every pair of these negative rows. There are $\sum_{j=0}^{q-r}\binom{N-r}j$ rows, giving the fixed-anchor inequality. Summing over the size-$r$ anchors counts exactly $\binom{N-|D_g|}r$ surviving choices for gate $g$. [Transcript argument](and-transcripts.md)

For example, suppose there are $a$ binary ANDs and choose a cutoff $d$ with $\binom{N-d}r/\binom Nr\le L_r/(2a)$, where $a>0$ and $r>0$. The gates with $|D_g|\ge d$ together provide at most $L_r/2$ of the required average. At least $\lceil L_r/2\rceil$ ANDs therefore have $|D_g|<d$. If $a$ is polynomial in $N$ and $r=\lfloor q/2\rfloor$, then $L_r=\Theta(q\log q)$ and $d=O(q\log q)$ suffices, with a constant depending on the polynomial degree. This uses $\binom{N-d}r/\binom Nr\le (1-d/N)^r\le e^{-rd/N}$. This is a bound on a gate's singleton responses. A gate with an empty footprint can still depend on many lines together.

At order 16, anchoring eight lines forces at least 49 surviving ANDs for **every** choice of the eight lines. In the exact completed dyadic circuit with 1,572 binary ANDs, the integer part of the average is 567. The same parameters force at least 25 ANDs to have fewer than 110 labels in their footprints for any qualifying circuit with at most 1,572 binary ANDs. [Exact-integer replay](anchor_profiles.py)

## Replay

Run `python3 tools/plane-incidence/anchor_profiles.py` from the repository root. Build dependencies as in the [plane bound](plane-gate-bound.md) and [anchored boundary](full-boundary.md), then check the two new modules from `lean/`.

```sh
for mod in AnchorPruning PlaneAnchorBudget; do
  lake env lean -R ../tools/plane-incidence -o ".lake/build/lib/lean/$mod.olean" "../tools/plane-incidence/$mod.lean" && lake env leanchecker -v "$mod" || exit 1
done
```
