# A charge for witnesses that use the active line once, with arbitrary point reuse

For a binary monotone circuit on an order-$q$ projective plane, let $M$ count incident pairs $(p,w)$ for which an accepting parse on the input $(\{p\},\{w\})$ uses the line input $y_w$ exactly once. The point input $x_p$ may occur any number of times. Under the one-line negative tests of L-meta-1629, a circuit of $s$ gates satisfies

$$M\le 3s+N,\qquad N=q^2+q+1.$$

In particular, if every positive pair has such a witness then $Nq\le3s$. This allows arbitrary AND depth, arbitrary fan-out, and repeated point tests at nested ANDs. If $s<Nq/100$, at most $3Nq/100+N$ of the $N(q+1)$ incidences can have such a witness. The proof needs only the unique-line axiom and single-line soundness for the inequality about $M$. [Lean theorem on the project's actual circuit type](PlaneLineOnce.lean)

## Computing all $N$ line flags in one circuit

Fix point inputs $X$ and set all line inputs to zero. Compute the forward values $v_i(X)$ on the original wires. Seed the output with reverse flag one. Visiting gates backwards, an OR passes its flag to each operand. An AND passes its flag AND the forward value of the *other* operand. Combine flags arriving at the same wire with OR. A line's resulting function $D_w(X)$ is true precisely when there is an accepting parse with one occurrence of $y_w$ and no other line occurrences. Following the path from that leaf to the output, every AND needs an accepting line-free parse at its sibling. All chosen ORs along the path merely pass the flag.

This is formal differentiation at zero of the positive gate expansion. It preserves variable multiplicity, so an output $y_w\land y_w$ has zero reverse flag at the origin. The classical reverse-mode construction is due to Baur–Strassen in the arithmetic setting. Here the forward path and its reverse are proved equivalent for Boolean OR/AND gains, with repeated operands, both nullary constants, and the project's missing-wire convention. [Formal forward/reverse identity](ReversePath.lean) · [Baur and Strassen](https://doi.org/10.1016/0304-3975(83)90110-X)

The forward circuit creates at most $s$ binary ORs. Each original gate has at most two incoming positions. Each position needs at most one new OR to merge a backward contribution, for at most $2s$ further ORs. The multiplications by sibling values use ANDs. Consequently all $N$ functions $D_w$ are available together with at most $3s$ binary OR gates. If $D_w(X)=1$ then the original circuit accepts $(X,\{w\})$. In particular $D_w$ rejects the set $O_w$ of all points outside $w$. [Shared reverse network, gate count and soundness](ReverseCost.lean)

## Charging partial Boolean sums

More generally, let $h_w(X)$ be any outputs of one monotone AND/OR network. Suppose $h_w(O_w)=0$ and let $S_w$ be the points $p$ with $h_w(\{p\})=1$. The outputs may have additional accepting point sets. If any two lines intersect in at most one point, and the shared network has $a$ binary ORs, then

$$\sum_w |S_w|\le a+\#\{w\}.$$

For a fixed $w$, inspect gates that are zero on $O_w$. Their true singleton points lie in $w$. At an AND with zero output, one zero operand suffices to cover every singleton where the AND fires. At an OR with zero output, both operands are zero on $O_w$. Following its two operands may increase the number of roots to be accounted for by one. A gate with at most one true singleton can instead be paid for as one root. Thus the output's $|S_w|$ costs at most one plus the number of ORs with two or more true singleton points contained in $w$. Any such OR can be charged to at most one line. Summing proves the inequality. For exact Boolean sums on linear set systems this recovers the classical Nečiporuk bound. The partial-output version is what the reverse circuit needs. [Lean budget for shared outputs](PartialSums.lean) · [Mehlhorn on disjoint Boolean sums](https://citeseerx.ist.psu.edu/document?doi=e3379453f082008ccb0af8ad2343089fcc298c6a&repid=rep1&type=pdf)

Applying this inequality with $h_w=D_w$ gives the displayed bound on $M$. Its scope is syntactic at positively witnessed pairs. A single redundant final gate $h\land h$ can force two line occurrences everywhere, so counts of repeated occurrences alone cannot prove the unrestricted conjecture.

## Replay

The checker compares the reverse pass against an independent forward minimum-occurrence calculation on every incident pair and tests every $D_w(O_w)$. At $q=16$ the direct circuit has $M=4,641$. In the dyadic shared prefix $M=545$ and in its published exact completion $M=0$. [Gate-by-gate comparison](line_derivative.py)

From the repository root run `python3 tools/plane-incidence/line_derivative.py`. Build the modules in [the earlier witness bound](two-leaf-witnesses.md) and [the plane gate bound](plane-gate-bound.md). From `lean/` run

```sh
for mod in JointWidth PartialSums ReversePath ReverseCost PlaneLineOnce; do
  lake env lean -R ../tools/plane-incidence -o ".lake/build/lib/lean/$mod.olean" "../tools/plane-incidence/$mod.lean" && lake env leanchecker -v "$mod" || exit 1
done
```
