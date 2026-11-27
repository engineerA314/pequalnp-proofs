# Accepting parses with a single use of either endpoint

On each incident singleton pair $(p,w)$, a parse of a binary monotone circuit keeps one true operand at an OR and both at an AND. Unfolding a shared wire twice counts its leaves twice. Let $M_P$ count incident inputs with **some** accepting parse using the point $x_p$ once, allowing any number of $y_w$ leaves. Write $M_L$ for the analogous one-line count. On the original order-$q$ tests, with $N=q^2+q+1$ and $s$ gates,

$$M_P\le 5s+N,\qquad M_L\le 3s+N,\qquad M_P+M_L\le 8s+2N.$$

These hold for all depths and every positive plane order. The number of incident inputs with some parse using either endpoint once is at most $8s+2N$, including when the two types of witnesses come from different parses. If $s<Nq/100$, then at least $N(q+1)-8s-2N$ incident inputs require **both endpoints to repeat in every accepting parse**. This is an asymptotic fraction of at least $0.92-o(1)$. The witness constraints alone do not count the cost of repeated work inside a gate. [Theorems on the project circuit](PlanePointOnce.lean) · [Earlier line-side argument](line-once.md)

## Why the sparse line promise matters

Set all point inputs to zero and keep every line variable. At a point input $p$, compute the reverse flag $D_p(Y)$ of the output. A true flag identifies a path from that input to the output along which every AND sibling has a true parse that uses no point. Such a path gives an accepting parse at $(\{p\},Y)$ with exactly one point occurrence. Conversely, following the unique point leaf in such a parse gives the path. At a singleton line this is precisely the witness counted by $M_P$. The line variable may be read repeatedly in any sibling. [Forward and reverse path identity](ReversePath.lean)

Compute all forward values at the all-zero point input in at most $s$ binary gates. Seed the reverse output flag with true. For each of the at most $2s$ operand positions, multiply the parent flag by the sibling value at an AND and accumulate arriving flags by OR. This takes at most $4s$ further binary gates, shared by **all** $N$ point flags. The bound also covers duplicate input positions and the project's constant conventions. [Shared reverse-network compiler](ReverseAll.lean)

$D_p$ rejects every set of at most $q$ lines missing $p$ because the original output rejects that input with only $p$ selected. The original promise allows larger line sets to behave arbitrarily. Distinct pencils meet in at most one line and each has $q+1$ lines. The partial sparse front-end bound therefore gives $\sum_p|\{w:D_p(\{w\})=1\}|\le5s+N$. The analogous line-side proof can use the entire complement of a line as a negative, and only needs to count the ORs in its reverse network. [Sparse partial-output theorem](SparseRows.lean) · [Line-side reverse compiler](ReverseCost.lean)

## Replay

Run `python3 tools/plane-incidence/point_derivative.py` from the repository root. The checker compares the reverse flags with a forward calculation on every incident input of four different orders. On each tested circuit at orders 2, 3 and 4 it additionally checks **every** allowed outside-line input for each point. At order 8 it checks all outside singletons and deterministic samples of larger outside sets. At order 4, repeating each line at its own AND leaves all 105 incident inputs with a one-point witness and none with a one-line witness. Repeating the final output loses both types of witness on every edge.

Build the dependencies in the [scalar cofactor note](honest-cofactor-cost.md) and [line-side note](line-once.md), then run from `lean/`

```sh
for mod in ReverseAll PlanePointOnce; do
  lake env lean -R ../tools/plane-incidence -o ".lake/build/lib/lean/$mod.olean" "../tools/plane-incidence/$mod.lean" && lake env leanchecker -v "$mod" || exit 1
done
```
