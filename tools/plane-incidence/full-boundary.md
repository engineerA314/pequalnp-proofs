# A downstream lower bound with every wire of the shared prefix available

The earlier one-bit result left open how much of its lower bound survives when the suffix can reuse the interior of the prefix. For both explicit plane networks considered here the downstream circuit still needs $\Omega(q\log q)$ distinct binary AND gates as $q$ grows, **even given all primary inputs and every prefix wire for free**. The statement concerns circuits that keep the specified prefix and correct its answers up to the project's $q$-line budget. [Earlier one-bit bound](and-transcripts.md)

## A sufficient condition on an arbitrary boundary

Fix a set $R$ of line inputs to one. Suppose each exported monotone feature, under this restriction, depends only on point inputs or only on line inputs. The choice of side can differ from wire to wire. In a linear incidence system with $L$ lines, each of length greater than $t$, consider all line sets $Y\supseteq R$ with $|Y|\le t$. For each $Y$, the negative input has active points $O(Y)$, the complement of the line union. If the suffix accepts every incident pair when fed its actual boundary values and rejects all these negative inputs, its number $a$ of binary ANDs satisfies

$$2^a\ge\sum_{j=0}^{t-|R|}\binom{L-|R|}{j},\qquad |R|\le t.$$

For different anchored rows, choose a line from their symmetric difference and a point on it untouched by the other row's at most $t$ lines. The positive pair is below their union on the raw inputs. Now take a boundary wire that fires on this pair $(p,w)$. By monotonicity it still fires at $(\{p\},R\cup\{w\})$. If it depends only on points when $R$ is present, it fires on the negative containing $p$. If it depends only on lines there, it fires on the negative containing $w$. Thus the positive signature is below the union on **all** wires at the cut. The transcript lemma applies to the suffix. [Lean theorem `all_extensions`](AnchoredBoundary.lean)

For the concrete networks restrict primary inputs to affine points and ordinary lines. There are $q^2$ ordinary lines, each with $q$ affine points. Take $t=q-1$. Setting every direction point, vertical line and line at infinity to zero on these tests is permitted by L-meta-1629. The proof uses the full netlist, including the gates that handle those inputs.

## Two horizontal lines suffice for the dyadic network

In the [shared one-line prefix](../shared-low-merges/sparse_line_circuit.py), turn on the horizontal lines with intercepts zero and the all-ones field word. These are distinct for every $q=2^k$. For every intercept bit, both rails are now true. At the horizontal-only assignment the encoded slope is zero. The dual-rail multiplication and addition therefore leave both ordinate rails true for every column. Monotonicity preserves this under further line activations. All wires up to the address computation are line-only. In each point multiplexer the selector rails are permanently one, so every internal gate becomes a point-only function. The ordinary-active guard is one. The affine-only restriction makes the live parts of the projective boundary point-only, line-only, or constant as well.

Taking $|R|=2$ forces at least $\lceil\log_2\sum_{j=0}^{q-3}\binom{q^2-2}{j}\rceil$ additional binary ANDs for dyadic $q\ge4$. At $q=8$, 7,068,621 negative rows give 23 ANDs. At $q=16$, the lower bound is 71. These counts hold after exposing every gate in the shared cone.

## Square-order projection networks

For the [square-order circuit](square-projections.md), make every selected projection attain every base-field value on the active horizontal intercepts. All three OR layers are line-only, and their final tests are permanently one. Each point intersection then specializes to its point bit. For $q=s^2$ and fewer than all $s+1$ directions, a line of $s$ intercepts in an omitted direction suffices. With all directions selected, the union of two intersecting base-field lines of intercepts suffices and has $2s-1$ members. Both choices give $|R|=O(\sqrt q)$, and the binomial lower bound still has logarithm $\Omega(q\log q)$. The $q=16$ network with all five directions has 5,539 input and gate wires. Exposing all of them leaves at least 49 additional binary ANDs.

## Replay

The Lean modules prove the general bound and the soundness of a gate-by-gate checker, respectively. The all-orders applications use the netlist structures described above. A separate executable traverses the generated binary circuits, propagating constants and recording whether a wire uses point inputs, line inputs or both. Its result on a given netlist covers all settings of the unfixed inputs. The replay checks dyadic orders 4 to 64 and every permitted number of selected projections at square orders 4, 9, 16 and 25. [Checker and counts](boundary_cofactors.py)

Build `AndTranscript`, `SparseNegatives` and `RepairAnds` using the [transcript replay](and-transcripts.md). From `lean/` run

```sh
lake env lean -R ../tools/plane-incidence -o .lake/build/lib/lean/AnchoredBoundary.olean ../tools/plane-incidence/AnchoredBoundary.lean
lake env lean -R ../tools/plane-incidence -o .lake/build/lib/lean/WireCofactor.olean ../tools/plane-incidence/WireCofactor.lean
lake env leanchecker -v AnchoredBoundary
lake env leanchecker -v WireCofactor
```

From the repository root run `python3 tools/plane-incidence/boundary_cofactors.py`. The project-wide $\Omega(Nq)$ target still requires a larger charge or a different argument for the general case.
