# An additive gate lower bound under the exact tests of L-meta-1629

Let $N=q^2+q+1$. Suppose a binary monotone circuit accepts each incident singleton point–line pair and rejects every independent input with at most $q$ active lines. Using exactly the project statement's incidence and circuit hypotheses, its total size is at least

$$2q^2+1+\left\lceil\log_2\left(\sum_{j=0}^q\binom{N}{j}\right)\right\rceil.$$

The first term counts distinct binary ORs. The second counts distinct binary ANDs. Fan-out and reuse are unrestricted. For large $q$ this gives $2N+\Omega(q\log q)$ total gates. Reaching the project's $Nq/100$ target for unbounded $q$ requires a further argument. [Lean theorem `PlaneGateBound.total`](PlaneGateBound.lean) · [Project conjecture](https://pequalnp.com/lemma#L-meta-1629)

## The OR cost of a single rejected input

If turning any of $d$ individual zero bits to one changes a monotone circuit's answer from false to true, the circuit has at least $d-1$ binary OR gates. Start at the false output. At a false AND choose one operand that is false on the baseline. All $d$ changes that can flip this AND must flip that operand too. At a false OR retain all its operands. The resulting trace must reach each of the $d$ sensitive input positions. Only a binary OR can branch. Replacing distinct gates in reverse topological order leaves at most one more source per binary OR, even with arbitrary fan-out. The formal proof tracks the union of the sensitive positions for a set of live wires. [Lean theorem `positive_sensitivity`](OrSensitivity.lean)

Pick $q$ lines $Y$ through a point. Their union has $q^2+1$ points, since the $q$ off-centre parts are disjoint and each has size $q$. Turn on the lines in $Y$ and every point outside this union. The circuit rejects. Turning on any covered point produces an incidence. Turning on any missing line also produces an incidence, since at most $q$ of its $q+1$ points are covered by $Y$. Monotonicity and acceptance of incident pairs give acceptance even when this change raises the active-line count to $q+1$. Thus $(q^2+1)+(N-q)=2q^2+2$ distinct flips change the answer, forcing $2q^2+1$ binary OR gates. The proof derives the required pencil directly from the statement's point-pair and line-length hypotheses. [Lean geometry and transfer](PlaneGateBound.lean)

The [binary AND transcript](and-transcripts.md) distinguishes all $\sum_{j=0}^q\binom{N}{j}$ sparse line sets. Binary ANDs and binary ORs are disjoint gate occurrences, so the two contributions add for the same circuit.

| $q$ | Required binary ORs | Required binary ANDs | Total lower bound |
| ---: | ---: | ---: | ---: |
| 4 | 33 | 13 | 46 |
| 8 | 129 | 34 | 163 |
| 16 | 513 | 85 | 598 |
| 32 | 2,049 | 204 | 2,253 |
| 256 | 131,073 | 2,413 | 133,486 |

## Replay

From `lean/`, build the three dependencies as in the [transcript replay](and-transcripts.md). Then run

```sh
lake build PEqualNP.MetaComplexity.Helpers.LowMergeWires PEqualNP.Defs.MetaComplexityLgpMono
lake env lean -R ../tools/plane-incidence -o .lake/build/lib/lean/OrSensitivity.olean ../tools/plane-incidence/OrSensitivity.lean
lake env lean -R ../tools/plane-incidence -o .lake/build/lib/lean/PlaneGateBound.olean ../tools/plane-incidence/PlaneGateBound.lean
lake env leanchecker -v OrSensitivity
lake env leanchecker -v PlaneGateBound
```

The final theorem prints the standard axioms `propext`, `Classical.choice` and `Quot.sound`.
