# Distinct binary AND gates required by incompatible negative tests

For a monotone circuit of fan-in at most two, let $a$ count its binary AND gates. Let $F$ be a family of rejected circuit inputs such that the coordinatewise union of any two distinct members contains some accepted input. Then $|F|\le 2^a$. Fan-out is unrestricted. A reused gate contributes one bit to the bound regardless of how many outputs read it. [Lean theorem `incompatible_count`](AndTranscript.lean)

Record the value of the first operand of each binary AND, in a fixed topological order. Suppose two negative inputs have the same record and an accepted test lies below their union. Induct through the circuit. At an OR that fires on the positive test, one operand fires and hence is on in at least one negative evaluation. At a binary AND that fires, the first operand fires on at least one negative and therefore on both, by the equal records. The negative evaluation where the second operand fires also has a true AND output. Constants and single-input gates preserve the same invariant. At the output this contradicts rejection. The record therefore identifies each member of $F$.

## Application to the projective-plane tests

Let $N=q^2+q+1$. For each set $Y$ of at most $q$ lines, turn on every point outside its line union. These inputs are negative. The union of any two distinct ones contains an incident pair, by the private-point argument in the [clause-repair note](clause-repair.md). Consequently **every** binary monotone circuit accepting all incident pairs and rejecting these sparse negatives satisfies

$$2^a\;\ge\;\sum_{j=0}^q\binom Nj.$$

The same reasoning separately charges a downstream circuit if it receives the original inputs and one prefix bit. If the bit equals one on the incident pairs and on $m$ canonical negative inputs, the suffix needs at least $\lceil\log_2 m\rceil$ binary ANDs for $m\ge1$. In particular, one false singleton-point test with $r$ active lines forces $\lceil\log_2 M_r\rceil$ ANDs for the $M_r$ in the clause-repair note. With more prefix wires crossing the boundary, the generic transcript theorem applies when the covering condition holds on the **full boundary signatures**. [Lean specializations `one_bit_repair` and `whole_circuit`](RepairAnds.lean)

| Order | Sparse line sets tested | Leaks of the published prefix | Exact minimum clauses | Required suffix ANDs |
| ---: | ---: | ---: | ---: | ---: |
| 2 | 29 | 2 | 2 | ≥1 |
| 4 | 7,547 | 6,740 | 6,740 | ≥13 |

These two rows enumerate all permitted line sets and evaluate the actual [one-line network](../shared-low-merges/sparse_line_circuit.py) on the canonical point assignment for each. At $q=8$, the single-witness inequality alone gives at least 27 suffix ANDs. The separate whole-circuit inequality gives at least 34. As $q$ grows the latter bound is $\Omega(q\log q)$. The project's target for total gates grows as $\Theta(Nq)$. [Counting script](repair_counts.py)

## Replay

From `lean/`, build the project's circuit helper and the module in the [clause-repair note](clause-repair.md), then compile and replay the two proofs

```sh
lake build PEqualNP.MetaComplexity.Helpers.Support
lake env lean -R ../tools/plane-incidence -o .lake/build/lib/lean/SparseNegatives.olean ../tools/plane-incidence/SparseNegatives.lean
lake env lean -R ../tools/plane-incidence -o .lake/build/lib/lean/AndTranscript.olean ../tools/plane-incidence/AndTranscript.lean
lake env lean -R ../tools/plane-incidence -o .lake/build/lib/lean/RepairAnds.olean ../tools/plane-incidence/RepairAnds.lean
lake env leanchecker -v AndTranscript
lake env leanchecker -v RepairAnds
```

From the repository root, `python3 tools/plane-incidence/repair_counts.py` reproduces the table and the binomial bounds for orders 4, 8, 16 and 32.
