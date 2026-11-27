# Exact SAT checks of the emitted square-order circuits

The [projection construction](square-projections.md) works for every quadratic finite-field extension. This replay checks specific binary netlists against a separate incidence oracle, for every point assignment and every allowed line set. It tests the implementation together with its projective boundary gates.

| Plane order | Line budget | Binary gates | Permitted line sets | Independently checked UNSAT certificates |
| ---: | ---: | ---: | ---: | ---: |
| 16 | 4 | 4,993 | 229,779,278 | 290 |
| 25 | 5 | 14,726 | 966,943,394,432 | 677 |
| 49 | 7 | 76,000 | 104,831,788,005,442,201,832 | 2,501 |

At each order, the positive query asks whether an incident point and line can both be on while the circuit rejects. All other primary variables are unrestricted. The negative query turns the output on, forbids each incident pair of primaries from being simultaneously true, and adds a sequential counter limiting the number of active lines. In the counter, an active input forces the first threshold bit, and a previous threshold together with an active input forces the next threshold. Exceeding the bound gives a contradiction. For every input within budget the true prefix counts supply a satisfying assignment to the auxiliary bits.

To divide the negative query into manageable proofs, trace only ORs backwards from the actual output and stop at the remaining wires. The output is exactly the disjunction of these wires. Each branch conjoins one wire to the full negative query, retaining every primary and every original gate. The counter may use a different permutation of the same line inputs in each branch. An affine term's projection directions give an effective ordering. The emitter checks the permutation before writing the CNF. Unsatisfiability of every branch implies unsatisfiability of the whole negative query. [DIMACS generator](projection_sat.py)

One further query increases the budget by one. The solver found satisfying assignments at every order. The replay checks every clause of the emitted CNF and reevaluates both the exact gate list and the independent incidence masks on the recovered primary variables. For example, at order 49 the line indices were 1, 2, 3, 5, 7, 23, 32 and 1954 in the generator's zero-based ordering. The 1,557 active points were independent of those eight lines, and the circuit accepted.

## Reproducing the certificates

These runs used CaDiCaL 2.1.2 and lrat-trim at commit `423194927df747528d5b7364806b5b77b2660c12`. The solver writes an LRAT proof for each negative result and a separate checker confirms it against that case's CNF. The generator and its translation from gate types to CNF are executable code. The LRAT checker certifies the emitted formulas. [CaDiCaL](https://github.com/arminbiere/cadical) · [lrat-trim](https://github.com/arminbiere/lrat-trim/tree/423194927df747528d5b7364806b5b77b2660c12)

From the repository root, with both programs on the path, run

```sh
python3 tools/plane-incidence/projection_sat_replay.py 4 4
python3 tools/plane-incidence/projection_sat_replay.py 5 5
python3 tools/plane-incidence/projection_sat_replay.py 7 7
```

The replay accepts explicit program paths via `--solver` and `--checker`. The final values below are SHA-256 digests of the sequence of binary SHA-256 digests of each CNF followed by its proof, positive case first and then negative branches in ascending wire order. Proof bytes can change across solver versions.

| Order | Digest |
| ---: | --- |
| 16 | `4eb3597f42fef5bb5757110a1cb703c58d942076ad7a47cac96a33e40ae1bac2` |
| 25 | `373f38823a4aae06d44367024bd95b5037f0756bce947deb6d0068cfa97eb4d3` |
| 49 | `edb47c71fcb679b5d37600fed53a92b43c8d860b5466157898efda5dcb94951a` |
