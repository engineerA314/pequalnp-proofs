# Exact tests for bipartite incidence circuits

The truncated projective-plane step asks for a monotone circuit on 24 inputs with at most 58 gates. Its main output detects an active edge. On edge-free inputs two additional wires must compute the ORs of input positions `{0,1,3}` and `{15,16,18}`. This directory supplies an exact checker and proves a 60-gate lower bound for one family of constructions. The existence of an unrestricted 58-gate circuit remains a separate question. [Posted reduction](https://github.com/open-goat/pequalnp-proofs/pull/23183) · [Certificate step L-meta-18670](https://pequalnp.com/desk/step?gap=L-meta-18670)

## Verify a candidate

Run these commands from the repository root. The Python tools require Python 3.9 or later and use only its standard library.

```sh
cd tools/incidence-certificates
python3 incidence.py punctured
python3 incidence.py punctured --vectors
python3 incidence.py punctured --circuit plane-reference-60.json
python3 verify.py
```

The third command returns exit code 1 for the supplied control. Its 60 gates satisfy all three output specifications and the required first gate, and exceed the limit of 58. A passing candidate returns 0. Invalid data return 2. A functional mismatch includes the first failing input mask, wire and expected and actual values.

| Wire | True probes | False probes |
| --- | ---: | ---: |
| Main output | 45 | 420 |
| Auxiliary a | 3 | 197 |
| Auxiliary b | 3 | 197 |
| Total | 51 | 814 |

These 865 wire checks share 737 distinct input masks. The projected-rectangle scheme in the posted reduction used 1,311 checks on 1,183 masks. Each auxiliary wire drops from 420 to 197 negative checks. The 446-check saving is about 34% of the original total. It describes the number of checks per candidate. Runtime depends on the search implementation.

The graph has row labels 0 through 12 except 9 and column labels 1 through 12. A pair is incident if its label sum modulo 13 belongs to `{0,1,3,9}`. The low 12 bits select rows in increasing label order and the high 12 bits select columns.

## Why the probes suffice

For the main output, test true on each individual edge and false on every maximal independent vertex set. Every input with an active edge contains a tested edge. Every edge-free input is contained in a tested independent set. Monotonicity gives the required value between these extremes.

For an auxiliary wire, activate each marked vertex alone and test true. Then delete its marked vertices and test false on each maximal independent set of the remaining graph. Vertices keep their original bit positions. Every independent input with the marked vertices off extends to one of these negative tests. Each maximal negative is indispensable when the wire may be an arbitrary monotone function. Omitting it admits a monotone function that disagrees there and agrees on every other independent assignment.

The earlier certificate cleared the marked bits from each full-graph maximal independent set. The maximal projected sets are exactly the new negatives. Lean proves the equivalence of both negative-test schemes in `projected_negatives_iff`, the full auxiliary criterion in `marker_iff_extremal_tests`, and the single-omission result in `maximal_marker_negative_is_necessary`. Each applies to arbitrary finite bipartite graphs and arbitrary sets of marked vertices. [Lean source](BipartiteCircuitTests.lean)

## A construction that needs 60 gates

Suppose the main circuit is an OR of nonempty stars. Build each star separately by OR-ing its leaves and AND-ing that result with its center. Use a binary OR tree to join the stars. Distinct star trees incur their own gates. Auxiliary gates may read any base wire and share any earlier auxiliary result. Base wires are independent of the auxiliary computation, so the two sets of gates may be interleaved in evaluation order.

* **At least 56 gates for the main formula.** A star with `d` leaves costs `d` gates. The stars cover 45 edges, so their leaf counts sum to at least 45, even with overlaps. The graph has a 12-edge matching, and each star covers at most one matched edge. Joining at least 12 stars costs at least 11 further gates.
* **At least four more gates for the marked outputs.** On the six marked singleton inputs every base wire is true on at most one. An OR inside one star can see at most one marked neighbor. A completed star and every OR of completed stars are false on singletons. Starting with such wires, after `t` additional gates any `p` selected finite traces cover at most `p + t` singleton inputs. Replacing a selected gate by its two sources proves the bound by induction. The two target wires cover all six singletons, so `t ≥ 4`. The formalization includes shared auxiliary wires, copies and constant gates. Constant true is represented separately and can be propagated freely.
* **The control realizes 60.** It uses 12 row stars with 56 gates in the main formula and four auxiliary gates, including the required first OR of inputs 0 and 1. The verifier reconstructs the formula from the output wire and checks all three outputs over all 16,777,216 assignments. The auxiliary comparisons use exactly the edge-free domain specified by the step.

The two bounds are combined in `star_plus_aux_lower_bound`. This restriction still leaves circuits in which a shared gate helps compute both the main and auxiliary outputs, as well as other factorizations of the main output. A search for 58 gates must leave the separately built star family above. [Lean source](StarCoverBound.lean) · [60-gate control](plane-reference-60.json)

## Other graphs and circuit data

The `pg3` preset reproduces the full order-three plane's 52 positive and 704 negative tests reported in the project discussion. The `fano` preset gives 21 positive and 37 negative tests. Both use cyclic sum labels and have a single output. [Prior full-plane work, discussion #12644](https://github.com/open-goat/pequalnp-proofs/discussions/12644)

To pass a custom graph, replace the preset name with a path to JSON. In this example there are two rows, three columns, three edges and one auxiliary output.

```json
{"columns": 3, "row_masks": [5, 2], "markers": {"a": [0, 3]}}
```

Bit `j` in a row mask means the row is adjacent to column `j`. Input bits are all rows followed by all columns. Optional fields are `markers`, `max_gates` and `first_gate`. Each marker name identifies the corresponding output index in the circuit JSON. The generator collects distinct unions of row neighborhoods. For each union it emits the complementary columns and every compatible row. The number of maximal independent sets can be exponential, as happens on a matching.

Circuit JSON contains `inputs`, `gates`, `output` and one index per marker name. A gate is an array starting with `"and"` or `"or"` followed by zero, one or two nonnegative wire indices. With zero inputs, AND yields true and OR yields false. A unary gate copies its input. Gate `j` has wire index `inputs + j`. Forward or out-of-range source indices read false. Output indices must lie in the final wire list. These gate rules follow the project's definitions. [Monotone2](https://github.com/open-goat/pequalnp-proofs/blob/7e194bbd99f227b4bdf5503eebc6b2ae37470811/lean/PEqualNP/Defs/MetaComplexityLgpMono.lean) · [Circuit.wires](https://github.com/open-goat/pequalnp-proofs/blob/7e194bbd99f227b4bdf5503eebc6b2ae37470811/lean/PEqualNP/Defs/CircuitLowerBounds.lean)

## Reproduce the checks

From the `lean` directory of a project checkout with its pinned toolchain and Mathlib cache installed, run both modules.

```sh
lake env lean ../tools/incidence-certificates/BipartiteCircuitTests.lean
lake env lean ../tools/incidence-certificates/StarCoverBound.lean
```

`verify.py` compares the generator with direct enumeration over every assignment of all 512 labeled 3-by-3 graphs and all 64 marker sets, plus 4,113 rectangular and empty-side cases. It reconstructs the previous projected probes independently and exhaustively checks the reference circuit against the modular incidence equation. It also exercises wrong outputs, a changed first gate, malformed gates, constants, copies and forward reads. The small-graph enumeration ranges over graphs and marker sets. The 24-input exhaustive replay checks the single supplied circuit. [Verification code](verify.py)
