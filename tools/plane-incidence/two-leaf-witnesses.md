# Counting short incident-pair witnesses in an arbitrary shared circuit

Let $C$ be any binary monotone gate DAG on the vertices of a simple four-cycle-free graph $G$. Suppose $C$ rejects every singleton and every pair of nonadjacent vertices. Count an edge $uv$ if, when only $u,v$ are on, the output has an accepting parse with just **two variable occurrences**. A parse chooses one true operand of an OR and takes both operands of an AND. Each input occurrence is counted separately, even when two paths visit the same wire. Constants are free in this count.

**The number of counted edges is at most the total number of gates of $C$.** There is no bound on depth or fan-out. Other accepting parses at the same edge can be arbitrarily long. Every circuit satisfying the project's plane hypotheses obeys these singleton and pair rejections for $q\ge2$. The plane has $N(q+1)$ incidences. Consequently at least $N(q+1)-|C|$ incident pairs require a repeated endpoint in every accepting parse on that pair. [Lean lower bound](CleanEdges.lean) · [Project target](https://pequalnp.com/lemma#L-meta-1629)

## Proof

Evaluate at each wire the least number of variable occurrences in a parse, keeping the four values $0,1,2,\ge3$. An unavailable variable or wire is placed in the last class. OR takes the smaller cost, AND adds costs with truncation at three. The root's answer to the question “is there a parse with at most two variable occurrences?” is exact.

In parallel, summarize a wire either as constant true or by a pair $(A,R)$. Here $A$ is a set of variables and $R$ a collection of ordered pairs of variable sets. The cost on an input $X$ is one if $X$ meets $A$. Otherwise it is two if $X$ meets both operands of some member of $R$, and at least three in the remaining case. For a primary variable $v$, use $A=\{v\}$ and $R=\varnothing$. OR of ordinary summaries takes the two unions. AND of ordinary summaries $(A,R)$ and $(B,T)$ has empty variable set and the single product $(A,B)$. True collapses an OR and acts as identity at AND. This recurrence gives the numerical cost for every input, with empty, unary and missing wires handled using the project's conventions. [Formal semantics and Boolean soundness](CleanWitness.lean)

During evaluation, charge an ordinary OR one preparation gate for its variable-set union. Charge an ordinary AND at most one new product. These are disjoint original gates. At the output every side of every product is present in the same shared OR preparation, and the preparation size plus the number of distinct products is at most $|C|$. [Formal extraction](CleanPreparation.lean)

For any output product $(A,B)$, each $a\in A,b\in B$ makes the circuit true on $\{a,b\}$. Singleton soundness gives $a\ne b$, and pair soundness makes $ab$ an edge. A nonempty product is therefore a star, since $G$ has no four-cycle. A preparation OR supported on two or more neighbors of a star center can be charged to only that center. The [shared-preparation bound](single-level-repair.md) now charges every edge covered by the output products to one preparation gate or one product. Each counted edge is covered, proving the result.

The related *read-1* model asks for a repetition-free witness for every prime implicant. The bound here counts the qualifying subset of edges in a circuit with a partial input specification. It is a property of the chosen gate representation. Replacing an output $h$ by $h\land h$ adds a gate and destroys all its two-leaf edge parses, even though that gate can be removed by idempotence. The universal lower bound would require a way to control the remaining circuits after such simplifications. [Jukna, Boolean read-k circuits](https://arxiv.org/abs/2207.08701)

## Replay

At order 16 the direct circuit has two-leaf parses on all 4,641 incidences. The 2,449-gate dyadic prefix and the 4,993-gate full projection prefix each have two-leaf parses on exactly 545. In these networks the other 4,096 are the ordinary affine incidences. The executable evaluates the truncated min-plus recurrence on every incident pair in each emitted circuit. [Witness enumeration](pair_witnesses.py)

Build the modules in [the star bound](single-level-repair.md) and [the AND transcript](and-transcripts.md). From `lean/` run

```sh
for mod in CleanWitness CleanPreparation CleanEdges; do
  lake env lean -R ../tools/plane-incidence -o ".lake/build/lib/lean/$mod.olean" "../tools/plane-incidence/$mod.lean" && lake env leanchecker -v "$mod" || exit 1
done
```

From the repository root run `python3 tools/plane-incidence/pair_witnesses.py`.
