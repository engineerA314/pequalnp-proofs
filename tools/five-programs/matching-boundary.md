# Extracting a saturated partial matching from a resolution proof

For the project's ordinary pigeonhole formula with $m$ pigeons and $h>0$ holes, every resolution refutation contains a clause with **exactly $h$ distinct pigeons** which a bijection from those pigeons to the holes falsifies. The two parents are locally valid and their resolution pivot belongs to a pigeon outside the conclusion. This describes an identifiable step in the actual proof DAG. [Project-model theorem](PigeonExactSupport.lean) · [Parent and pivot extraction](PigeonResolutionBoundary.lean)

The graph version gives further information. Give each pigeon $p$ a nonempty list $E(p)$ of allowed holes. Call a clause locally valid if every injective placement of its mentioned pigeons along allowed edges makes it true. Inputs are locally valid and the empty clause is locally falsifiable. At the first failure, take any locally falsifying matching $M$ for the conclusion. The pivot pigeon $p$ lies outside its domain, and **every hole in $E(p)$ belongs to the image of $M$**. Otherwise $M$ extends by one edge and both parents must be true on the extension, contradicting soundness. Complete neighborhoods give the exact support count. [Local semantics and extension](PigeonLocalMatching.lean)

A polynomial-time diagnostic scans a supplied trace and tests each clause by bipartite matching. A positive literal forbids its edge in a falsifying placement and a negative literal forces its edge. An augmenting-path algorithm finds a placement or certifies local validity. On the included family of ordinary-resolution certificates, the first failure occurs on line 47 of 58 for three holes and line 138 of 157 for four. The checker replayed every pivot for one through eight holes and compared 650 random graph-clause matching decisions against exhaustive injections. [Executable generator, locator and verifier](pigeon_matching.py)

This formalizes a matching adversary for pigeon-width. The test concerns the pigeons on one clause and its pivot. Resolution length lower bounds require additional arguments. Classical results on PHP proof length and stronger results for sparse graphs provide context. [Buss and Pitassi](https://mathweb.ucsd.edu/~sbuss/ResearchWeb/resolutionPHP/index.html) · [de Rezende, Nordström, Risse and Sokolov](https://arxiv.org/abs/1912.00534)

Replay in `lean/`.

```sh
lake build PEqualNP.ProofComplexity.Helpers.Resolution
for m in PigeonLocalMatching PigeonResolutionBoundary PigeonExactSupport
do
  lake env lean -R ../tools/five-programs -o ".lake/build/lib/lean/$m.olean" "../tools/five-programs/$m.lean" && lake env leanchecker -v "$m" || exit 1
done
python3 ../tools/five-programs/pigeon_matching.py
```
