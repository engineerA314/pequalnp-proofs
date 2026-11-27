# Exact raw SAT counting by merging residual clause sets

Process the variables of a CNF in a supplied order. After each decision delete the satisfied clauses and false literals, discard tautological clauses, deduplicate, and remove clauses that strictly contain another surviving clause. Merge identical resulting clause sets by adding their prefix counts. If $s$ is the maximum number of surviving distinct states in any layer and $L$ is the encoded formula length, the algorithm uses $s\,\mathrm{poly}(L)$ bit operations. Polynomially many states give polynomial-time exact counting and model reconstruction. The algorithm runs directly on the project's raw binary CNF language, counts over all original variable names, and handles empty clauses, tautologies and malformed words. [Normalization and branching](ResidualAntichain.lean) · [Multiplicity-preserving transitions](ResidualStateCount.lean) · [Exact raw-language bridge](ResidualRawSAT.lean) · [Model theorem](ResidualModel.lean)

At each edge the truth of the residual formula is exactly the truth of the corresponding restriction. Summing the counts of completions against the current state multiplicities is invariant. When both choices lead to the same state, both multiplicities are preserved. The program retains one representative prefix in each state, which produces a full assignment for every positive count. Finite sets of literals and inclusion-minimal clauses are canonical for these syntactic reductions. Two logically equivalent residual functions can still have different normal forms. General Boolean decision diagrams give context for the use of shared residual functions. [Bryant, Graph-Based Algorithms for Boolean Function Manipulation](https://www.cs.cmu.edu/~bryant/pubdir/ieeetc86.pdf)

For $k,b\ge1$, take the $k$ clauses $x_i\lor y_1\lor\cdots\lor y_b$ and process the $x$ variables first. At the cut each of the $2^k$ subsets of original clauses can have failed to see a true prefix literal, but at most **two residual states** suffice throughout. Once a guard is false, the common tail clause subsumes all remaining guarded copies. When all guards so far are true, exactly the unprocessed guarded clauses survive. During the tail, its first true literal satisfies all remaining clauses. The exact answer is $2^{k+b}-2^k+1$. For this same family the primal graph contains a $(b+1)$-clique, and the violation-compatibility graph is complete on $k$ vertices. [All-size count](ResidualCommonTail.lean) · [Two prefix shapes and exact restriction semantics](ResidualPrefixShapes.lean)

The checker compares 800 random counts against exhaustive enumeration, validates returned assignments, and tests malformed words. With $k=72,b=60$ it reaches a peak of two states and returns 5,444,517,870,735,015,410,691,627,236,038,646,169,601 models. [Executable](residual_sat.py) · [Project algorithm-search target](https://pequalnp.com/lemma#L-alg-001)

The [grid lower bound for every ordering](grid-residuals.md) shows a family on which these reachable-state counts grow superpolynomially. For a clean replay, follow the [clause-counting prerequisite](clique-sat.md), then run in `lean/`.

```sh
for m in ResidualAntichain ResidualStateCount ResidualModel ResidualRawSAT ResidualCommonTail ResidualPrefixShapes
do
  lake env lean -R ../tools/five-programs -o ".lake/build/lib/lean/$m.olean" "../tools/five-programs/$m.lean" && lake env leanchecker -v "$m" || exit 1
done
python3 ../tools/five-programs/residual_sat.py
```
