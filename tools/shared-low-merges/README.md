# How much does it cost to share a low merge across lines?

For a projective plane of order $q$, let $N=q^2+q+1$. A single OR gate can be a low merge on all $N$ lines. Its upstream computation requires at least $N+2q$ gates, and a construction uses $4N-1$. More generally, counting the distinct gates feeding **all** shared low merges can still give only $O(N)$ gates even when those gates perform $\Theta(Nq)$ genuine component merges. The latter construction works on $PG(2,2^k)$ for every $k\ge1$.

These results concern the approach to L-meta-1629 that charges merges to the gates upstream of them. The target concerns the size of the entire circuit under tests with up to $q$ active lines. [Project target](https://pequalnp.com/lemma#L-meta-1629)

Two existing project results give the starting point. L663 counts low merges at each line. L-meta-697 shows that a wire whose value ignores the line inputs can merge at most once across lines in this geometry. The toggle witness below identifies each particular line input that a shared gate needs. [Per-line inequality](../../lean/PEqualNP/MetaComplexity/L663.lean) · [Line-independent wires](../../lean/PEqualNP/Outside/L_meta_697.lean)

## A lower bound on the union of the cones

Work in a fan-in-two monotone AND/OR circuit on point and line inputs. A point is *alive* at gate $g$ on line $w$ if $g$ accepts the input with just that point and $w$ active. A gate is *low* on $w$ if, whenever just $w$ is active, acceptance requires some active point on $w$. A low OR gate is a *low merge* when the alive sets of its two operands are incomparable. [Project definitions](../../lean/PEqualNP/Defs/LowMerge.lean)

Select a set $D$ of gate wires. Count $K$ distinct gates in the union of their backward cones, including the selected gates themselves. Let $U$ be a set of distinct points, each alive at some selected gate on a line on which that gate is low. Let $T$ be a set of distinct lines, each sharing a selected low merge with another line. If two distinct points lie on at most one common line, then

$$|U|+|T|\le K+|D|.$$

Here is why each input enters the cone. If a gate merges on distinct lines $w,v$, at least two points on $w$ are alive there. Some such point $p$ lies off $v$. With just $p$ active the gate accepts when $w$ is on and rejects when $v$ is on. Monotonicity gives rejection with all lines off. Thus toggling just $w$ changes the gate. Each alive point at a low gate also changes its value against the all-points-off input on that line. Tracing the selected outputs backwards, each encountered binary gate increases the number of required wires by at most one. The traversal charges each gate once. [Lean proof including the toggle witness](UniformSharedFront.lean)

For one gate merging on every line, its alive points hit each line at least twice. Each point lies on $q+1$ lines, so $|U|(q+1)\ge 2N$ and $|U|\ge 2q+1$. This gives $K\ge N+2q$ for $q\ge2$. For the upper bound choose two different marked points on each line. Form two ORs of incident point–line ANDs, one OR for each choice of mark, then OR the two results. This cone uses $2N$ ANDs and $2N-1$ ORs. At each line its operands have different singleton alive sets. Adding the unmarked incidences downstream completes the exact function on every input.

## Why new merges can still share a small cone

In $PG(2,q)$ for $q=2^k$, the $q^2$ ordinary affine lines have equations $z=ax+b$. Group their inputs by slope and separately by intercept. When just one ordinary line is active, each group encoding identifies exactly one value. For each field coordinate $x$, compute the bits of $ax+b$. Multiplication by fixed $x$ is binary linear. Represent each bit by indicators for both values, so an XOR uses four ANDs and two ORs. A binary selection tree in column $x$ then reads $X_{x,ax+b}$. The $q$ selection trees cost $3q(q-1)$ gates and the linear maps cost at most $6qk^2$. With the encoders, vertical lines and points at infinity included, the prefix $A$ uses at most $30q^2$ gates and is exact on arbitrary point sets with zero or one active line.

The same $q-1$ OR gates combine the $q$ column answers for every ordinary line. Before this tree, each low wire has at most one alive point on that line. At each OR, the earlier nodes of the tree have joined points only within one child block or within a disjoint block. Each OR therefore joins two previously separate components for each of the $q^2$ lines. This gives $q^2(q-1)$ distinct gate–line uses in the project's sense of a new low merge. [Component definition](../../lean/PEqualNP/Defs/NewLowMerge.lean)

To obtain an exact circuit, let $F$ be full incidence and build $B$ as an OR with one leaf $y_w\land(\bigvee_{p\in w}x_p)$ per line and one leaf $\bigwedge_p x_p$. Then $A\land B=F$. Every incidence activates $A$ by monotonicity. The only extra input accepted by $B$ has all points on and all lines off, which $A$ rejects. Both final operands matter. For example, the point $(1,1)$ misses both $z=0$ and $z=x+1$, yet their slope and intercept encodings jointly activate $A$ there.

Every shared low merge of this exact circuit lies in $A$. A point-only OR in $B$ needs two distinct alive points to be a merge, so it can merge on at most one line. In the final OR tree of $B$, at most one leaf has a nonempty singleton profile on each line. The last gate is an AND. The union of all shared-merge cones thus has size at most $30q^2$, while the complete circuit also pays for $B$. A lower bound using a size-minimal circuit or downstream gates remains open. [Construction and replay](sparse_line_circuit.py)

## Reproduce the results

Use the repository's pinned Lean 4.36.0 environment. From the repository root run

```sh
cd lean
lake build PEqualNP.MetaComplexity.Helpers.EdgeUpperMono PEqualNP.MetaComplexity.L663 PEqualNP.Defs.MetaComplexityLgpMono PEqualNP.MetaComplexity.Helpers.Support PEqualNP.MetaComplexity.Helpers.LowMergeFacts
lake env lean ../tools/shared-low-merges/UniformSharedFront.lean
lake env lean ../tools/shared-low-merges/UniformLineMerges.lean
python3 ../tools/shared-low-merges/sparse_line_circuit.py
```

The Lean files check the cone inequality, the all-lines corollary, the line toggle, the total one-line merge count, and existence of an exact circuit whose output merges on every line. The six printed axiom lists contain only `propext`, `Classical.choice` and `Quot.sound`. The $4N-1$ gate count and the finite-field family above have construction proofs. Python checks the actual gate lists at the orders below. [Companion Lean source](UniformLineMerges.lean)

For a separate kernel replay of the two compiled modules, run each command from `lean/` after building the dependencies above.

```sh
lake env lean -R ../tools/shared-low-merges -o .lake/build/lib/lean/UniformSharedFront.olean ../tools/shared-low-merges/UniformSharedFront.lean
lake env leanchecker -v UniformSharedFront
lake env lean -R ../tools/shared-low-merges -o .lake/build/lib/lean/UniformLineMerges.olean ../tools/shared-low-merges/UniformLineMerges.lean
lake env leanchecker -v UniformLineMerges
```

| $q$ | $N$ | Gates in prefix $A$ | Gates in union of all shared-merge cones in the completed circuit | New column merges across ordinary lines |
|---:|---:|---:|---:|---:|
| 2 | 7 | 35 | 23 | 4 |
| 4 | 21 | 161 | 131 | 48 |
| 8 | 73 | 653 | 563 | 448 |
| 16 | 273 | 2,449 | 2,143 | 3,840 |

The Python replay uses the standard library. For each tested line set, it checks every singleton point and the assignment with all points outside its union active. By monotonicity these probes decide correctness for **every** point set at that line set. It checks every line set for the two exact completions at $q=2$, every zero- and one-line set for the four prefixes, and every set of up to two lines for the binary-partition construction at $q=2,4,8$.

For the latter construction, split line labels on each bit, run a copy of $A$ on each side, OR the two sides and AND across bits. Some bit separates any two distinct lines, and every partition preserves every positive incidence. This gives size $O(N\log N)$ with at most two lines active. The script also gives the nonuniform extension to $t$ active lines by perfect hashing, of size $O(Nt^3\log N)$.
