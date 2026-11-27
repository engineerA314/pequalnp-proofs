# Why local gate necessity cannot bound simultaneous rises

The [simultaneous-rise inequality](fork-tradeoff.md) suggests charging each incident pair where both operands of a shared AND turn on. The total number of these events can exceed the circuit size by an unbounded factor, even when deleting either child of any joining AND changes a promised answer. A distributive rewrite can eliminate every event.

Take any plane of order $q$, and compute its exact incidence function $F$ as an OR of the $N$ line stars. Choose $q+1$ distinct line labels $K$. Build a binary tree for

$$H=\bigwedge_{i\in K}(F\lor y_i).$$

Every leaf reads the same gate for $F$. On every Boolean input, $H=F\lor\bigwedge_{i\in K}y_i$. For at most $q$ active lines at least one selector is zero, so $H=F$ on the complete project promise. The direct star circuit costs $Nq+2N-1$ gates. The new circuit adds exactly $2q+1$ gates. [Formal identities and sparse-promise theorem](ForkFactoring.lean)

For every incident $(p,w)$ the point-only baseline gives zero at every tree leaf and the incident input gives one at every leaf. Consequently each of the $q$ joining ANDs experiences simultaneous rises at all $N(q+1)$ incidences. There are exactly $qN(q+1)$ events, since no AND in the direct star circuit has both operands rise. At $q=16$ this gives 74,256 events in 4,946 gates. At all orders the union of exceptional pairs is also the whole incidence relation. This example limits a gate-by-gate route to the inequality. Its size is above the conjectured lower bound.

The two operands of each joining AND compute different, incomparable Boolean functions even on sparse inputs. At empty point input, a subtree on leaf labels $A$ computes $A\subseteq Y$. For disjoint nonempty sibling sets $A,B$, taking $Y=A$ or $Y=B$ separates the two functions, and each set has at most $q$ elements. Replacing an internal AND by either of its children removes at least one selector from the whole tree. Take $Y$ equal to all retained selectors and take no points. The modified circuit accepts this valid negative input. Thus the events persist after tests for repeated operands, constant gates, child comparability and direct child deletion.

Computing $F\lor\bigwedge_{i\in K}y_i$ directly instead uses only $q+1$ added gates and agrees with $H$ on **every** input. No AND in the factored circuit experiences simultaneous rises on an incident singleton pair. The selector tree has disjoint line supports at its two children, and every AND inside $F$ has a point-only operand. Further progress could use an invariant of the computed function or a normal form with a size guarantee.

The [netlist replay](fork_events.py) evaluates every wire in both presentations, enumerates every incidence and checks all single-clause omission inputs at $q=2,4,8,16$. Run `python3 tools/plane-incidence/fork_events.py` from the repository root. From `lean/`, run `lake env lean -R ../tools/plane-incidence -o .lake/build/lib/lean/ForkFactoring.olean ../tools/plane-incidence/ForkFactoring.lean` and `lake env leanchecker -v ForkFactoring`.
