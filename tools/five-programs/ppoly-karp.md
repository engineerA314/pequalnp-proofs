# Nonuniform closure under variable-length Karp reductions

If a polynomial-time TM2 transducer reduces a Boolean language $A$ to a language $B$ with polynomial-size bounded-fanin circuits, then $A$ has polynomial-size bounded-fanin circuits. This is the standard downward-closure theorem for P/poly in the project's exact circuit and machine models. Applying it to the fully clocked [3-colourability reduction](three-colour-complete.md) gives the entire conditional statement of L-lib-348. [Closure and graph consequence](PPolyKarpClosure.lean) · [Project target](https://pequalnp.com/lemma#L-lib-348)

For input length $n$, let $q(n)$ bound the length of the reduction output. One uniform decision machine queries a specified output bit. A second one tests whether the output length equals $j$. Hardwiring the unary address gives polynomial-size circuits for both queries. For each $0\le j\le q(n)$ attach the circuit for $B$ on inputs of length $j$, supply the first $j$ bits, and gate its answer with the exact length test. Taking the disjunction selects the unique correct circuit, including when the reduction emits the empty word. [Query circuits](CircuitQueryFamily.lean) · [Bounded-fanin connectors](CircuitPortBoolean.lean)

When composing $m$ source circuits $C_i$ with a consumer $D$, the verified layout uses exactly $\sum_{i=1}^m(|C_i|+1)+|D|+1$ gates. Each local output is copied before a later block can occupy its wire index. This retains the project's default-false semantics for out-of-range and forward references. The executable checked 1,200 randomly generated compositions on all 12,721 associated inputs and exercises a length-sensitive empty output. [Port semantics](CircuitPortBlock.lean) · [Composition proof](CircuitPortCompose.lean) · [Regression check](port_compose.py)

To replay, first follow the [library completeness build](three-colour-complete.md). Then run these commands in the same `lean/` directory.

```sh
lake build PEqualNP.CircuitLowerBounds.L006
for m in CircuitPortBlock CircuitPortCompose CircuitPortBoolean CircuitQueryFamily PPolyKarpClosure
do
  lake env lean -R ../tools/five-programs -o ".lake/build/lib/lean/$m.olean" "../tools/five-programs/$m.lean" && lake env leanchecker -v "$m" || exit 1
done
python3 ../tools/five-programs/port_compose.py
```

The implication assumes polynomial-size circuits for three-colourability. The formalization supplies a reusable transfer theorem. The project desk reported this target closed to proof submissions.
