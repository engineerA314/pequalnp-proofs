# Research contributions across five project programs

These notes use the project's pinned Lean toolchain and the exact program definitions cited in each entry. The repository branch contains contributor research. The project desk records a checked gap after its corresponding proof passes the upstream process. [Project programs](https://pequalnp.com/programs)

| Program | Result and verification |
| --- | --- |
| Library of known results | A graph with $3+2n+8m$ vertices encodes every formula on $n$ variables with $m$ three-literal clauses. Lean proves the equivalence for the exact row-major language in L-lib-349. [Construction, scope and replay](three-colour.md) |
| Geometric complexity theory | An exact coefficient-support criterion for arbitrary rank-one-generated permanent families. Every failure has an integer witness in the grid from 0 to $n$. [Converse, search and symmetric obstruction](permanent-support.md) |
| Circuit lower bounds via algorithms | Exact counting on the project’s signed depth-two threshold circuits by weighted dominance. With $h=o(n/\log n)$ bottom gates, the algorithm takes $2^{n/2+o(n)}$ time for polynomial-size encodings. [Counting identity, runtime and replay](threshold-count.md) |
| Proof complexity | A sound binary proof DAG with $K$ essential inputs needs at least $2K-1$ lines. Applying this to parity resolution improves the bit pigeonhole baseline for every positive bit length. [Lower bound and tight examples](proof-dag-budget.md) |
| P = NP algorithm search | For the corrected syntactic integer system L-alg-006, counting input-equation bits and shared inference lines forces a weighted size of at least $(4\ell+2)K-1$ at every binary pigeonhole size. [Statement and dependency on the input encoding](integer-pigeonhole.md) |
