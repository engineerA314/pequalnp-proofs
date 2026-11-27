# The exact number of positive clauses required to repair a prefix

Let $I(w)$ be the points on line $w$. Suppose every line contains more than $q$ points, distinct lines share at most one point, and $q\ge1$. A positive input contains an incident pair. We test every point assignment $X$ and every set $Y$ of at most $q$ active lines. A prefix $A(X,Y)$ accepts all positive tests and is monotone in $X$.

For fixed $Y$, write $O(Y)=P\setminus\bigcup_{w\in Y}I(w)$. Call $Y$ a leak if $A(O(Y),Y)=1$. A positive clause is an OR of any subset of the original point and line variables. Then the minimum number of clauses in an exact repair $A\wedge C_1\wedge\cdots\wedge C_m$ is **exactly the number of leaking sets $Y$**. The formula permits arbitrary sharing of wires computing the clauses. Its cost measure is the number of distinct clauses. [Lean theorem `exact_minimum`](SparseNegatives.lean)

To see the lower bound, every clause must include one endpoint of each incident pair. Suppose it rejects the rows for distinct $Y,Z$. After exchanging them if needed, take $w\in Y\setminus Z$. Each line in $Z$ covers at most one of the more than $q$ points on $w$, so there is a point $p\in I(w)\cap O(Z)$. The clause omits $w$ to reject the first row and omits $p$ to reject the second. It then rejects the positive test $\{p,w\}$.

For the matching construction, add one clause per leaking $Y$. Include every point outside $O(Y)$ and every line outside $Y$. This covers every incident pair. On any erroneous input $(X,Y)$ one has $X\subseteq O(Y)$, so monotonicity in $X$ makes $Y$ a leak and its own clause rejects that input.

## What follows from one observed error

In a projective plane of order $q$, suppose $A$ is also monotone in the line inputs and accepts a single point $p$ together with $r\le q$ nonincident lines $R$. Extend $R$ using any of the $q^2-r$ remaining lines that miss $p$, while keeping at most $q$ active. Each extension gives a different leak. This forces at least

$$M_r=\sum_{j=0}^{q-r}\binom{q^2-r}{j}$$

clauses. For fixed $r$ and growing $q$, $M_r=q^{\Theta(q)}$. The [published one-line prefix](../shared-low-merges/sparse_line_circuit.py) on dyadic orders has such an error at $r=2$. The sum is already 106 at $q=4$ and 68,543,140 at $q=8$. [Lean theorem `plane_witness_bound`](SparseNegatives.lean)

## Replay

From `lean/` in the project checkout with its Mathlib dependencies, run

```sh
lake env lean -R ../tools/plane-incidence -o .lake/build/lib/lean/SparseNegatives.olean ../tools/plane-incidence/SparseNegatives.lean
lake env leanchecker -v SparseNegatives
```

The formal statements are uniform in the size of the finite incidence system. The specialization uses only the plane's number of lines and the degree of $p$.
