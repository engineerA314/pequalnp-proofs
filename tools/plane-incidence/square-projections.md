# Square-order plane incidence with up to $\sqrt q$ active lines

Let $q=s^2$ for a prime power $s$, let $N=q^2+q+1$, and let $1\le t\le s$. On the Desarguesian plane $PG(2,q)$ there is an explicit binary monotone circuit of size $O(N(t+1))$ that computes incidence on **every point assignment and every assignment with at most $t$ active lines**. At $t=\sqrt q$ the size is $O(N\sqrt q)=o(Nq)$. Thus even a growing line budget of $\sqrt q$ cannot establish the proposed uniform $\Omega(Nq)$ lower bound through correctness on those assignments alone. The project conjecture uses the larger budget $q$. [Project statement](https://pequalnp.com/lemma#L-meta-1629)

## Distinguishing a point from the wrong ordinates

Write $E=\mathbb F_{s^2}=K+K\theta$ over $K=\mathbb F_s$. For an affine point $(x,z)$ and an ordinary line with slope $a$ and intercept $b$, test whether $z=ax+b$. For a pair $(u,v)\in K^2$, use projections $h_\lambda(u,v)=u+\lambda v$ with $\lambda\in K$ and $h_\infty(u,v)=v$. Two distinct ordinates agree in at most one of the $s+1$ directions. Choose any $t+1$ directions. Accept a point when every direction sees some active line with the same projected ordinate as the point. With at most $t$ active ordinary lines, every nonincident line spoils at most one test. Incidence passes every test. This is the agreement argument for superimposed codes applied to the ordinates. [Lean proof](ProjectionTests.lean) · [Kautz and Singleton, 1964](https://doi.org/10.1109/TIT.1964.1053689)

The guarantee is sharp for this network. At the affine origin take one horizontal line at a nonzero ordinate from the kernel of each selected direction. These $t+1$ lines are distinct and miss the origin, yet the origin passes every projected test. [Lean theorem `sharp`](ProjectionTests.lean)

## Computing the projected incidences with shared gates

Write $a=a_0+a_1\theta$ and let $Y_{a,b}$ be a line bit. For each selected direction $h$, build the following three layers. Each displayed OR is a binary OR tree.

$$W[a_0,a_1,j]=\bigvee_{b:\,h(b)=j}Y_{a_0+a_1\theta,b}$$

$$V[a_0,c_1,j]=\bigvee_{a_1\in K}W[a_0,a_1,j-c_1a_1]$$

$$H[c_0,c_1,j]=\bigvee_{a_0\in K}V[a_0,c_1,j-c_0a_0].$$

For a fixed $x$, use $c_0=h(x)$ and $c_1=h(\theta x)$. Linearity gives $h(ax+b)=c_0a_0+c_1a_1+h(b)$. Thus $H[c_0,c_1,h(z)]$ is the projected test for $(x,z)$. The same $W,V,H$ serve all $q^2$ affine points. Each layer has $s^3$ groups of $s$ wires. The three layers cost exactly $3s^3(s-1)$ binary ORs per direction. [Lean theorem `three_layers`](ProjectionTests.lean)

For each affine point, intersect its $t+1$ predicates, intersect with its point bit, and take the OR over the points. Separately add the intersections at the slope points at infinity, the vertical lines, and the line at infinity. The gate count of the supplied construction is

$$3(t+1)s^3(s-1)+(t+2)q^2-1+(q^2+q-1)+(q^2+2q-1)+(q+1)+3=(4t+7)q^2-3(t+1)s^3+4q+1.$$

The first summand builds the shared layers. The second handles affine point bits. The next three are the three projective boundary cases. The last three OR gates combine the four answers. The formula counts the emitted netlist before any common-subexpression elimination. [Binary circuit generator](square_projection_circuit.py)

## Replay and coverage

From `lean/` run

```sh
lake env lean -R ../tools/plane-incidence -o .lake/build/lib/lean/ProjectionTests.olean ../tools/plane-incidence/ProjectionTests.lean
lake env leanchecker -v ProjectionTests
```

The Lean file proves direction uniqueness over any field, all three logical layers, sparse membership, and the one-extra-line witness. The binary gate count follows from the layer sizes above and is asserted when building each concrete netlist. From the repository root run `python3 tools/plane-incidence/square_projection_circuit.py`.

| $q$ | $t$ | Gates | Line sets checked at this $t$ |
| ---: | ---: | ---: | ---: |
| 4 | 2 | 185 | all 232 |
| 9 | 3 | 1,252 | all 125,672 |
| 16 | 4 | 4,993 | 512 deterministic samples |
| 25 | 5 | 14,726 | 512 deterministic samples |

For each tested line set, the verifier activates each point singly and then activates all points outside the line union. Monotonicity makes those probes sufficient for every point assignment. All instances also check their specific false positive at $t+1$ lines against a separate field-arithmetic incidence oracle.
