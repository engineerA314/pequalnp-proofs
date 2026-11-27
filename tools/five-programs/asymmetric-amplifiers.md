# Optimal simultaneous modulus amplification at two endpoints

For any positive precisions $a,b$, there is a single integer polynomial $F$ of degree $a+b-1$ such that, for every modulus $m\ge0$, $m\mid x$ implies $m^a\mid F(x)$ and $m\mid x-1$ implies $m^b\mid F(x)-1$. This degree is minimal for a polynomial serving every modulus. The case $a=b=k$ gives the polynomial and degree $2k-1$ in L-clb-033. [Construction and exact project statement](ModulusAmplifier.lean) · [Project target](https://pequalnp.com/lemma#L-clb-033)

All simultaneous amplifiers satisfy exactly the two polynomial congruences
$$X^a\mid F,\qquad (1-X)^b\mid 1-F.$$
For necessity at zero it suffices to test $x=m$ for each positive $m$. Polynomial evaluation gives $m\mid F(m)-F(0)$. If $a>0$, then $F(0)$ is divisible by every positive integer, so $F=XQ$. Cancelling $m$ in the sample identity gives the same test at precision $a-1$ for $Q$. Applying the argument to $1-F(1-X)$ treats the other endpoint. [Converse and sharp degree](ModulusConverse.lean)

The construction uses $F_{0,b}=1$, $F_{a,0}=0$ for $a>0$, and
$$F_{a+1,b+1}=X F_{a,b+1}+(1-X)F_{a+1,b}.$$
Every solution is $F_{a,b}+X^a(1-X)^b H$ for an integer polynomial $H$. There is a unique solution of degree below $a+b$. Since $F(0)=0$ and $F(1)=1$, the derivative is nonzero and divisible by $X^{a-1}(1-X)^{b-1}$. This proves the lower bound. The modulus quantifier matters: at the particular modulus $2$, $X^2$ already works for $a=b=2$. [Classification, uniqueness and fixed-modulus example](ModulusClassification.lean)

For $(a,b)=(2,3)$, the polynomial is $6X^2-8X^3+3X^4$. The companion code constructs its integer coefficients and tests the endpoint multiplicities and 118,272 evaluations across 64 asymmetric precision pairs. [Reproducible calculation](modulus_amplifier.py)

From `lean/` run

```sh
for m in ModulusAmplifier ModulusConverse ModulusClassification
do
  lake env lean -R ../tools/five-programs -o ".lake/build/lib/lean/$m.olean" "../tools/five-programs/$m.lean" && lake env leanchecker -v "$m" || exit 1
done
python3 ../tools/five-programs/modulus_amplifier.py
```
