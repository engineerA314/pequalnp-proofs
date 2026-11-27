# The exact number of lines needed to saturate the projection tests

Let $q=s^2$, let $K=\mathbb F_s$, and use a nonempty collection $D$ of the $s+1$ directions from the [square-order construction](square-projections.md). Say a set $R$ of active ordinary lines *saturates* the tests when, at **every** affine abscissa and in **every** selected direction, all $s$ projected ordinates occur. One can then treat each point membership test of that network as permanently true on supersets of $R$.

The exact minimum number of ordinary lines required is **$s$ if a direction is omitted and $2s-1$ if all directions are selected**. The minimum allows arbitrary slopes. In both cases horizontal lines attain it. [Lean theorems `proper_optimum` and `full_optimum`](ProjectionAnchors.lean)

Inspect the single column $x=0$. The intercepts of the active lines must attain all $s$ values in every selected projection. This requires at least $s$ intercepts. If direction $m$ is omitted, take as horizontal intercepts all vectors on the one-dimensional kernel of $m$. Every selected projection is nonzero on that kernel and takes all $s$ values.

If all directions are selected, the intercepts must meet every affine line of $K^2$. The finite affine blocking theorem of Jamison and of Brouwer and Schrijver gives the lower bound $2s-1$. Two intersecting coordinate axes attain it. Taking all those intercepts on horizontals gives the same collection in every column. The characterization is of simultaneous saturation of the projection tests. The separate downstream gate lower bound uses saturation as a sufficient condition. [Original Brouwer–Schrijver paper](https://ir.cwi.nl/pub/9858/9858D.pdf) · [Application to shared boundary wires](full-boundary.md)

## A Lean proof of the geometric input

The accompanying module proves the blocking theorem in every positive dimension $d$ over a finite field. If $B\subseteq K^d$ meets every affine hyperplane, fix $a\in B$ and form

$$F(v)=\prod_{b\in B\setminus\{a\}}(1-(b-a)\cdot v).$$

It equals one at $v=0$. For $v\ne0$, some $b\in B$ lies on $b\cdot v=a\cdot v+1$, so the product is zero. Its sum over all $v$ is therefore one. The finite-field summation lemma used in Mathlib's Chevalley–Warning proof shows that every polynomial of total degree below $d(s-1)$ has sum zero. Consequently $|B|-1\ge d(s-1)$. The union of the coordinate axes has $d(s-1)+1$ points and meets every affine hyperplane. The module proves both bounds. This formalizes a classical finite-geometry theorem and applies it to the cost of saturating a circuit boundary. [Lean source](AffineBlocking.lean)

## Replay

From `lean/` run

```sh
lake env lean -R ../tools/plane-incidence -o .lake/build/lib/lean/ProjectionTests.olean ../tools/plane-incidence/ProjectionTests.lean
lake env lean -R ../tools/plane-incidence -o .lake/build/lib/lean/AffineBlocking.olean ../tools/plane-incidence/AffineBlocking.lean
lake env lean -R ../tools/plane-incidence -o .lake/build/lib/lean/ProjectionAnchors.olean ../tools/plane-incidence/ProjectionAnchors.lean
lake env leanchecker -v AffineBlocking
lake env leanchecker -v ProjectionAnchors
```
