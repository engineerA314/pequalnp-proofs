# Which point inputs must an all-lines merge read?

Let $U$ be a set of points in a finite incidence system. There exists a fan-in-two monotone circuit with a gate that merges on every line and whose value is unchanged by **every** modification of point inputs outside $U$, with arbitrary line inputs fixed, if and only if every line contains at least two points of $U$. In finite geometry the latter condition says that $U$ is a *double blocking set*. [Lean equivalence](BlockingSupport.lean)

For the forward implication, a low merge has at least two distinct alive points on its line. Each such point is essential to that gate. Its singleton assignment with the line on makes the gate true, while turning the point off makes the gate false by lowness. Conversely, restrict the incidence relation to points in $U$. Split its incidences on each line into one marked point and all the other points. The OR of the two corresponding edge functions merges on every line and depends only on points of $U$. One can complete this gate to the full incidence function by including the incidences outside $U$ in a later OR. [Construction used by the Lean proof](../shared-low-merges/UniformLineMerges.lean)

Write $b_2$ for the smallest size of a double blocking set. It follows that $b_2$ is **exactly** the minimum point-support size of an all-lines merge. If the plane has $N$ lines, the gate also depends on all $N$ line inputs. Its inclusive backward cone therefore has at least $N+b_2-1$ distinct gates. The Lean theorem `cone_from_blocking` accepts any proved numerical lower bound on double blocking sets as its hypothesis. [Cone theorem](BlockingSupport.lean)

In the Desarguesian plane $PG(2,q)$ with square $q>16$, Ball and Blokhuis give $b_2=2q+2\sqrt q+2$. Their Theorem 3.1 gives the lower bound and two disjoint Baer subplanes attain it. Substitution yields an inclusive cone lower bound of $N+2q+2\sqrt q+1$, and the optimal number of distinct **point inputs** is $2q+2\sqrt q+2$. The numerical specialization uses their published finite-geometry result. The equivalence and the transfer to gate count have local Lean proofs. [Ball and Blokhuis, On the size of a double blocking set in PG(2,q)](https://web.mat.upc.edu/simeon.michael.ball/double.pdf)

## Replay

From the repository's `lean/` directory, build the dependencies listed in the earlier [shared-merge replay](../shared-low-merges/README.md#reproduce-the-results), then run

```sh
lake env lean -R ../tools/shared-low-merges -o .lake/build/lib/lean/UniformSharedFront.olean ../tools/shared-low-merges/UniformSharedFront.lean
lake env lean -R ../tools/shared-low-merges -o .lake/build/lib/lean/UniformLineMerges.olean ../tools/shared-low-merges/UniformLineMerges.lean
lake env lean -R ../tools/plane-incidence -o .lake/build/lib/lean/BlockingSupport.olean ../tools/plane-incidence/BlockingSupport.lean
lake env leanchecker -v BlockingSupport
```

Both printed axiom lists contain only `propext`, `Classical.choice` and `Quot.sound`. This is a result about a particular wire's cone in the approach to [L-meta-1629](https://pequalnp.com/lemma#L-meta-1629).
