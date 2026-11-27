# Total OR cost of the projection front end

Let $q=s^2$, with $s$ any prime power, and select $d$ directions in the [square-order circuit](square-projections.md). Even if one redesigns the whole front end with arbitrary binary ANDs, ORs, fan-out and depth, producing all its projected line-membership signals requires at least

$$d\,s^3(s-1)$$

distinct binary OR gates. The explicit three-layer construction uses $3d\,s^3(s-1)$ ORs. Its first layer, if itself requested at the boundary, has exact minimum $d\,s^3(s-1)$. The bound applies when those output signals accept each of their prescribed singleton lines and reject the full complement of the corresponding line set. Arbitrary other inputs may behave monotonically. The single output in L-meta-1629 does not require these intermediate signals. [Lean lower bounds](ProjectionFrontCost.lean)

## Which output rows can share an OR

For a selected projection $h:\mathbb F_q\to\mathbb F_s$, an affine abscissa $x$ and a projected value $j$, the prescribed row is the set of ordinary line labels $(a,b)$ such that $h(ax+b)=j$. There are $dqs=ds^3$ rows. Each contains $qs=s^3$ ordinary lines. Two different rows have at most $s^2$ line labels in common. For different abscissas, the two ordinates determine the line and there are only $s^2$ possible pairs from the two fibers. For the same abscissa, two different directions determine the ordinate uniquely, leaving one intercept per slope. Different bins of the same direction at the same abscissa are disjoint. [Finite-field row counts and intersections](ProjectionRows.lean)

For a general family of rows $R_i$ whose pairwise intersections have size at most $b\ge1$, let $A_i$ be the singleton inputs recognized by output $i$. Suppose that output $i$ rejects the full complement of $R_i$. With $k$ binary ORs shared across $m$ such outputs,

$$\sum_i |A_i|\ \le\ b(k+m).$$

On a fixed complement, a false AND needs only one false operand to cover its accepted singletons. A false OR may need both operands. Stop tracing a wire when its singleton support has at most $b$ members. A larger false wire's singleton support lies wholly in the row, so a large false OR can be charged to at most one output. For a given row each charged OR adds at most one extra stopped wire to its trace, giving at most $b$ extra singleton inputs. The exact Boolean-sum lower bound for pairwise overlap $b$ goes back to Wegener, following Nečiporuk, Lamagna, Savage and Tarjan. Mehlhorn states this history and proves a more general exact-sum bound. Here the formal argument is stated for partial outputs and charges OR gates individually. [Shared-network proof](OverlapSums.lean) · [Mehlhorn, 1979](https://citeseerx.ist.psu.edu/document?doi=e3379453f082008ccb0af8ad2343089fcc298c6a&repid=rep1&type=pdf)

Taking $b=s^2$ and $|A_i|\ge s^3$ gives at least $ds^3(s-1)$ ORs even without constructing any particular first-layer wires. For the first layer alone, a row fixes a slope $a$ and the value $h(b)$ of its intercept. Different slopes give disjoint rows and two projections at the same slope determine a unique intercept. Here $b=1$, every row has $s$ input lines, and the same lower bound matches the first layer's OR trees exactly.

## Replay

The [netlist comparison](projection_front_check.py) evaluates all ordinary-line singleton inputs of every projected wire and compares them with independently evaluated field ordinates. It checks every pairwise row intersection at orders $4,9,16,25,49,64,121$. At $q=121$, $d=12$, the front end provides 15,972 rows using 479,160 ORs. The lower bound is 159,720. Each pair of distinct rows meets in either zero or 121 ordinary line labels.

Run `python3 tools/plane-incidence/projection_front_check.py 2 3 4 5 7 8 11` from the repository root. Build dependencies from [the projection construction](square-projections.md) and [the shared-output bound](line-once.md). Then run from `lean/`.

```sh
for mod in ScaledWidth OverlapSums ProjectionRows ProjectionFrontCost; do
  lake env lean -R ../tools/plane-incidence -o ".lake/build/lib/lean/$mod.olean" "../tools/plane-incidence/$mod.lean" && lake env leanchecker -v "$mod" || exit 1
done
```
