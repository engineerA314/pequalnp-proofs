# Gate costs after fixing one point in the original scalar circuit

Let $C$ be any binary monotone circuit satisfying the project's incident singleton positives and all negatives with at most $q$ selected lines. Write $N=q^2+q+1$. Fix the sole selected point $p$ and keep **all** line selectors as variables. For an original gate $g$, let $f_{g,p}(Y)$ be its cofactor function. Assign $g$ one count at $p$, for parameters $b,r\ge1$, if

1. More than $b$ different singleton lines turn $f_{g,p}$ on.
2. Every set of at most $r$ lines missing $p$ leaves it off. In particular the singleton lines in (1) all go through $p$.
3. This Boolean function of **all** line subsets differs from both constants and every earlier wire's cofactor, including raw inputs.

For **every point** the number of distinct original gates meeting these tests is at least

$$\min(\lfloor q/b\rfloor,\lfloor q/r\rfloor).$$

There is no depth restriction. The circuit has one scalar output. Constants, copies and semantic duplicates cannot contribute, even if the repeated function is computed by a different gate type. For $b=r=1$, at least $q$ gates pass at each point. Writing $m_g$ for the number of points where $g$ passes gives

$$Nq\le\sum_{g\in C}m_g.$$

A line-only gate can count for at most one point because two different pencils have only one line in common. A point-only gate has a constant cofactor. Thus if every mixed gate counts at most $K\ge1$ times, the circuit needs at least $Nq/K$ gates. In the unrestricted scalar problem the multiplicities need their own bound. [Formal theorem on the original circuit](PlaneHonestCost.lean) · [Project conjecture](https://pequalnp.com/lemma#L-meta-1629)

## Counting a shared subcircuit

For a fixed point, identify a wire with any earlier identical cofactor, free of charge. Trace backwards from the output through the remaining gates satisfying (1) and (2), stopping at other wires. The trace can be represented with at most $c+1$ stopping wires if it crosses $c$ charged gates. Sharing and repeated uses of the same wire do not add a new stopping wire. If the stopping wires true on $Y$ are all true on $Y'$, monotonicity transfers acceptance from $Y$ to $Y'$. [Physical gate accounting](WireFrontier.lean)

Suppose $c<z$ where $bz\le q$ and $rz\le q$. For each stopping wire that can be activated by at most $r$ lines missing $p$, select one such set of lines. Their union $U$ misses $p$ and has size at most $r(c+1)\le q$. Every other stopping wire accepts at most $b$ singleton lines. Together those wires cover at most $b(c+1)\le q$ lines, while $q+1$ lines pass through $p$. Choose an uncovered one, $w$. Every stopping wire true at $\{w\}$ is true at $U$. This contradicts acceptance at $\{w\}$ and rejection at $U$. The project previously used outside witnesses to find an honest member of a specified AND-list. The frontier argument applies them to every monotone DAG and counts physically distinct, fresh gates within one cofactor. [Project definition of honesty](../../lean/PEqualNP/MetaComplexity/Helpers/Deg2Defs.lean) · [Project factor-list argument](../../lean/PEqualNP/MetaComplexity/Helpers/Deg2Cover.lean) · [Sparse frontier lemma](SparseRows.lean)

One can also sum over $b=1,\ldots,q$ with $r=1$. The degree-weighted sum of gate–point counts is at least $N\sum_{b=1}^q\lfloor q/b\rfloor=\Theta(Nq\log q)$. Each eligible pair with $d$ singleton neighbors contributes $d-1$. The extra logarithm weights multiple singleton neighbors of the same gate. [Formal harmonic inequality](PlaneHonestCost.lean)

## Replay

The executable tests every point, all $2^N$ line assignments and every parameter pair $1\le b,r\le q$ at orders 2, 3 and 4. Repeating the output as both operands of a new AND changes none of the charges. At $q=4$ the direct circuit has 84 fresh gate–point pairs, exactly $Nq$, with one gate counted at 20 points. The completed selector circuit has 125 pairs. Run the following from the repository root.

```sh
python3 tools/plane-incidence/honest_cofactors.py 2 3 4
```

After building the dependencies of the [sparse point-output theorem](sparse-point-outputs.md) and the [fork tradeoff](fork-tradeoff.md), build and replay each new module from `lean/`.

```sh
for mod in WireFrontier PlaneHonestCost; do
  lake env lean -R ../tools/plane-incidence -o ".lake/build/lib/lean/$mod.olean" "../tools/plane-incidence/$mod.lean" && lake env leanchecker -v "$mod" || exit 1
done
```
