# How many proof lines does a critical assignment falsify?

For each of $K$ indispensable axioms, fix one assignment satisfying all other axioms. If $t_i$ is the number of lines falsified by assignment $i$ in a shared, sound, binary refutation, then
$$\sum_i 2^{-t_i}\le \tfrac12.$$
Consequently, for every integer $m\ge0$,
$$\sum_i t_i \ \ge\ (m+3)K-2^{m+1}.$$
At $m=\lfloor\log_2 K\rfloor$ this gives the exact least possible total for the abstract binary semantic model. For $K=2^m$, the bound is $K(m+1)$. A premise may be reused arbitrarily often. Each recorded line occurrence is counted once for each assignment falsifying it. [Kraft inequality for every line](ProofWitnessKraft.lean) · [Integer bound and both pigeonhole applications](ProofWitnessIncidence.lean)

To see the source of the inequality, start each witness at weight one and halve its weight each time it falsifies a new line. The sum of the current weights of witnesses falsifying any single line is at most one half. An input line has at most one such witness. At a derived line, each witness falsifying the conclusion already falsified one of at most two parents. Their combined previous weight is at most one, and the update immediately halves it. The contradiction is false on every witness. The final integral bound follows by applying $m+3\le t+2^{m+2-t}$ separately to every witness and summing.

There is also a bound for each threshold $q\ge1$. If $M_q$ is the number of lines falsified by more than $q$ witnesses, then $K\le q(M_q+1)$. Treating every other line as an extra source yields a frontier of at most $M_q+1$ sources covering all witnesses. This proof applies to an arbitrary finite test family when every input line is false on at most $q$ tests. [Threshold theorem](ProofWitnessScale.lean)

The exact bound is attained by taking the witnesses as leaves of a balanced binary tree. A node's line is false exactly on the leaves below it, and its children semantically imply the node. For a power of two there are $m+1$ false lines per witness. For a general $K$, split $K$ recursively into halves: the leaves have the two adjacent depths and splitting one leaf at depth $m$ increases the total incidence by $m+3$. On the project's parity-resolution and syntactic integer bit-pigeonhole refutations, $K=2^\ell\binom{2^\ell+1}{2}$. At $\ell=2,3$ any refutation has respectively at least **256** and **2,656** witness–line incidences. The measure is semantic. Converting it into stronger bit-size bounds requires a cap on the incidences one cheap derived line can carry. [Project parity target](https://pequalnp.com/lemma#L-pcx-023) · [Integer-system target](https://pequalnp.com/lemma#L-alg-006)

The companion test uses exact rational arithmetic on 128 balanced trees and 500 reproducible shared binary derivations. From `lean/` rebuild the parity and integer modules listed in the [previous integer-system note](integer-pigeonhole.md), then run

```sh
for m in ProofWitnessScale ProofWitnessKraft ProofWitnessIncidence
do
  lake env lean -R ../tools/five-programs -o ".lake/build/lib/lean/$m.olean" "../tools/five-programs/$m.lean" && lake env leanchecker -v "$m" || exit 1
done
python3 ../tools/five-programs/witness_incidence.py
```
