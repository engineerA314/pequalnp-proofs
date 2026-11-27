# Counting SAT by the compatibility graph of clause violations

The solver returns the exact number of assignments over the variable identifiers occurring in a project-format binary CNF, and one satisfying assignment when the count is positive. It runs in polynomial time when the compatibility graph of clause violations has degeneracy $O(\log L)$, where $L$ is the input length. Its running time can grow exponentially on unrestricted formulas. [Executable solver](clique_sat.py) · [Count and decision equivalence on the project's words](ClauseCliqueSAT.lean)

Falsifying a clause fixes a partial assignment. Remove tautological clauses and identify duplicate events, while keeping all original variable identifiers for counting. Two partial assignments are compatible precisely when they agree wherever both are defined. Pairwise compatibility guarantees simultaneous compatibility. Inclusion–exclusion therefore only visits cliques in the graph that joins compatible events. A clique $S$ fixing $r$ variables contributes $(-1)^{|S|}2^{n-r}$. The empty clique contributes $2^n$. [Subcube volume and exact sum](ClauseSubcubes.lean)

Order the vertices by repeatedly removing a remaining vertex of minimum degree. If the largest number of neighbours remaining at removal is $d$, every nonempty clique is determined by its first vertex and a subset of at most $d$ later neighbours. With $m$ deduplicated events there are at most $1+m2^d$ terms. Each term uses two $n$-bit masks, and each coefficient has polynomial bit length when $d=O(\log L)$. The code builds this order and enumerates every clique exactly once. The same terms count completions under any fixed assignment prefix, giving a witness in at most $n$ further counting passes. The kernel checks the clique bound and exact counting identity. The implementation and its runtime analysis are supplied alongside them. [Clique bound for any forward-degree order](ClauseCliqueBound.lean)

As a comparison to the earlier [induced-width solver](bucket-sat.md), a clause containing all $n$ variables makes the primal graph complete. A collection of full-width clauses forbidding different assignments nevertheless has a compatibility graph with no edges. On 48 variables and 256 distinct forbidden words, the new solver uses 257 terms and returns **281,474,976,710,400** models. A 1,024-variable clause uses two terms. Exact counts and the returned witnesses also agreed with exhaustive enumeration on 900 random formulas. [Runnable checks](clique_sat.py)

From `lean/` rebuild `CNFReader` as described in [the word parser](three-colour-words.md), then run

```sh
for m in ClauseSubcubes ClauseCliqueBound ClauseCliqueSAT
do
  lake env lean -R ../tools/five-programs -o ".lake/build/lib/lean/$m.olean" "../tools/five-programs/$m.lean" && lake env leanchecker -v "$m" || exit 1
done
python3 ../tools/five-programs/clique_sat.py
```
