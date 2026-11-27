# Counting SAT models and recovering a witness by variable elimination

This gives a positive, restricted algorithm for the P = NP search program. Given a variable order, bucket elimination computes the exact number of satisfying assignments on the variables that occur and returns a satisfying assignment whenever one exists. The semantic Lean solver accepts exactly the project's SAT language, including malformed binary inputs. The table implementation is polynomial time on inputs supplied with an order of induced width $O(\log L)$, where $L$ is the encoded input length. On unrestricted input the width can grow linearly. [Raw-word acceptance and model count](BucketBits.lean) · [Search and witness theorem](BucketWitness.lean)

Build one factor per clause, with value 0 or 1. At variable $v$, multiply together the factors whose scopes contain $v$. For each assignment of their remaining scope, sum the products obtained at $v=0$ and $v=1$, and replace the bucket by this table. All other factors are independent of $v$. Store a bit telling which extension had positive count and read those bits in reverse elimination order to recover a model. Empty clauses, empty formulas, duplicate signs, tautologies and sparse binary identifiers follow the project's CNF evaluation. [Verified factor projection](BucketCount.lean) · [Classical directional resolution connection](https://www.sciencedirect.com/science/article/pii/B9781483214528501093) · [Dechter’s bucket elimination framework](https://ics.uci.edu/~dechter/publications/r76A.pdf)

Let $w$ be the maximum number of distinct *remaining* variables in a processed bucket. There are at most $2^w$ output rows per bucket. Each clause begins in one bucket and each computed table is routed to at most one later bucket. Reading the original clauses and multiplying the incident tables therefore costs $2^{w+1}$ times a polynomial in $L$ for the executable representation. Each stored number counts assignments to eliminated variables. Factors merged into a bucket have disjoint sets of previously eliminated variables, so these counts and their products have $O(n+1)$ bits. The executable records $w$ while it runs. A good supplied order is sufficient; the bound makes no assumption that every input admits one. The formal identities cover correctness and model recovery, and the running-time argument here analyzes the separate explicit table implementation. [Counter and search implementation](bucket_sat.py)

Against exhaustive truth assignments, the implementation passed 1,424 comparisons. On a chain of 256 variables it counted 257 models at width one and returned a model. Pinning the two ends to conflicting truth values returned zero. On a star with 11 leaves, changing the order changed the width from 11 to one, while both runs counted 2,049 models. Run `python3 tools/five-programs/bucket_sat.py`.

From the repository's `lean/` directory run

```sh
lake build PEqualNP.Defs.Search
for module in CNFReader BucketCount BucketWitness BucketBits; do
  lake env lean -R ../tools/five-programs -o ".lake/build/lib/lean/$module.olean" "../tools/five-programs/$module.lean" && lake env leanchecker -v "$module" || exit 1
done
```
