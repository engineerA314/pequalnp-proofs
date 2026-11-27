# From a conjugation rank violation to a permanent witness

Flatten any spanning matrices into the columns of a complex matrix $B$, and put $k=\operatorname{rank}B$ and $r=\operatorname{rank}[B\ \overline B]$. The conjugation-stable part of their span has dimension exactly $2k-r$. For $n\ge2$, if $2k-r>2n-2$, some input direction $T$ and integer $1\le s\le n$ satisfy $\operatorname{per}(J+sT)\ne n!$. The strict inequality is a sufficient screening condition. [Rank identity](ConjugateRankTest.lean) · [Finite probe theorem](PermanentLineProbes.lean) · [Underlying dimension bound](conjugate-permanent.md)

If any input direction has nonzero entry sum, the linear term detects it. Otherwise the rank violation yields a nonzero centered matrix in the conjugation-stable part. Taking a real or imaginary component gives a nonzero real centered $T$ in the span. Its ordered different-row-and-column product sum is $\sum_{ij} T_{ij}^2>0$. The polynomial along the line has degree at most $n$. If it agreed with $n!$ at all $n+1$ integers from 0 through $n$, it would be constant and both derivative tests would vanish. At zero the value is already $n!$. [Directional certificate and energy](PermanentRealWitness.lean)

For Gaussian-rational input the executable uses rational row reduction. It computes the real directions in the complex span, extracts an integer direction by clearing denominators, and returns complex generator coefficients along with the first disagreeing probe. Coefficients are checked by direct reconstruction. The rank test and linear algebra take polynomially many rational operations. The optional exact permanent evaluations use subset dynamic programming and have exponential worst-case cost. A size-four example with $k=8$, $r=9$ yields a nonzero centered $2$-by-$2$ block with rows $(-1,1)$ and $(1,-1)$. At $s=1$ the permanent is 28 and $4!=24$. [Rational checker and example](conjugate_probe.py)

Replay the [conjugation calculation](conjugate-permanent.md) first, then run in `lean/`.

```sh
for m in ConjugateRankTest PermanentRealWitness PermanentLineProbes
do
  lake env lean -R ../tools/five-programs -o ".lake/build/lib/lean/$m.olean" "../tools/five-programs/$m.lean" && lake env leanchecker -v "$m" || exit 1
done
python3 ../tools/five-programs/conjugate_probe.py
```
