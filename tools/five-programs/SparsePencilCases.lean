import SparsePencilDIV

namespace SparsePencilCases

open Polynomial SparsePencilChart SparsePencilRoots SparsePencilDIV

theorem rank_one {K N : ℕ} (s : Fin K → ℤ) (g : Fin K → Polynomial ℤ) (d : ℕ) (B : Polynomial ℝ)
    (b : Fin K → ℝ) (span : ∀ i,(g i).map realMap=C (b i)*B) (live : sumP s g d≠0)
    (fac : factorialPoly N∣sumP s g d) (hb : B≠0) : N+1≤B.support.card := by
  let k := ∑ i,(s i:ℝ)*(b i)^d
  have eq : (sumP s g d).map realMap=C k*B^d := by
    simp only [sumP,Polynomial.map_sum,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_pow,span,mul_pow]
    simp [k,Finset.sum_mul,mul_assoc,realMap]
  have nz : (sumP s g d).map realMap≠0 := (Polynomial.map_ne_zero_iff (Int.cast_injective (α:=ℝ))).mpr live
  have scalar : k≠0 := by intro z; rw [eq,z] at nz; simp at nz
  have h := SparseNegativeRoots.negative B hb (samples N) (by
    intro x hx
    refine ⟨neg_samples x hx,?_⟩
    have z := real_roots fac x hx
    rw [eq,eval_mul,eval_C,eval_pow] at z
    by_contra b
    exact (mul_ne_zero scalar (pow_ne_zero _ b)) z)
  simpa only [size_samples] using h

theorem cubic_exponent {N T : ℕ} (linear : N≤3*(2*T-1)) (enough : 6^13≤T) : N^25≤T^27 := by
  have small : N≤6*T := by omega
  have base : 6^25≤T^2 := by
    calc 6^25 ≤ (6^13)^2 := by decide
         _ ≤ T^2 := Nat.pow_le_pow_left enough 2
  calc N^25 ≤ (6*T)^25 := Nat.pow_le_pow_left small 25
       _ = 6^25*T^25 := mul_pow _ _ _
       _ ≤ T^2*T^25 := Nat.mul_le_mul_right _ base
       _ = T^27 := by ring

theorem quartic_exponent {N T : ℕ} (linear : N≤4*(2*T-1)) (enough : 8^5≤T) : N^5≤T^6 := by
  have small : N≤8*T := by omega
  calc N^5 ≤ (8*T)^5 := Nat.pow_le_pow_left small 5
       _ = 8^5*T^5 := mul_pow _ _ _
       _ ≤ T*T^5 := Nat.mul_le_mul_right _ enough
       _ = T^6 := by ring

theorem cubic_sharp (x : Polynomial ℤ) :
    (2*(x+2))^3-(x+3)^3-(x+1)^3=6*(x+1)*(x+2)*(x+3) := by ring

theorem quartic_sharp (x : Polynomial ℤ) :
    (2*(2*x+5))^4-5*((2*x+6)^4+(2*x+4)^4)+4*(2:Polynomial ℤ)^4 =
      96*(x+1)*(x+2)*(x+3)*(x+4) := by ring

#print axioms rank_one
#print axioms cubic_exponent
#print axioms quartic_sharp

end SparsePencilCases
