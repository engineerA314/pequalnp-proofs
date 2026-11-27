import SparseNegativeRoots

namespace SparsePencilChart

open Polynomial

variable {ι : Type} [Fintype ι]

noncomputable def mix (s a b : ι → ℝ) (d : ℕ) (A B : Polynomial ℝ) : Polynomial ℝ :=
  ∑ i, C (s i)*(C (a i)*A+C (b i)*B)^d

noncomputable def chart (s a b : ι → ℝ) (d : ℕ) := mix s a b d X 1

theorem readMix (s a b : ι → ℝ) (d : ℕ) (A B : Polynomial ℝ) (x : ℝ) :
    (mix s a b d A B).eval x=∑ i,s i*(a i*A.eval x+b i*B.eval x)^d := by
  simp [mix,eval_finsetSum]

theorem chart_value (s a b : ι → ℝ) (d : ℕ) (x : ℝ) :
    (chart s a b d).eval x=∑ i,s i*(a i*x+b i)^d := by simp [chart,readMix]

theorem affine_degree (a b : ℝ) : (C a*X+C b : Polynomial ℝ).natDegree≤1 := by
  apply natDegree_add_le_of_degree_le
  · exact (natDegree_C_mul_le a X).trans (by simp)
  · simp

theorem chart_degree (s a b : ι → ℝ) (d : ℕ) : (chart s a b d).natDegree≤d := by
  simp only [chart,mix,mul_one]
  apply natDegree_sum_le_of_forall_le
  intro i _
  exact (natDegree_C_mul_le _ _).trans (by simpa using natDegree_pow_le_of_le d (affine_degree (a i) (b i)))

theorem chart_top (s a b : ι → ℝ) (d : ℕ) : (chart s a b d).coeff d=∑ i,s i*(a i)^d := by
  simp only [chart,mix,mul_one,finsetSum_coeff,coeff_C_mul]
  apply Finset.sum_congr rfl
  intro i _
  have top := coeff_pow_of_natDegree_le (m:=d) (affine_degree (a i) (b i))
  simpa [coeff_C_mul_X] using congrArg (fun x : ℝ => s i*x) top

theorem nonpole (s a b : ι → ℝ) (d : ℕ) (A B : Polynomial ℝ) (x : ℝ) (hb : B.eval x≠0) :
    (mix s a b d A B).eval x=(chart s a b d).eval (A.eval x/B.eval x)*(B.eval x)^d := by
  rw [readMix,chart_value,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_assoc,←mul_pow]
  congr 2
  field_simp

theorem pole (s a b : ι → ℝ) (d : ℕ) (A B : Polynomial ℝ) (x : ℝ) (hb : B.eval x=0) :
    (mix s a b d A B).eval x=(chart s a b d).coeff d*(A.eval x)^d := by
  simp only [readMix,chart_top,hb,mul_zero,add_zero,mul_pow,Finset.sum_mul,mul_assoc]

theorem chart_ne (s a b : ι → ℝ) (d : ℕ) (A B : Polynomial ℝ) (hb : B≠0) (live : mix s a b d A B≠0) :
    chart s a b d≠0 := by
  intro vanish
  apply mul_ne_zero live hb
  apply Polynomial.funext
  intro x
  by_cases zero : B.eval x=0
  · simp [zero]
  · rw [eval_mul,nonpole s a b d A B x zero,vanish]
    simp

#print axioms chart_ne

end SparsePencilChart
