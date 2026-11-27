import GramMatrixLevel

namespace GramWeights

open scoped ComplexConjugate
open PermanentSupport GramPermanent
variable {n d : ℕ}

noncomputable def weighted (u : Fin d → Fin n → ℂ) (t : Fin d → ℝ) :=
  fun i j => (Real.sqrt (t i) : ℂ) * u i j

theorem rescale (u : Fin d → Fin n → ℂ) (t : Fin d → ℝ) (ht : ∀ i,0≤t i) :
    value u (dual u) (fun i => (t i : ℂ)) =
      value (weighted u t) (dual (weighted u t)) (fun _ => 1) := by
  apply congrArg (fun g => MvPolynomial.eval g (PEqualNP.Gct.permPoly ℂ n))
  funext p
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have sq : ((Real.sqrt (t i) : ℝ) : ℂ)*((Real.sqrt (t i) : ℝ) : ℂ)=(t i : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt (ht i)
  simp only [weighted,dual,map_mul,Complex.conj_ofReal,one_mul]
  rw [← sq]
  ring

theorem zero_value : value (fun _ : Fin d => fun _ : Fin n => (0 : ℂ))
    (dual (fun _ : Fin d => fun _ : Fin n => (0 : ℂ))) (fun _ => 1)=(n.factorial : ℂ) := by
  simp [value,dual,PEqualNP.Gct.permPoly,Matrix.permanent,Matrix.mvPolynomialX_apply,Fintype.card_perm]

theorem active_iff (u : Fin d → Fin n → ℂ) (t : Fin d → ℝ) (ht : ∀ i,0≤t i) :
    (n.factorial : ℝ)<(value u (dual u) (fun i => (t i : ℂ))).re ↔
    ∃ i j, 0<t i ∧ u i j≠0 := by
  rw [rescale u t ht]
  constructor
  · intro lt
    by_contra! absent
    have z : weighted u t=(fun _ _ => 0) := by
      funext i j
      by_cases positive : 0<t i
      · simp [weighted,absent i j positive]
      · have eq : t i=0 := le_antisymm (le_of_not_gt positive) (ht i)
        simp [weighted,eq]
    rw [z,zero_value] at lt
    simp at lt
  · rintro ⟨i,j,pos,nz⟩
    exact strict (weighted u t) (fun _ => 1) (fun _ => by norm_num) i j
      (mul_ne_zero (by exact_mod_cast (Real.sqrt_pos.mpr pos).ne') nz)

#print axioms active_iff

end GramWeights
