import PermanentSymmetric

/-! The multivariate permanent on a Hermitian Gram family is a sum of squares. -/
namespace GramPermanent

open Finset MvPolynomial PermanentSupport
open scoped ComplexConjugate
variable {n d : ℕ}

def dual (u : Fin d → Fin n → ℂ) := fun i j => conj (u i j)

theorem mapped (u : Fin d → Fin n → ℂ) :
    forms (dual u)=MvPolynomial.map (starRingEnd ℂ) (forms u) := by
  classical
  simp [forms,dual]

theorem conjugate_coeff (u : Fin d → Fin n → ℂ) (a : Fin d →₀ ℕ) :
    (forms (dual u)).coeff a=conj ((forms u).coeff a) := by
  rw [mapped,MvPolynomial.coeff_map]

theorem same_support (u : Fin d → Fin n → ℂ) : (forms (dual u)).support=(forms u).support := by
  classical
  ext a
  simp [MvPolynomial.mem_support_iff,conjugate_coeff]

noncomputable def scale (n : ℕ) (a : Fin d →₀ ℕ) : ℝ :=
  ((n-∑ i,a i).factorial : ℝ) * ∏ i, ((a i).factorial : ℝ)

noncomputable def term (u : Fin d → Fin n → ℂ) (t : Fin d → ℝ) (a : Fin d →₀ ℕ) : ℝ :=
  scale n a * Complex.normSq ((forms u).coeff a) * ∏ i, t i ^ a i

theorem square_sum (u : Fin d → Fin n → ℂ) (t : Fin d → ℝ) :
    value u (dual u) (fun i => (t i : ℂ)) =
    ((∑ a∈(forms u).support,term u t a : ℝ) : ℂ) := by
  classical
  rw [value,PEqualNP.Gct.Helpers.Support.support_criterion]
  change (∑ a∈(forms (dual u)).support,weight n a*(forms u).coeff a*(forms (dual u)).coeff a*
    ∏ i,(t i : ℂ)^a i)=_
  rw [same_support,Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [conjugate_coeff,mul_assoc (weight n a),Complex.mul_conj]
  simp [term,weight,scale,Complex.ofReal_prod]

theorem scale_pos (n : ℕ) (a : Fin d →₀ ℕ) : 0<scale n a := by
  unfold scale
  exact mul_pos (by exact_mod_cast Nat.factorial_pos _) (Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos _)

theorem constant_term (u : Fin d → Fin n → ℂ) (t : Fin d → ℝ) : term u t 0=n.factorial := by
  simp [term,scale,forms,PEqualNP.Gct.Helpers.Support.coeff_zero_prod]

theorem in_support (u : Fin d → Fin n → ℂ) : 0∈(forms u).support := by
  simp [mem_support_iff,forms,PEqualNP.Gct.Helpers.Support.coeff_zero_prod]

theorem nonzero_term (u : Fin d → Fin n → ℂ) (i : Fin d) (j : Fin n) (nz : u i j≠0) :
    ∃ a : Fin d →₀ ℕ, a≠0 ∧ a∈(forms u).support := by
  classical
  by_contra! h
  apply PermanentSymmetric.nonconstant u i j nz
  ext a
  by_cases ha : a=0
  · subst a
    simp [forms,PEqualNP.Gct.Helpers.Support.coeff_zero_prod]
  · rw [notMem_support_iff.mp (h a ha),MvPolynomial.coeff_one]
    simp [Ne.symm ha]

theorem strict (u : Fin d → Fin n → ℂ) (t : Fin d → ℝ) (ht : ∀ i,0<t i)
    (i : Fin d) (j : Fin n) (nz : u i j≠0) :
    (n.factorial : ℝ)<(value u (dual u) (fun k => (t k : ℂ))).re := by
  classical
  obtain ⟨a,ne,occurs⟩ := nonzero_term u i j nz
  have pos (b : Fin d →₀ ℕ) (hb : b∈(forms u).support) : 0<term u t b :=
    mul_pos (mul_pos (scale_pos _ _) (Complex.normSq_pos.mpr (mem_support_iff.mp hb)))
      (Finset.prod_pos fun k _ => pow_pos (ht k) _)
  have remainder : 0<∑ b∈(forms u).support.erase 0, term u t b := by
    apply Finset.sum_pos'
    · intro b hb
      exact (pos b (Finset.mem_of_mem_erase hb)).le
    · exact ⟨a,Finset.mem_erase.mpr ⟨ne,occurs⟩,pos a occurs⟩
  have aggregate := Finset.sum_erase_add (forms u).support (term u t) (in_support u)
  rw [square_sum,Complex.ofReal_re]
  rw [constant_term] at aggregate
  linarith

#print axioms square_sum
#print axioms strict

end GramPermanent
