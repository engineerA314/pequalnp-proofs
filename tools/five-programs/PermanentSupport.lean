import PEqualNP.Gct.Helpers.SupportCriterion
import Mathlib

/-! Converse to the project's rank-one support test. An overlapping
nonconstant coefficient certifies failure on the parametrized family. -/

namespace PermanentSupport

open Finset MvPolynomial PEqualNP.Gct.Helpers.Support
variable {n d : ℕ}

noncomputable def forms (u : Fin d → Fin n → ℂ) : MvPolynomial (Fin d) ℂ :=
  ∏ j, (1+∑ i, C (u i j) * X i)

noncomputable def weight (n : ℕ) (a : Fin d →₀ ℕ) : ℂ :=
  ((n-∑ i,a i).factorial : ℂ) * ∏ i, ((a i).factorial : ℂ)

noncomputable def family (u w : Fin d → Fin n → ℂ) : MvPolynomial (Fin d) ℂ :=
  ∑ a∈(forms w).support, monomial a (weight n a * (forms u).coeff a * (forms w).coeff a)

noncomputable def value (u w : Fin d → Fin n → ℂ) (c : Fin d → ℂ) :=
  MvPolynomial.eval (fun p : Fin n × Fin n => 1+∑ i,c i*u i p.1*w i p.2) (PEqualNP.Gct.permPoly ℂ n)

theorem value_eq (u w : Fin d → Fin n → ℂ) (c : Fin d → ℂ) :
    value u w c = MvPolynomial.eval c (family u w) := by
  classical
  rw [value,support_criterion]
  simp [family,forms,weight,eval_monomial,Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]

theorem family_coeff (u w : Fin d → Fin n → ℂ) (a : Fin d →₀ ℕ) :
    (family u w).coeff a = weight n a * (forms u).coeff a * (forms w).coeff a := by
  classical
  rw [family,MvPolynomial.coeff_sum]
  by_cases ha : a∈(forms w).support
  · rw [Finset.sum_eq_single_of_mem a ha]
    · simp
    · intro b hb diff
      simp [MvPolynomial.coeff_monomial,diff]
  · have off : (forms w).coeff a=0 := MvPolynomial.notMem_support_iff.mp ha
    rw [off,mul_zero]
    apply Finset.sum_eq_zero
    intro b hb
    have ne : b≠a := fun e => ha (e ▸ hb)
    simp [MvPolynomial.coeff_monomial,ne]

theorem weight_ne (n : ℕ) (a : Fin d →₀ ℕ) : weight n a≠0 := by
  unfold weight
  exact mul_ne_zero (by exact_mod_cast (Nat.factorial_pos _).ne')
    (Finset.prod_ne_zero_iff.mpr fun _ _ => by exact_mod_cast (Nat.factorial_pos _).ne')

theorem iff_disjoint (u w : Fin d → Fin n → ℂ) :
    (∀ c, value u w c=(n.factorial : ℂ)) ↔
    ∀ a : Fin d →₀ ℕ, a≠0 → (forms u).coeff a * (forms w).coeff a=0 := by
  classical
  constructor
  · intro fixed a nonzero
    have eq : family u w=C (n.factorial : ℂ) := by
      apply MvPolynomial.funext
      intro c
      simpa only [← value_eq,eval_C] using fixed c
    have same := congrArg (fun f : MvPolynomial (Fin d) ℂ => f.coeff a) eq
    rw [family_coeff,MvPolynomial.coeff_C] at same
    simp [Ne.symm nonzero] at same
    have zero : weight n a * ((forms u).coeff a * (forms w).coeff a)=0 := by
      rw [← mul_assoc]
      simpa only [mul_eq_zero] using same
    exact (mul_eq_zero.mp zero).resolve_left (weight_ne _ _)
  · intro dis
    exact level_of_disjoint n d u w dis

theorem overlap_witness (u w : Fin d → Fin n → ℂ) (a : Fin d →₀ ℕ) (nz : a≠0)
    (left : a∈(forms u).support) (right : a∈(forms w).support) :
    ∃ c, value u w c≠(n.factorial : ℂ) := by
  classical
  by_contra! fixed
  exact (mul_ne_zero (mem_support_iff.mp left) (mem_support_iff.mp right)) ((iff_disjoint u w).mp fixed a nz)

#print axioms iff_disjoint
#print axioms overlap_witness

end PermanentSupport
