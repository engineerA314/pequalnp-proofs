import PermanentSupport
import Mathlib.Combinatorics.Nullstellensatz

namespace PermanentGrid

open MvPolynomial PermanentSupport
variable {n d : ℕ}

theorem form_degree (w : Fin d → Fin n → ℂ) (i : Fin d) : (forms w).degreeOf i≤n := by
  classical
  unfold forms
  apply (degreeOf_prod_le _ _ _).trans
  calc
    _ ≤ ∑ _j : Fin n, 1 := by
      apply Finset.sum_le_sum
      intro j _
      apply (degreeOf_add_le _ _ _).trans (max_le (by simp) ?_)
      apply (degreeOf_sum_le _ _ _).trans
      apply Finset.sup_le
      intro a _
      apply (degreeOf_mul_le _ _ _).trans
      simp [degreeOf_X]
      split <;> omega
    _ = n := by simp

theorem family_degree (u w : Fin d → Fin n → ℂ) (i : Fin d) : (family u w).degreeOf i≤n := by
  apply degreeOf_le_iff.mpr
  intro a ha
  have nz := mem_support_iff.mp ha
  rw [family_coeff] at nz
  have inW : a∈(forms w).support := mem_support_iff.mpr (right_ne_zero_of_mul nz)
  exact (monomial_le_degreeOf i inW).trans (form_degree w i)

def grid (n : ℕ) : Finset ℂ := (Finset.range (n+1)).map (Nat.castEmbedding : ℕ ↪ ℂ)

theorem grid_iff (u w : Fin d → Fin n → ℂ) :
    (∀ c : Fin d → ℂ, (∀ i,c i∈grid n) → value u w c=(n.factorial : ℂ)) ↔
    (∀ c : Fin d → ℂ, value u w c=(n.factorial : ℂ)) := by
  classical
  refine ⟨fun onGrid => ?_,fun all c _ => all c⟩
  let P := family u w - C (n.factorial : ℂ)
  have eq : P=0 := by
    apply eq_zero_of_eval_zero_at_prod_finset P (fun _ => grid n)
    · intro i
      have bound : P.degreeOf i≤n := by
        rw [show P=family u w+ -C (n.factorial : ℂ) by simp [P,sub_eq_add_neg]]
        apply (degreeOf_add_le _ _ _).trans (max_le (family_degree u w i) ?_)
        rw [← map_neg,degreeOf_C]
        exact Nat.zero_le _
      simpa [grid] using Nat.lt_succ_of_le bound
    · intro c hc
      simp [P,← value_eq,onGrid c hc]
  have identity : family u w=C (n.factorial : ℂ) := sub_eq_zero.mp eq
  intro c
  rw [value_eq,identity,eval_C]

theorem integer_witness (u w : Fin d → Fin n → ℂ) (a : Fin d →₀ ℕ) (nz : a≠0)
    (left : a∈(forms u).support) (right : a∈(forms w).support) :
    ∃ c : Fin d → ℂ, (∀ i,c i∈grid n) ∧ value u w c≠(n.factorial : ℂ) := by
  classical
  by_contra! fixed
  obtain ⟨c,diff⟩ := overlap_witness u w a nz left right
  exact diff ((grid_iff u w).mp fixed c)

#print axioms integer_witness

end PermanentGrid
