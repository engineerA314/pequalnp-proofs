import PEqualNP.Gct.Helpers.PermHessian
import PEqualNP.Gct.Helpers.OrderConditions
import PEqualNP.Gct.Helpers.RealLevel

namespace PermanentJetOnes

open Finset MvPolynomial PEqualNP.Gct PEqualNP.Gct.Helpers

abbrev Mat (p q : ℕ) := Fin p × Fin q → ℂ
abbrev J (n : ℕ) : Mat n n := fun _ => 1

def flat {n : ℕ} (L : Submodule ℂ (Mat n n)) :=
  ∀ t ∈ L, eval (fun a => 1 + t a) (permPoly ℂ n) = (n.factorial : ℂ)

def total {p q : ℕ} (t : Mat p q) := ∑ i, ∑ j, t (i,j)
def disjointSum {p q : ℕ} (t : Mat p q) := ∑ i, ∑ k, ∑ j, ∑ l,
  if i=k ∨ j=l then 0 else t (i,j)*t (k,l)

theorem grad_entry (n : ℕ) (a : Fin (n+1) × Fin (n+1)) :
    eval (J _) (pderiv a (permPoly ℂ (n+1))) = (n.factorial : ℂ) := by
  classical
  simp only [permPoly,Matrix.permanent,Matrix.mvPolynomialX_apply,map_sum,pderiv_perm_mon]
  have card : #{σ : Equiv.Perm (Fin (n+1)) | σ a.2 = a.1} = n.factorial := by
    simpa using (card_perm_agree ({a.2} : Finset _) (fun _ : Fin (n+1) => a.1) (by simp))
  simp only [mem_univ,true_and]
  simp_rw [apply_ite (eval (J _)),eval_prod,eval_X,map_zero]
  simpa [J] using congrArg (fun k : ℕ => (k : ℂ)) card

theorem hess_entry (n : ℕ) (a b : Fin (n+2) × Fin (n+2)) :
    eval (J _) (pderiv a (pderiv b (permPoly ℂ (n+2)))) =
      if a.1=b.1 ∨ a.2=b.2 then 0 else (n.factorial : ℂ) := by
  classical
  let pred := fun σ : Equiv.Perm (Fin (n+2)) => σ b.2=b.1 ∧ a.2≠b.2 ∧ σ a.2=a.1
  have sum : eval (J _) (pderiv a (pderiv b (permPoly ℂ (n+2)))) =
      ∑ σ : Equiv.Perm (Fin (n+2)), if pred σ then (1 : ℂ) else 0 := by
    simp only [permPoly,Matrix.permanent,Matrix.mvPolynomialX_apply,map_sum]
    refine sum_congr rfl fun σ _ => ?_
    rw [pderiv_perm_mon]
    by_cases hb : σ b.2=b.1
    · rw [ite_eq_left ⟨mem_univ _,hb⟩,pderiv_perm_mon]
      by_cases ha : a.2≠b.2 ∧ σ a.2=a.1
      · simp [ha.1,ha.2,hb,pred,J]
      · simp [ha,hb,pred]
    · simp [hb,pred]
  rw [sum]
  by_cases h : a.1=b.1 ∨ a.2=b.2
  · rw [ite_eq_left h]
    apply sum_eq_zero
    intro σ _
    rw [ite_eq_right]
    rintro ⟨hb,ne,ha⟩
    rcases h with hr|hc
    · exact ne (σ.injective (ha.trans (hr.trans hb.symm)))
    · exact ne hc
  · push Not at h
    rw [ite_eq_right (not_or.mpr h)]
    simpa [pred] using congrArg (fun k : ℕ => (k : ℂ)) (card_two a b h.2 h.1)

theorem gradient_hessian {n : ℕ} (L : Submodule ℂ (Mat n n)) (hL : flat L) (t : Mat n n) (ht : t∈L) :
    (∑ a, eval (J n) (pderiv a (permPoly ℂ n)) * t a = 0) ∧
    (∑ a, ∑ b, eval (J n) (pderiv a (pderiv b (permPoly ℂ n))) * t a * t b = 0) := by
  have line (s : ℂ) : eval (J n+s • t) (permPoly ℂ n - C (n.factorial : ℂ)) = 0 := by
    rw [map_sub,eval_C]
    exact sub_eq_zero.mpr (hL _ (L.smul_mem s ht))
  have jet := OrderCond.order_conditions_of_vanish_on_line _ (J n) t line
  simpa using jet

theorem linear_condition (n : ℕ) (L : Submodule ℂ (Mat (n+1) (n+1))) (level : flat L) (t) (ht : t∈L) :
    total t=0 := by
  have h := (gradient_hessian L level t ht).1
  simp only [grad_entry,← mul_sum,Fintype.sum_prod_type] at h
  exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast Nat.factorial_ne_zero n)

theorem quadratic_condition (n : ℕ) (L : Submodule ℂ (Mat (n+2) (n+2))) (level : flat L) (t) (ht : t∈L) :
    disjointSum t=0 := by
  classical
  have h := (gradient_hessian L level t ht).2
  have eq (i j k l : Fin (n+2)) :
      eval (J _) (pderiv (i,j) (pderiv (k,l) (permPoly ℂ (n+2)))) * t (i,j) * t (k,l) =
        (n.factorial : ℂ) * (if i=k ∨ j=l then 0 else t (i,j)*t (k,l)) := by
    rw [hess_entry]
    by_cases h : i=k ∨ j=l <;> simp [h,mul_assoc]
  simp only [Fintype.sum_prod_type,eq,← mul_sum] at h
  have h0 := (mul_eq_zero.mp h).resolve_left (by exact_mod_cast Nat.factorial_ne_zero n)
  unfold disjointSum
  convert h0 using 1
  exact sum_congr rfl fun i _ => sum_comm

#print axioms linear_condition
#print axioms quadratic_condition

end PermanentJetOnes
