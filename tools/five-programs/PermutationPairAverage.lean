import PermanentJetOnes

namespace PermutationPairAverage

open Finset PEqualNP.Gct.Helpers

theorem two_positions (k : ℕ) (r s : Fin (k+2)) (hrs : r≠s) (f : Fin (k+2) → Fin (k+2) → ℂ) :
    (∑ σ : Equiv.Perm (Fin (k+2)), f (σ r) (σ s)) =
      (k.factorial : ℂ) * ∑ i, ∑ j, if i=j then 0 else f i j := by
  classical
  have split (σ : Equiv.Perm (Fin (k+2))) :
      f (σ r) (σ s)=∑ i,∑ j,(if σ r=i ∧ σ s=j then (1 : ℂ) else 0)*f i j := by
    simp [ite_and,ite_mul]
  have card (i j : Fin (k+2)) : (∑ σ : Equiv.Perm (Fin (k+2)), if σ r=i ∧ σ s=j then (1 : ℂ) else 0) =
      if i=j then 0 else (k.factorial : ℂ) := by
    by_cases h : i=j
    · subst j
      have impossible (σ : Equiv.Perm (Fin (k+2))) : ¬(σ r=i ∧ σ s=i) :=
        fun z => hrs (σ.injective (z.1.trans z.2.symm))
      simp [impossible]
    · have z := card_two (i,r) (j,s) hrs h
      simpa [hrs,h,and_comm] using congrArg (fun x : ℕ => (x : ℂ)) z
  rw [sum_congr rfl (fun σ _ => split σ),sum_comm]
  simp only [mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [← sum_mul,card]
  by_cases h : i=j <;> simp [h]

theorem off_diag (k : ℕ) (a : Fin (k+2) → ℂ) (h : ∑ i,a i=0) (c d : ℂ) :
    (∑ i,∑ j,if i=j then 0 else (c+d*a i)*(c-d*a j)) =
      ((k+2 : ℕ) : ℂ)*((k+1 : ℕ) : ℂ)*c^2+d^2*∑ i,a i^2 := by
  classical
  have remove (i j : Fin (k+2)) : (if i=j then 0 else (c+d*a i)*(c-d*a j)) =
      (c+d*a i)*(c-d*a j)-(if i=j then (c+d*a i)*(c-d*a i) else 0) := by
    by_cases eq : i=j <;> simp [eq]
  simp_rw [remove,sum_sub_distrib,Finset.sum_ite_eq,mem_univ,ite_true,← mul_sum]
  have diag (i : Fin (k+2)) : (c+d*a i)*(c-d*a i)=c^2-d^2*a i^2 := by ring
  simp_rw [diag]
  simp [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.sum_mul,h]
  ring

#print axioms two_positions
#print axioms off_diag

end PermutationPairAverage
