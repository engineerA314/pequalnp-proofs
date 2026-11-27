import ConjugateMatrixCore

namespace PermanentConjugateBound

open Finset PermanentJetOnes ConjugateMatrixCore Module

def projection (p q : ℕ) : Mat (p+1) (q+1) →ₗ[ℂ] (Fin p → ℂ) × (Fin q → ℂ) where
  toFun t := (fun i => ∑ j,t (i.castSucc,j),fun j => ∑ i,t (i,j.castSucc))
  map_add' _ _ := by ext <;> simp [Finset.sum_add_distrib]
  map_smul' _ _ := by ext <;> simp [Finset.mul_sum]

theorem all_zero {m : ℕ} (v : Fin (m+1) → ℂ) (totalZero : ∑ i,v i=0)
    (initial : ∀ j : Fin m,v j.castSucc=0) : ∀ i,v i=0 := by
  rw [Fin.sum_univ_castSucc] at totalZero
  have last : v (Fin.last m)=0 := by simpa [initial] using totalZero
  exact Fin.lastCases last initial

theorem raw_bound (p q : ℕ) (L : Submodule ℂ (Mat (p+1) (q+1)))
    (one : ∀ t∈L,total t=0) (two : ∀ t∈L,disjointSum t=0) : finrank ℂ (core L) ≤ p+q := by
  let F := (projection p q).domRestrict (core L)
  have inj : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨t,ht⟩ h
    have row (i : Fin p) : ∑ j,t (i.castSucc,j)=0 := congrFun (congrArg Prod.fst h) i
    have col (j : Fin q) : ∑ i,t (i,j.castSucc)=0 := congrFun (congrArg Prod.snd h) j
    have tot : ∑ i,∑ j,t (i,j)=0 := one t ht.1
    have tot' : ∑ j,∑ i,t (i,j)=0 := by rw [sum_comm]; exact tot
    have z := centered_in_core two ht ⟨all_zero _ tot row,all_zero _ tot' col⟩
    exact Subtype.ext z
  simpa [finrank_prod] using (LinearMap.finrank_le_finrank_of_injective inj)

theorem core_bound (n : ℕ) (L : Submodule ℂ (Mat (n+1) (n+1))) (h : flat L) :
    finrank ℂ (core L) ≤ 2*n := by
  rw [two_mul]
  apply raw_bound n n L (linear_condition n L h)
  cases n with
  | zero => intro t _; simp [disjointSum,Finset.univ_unique]
  | succ n => exact quadratic_condition n L h

noncomputable def defect {p q : ℕ} (L : Submodule ℂ (Mat p q)) : ℕ := finrank ℂ L - finrank ℂ (core L)

theorem defect_bound (n : ℕ) (L : Submodule ℂ (Mat (n+1) (n+1))) (h : flat L) :
    finrank ℂ L ≤ 2*n + defect L := by
  unfold defect
  have := core_bound n L h
  omega

theorem stable_bound (n : ℕ) (L : Submodule ℂ (Mat (n+1) (n+1))) (h : flat L)
    (closed : ∀ x∈L,bar x∈L) : finrank ℂ L ≤ 2*n := by
  have b := core_bound n L h
  rw [core_eq L closed] at b
  exact b

theorem few_exceptions (n : ℕ) (L E : Submodule ℂ (Mat (n+1) (n+1))) (h : flat L)
    (span : L ≤ core L ⊔ E) : finrank ℂ L ≤ 2*n+finrank ℂ E := by
  have inc := Submodule.finrank_mono span
  have dim := Submodule.finrank_sup_add_finrank_inf_eq (core L) E
  have := core_bound n L h
  omega

#print axioms core_bound
#print axioms few_exceptions

end PermanentConjugateBound
