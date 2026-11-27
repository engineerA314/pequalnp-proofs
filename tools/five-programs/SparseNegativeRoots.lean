import Mathlib

namespace SparseNegativeRoots

open Polynomial

theorem variations (p : Polynomial ℝ) (h : p≠0) : p.signVariations+1 ≤ p.support.card := by
  by_cases e : p.eraseLead=0
  · have one := card_support_eq_one_of_eraseLead_eq_zero h e
    rw [signVariations_eq_eraseLead_add_ite h,e]
    simp [h,one]
  · have ih := variations p.eraseLead e
    have sz := card_support_eraseLead_add_one h
    have step := signVariations_le_eraseLead_succ p
    omega
termination_by p.support.card
decreasing_by have := card_support_eraseLead_add_one h; omega

noncomputable def reflect (p : Polynomial ℝ) := p.sum fun n a => monomial n (a*(-1)^n)

theorem reflect_coeff (p : Polynomial ℝ) (k : ℕ) :
    (reflect p).coeff k=p.coeff k*(-1)^k := by
  classical
  rw [reflect,coeff_sum,sum_def]
  by_cases hk : k∈p.support
  · rw [Finset.sum_eq_single k]
    · simp
    · intro i _ ne
      simp [coeff_monomial,Ne.symm ne]
    · exact fun h => False.elim (h hk)
  · have zero := notMem_support_iff.mp hk
    rw [zero,zero_mul,Finset.sum_eq_zero]
    intro i hi
    have ne : i≠k := fun h => hk (h ▸ hi)
    simp [coeff_monomial,Ne.symm ne]

theorem reflect_support (p : Polynomial ℝ) : (reflect p).support=p.support := by
  ext k
  simp [mem_support_iff,reflect_coeff]

theorem reflect_eval (p : Polynomial ℝ) (x : ℝ) : (reflect p).eval x=p.eval (-x) := by
  rw [eval_eq_sum,eval_eq_sum,sum_def,sum_def,reflect_support]
  apply Finset.sum_congr rfl
  intro k _
  rw [reflect_coeff,show -x=(-1)*x by ring,mul_pow]
  ring

theorem positive (p : Polynomial ℝ) (h : p≠0) (S : Finset ℝ)
    (roots : ∀ x∈S,0<x ∧ p.eval x=0) : S.card+1≤p.support.card := by
  classical
  let pos := p.roots.filter (fun x => 0<x)
  have sub : S⊆pos.toFinset := by
    intro x hx
    exact Multiset.mem_toFinset.mpr (Multiset.mem_filter.mpr ⟨(mem_roots h).mpr (roots x hx).2,(roots x hx).1⟩)
  have sizes := (Finset.card_le_card sub).trans (Multiset.toFinset_card_le pos)
  have v := p.roots_countP_pos_le_signVariations
  rw [Multiset.countP_eq_card_filter] at v
  have limit := variations p h
  change S.card≤(p.roots.filter (fun x => 0<x)).card at sizes
  omega

theorem negative (p : Polynomial ℝ) (h : p≠0) (S : Finset ℝ)
    (roots : ∀ x∈S,x<0 ∧ p.eval x=0) : S.card+1≤p.support.card := by
  classical
  have non : reflect p≠0 := by
    intro z
    have e := reflect_support p
    rw [z,support_zero] at e
    exact h (support_eq_empty.mp e.symm)
  have pos := positive (reflect p) non (S.image (fun x => -x)) (by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    exact ⟨neg_pos.mpr (roots x hx).1,by simpa [reflect_eval] using (roots x hx).2⟩)
  simpa [reflect_support,Finset.card_image_of_injective _ neg_injective] using pos

#print axioms negative

end SparseNegativeRoots
