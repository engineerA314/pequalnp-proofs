import Mathlib

namespace ClauseSubcubes

variable {V : Type} [Fintype V] [DecidableEq V]
abbrev Cube (V : Type) := Finset (V × Bool)

def Fits (M : Cube V) (x : V → Bool) := ∀ v b,(v,b)∈M → x v=b
def OK (M : Cube V) := ∀ v,(v,false)∈M → (v,true)∉M
def coords (M : Cube V) := M.image Prod.fst
def forced (M : Cube V) (v : V) := decide ((v,true)∈M)

noncomputable def models (M : Cube V) : Finset (V → Bool) := by
  classical exact Finset.univ.filter (Fits M)

theorem mem_models (M : Cube V) (x : V → Bool) : x∈models M ↔ Fits M x := by
  classical simp [models]

omit [Fintype V] in
theorem force_fit (M : Cube V) (ok : OK M) : Fits M (forced M) := by
  intro v b h
  cases b with
  | false => simp [forced,ok v h]
  | true => simp [forced,h]

omit [Fintype V] in
theorem same_coord (M : Cube V) (ok : OK M) (x : V → Bool) (hx : Fits M x) (v : V) (hv : v∈coords M) :
    x v=forced M v := by
  obtain ⟨⟨u,b⟩,hu,rfl⟩ := Finset.mem_image.mp hv
  exact (hx u b hu).trans ((force_fit M ok) u b hu).symm

noncomputable def complete (M : Cube V) (z : (↥(coords M)ᶜ) → Bool) (v : V) :=
  if h : v∈coords M then forced M v else z ⟨v,Finset.mem_compl.mpr h⟩

noncomputable def freeEquiv (M : Cube V) (ok : OK M) : ↥(models M) ≃ (↥(coords M)ᶜ → Bool) where
  toFun x := fun v => x.val v.val
  invFun z := ⟨complete M z,(mem_models M _).mpr (by
    intro v b h
    have mem : v∈coords M := Finset.mem_image.mpr ⟨(v,b),h,rfl⟩
    simp [complete,mem,force_fit M ok v b h])⟩
  left_inv x := by
    apply Subtype.ext
    funext v
    by_cases mem : v∈coords M
    · simpa [complete,mem] using (same_coord M ok _ ((mem_models _ _).mp x.property) v mem).symm
    · simp [complete,mem]
  right_inv z := by
    funext v
    have no : v.val∉coords M := Finset.mem_compl.mp v.property
    simp [complete,no]

noncomputable def volume (M : Cube V) := by
  classical exact if OK M then 2^(Fintype.card V-(coords M).card) else 0

theorem exact_volume (M : Cube V) : (models M).card=volume M := by
  classical
  by_cases h : OK M
  · simpa [volume,h,Finset.card_compl] using Fintype.card_congr (freeEquiv M h)
  · have empty : models M=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x mem
      have fits := (mem_models _ _).mp mem
      apply h
      intro v f t
      exact Bool.false_ne_true ((fits v false f).symm.trans (fits v true t))
    simp [volume,h,empty]

variable {I : Type} [DecidableEq I]

def compatible (C : I → Cube V) (J : Finset I) := ∀ i∈J,∀ j∈J,OK (C i∪C j)

omit [Fintype V] [DecidableEq I] in
theorem pairwise_iff (C : I → Cube V) (J : Finset I) : OK (J.biUnion C) ↔ compatible C J := by
  constructor
  · intro ok i hi j hj v f t
    have sub : C i∪C j ⊆ J.biUnion C := by
      intro q h
      rcases Finset.mem_union.mp h with left | right
      · exact Finset.mem_biUnion.mpr ⟨i,hi,left⟩
      · exact Finset.mem_biUnion.mpr ⟨j,hj,right⟩
    exact ok v (sub f) (sub t)
  · intro all v f t
    obtain ⟨i,hi,fi⟩ := Finset.mem_biUnion.mp f
    obtain ⟨j,hj,tj⟩ := Finset.mem_biUnion.mp t
    exact all i hi j hj v (Finset.mem_union_left _ fi) (Finset.mem_union_right _ tj)

omit [DecidableEq I] in
theorem intersection (C : I → Cube V) (J : Finset I) :
    J.inf (fun i => models (C i))=models (J.biUnion C) := by
  classical
  ext x
  simp only [Finset.mem_inf,mem_models]
  constructor
  · intro all v b mem
    obtain ⟨i,hi,pair⟩ := Finset.mem_biUnion.mp mem
    exact all i hi v b pair
  · intro all i hi v b mem
    exact all v b (Finset.mem_biUnion.mpr ⟨i,hi,mem⟩)

omit [DecidableEq I] in
open Classical in
theorem count (C : I → Cube V) (J : Finset I) :
    (((J.inf (fun i => (models (C i))ᶜ)).card : ℤ)) =
      ∑ t ∈ J.powerset.filter (fun t => decide (compatible C t)),
        (-1:ℤ)^t.card*(2^(Fintype.card V-(coords (t.biUnion C)).card) : ℕ) := by
  classical
  rw [Finset.inclusion_exclusion_card_inf_compl,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t _
  rw [intersection,exact_volume]
  by_cases ok : compatible C t <;> simp [volume,pairwise_iff,ok]

#print axioms count

end ClauseSubcubes
