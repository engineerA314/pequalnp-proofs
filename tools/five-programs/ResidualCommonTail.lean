import ResidualStateCount

namespace ResidualCommonTail

open Finset ResidualAntichain ResidualStateCount

theorem absorb {V : Type} [Fintype V] [DecidableEq V] (f : F V) (c : C V)
    (mem : c∈f) (proper : ¬taut c) (below : ∀ d∈f,c⊆d) : normal f={c} := by
  classical
  ext d
  constructor
  · intro hd
    obtain ⟨u,minimal⟩ := Finset.mem_filter.mp hd
    have inc := below d (Finset.mem_filter.mp u).1
    by_contra no
    have diff : c≠d := fun eq => no (Finset.mem_singleton.mpr eq.symm)
    exact minimal c (Finset.mem_filter.mpr ⟨mem,proper⟩) (Finset.ssubset_iff_subset_ne.mpr ⟨inc,diff⟩)
  · intro eq
    rw [Finset.mem_singleton.mp eq]
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨mem,proper⟩,?_⟩
    intro e incl lt
    exact lt.not_ge (below e (Finset.mem_filter.mp incl).1)

def tailClause (a b : ℕ) : C (Fin a ⊕ Fin b) := univ.image fun j : Fin b => (Sum.inr j,true)
def family (a b : ℕ) : F (Fin a ⊕ Fin b) :=
  univ.image fun i : Fin a => insert (Sum.inl i,true) (tailClause a b)

theorem evaluates (a b : ℕ) (x : Fin a → Bool) (y : Fin b → Bool) :
    sat (Sum.elim x y) (family a b) ↔ (∀ i,x i=true) ∨ ∃ j,y j=true := by
  classical
  have perClause (i : Fin a) : hit (Sum.elim x y) (insert (Sum.inl i,true) (tailClause a b)) ↔
      x i=true ∨ ∃ j,y j=true := by simp [hit,tailClause]
  constructor
  · intro h
    by_cases ty : ∃ j,y j=true
    · exact Or.inr ty
    · left
      intro i
      exact ((perClause i).mp (h _ (Finset.mem_image_of_mem _ (mem_univ i)))).resolve_right ty
  · intro h c hc
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hc
    exact (perClause i).mpr (h.imp (fun yes => yes i) id)

theorem tail_count (a b : ℕ) :
    (∑ y : Fin b → Bool,∑ x : Fin a → Bool, if sat (Sum.elim x y) (family a b) then 1 else 0 : ℕ) =
      (2^b-1)*2^a+1 := by
  classical
  let off : Fin b → Bool := fun _ => false
  let on : Fin a → Bool := fun _ => true
  have hx (x : Fin a → Bool) : (∀ i,x i=true) ↔ x=on := ⟨fun h => funext h,fun h _ => h ▸ rfl⟩
  have hy (y : Fin b → Bool) : (∃ j,y j=true) ↔ y≠off := by
    constructor
    · rintro ⟨j,h⟩ rfl
      contradiction
    · intro h
      by_contra! neg
      exact h (funext fun i => by have := neg i; cases e : y i <;> simp_all [off])
  have per (y : Fin b → Bool) : (∑ x : Fin a → Bool,if sat (Sum.elim x y) (family a b) then (1 : ℕ) else 0) =
      if y=off then 1 else 2^a := by
    by_cases e : y=off <;> simp [evaluates,hx,hy,e]
  simp_rw [per]
  rw [Finset.sum_ite]
  have one : (univ.filter (fun y : Fin b → Bool => y=off))={off} := by ext; simp
  simp [one,Finset.filter_ne',Finset.card_erase_of_mem,Nat.mul_comm,Nat.add_comm]

#print axioms absorb
#print axioms tail_count

end ResidualCommonTail
