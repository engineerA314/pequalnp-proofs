import ResidualCommonTail

namespace ResidualPrefixShapes

open Finset ResidualAntichain ResidualCommonTail

def waiting {a : ℕ} (b : ℕ) (s : Finset (Fin a)) : F (Fin a ⊕ Fin b) :=
  (univ\s).image (fun i => insert (Sum.inl i,true) (tailClause a b))

def afterPrefix {a : ℕ} (b : ℕ) (s : Finset (Fin a)) (x : Fin a → Bool) :=
  normal (if ∀ i∈s,x i=true then waiting b s else insert (tailClause a b) (waiting b s))

theorem exact_shapes {a b : ℕ} (s : Finset (Fin a)) (x : Fin a → Bool) :
    afterPrefix b s x=if ∀ i∈s,x i=true then normal (waiting b s) else {tailClause a b} := by
  classical
  unfold afterPrefix
  split <;> rename_i h
  · rfl
  · apply absorb _ _ (Finset.mem_insert_self ..)
    · rintro ⟨v,neg,_⟩
      simp [tailClause] at neg
    · intro d hd
      rcases Finset.mem_insert.mp hd with rfl|hd
      · exact Subset.rfl
      · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hd
        exact Finset.subset_insert _ _

theorem two {a b : ℕ} (s : Finset (Fin a)) :
    (univ.image (afterPrefix (a := a) b s)).card ≤ 2 := by
  have inc : univ.image (afterPrefix (a := a) b s) ⊆ {normal (waiting b s),{tailClause a b}} := by
    intro c hc
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hc
    rw [exact_shapes]
    split <;> simp
  exact (Finset.card_le_card inc).trans Finset.card_le_two

theorem semantics {a b : ℕ} (s : Finset (Fin a)) (x z : Fin a → Bool) (y : Fin b → Bool) :
    sat (Sum.elim z y) (afterPrefix b s x) ↔
      sat (Sum.elim (fun i => if i∈s then x i else z i) y) (family a b) := by
  classical
  have tailYes : hit (Sum.elim z y) (tailClause a b) ↔ ∃ j,y j=true := by simp [hit,tailClause]
  have wait : sat (Sum.elim z y) (waiting b s) ↔ (∀ i,i∉s → z i=true) ∨ ∃ j,y j=true := by
    by_cases hy : ∃ j,y j=true
    · have hh := tailYes.mpr hy
      constructor
      · exact fun _ => Or.inr hy
      · intro _ d hd
        obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hd
        exact hit_mono _ (Finset.subset_insert _ _) hh
    · simp only [hy,or_false]
      constructor
      · intro all i hi
        have yes := all _ (Finset.mem_image_of_mem _ (Finset.mem_sdiff.mpr ⟨mem_univ i,hi⟩))
        simpa [hit,tailClause,hy] using yes
      · intro all d hd
        obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hd
        exact ⟨(Sum.inl i,true),Finset.mem_insert_self ..,all i (Finset.mem_sdiff.mp hi).2⟩
  rw [exact_shapes,evaluates]
  split <;> rename_i prefixOn
  · rw [normalized,wait]
    apply or_congr_left
    constructor
    · intro h i
      split <;> rename_i hs
      · exact prefixOn i hs
      · exact h i hs
    · intro h i hs
      simpa [hs] using h i
  · have bad : ¬∀ i : Fin a,(if i∈s then x i else z i)=true := by
      intro h
      apply prefixOn
      intro i hi
      simpa [hi] using h i
    rw [or_iff_right bad]
    simpa [sat] using tailYes

#print axioms two
#print axioms semantics

end ResidualPrefixShapes
