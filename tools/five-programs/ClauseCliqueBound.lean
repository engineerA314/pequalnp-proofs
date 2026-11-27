import ClauseSubcubes

namespace ClauseCliqueBound

open ClauseSubcubes
variable {V : Type} [DecidableEq V] {I : Type} [LinearOrder I]

noncomputable def forward (C : I → Cube V) (J : Finset I) (i : I) : Finset I := by
  classical exact J.filter (fun j => i<j ∧ OK (C i∪C j))

noncomputable def cliques (C : I → Cube V) (J : Finset I) : Finset (Finset I) := by
  classical exact J.powerset.filter (compatible C)

theorem bound (C : I → Cube V) (J : Finset I) :
    (cliques C J).card ≤ 1+∑ i ∈ J,2^(forward C J i).card := by
  classical
  let box := fun i => (forward C J i).powerset.image (fun t => insert i t)
  have sub : cliques C J⊆insert ∅ (J.biUnion box) := by
    intro t ht
    obtain ⟨incl,ok⟩ := Finset.mem_filter.mp ht
    have inc := Finset.mem_powerset.mp incl
    by_cases empty : t=∅
    · simp [empty]
    · have live := Finset.nonempty_iff_ne_empty.mpr empty
      let i := t.min' live
      have atI : i∈t := Finset.min'_mem _ _
      refine Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨i,inc atI,?_⟩)
      refine Finset.mem_image.mpr ⟨t.erase i,Finset.mem_powerset.mpr ?_,Finset.insert_erase atI⟩
      intro j hj
      obtain ⟨diff,hit⟩ := Finset.mem_erase.mp hj
      refine Finset.mem_filter.mpr ⟨inc hit,lt_of_le_of_ne (Finset.min'_le _ _ hit) diff.symm,ok i atI j hit⟩
  have boxes (i : I) : (box i).card ≤ 2^(forward C J i).card :=
    (Finset.card_image_le).trans (le_of_eq (Finset.card_powerset _))
  calc (cliques C J).card ≤ (insert ∅ (J.biUnion box)).card := Finset.card_le_card sub
       _ ≤ (J.biUnion box).card+1 := Finset.card_insert_le _ _
       _ ≤ (∑ i ∈ J,(box i).card)+1 := Nat.add_le_add_right Finset.card_biUnion_le _
       _ ≤ (∑ i ∈ J,2^(forward C J i).card)+1 := Nat.add_le_add_right (Finset.sum_le_sum (fun i _ => boxes i)) _
       _ = _ := Nat.add_comm _ _

theorem degeneracy (C : I → Cube V) (J : Finset I) (d : ℕ) (order : ∀ i∈J,(forward C J i).card≤d) :
    (cliques C J).card≤1+J.card*2^d := by
  calc (cliques C J).card ≤ _ := bound C J
       _ ≤ 1+∑ _i ∈ J,2^d := Nat.add_le_add_left (Finset.sum_le_sum fun i hi => Nat.pow_le_pow_right (by decide) (order i hi)) _
       _ = _ := by simp

#print axioms degeneracy

end ClauseCliqueBound
