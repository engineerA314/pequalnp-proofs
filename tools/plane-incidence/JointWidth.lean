import SharedOrStars

namespace JointWidth

open SharedOrStars PEqualNP.MetaComplexity.Helpers

variable {V : Type} [DecidableEq V]

def Wide (t : ℕ) (S : List (Finset V)) : Prop := ∀ J : Finset ℕ, (joint S J).card≤t+J.card

theorem initial (S : List (Finset V)) (one : ∀ j, (S.getD j ∅).card≤1) : Wide 0 S := by
  intro J
  apply le_trans Finset.card_biUnion_le
  rw [zero_add,Finset.card_eq_sum_ones]
  exact Finset.sum_le_sum fun j _ => one j

private theorem snoc_sub (S : List (Finset V)) (U : Finset V) (J : Finset ℕ) :
    joint (S++[U]) J ⊆ joint S (J.erase S.length) ∪ U := by
  intro x h
  obtain ⟨j,hj,hx⟩ := Finset.mem_biUnion.mp h
  by_cases eq : j=S.length
  · subst j
    exact Finset.mem_union_right _ (by simpa only [getD_snoc_eq] using hx)
  · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
      ⟨j,Finset.mem_erase.mpr ⟨eq,hj⟩,by rwa [getD_snoc_ne _ _ _ _ eq] at hx⟩)

private theorem unchanged (S : List (Finset V)) (U : Finset V) (J : Finset ℕ) (notUsed : S.length ∉ J) :
    joint (S++[U]) J=joint S J := Finset.biUnion_congr rfl fun _j hj =>
  getD_snoc_ne _ _ _ _ (fun e => notUsed (e ▸ hj))

theorem small (t : ℕ) (S : List (Finset V)) (old : Wide t S) (U : Finset V) (one : U.card≤1) :
    Wide t (S++[U]) := by
  intro J
  by_cases used : S.length ∈ J
  · have b := (Finset.card_le_card (snoc_sub S U J)).trans (Finset.card_union_le _ _)
    have h := old (J.erase S.length)
    have c := Finset.card_erase_add_one used
    omega
  · rw [unchanged S U J used]; exact old J

theorem parents (t k : ℕ) (S : List (Finset V)) (old : Wide t S) (U : Finset V) (F : Finset ℕ)
    (cover : U⊆joint S F) (few : F.card≤k+1) : Wide (t+k) (S++[U]) := by
  intro J
  by_cases used : S.length ∈ J
  · let K := J.erase S.length
    have sub : joint S K ∪ U ⊆ joint S (K∪F) := by
      intro x hx
      rcases Finset.mem_union.mp hx with h | h
      · obtain ⟨j,hj,mem⟩ := Finset.mem_biUnion.mp h
        exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_union_left _ hj,mem⟩
      · obtain ⟨j,hj,mem⟩ := Finset.mem_biUnion.mp (cover h)
        exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_union_right _ hj,mem⟩
    have h := (Finset.card_le_card ((snoc_sub S U J).trans sub)).trans (old (K∪F))
    have union := Finset.card_union_le K F
    have c : K.card+1=J.card := Finset.card_erase_add_one used
    omega
  · rw [unchanged S U J used]
    have := old J
    omega

theorem dominated (t : ℕ) (S : List (Finset V)) (old : Wide t S) (U : Finset V) (i : ℕ)
    (h : U⊆S.getD i ∅) : Wide t (S++[U]) := by
  exact parents t 0 S old U {i} (by simpa [joint] using h) (by simp)

theorem join (t : ℕ) (S : List (Finset V)) (old : Wide t S) (U : Finset V) (i j : ℕ)
    (h : U⊆S.getD i ∅ ∪ S.getD j ∅) : Wide (t+1) (S++[U]) := by
  exact parents t 1 S old U {i,j} (by simpa [joint] using h) Finset.card_le_two

theorem each (t : ℕ) (S : List (Finset V)) (h : Wide t S) (i : ℕ) : (S.getD i ∅).card≤t+1 := by
  simpa [joint] using h {i}

end JointWidth
