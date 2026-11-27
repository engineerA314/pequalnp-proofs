import PartialSums

/-! Joint support accounting when a paid-for leaf set may have b variables.
At an uncharged small gate a root pays b; consulting one or two parents
uses the usual shared DAG accounting. -/

namespace ScaledWidth

open SharedOrStars PEqualNP.MetaComplexity.Helpers

variable {V : Type} [DecidableEq V]

def Wide (b t : ℕ) (S : List (Finset V)) := ∀ J : Finset ℕ, (joint S J).card≤b*(t+J.card)

theorem initial (b : ℕ) (S : List (Finset V)) (small : ∀ i, (S.getD i ∅).card≤b) : Wide b 0 S := by
  intro J
  apply le_trans Finset.card_biUnion_le
  simpa [Nat.mul_comm] using Finset.sum_le_sum (s := J) (fun i _ => small i)

theorem snoc (S : List (Finset V)) (U : Finset V) (J : Finset ℕ) :
    joint (S++[U]) J ⊆ joint S (J.erase S.length) ∪ U := by
  intro x hx
  obtain ⟨i,hi,on⟩ := Finset.mem_biUnion.mp hx
  by_cases eq : i=S.length
  · subst i; exact Finset.mem_union_right _ (by simpa only [getD_snoc_eq] using on)
  · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
      ⟨i,Finset.mem_erase.mpr ⟨eq,hi⟩,by rwa [getD_snoc_ne _ _ _ _ eq] at on⟩)

theorem unchanged (S : List (Finset V)) (U : Finset V) (J : Finset ℕ) (no : S.length∉J) :
    joint (S++[U]) J=joint S J := Finset.biUnion_congr rfl fun _j hj =>
  getD_snoc_ne _ _ _ _ (fun eq => no (eq ▸ hj))

theorem small (b t : ℕ) (S : List (Finset V)) (old : Wide b t S) (U : Finset V) (few : U.card≤b) :
    Wide b t (S++[U]) := by
  intro J
  by_cases used : S.length∈J
  · have h := (Finset.card_le_card (snoc S U J)).trans (Finset.card_union_le _ _)
    have c := Finset.card_erase_add_one used
    calc
      _ ≤ _ := h
      _ ≤ b*(t+(J.erase S.length).card)+b := Nat.add_le_add (old _) few
      _ = b*(t+J.card) := by rw [← c]; ring
  · rw [unchanged S U J used]; exact old J

theorem parents (b t k : ℕ) (S : List (Finset V)) (old : Wide b t S) (U : Finset V) (F : Finset ℕ)
    (cover : U⊆joint S F) (few : F.card≤k+1) : Wide b (t+k) (S++[U]) := by
  intro J
  by_cases used : S.length∈J
  · let K := J.erase S.length
    have sub : joint S K ∪ U ⊆ joint S (K∪F) := by
      intro x hx
      rcases Finset.mem_union.mp hx with a | a
      · obtain ⟨j,hj,hx⟩ := Finset.mem_biUnion.mp a
        exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_union_left _ hj,hx⟩
      · obtain ⟨j,hj,hx⟩ := Finset.mem_biUnion.mp (cover a)
        exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_union_right _ hj,hx⟩
    have h := (Finset.card_le_card ((snoc S U J).trans sub)).trans (old (K∪F))
    have c : K.card+1=J.card := Finset.card_erase_add_one used
    have bound := Finset.card_union_le K F
    exact h.trans (Nat.mul_le_mul_left _ (by omega))
  · rw [unchanged S U J used]
    exact (old J).trans (Nat.mul_le_mul_left _ (by omega))

theorem dominated (b t : ℕ) (S : List (Finset V)) (old : Wide b t S) (U : Finset V) (i : ℕ)
    (h : U⊆S.getD i ∅) : Wide b t (S++[U]) :=
  parents b t 0 S old U {i} (by simpa [joint] using h) (by simp)

theorem join (b t : ℕ) (S : List (Finset V)) (old : Wide b t S) (U : Finset V) (i j : ℕ)
    (h : U⊆S.getD i ∅ ∪ S.getD j ∅) : Wide b (t+1) (S++[U]) :=
  parents b t 1 S old U {i,j} (by simpa [joint] using h) Finset.card_le_two

theorem widen {b t u : ℕ} {S : List (Finset V)} (le : t≤u) (h : Wide b t S) : Wide b u S :=
  fun J => (h J).trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right le _))

theorem each (b t : ℕ) (S : List (Finset V)) (h : Wide b t S) (i : ℕ) : (S.getD i ∅).card≤b*(t+1) := by
  simpa [joint] using h {i}

end ScaledWidth
