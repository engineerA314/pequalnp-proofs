import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! A sparse-promise example with a simultaneous rise at every incidence
at every joining AND of a selector tree, even when each child is necessary. -/

namespace ForkFactoring

variable {L : Type*} [DecidableEq L]

def block (F : Prop) (K Y : Finset L) : Prop := ∀ w ∈ K, F ∨ w ∈ Y

theorem factor (F : Prop) (K Y : Finset L) : block F K Y ↔ F ∨ K ⊆ Y := by
  classical
  by_cases h : F
  · simp [block,h]
  · simp only [block,h,false_or]
    exact ⟨fun a w hw => a w hw,fun a w hw => a hw⟩

theorem promised (F : Prop) (K Y : Finset L) (short : Y.card < K.card) : block F K Y ↔ F := by
  rw [factor]
  exact or_iff_left (fun h => (Nat.not_le_of_lt short) (Finset.card_le_card h))

theorem join (F : Prop) (A B Y : Finset L) : block F (A ∪ B) Y ↔ block F A Y ∧ block F B Y := by
  rw [factor,factor,factor,Finset.union_subset_iff]
  tauto

theorem both_rise (A B Y : Finset L) (ha : A.Nonempty) (hb : B.Nonempty) :
    (¬block False A ∅ ∧ block True A Y) ∧ (¬block False B ∅ ∧ block True B Y) := by
  simp [factor,ha.ne_empty,hb.ne_empty]

theorem incomparable (A B : Finset L) (ha : A.Nonempty) (hb : B.Nonempty) (apart : Disjoint A B) :
    (block False A A ∧ ¬block False B A) ∧ (block False B B ∧ ¬block False A B) := by
  obtain ⟨a,am⟩ := ha
  obtain ⟨b,bm⟩ := hb
  simp only [factor,false_or,Finset.Subset.refl]
  exact ⟨⟨trivial, fun h => Finset.disjoint_left.mp apart (h bm) bm⟩,
         ⟨trivial, fun h => Finset.disjoint_left.mp apart am (h am)⟩⟩

/-- The set of all retained selectors witnesses failure whenever at least
one leaf is omitted, including replacing a joining AND by either child. -/
theorem necessary (K keep : Finset L) (proper : keep ⊂ K) :
    keep.card < K.card ∧ block False keep keep ∧ ¬block False K keep := by
  have less := Finset.card_lt_card proper
  exact ⟨less,(factor ..).mpr (Or.inr Finset.Subset.rfl),fun h =>
    (Nat.not_le_of_lt less) (Finset.card_le_card ((factor ..).mp h |>.resolve_left id))⟩

#print axioms promised
#print axioms necessary
#print axioms incomparable

end ForkFactoring
