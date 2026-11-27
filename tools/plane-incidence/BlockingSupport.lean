import UniformSharedFront
import UniformLineMerges

/-! The minimum point-input support of an all-lines low merge is the double
blocking number of the incidence system. Size bounds from finite geometry
therefore give gate bounds for the union of ancestors of that one wire. -/

namespace BlockingSupport

open PEqualNP.CircuitLowerBounds PEqualNP.LowMerge PEqualNP.MetaComplexity
open LowMergeProof

variable {P L : ℕ}

def DoubleBlocks (I : Fin P → Fin L → Bool) (U : Finset (Fin P)) : Prop :=
  ∀ w : Fin L, 2 ≤ (U.filter fun p => I p w = true).card

/-- Hold line inputs fixed. Changing any subset of points outside U preserves g. -/
def UsesOnly (C : Circuit) (g : ℕ) (U : Finset (Fin P)) (L : ℕ) : Prop :=
  ∀ (x x' : Fin P → Bool) (y : Fin L → Bool), (∀ p ∈ U, x p = x' p) →
    wireVal C (List.ofFn x ++ List.ofFn y) g = wireVal C (List.ofFn x' ++ List.ofFn y) g

private theorem low_at {I : Fin P → Fin L → Bool} {C : Circuit} {g : ℕ} {w : Fin L}
    (h : IsLowMerge P L I C g w) : IsLow P L I C g w := by
  obtain ⟨_, _, _, _, _, _, h, _, _⟩ := h
  exact h

theorem alive_in_support (I : Fin P → Fin L → Bool) (C : Circuit) (g : ℕ)
    (U : Finset (Fin P)) (support : UsesOnly C g U L) (w : Fin L)
    (low : IsLow P L I C g w) : aliveSet P L C g w ⊆ U := by
  intro p hp
  by_contra missing
  have eq := support (ind p) (fun _ => false) (ind w) (by
    intro t ht
    have ne : t ≠ p := fun h => missing (h ▸ ht)
    simp [ind, ne])
  have on : V C w g (ind p) = true := (alive_mem ..).mp hp
  have none : V C w g (fun _ : Fin P => false) = true := eq.symm.trans on
  have bad := low _ none
  rw [lineSum_false] at bad
  contradiction

/-- Any geometric lower bound on double blockers applies to the set of alive
points of a gate merging at all lines. -/
theorem alive_double_blocks (I : Fin P → Fin L → Bool) (C : Circuit) (g : ℕ)
    (merges : ∀ w : Fin L, IsLowMerge P L I C g w) (U : Finset (Fin P))
    (contains : ∀ w : Fin L, aliveSet P L C g w ⊆ U) : DoubleBlocks I U := by
  intro w
  obtain ⟨p, r, ne, hp, hr⟩ := UniformSharedFront.merge_points I C g w (merges w)
  have onLine := alive_sub_line I C g w (low_at (merges w))
  apply Finset.one_lt_card.mpr
  exact ⟨p, Finset.mem_filter.mpr ⟨contains w hp, (Finset.mem_filter.mp (onLine hp)).2⟩,
    r, Finset.mem_filter.mpr ⟨contains w hr, (Finset.mem_filter.mp (onLine hr)).2⟩, ne⟩

/-- Exact support criterion. The realizing circuit is monotone of fan-in two. -/
theorem support_iff_double_blocks (I : Fin P → Fin L → Bool) (U : Finset (Fin P)) :
    DoubleBlocks I U ↔ ∃ (C : Circuit) (g : ℕ), Monotone2 C ∧ UsesOnly C g U L ∧
      ∀ w : Fin L, IsLowMerge P L I C g w := by
  classical
  constructor
  · intro h
    let J := fun p w => decide (p ∈ U) && I p w
    have two (w : Fin L) : ∃ p r, p ≠ r ∧ J p w = true ∧ J r w = true := by
      obtain ⟨p,hp,r,hr,ne⟩ := Finset.one_lt_card.mp (h w)
      exact ⟨p, r, ne, by simp [J, (Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2],
        by simp [J, (Finset.mem_filter.mp hr).1, (Finset.mem_filter.mp hr).2]⟩
    obtain ⟨C, mono, evals, merges⟩ := UniformLineMerges.exists_root_merging_all_lines J two
    refine ⟨C, C.output, mono, ?_, ?_⟩
    · intro x x' y agree
      change C.eval _ = C.eval _
      rw [evals, evals]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      constructor
      · rintro ⟨p, w, edge, on, line⟩
        have mem : p ∈ U := of_decide_eq_true (Bool.and_eq_true_iff.mp edge).1
        exact ⟨p, w, edge, (agree p mem) ▸ on, line⟩
      · rintro ⟨p, w, edge, on, line⟩
        have mem : p ∈ U := of_decide_eq_true (Bool.and_eq_true_iff.mp edge).1
        exact ⟨p, w, edge, (agree p mem).symm ▸ on, line⟩
    · intro w
      obtain ⟨base, a, ha, b, hb, gate, low, left, right⟩ := merges w
      refine ⟨base, a, ha, b, hb, gate, ?_, left, right⟩
      intro x on
      obtain ⟨p, edge, xp⟩ := of_decide_eq_true (low x on)
      exact decide_eq_true ⟨p, (Bool.and_eq_true_iff.mp edge).2, xp⟩
  · rintro ⟨C, g, _, support, merges⟩
    exact alive_double_blocks I C g merges U fun w => alive_in_support I C g U support w (low_at (merges w))

/-- A double-blocking lower bound b improves the inclusive gate-cone bound
to L+b-1. This counts every shared ancestor once. -/
theorem cone_from_blocking (I : Fin P → Fin L → Bool)
    (unique : ∀ {p r : Fin P} {w v : Fin L}, p ≠ r →
      I p w = true → I r w = true → I p v = true → I r v = true → w = v)
    (b : ℕ) (bound : ∀ U, DoubleBlocks I U → b ≤ U.card)
    (other : ∀ w : Fin L, ∃ v : Fin L, w ≠ v) (C : Circuit) (g : ℕ)
    (mono : IsMonotoneCircuit C) (fan : ∀ t ∈ C.gates, t.inputs.length ≤ 2)
    (merges : ∀ w : Fin L, IsLowMerge P L I C g w) :
    L+b ≤ UniformSharedFront.coneCost (P+L) C.gates.reverse {g} + 1 := by
  classical
  let U := Finset.univ.biUnion fun w : Fin L => aliveSet P L C g w
  have contains (w : Fin L) : aliveSet P L C g w ⊆ U := fun _ hp =>
    Finset.mem_biUnion.mpr ⟨w, Finset.mem_univ _, hp⟩
  have hu := bound U (alive_double_blocks I C g merges U contains)
  have h := UniformSharedFront.shared_front_bound I unique C mono fan {g} U Finset.univ (by
    intro p hp
    obtain ⟨w, _, alive⟩ := Finset.mem_biUnion.mp hp
    exact ⟨g, Finset.mem_singleton_self _, w, low_at (merges w), alive⟩) (by
    intro w _
    obtain ⟨v, ne⟩ := other w
    exact ⟨g, Finset.mem_singleton_self _, v, ne, merges w, merges v⟩)
  simp only [Finset.card_singleton, Finset.card_univ, Fintype.card_fin] at h
  omega

#print axioms support_iff_double_blocks
#print axioms cone_from_blocking

end BlockingSupport
