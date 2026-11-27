import ParityProofBudget

namespace ProofWitnessScale

open ProofDagBudget
variable {L X I : Type} [DecidableEq L] [DecidableEq I]

noncomputable def failures (H : L → X → Prop) (indices : Finset I) (x : I → X) (l : L) : Finset I := by
  classical exact indices.filter (fun k => ¬H l (x k))

omit [DecidableEq L] [DecidableEq I] in
theorem mem_failures (H : L → X → Prop) (indices : Finset I) (x : I → X) (l : L) (k : I) :
    k∈failures H indices x l ↔ k∈indices ∧ ¬H l (x k) := by classical simp [failures]

omit [DecidableEq L] in
theorem weaken {H : L → X → Prop} {A S : Finset L} {W : List L} (run : Derives H A W) (sub : A⊆S) :
    Derives H S W := by
  induction run with
  | nil => exact .nil
  | step d l legal ih => exact .step ih l (legal.imp_left (fun h => sub h))

def heavy (size : L → ℕ) (q : ℕ) (W : List L) := (W.filter (fun l => decide (q<size l))).length

theorem scale (H : L → X → Prop) (indices : Finset I) (x : I → X) (A : Finset L)
    (q : ℕ) (light : ∀ l∈A,(failures H indices x l).card≤q) (W : List L) (run : Derives H A W)
    (z : L) (last : z∈W) (dead : ∀ k∈indices,¬H z (x k)) :
    indices.card≤(heavy (fun l => (failures H indices x l).card) q W+1)*q := by
  classical
  let size := fun l => (failures H indices x l).card
  let S := A ∪ (W.toFinset.filter (fun l => size l≤q))
  have bounded (l : L) (hl : l∈S) : size l≤q := by
    rcases Finset.mem_union.mp hl with ax | low
    · exact light l ax
    · exact (Finset.mem_filter.mp low).2
  have eq : paid S W=heavy size q W := by
    unfold paid heavy
    congr 1
    apply List.filter_congr
    intro l hl
    have iff : l∉S ↔ q<size l := by
      constructor
      · intro h
        by_contra! low
        exact h (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hl,low⟩))
      · intro h incl
        exact (Nat.not_lt_of_ge (bounded l incl)) h
    simp [iff]
  obtain ⟨D,inside,_,cap,ent⟩ := frontier H S W (weaken run Finset.subset_union_left) {z} (by simpa)
  have covers : indices⊆D.biUnion (failures H indices x) := by
    intro k hk
    by_contra hole
    apply dead k hk
    apply ent (x k) _ z (by simp)
    intro d hd
    by_contra wrong
    exact hole (Finset.mem_biUnion.mpr ⟨d,hd,(mem_failures _ _ _ _ _).mpr ⟨hk,wrong⟩⟩)
  have limit : D.card≤heavy size q W+1 := by simpa [eq] using cap
  calc indices.card ≤ (D.biUnion (failures H indices x)).card := Finset.card_le_card covers
       _ ≤ ∑ l ∈ D, (failures H indices x l).card := Finset.card_biUnion_le
       _ ≤ ∑ _l ∈ D, q := Finset.sum_le_sum fun l h => bounded l (inside h)
       _ = D.card*q := by simp
       _ ≤ _ := Nat.mul_le_mul_right _ limit

noncomputable def witnesses {H : L → X → Prop} {A : Finset L} (critical : Critical H A) (k : A) : X :=
  Classical.choose (critical k.val k.property)

theorem source_light (H : L → X → Prop) (A : Finset L) (critical : Critical H A) (l : L) (hl : l∈A) :
    (failures H Finset.univ (witnesses critical) l).card≤1 := by
  classical
  calc _ ≤ ({⟨l,hl⟩} : Finset A).card := by
           apply Finset.card_le_card
           intro k hk
           apply Finset.mem_singleton.mpr
           apply Subtype.ext
           by_contra diff
           exact ((mem_failures _ _ _ _ _).mp hk).2
             (Classical.choose_spec (critical k.val k.property) l hl (Ne.symm diff))
       _ = 1 := Finset.card_singleton _

theorem critical_scale (H : L → X → Prop) (A : Finset L) (critical : Critical H A) (q : ℕ) (hq : 0<q)
    (W : List L) (run : Derives H A W) (z : L) (last : z∈W) (dead : ∀ v,¬H z v) :
    A.card ≤ (heavy (fun l => (failures H Finset.univ (witnesses critical) l).card) q W+1)*q := by
  simpa using scale H Finset.univ (witnesses critical) A q
    (fun l h => (source_light H A critical l h).trans hq) W run z last (fun k _ => dead _)

#print axioms critical_scale

end ProofWitnessScale
