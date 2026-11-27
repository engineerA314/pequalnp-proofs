import SharedOrStars

/-! Single-AND-level monotone circuits for a C4-free graph. Correctness on
singleton and two-variable tests already suffices. Preparatory binary ORs
can have unrestricted fan-out. -/

namespace SingleLevelStars

open SharedOrStars

variable {V : Type} [Fintype V] [DecidableEq V]

def neighbors (E : Finset (Finset V)) (c : V) := Finset.univ.filter fun u => {c,u} ∈ E

theorem mem_neighbors (E : Finset (Finset V)) (c u : V) : u ∈ neighbors E c ↔ {c,u} ∈ E := by
  simp [neighbors]

omit [Fintype V] in
theorem swap_pair (u v : V) : ({u,v} : Finset V) = {v,u} := Finset.pair_comm _ _

def Covers (E : Finset (Finset V)) (Z : Finset V) : Prop := ∀ e ∈ E, ∃ v ∈ Z, v ∈ e

def Fires (A X : Finset V) : Prop := ∃ v ∈ A, v ∈ X

/-- A nonempty product of positive ORs with all pairs valid has a singleton
side whenever the graph has no two vertices with two common neighbors. -/
theorem rectangle_is_star (E : Finset (Finset V))
    (linear : ∀ c d, c ≠ d → (neighbors E c ∩ neighbors E d).card ≤ 1)
    (A B : Finset V) (liveA : A.Nonempty) (liveB : B.Nonempty)
    (valid : ∀ u ∈ A, ∀ v ∈ B, {u,v} ∈ E) :
    (∃ c, A = {c} ∧ B ⊆ neighbors E c) ∨ (∃ c, B = {c} ∧ A ⊆ neighbors E c) := by
  have singleton {S : Finset V} (one : S.card ≤ 1) (a : V) (ha : a ∈ S) : S = {a} := by
    apply Finset.Subset.antisymm _ (Finset.singleton_subset_iff.mpr ha)
    intro b hb
    exact Finset.mem_singleton.mpr (Finset.card_le_one.mp one b hb a ha)
  by_cases one : A.card ≤ 1
  · obtain ⟨a,ha⟩ := liveA
    exact Or.inl ⟨a,singleton one a ha,fun v hv => (mem_neighbors E _ _).mpr (valid a ha v hv)⟩
  · have thin : B.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro b hb d hd
      by_contra ne
      have sub : A ⊆ neighbors E b ∩ neighbors E d := by
        intro a ha
        apply Finset.mem_inter.mpr
        exact ⟨(mem_neighbors E _ _).mpr (swap_pair a b ▸ valid a ha b hb),
          (mem_neighbors E _ _).mpr (swap_pair a d ▸ valid a ha d hd)⟩
      exact one ((Finset.card_le_card sub).trans (linear b d ne))
    obtain ⟨b,hb⟩ := liveB
    exact Or.inr ⟨b,singleton thin b hb,fun a ha => (mem_neighbors E _ _).mpr (swap_pair a b ▸ valid a ha b hb)⟩

/-- Take shared binary OR preprocessing followed by r binary products and a
final OR. If every vertex cover has at least k members, prep+r+(r-1) is at
least |E|+k-1 for a nonempty graph. This additive form also covers r=0. -/
theorem lower (E : Finset (Finset V)) (simple : ∀ e ∈ E, e.card = 2)
    (linear : ∀ c d, c ≠ d → (neighbors E c ∩ neighbors E d).card ≤ 1)
    (prep : List OrGate) (raw : List (Finset V)) (atomic : ∀ j, (raw.getD j ∅).card ≤ 1)
    {r : ℕ} (left right : Fin r → ℕ)
    (correct : ∀ u v : V, (∃ i : Fin r,
      Fires ((run prep raw).getD (left i) ∅) {u,v} ∧ Fires ((run prep raw).getD (right i) ∅) {u,v}) ↔ {u,v} ∈ E)
    (k : ℕ) (coverLower : ∀ Z : Finset V, Covers E Z → k ≤ Z.card) :
    E.card + k ≤ prep.length + 2*r := by
  classical
  let S := run prep raw
  let A (i : Fin r) := S.getD (left i) ∅
  let B (i : Fin r) := S.getD (right i) ∅
  let U := Finset.univ.filter fun i => (A i).Nonempty ∧ (B i).Nonempty
  have rawPair (i : Fin r) (a : V) (ha : a ∈ A i) (b : V) (hb : b ∈ B i) : {a,b} ∈ E :=
    (correct a b).mp ⟨i,⟨a,ha,by simp⟩,b,hb,by simp⟩
  have star (i : {j // j ∈ U}) : ∃ c j, S.getD j ∅ ⊆ neighbors E c ∧
      ∀ a ∈ A i.val, ∀ b ∈ B i.val, ∃ v ∈ S.getD j ∅, ({a,b} : Finset V) = {c,v} := by
    obtain ⟨liveA,liveB⟩ := (Finset.mem_filter.mp i.property).2
    rcases rectangle_is_star E linear _ _ liveA liveB (rawPair i.val) with ⟨c,hc,sub⟩ | ⟨c,hc,sub⟩
    · refine ⟨c,right i.val,sub,?_⟩
      intro a ha b hb
      rw [hc,Finset.mem_singleton] at ha
      exact ⟨b,hb,by rw [ha]⟩
    · refine ⟨c,left i.val,sub,?_⟩
      intro a ha b hb
      rw [hc,Finset.mem_singleton] at hb
      exact ⟨a,ha,by rw [hb,swap_pair a c]⟩
  choose center arm contained includes using star
  have cover (e : Finset V) (he : e ∈ E) : ∃ i ∈ (Finset.univ : Finset {j // j ∈ U}),
      ∃ v ∈ S.getD (arm i) ∅, e = {center i,v} := by
    obtain ⟨u,v,_,rfl⟩ := Finset.card_eq_two.mp (simple e he)
    obtain ⟨i,⟨a,ha,au⟩,b,hb,bu⟩ := (correct u v).mpr he
    have hi : i ∈ U := Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨a,ha⟩,⟨b,hb⟩⟩
    have sub : ({a,b} : Finset V) ⊆ {u,v} := Finset.insert_subset au (Finset.singleton_subset_iff.mpr bu)
    have e := Finset.eq_of_subset_of_card_le sub (by rw [simple _ he,simple _ (rawPair i a ha b hb)])
    obtain ⟨x,hx,eq⟩ := includes ⟨i,hi⟩ a ha b hb
    exact ⟨⟨i,hi⟩,Finset.mem_univ _,x,hx,e.symm.trans eq⟩
  have edgeBound := cover_cost (neighbors E) linear E prep raw atomic Finset.univ center arm (fun i _ => contained i) cover
  let Z := Finset.univ.image center
  have cv : Covers E Z := by
    intro e he
    obtain ⟨i,hi,v,_,rfl⟩ := cover e he
    exact ⟨center i,Finset.mem_image_of_mem _ hi,by simp⟩
  have zbound : Z.card ≤ U.card := by simpa [Z] using (Finset.card_image_le (s := Finset.univ) (f := center))
  have kz := coverLower Z cv
  have ub : U.card ≤ r := by simpa using (Finset.card_le_card (Finset.filter_subset (fun i => (A i).Nonempty ∧ (B i).Nonempty) Finset.univ))
  simp only [Finset.card_univ,Fintype.card_coe] at edgeBound
  omega

#print axioms rectangle_is_star
#print axioms lower

end SingleLevelStars
