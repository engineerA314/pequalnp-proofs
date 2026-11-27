import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

/-! Exact cost of correcting a monotone incidence prefix with positive clauses.
Each allowed line set has a canonical independent input, with every point
outside its line union active. A single valid clause can reject at most one
such input when the number of active lines is smaller than the line length. -/

namespace SparseNegatives

variable {P L : ℕ}

abbrev Lines (P L : ℕ) := Fin L → Finset (Fin P)
abbrev Clause (P L : ℕ) := Finset (Fin P) × Finset (Fin L)

def covered (I : Lines P L) (Y : Finset (Fin L)) := Y.biUnion I
def outside (I : Lines P L) (Y : Finset (Fin L)) := Finset.univ \ covered I Y

def Hits (I : Lines P L) (X : Finset (Fin P)) (Y : Finset (Fin L)) : Prop :=
  ∃ w ∈ Y, ∃ p ∈ X, p ∈ I w

def Rejects (c : Clause P L) (X : Finset (Fin P)) (Y : Finset (Fin L)) : Prop :=
  Disjoint c.1 X ∧ Disjoint c.2 Y

def Valid (I : Lines P L) (c : Clause P L) : Prop :=
  ∀ w p, p ∈ I w → p ∈ c.1 ∨ w ∈ c.2

def canonical (I : Lines P L) (Y : Finset (Fin L)) : Clause P L :=
  (covered I Y, Finset.univ \ Y)

def Fixes (I : Lines P L) (q : ℕ) (A : Finset (Fin P) → Finset (Fin L) → Prop)
    (C : Finset (Clause P L)) : Prop :=
  ∀ X Y, Y.card ≤ q → ((A X Y ∧ ∀ c ∈ C, ¬ Rejects c X Y) ↔ Hits I X Y)

noncomputable def leaks (I : Lines P L) (q : ℕ) (A : Finset (Fin P) → Finset (Fin L) → Prop) :
    Finset (Finset (Fin L)) := by
  classical
  exact Finset.univ.filter fun Y => Y.card ≤ q ∧ A (outside I Y) Y

theorem mem_leaks (I : Lines P L) (q : ℕ) (A : Finset (Fin P) → Finset (Fin L) → Prop)
    (Y : Finset (Fin L)) :
    Y ∈ leaks I q A ↔ Y.card ≤ q ∧ A (outside I Y) Y := by classical simp [leaks]

theorem no_hit_iff (I : Lines P L) (X : Finset (Fin P)) (Y : Finset (Fin L)) :
    ¬ Hits I X Y ↔ X ⊆ outside I Y := by
  constructor
  · intro h p hp
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rintro hcov
    obtain ⟨w, hw, hpw⟩ := Finset.mem_biUnion.mp hcov
    exact h ⟨w, hw, p, hp, hpw⟩
  · intro sub
    rintro ⟨w, hw, p, hp, hpw⟩
    exact (Finset.mem_sdiff.mp (sub hp)).2 (Finset.mem_biUnion.mpr ⟨w, hw, hpw⟩)

theorem private_point (I : Lines P L) (q : ℕ) (size : ∀ w, q < (I w).card)
    (linear : ∀ w v, w ≠ v → ((I w) ∩ (I v)).card ≤ 1)
    (Y : Finset (Fin L)) (small : Y.card ≤ q) (w : Fin L) (missing : w ∉ Y) :
    ∃ p ∈ I w, p ∈ outside I Y := by
  classical
  have limit : (I w ∩ covered I Y).card ≤ Y.card := calc
    _ ≤ (Y.biUnion fun v => I w ∩ I v).card := by
      apply Finset.card_le_card
      intro p hp
      obtain ⟨pw, inUnion⟩ := Finset.mem_inter.mp hp
      obtain ⟨v,hv,pv⟩ := Finset.mem_biUnion.mp inUnion
      exact Finset.mem_biUnion.mpr ⟨v,hv,Finset.mem_inter.mpr ⟨pw,pv⟩⟩
    _ ≤ ∑ v ∈ Y, (I w ∩ I v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ Y, 1 := Finset.sum_le_sum fun v hv => linear w v (fun h => missing (h ▸ hv))
    _ = _ := by simp
  by_contra! none
  have sub : I w ⊆ covered I Y := by
    intro p hp
    by_contra notcov
    exact none p hp (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, notcov⟩)
  rw [Finset.inter_eq_left.mpr sub] at limit
  exact (Nat.not_lt_of_ge (limit.trans small)) (size w)

theorem canonical_valid (I : Lines P L) (Y : Finset (Fin L)) : Valid I (canonical I Y) := by
  intro w p pw
  by_cases h : w ∈ Y
  · exact Or.inl (Finset.mem_biUnion.mpr ⟨w,h,pw⟩)
  · exact Or.inr (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h⟩)

theorem canonical_rejects (I : Lines P L) (X : Finset (Fin P)) (Y : Finset (Fin L))
    (sub : X ⊆ outside I Y) : Rejects (canonical I Y) X Y := by
  constructor <;> rw [Finset.disjoint_left]
  · intro p pc px
    exact (Finset.mem_sdiff.mp (sub px)).2 pc
  · intro w wc wy
    exact (Finset.mem_sdiff.mp wc).2 wy

theorem good_on_hits (I : Lines P L) (c : Clause P L) (valid : Valid I c)
    {X : Finset (Fin P)} {Y : Finset (Fin L)} (edge : Hits I X Y) : ¬ Rejects c X Y := by
  rintro ⟨points, lines⟩
  obtain ⟨w,wy,p,px,pw⟩ := edge
  rcases valid w p pw with pc | wc
  · exact Finset.disjoint_left.mp points pc px
  · exact Finset.disjoint_left.mp lines wc wy

/-- Distinct sparse line sets have incompatible maximal independent inputs. -/
theorem one_row_per_clause (I : Lines P L) (q : ℕ) (size : ∀ w, q < (I w).card)
    (linear : ∀ w v, w ≠ v → (I w ∩ I v).card ≤ 1)
    (c : Clause P L) (valid : Valid I c) (Y Z : Finset (Fin L))
    (sy : Y.card ≤ q) (sz : Z.card ≤ q)
    (ry : Rejects c (outside I Y) Y) (rz : Rejects c (outside I Z) Z) : Y = Z := by
  have incl (A B : Finset (Fin L)) (sb : B.card ≤ q)
      (ra : Rejects c (outside I A) A) (rb : Rejects c (outside I B) B) : A ⊆ B := by
    intro w ha
    by_contra hb
    obtain ⟨p, pw, po⟩ := private_point I q size linear B sb w hb
    rcases valid w p pw with pc | wc
    · exact Finset.disjoint_left.mp rb.1 pc po
    · exact Finset.disjoint_left.mp ra.2 wc ha
  exact Finset.Subset.antisymm (incl Y Z sz ry rz) (incl Z Y sy rz ry)

/-- The canonical clauses indexed by leaking line sets repair every point assignment. -/
theorem canonical_fixes (I : Lines P L) (q : ℕ) (A : Finset (Fin P) → Finset (Fin L) → Prop)
    (monoX : ∀ X X' Y, X ⊆ X' → A X Y → A X' Y)
    (positive : ∀ X Y, Y.card ≤ q → Hits I X Y → A X Y) :
    Fixes I q A ((leaks I q A).image (canonical I)) := by
  classical
  intro X Y small
  constructor
  · rintro ⟨on, pass⟩
    by_contra noedge
    have sub := (no_hit_iff I X Y).mp noedge
    have leak := (mem_leaks I q A Y).mpr ⟨small, monoX _ _ _ sub on⟩
    exact pass _ (Finset.mem_image_of_mem _ leak) (canonical_rejects I X Y sub)
  · intro hit
    refine ⟨positive X Y small hit, ?_⟩
    intro c hc
    obtain ⟨Z, _, rfl⟩ := Finset.mem_image.mp hc
    exact good_on_hits I _ (canonical_valid I Z) hit

/-- Every positive-clause repair pays one distinct clause per leaking maximal input. -/
theorem clause_lower (I : Lines P L) (q : ℕ) (hq : 1 ≤ q) (size : ∀ w, q < (I w).card)
    (linear : ∀ w v, w ≠ v → (I w ∩ I v).card ≤ 1)
    (A : Finset (Fin P) → Finset (Fin L) → Prop) (C : Finset (Clause P L))
    (correct : Fixes I q A C) : (leaks I q A).card ≤ C.card := by
  classical
  have valid (c : Clause P L) (hc : c ∈ C) : Valid I c := by
    intro w p pw
    have hit : Hits I {p} {w} := ⟨w, by simp, p, by simp, pw⟩
    have pass := ((correct {p} {w} (by simpa using hq)).mpr hit).2 c hc
    by_contra! neither
    exact pass ⟨by simpa using neither.1, by simpa using neither.2⟩
  have pick (Y : {Y // Y ∈ leaks I q A}) : ∃ c ∈ C, Rejects c (outside I Y.val) Y.val := by
    have h := (mem_leaks I q A Y.val).mp Y.property
    by_contra! pass
    have hit := (correct _ _ h.1).mp ⟨h.2,pass⟩
    exact ((no_hit_iff I _ _).mpr (fun _ hm => hm)) hit
  choose f mem kills using pick
  let F (y : {Y // Y ∈ leaks I q A}) : {c // c ∈ C} := ⟨f y, mem y⟩
  have inj : Function.Injective F := by
    intro y z eq
    have e : f y = f z := congrArg Subtype.val eq
    apply Subtype.ext
    exact one_row_per_clause I q size linear (f y) (valid _ (mem y)) y.val z.val
      ((mem_leaks I q A _).mp y.property).1 ((mem_leaks I q A _).mp z.property).1
      (kills y) (e ▸ kills z)
  simpa using Fintype.card_le_of_injective F inj

/-- The lower bound is attained, giving the exact optimum for every prefix with
the indicated one-sided guarantees. -/
theorem exact_minimum (I : Lines P L) (q : ℕ) (hq : 1 ≤ q) (size : ∀ w, q < (I w).card)
    (linear : ∀ w v, w ≠ v → (I w ∩ I v).card ≤ 1)
    (A : Finset (Fin P) → Finset (Fin L) → Prop)
    (monoX : ∀ X X' Y, X ⊆ X' → A X Y → A X' Y)
    (positive : ∀ X Y, Y.card ≤ q → Hits I X Y → A X Y) :
    (∃ C, Fixes I q A C ∧ C.card = (leaks I q A).card) ∧
    (∀ C, Fixes I q A C → (leaks I q A).card ≤ C.card) := by
  classical
  have lower := clause_lower I q hq size linear A
  have witness := canonical_fixes I q A monoX positive
  exact ⟨⟨_, witness, Nat.le_antisymm Finset.card_image_le (lower _ witness)⟩, lower⟩

/-- An edge in the union of two different canonical negative inputs. -/
theorem crossing_pair (I : Lines P L) (q : ℕ) (size : ∀ w, q < (I w).card)
    (linear : ∀ w v, w ≠ v → (I w ∩ I v).card ≤ 1)
    (Y Z : Finset (Fin L)) (sy : Y.card ≤ q) (sz : Z.card ≤ q) (ne : Y ≠ Z) :
    ∃ p w, p ∈ I w ∧ (p ∈ outside I Y ∨ p ∈ outside I Z) ∧ (w ∈ Y ∨ w ∈ Z) := by
  by_cases h : Y ⊆ Z
  · have h' : ¬ Z ⊆ Y := fun h' => ne (Finset.Subset.antisymm h h')
    obtain ⟨w, wz, wy⟩ := Finset.not_subset.mp h'
    obtain ⟨p, pw, py⟩ := private_point I q size linear Y sy w wy
    exact ⟨p,w,pw,Or.inl py,Or.inr wz⟩
  · obtain ⟨w, wy, wz⟩ := Finset.not_subset.mp h
    obtain ⟨p, pw, pz⟩ := private_point I q size linear Z sz w wz
    exact ⟨p,w,pw,Or.inr pz,Or.inl wy⟩

theorem count_small_subsets {α : Type*} [DecidableEq α] (pool : Finset α) (t : ℕ) :
    (pool.powerset.filter fun Z => Z.card ≤ t).card = ∑ j ∈ Finset.range (t+1), pool.card.choose j := by
  classical
  let S := pool.powerset.filter fun Z => Z.card ≤ t
  have memS (Z : Finset α) : Z ∈ S ↔ Z ⊆ pool ∧ Z.card ≤ t := by simp [S]
  change S.card = _
  have hmaps : ∀ Z ∈ S, Z.card ∈ Finset.range (t+1) := by
    intro Z hZ
    exact Finset.mem_range.mpr (by have := ((memS Z).mp hZ).2; omega)
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_congr rfl
  intro j hj
  have hjt : j ≤ t := by have := Finset.mem_range.mp hj; omega
  have eq : S.filter (fun Z => Z.card = j) = pool.powersetCard j := by
    ext Z
    simp only [Finset.mem_filter, memS, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨sub,_⟩,rfl⟩
      exact ⟨sub,rfl⟩
    · rintro ⟨sub,rfl⟩
      exact ⟨⟨sub,hjt⟩,rfl⟩
  rw [eq, Finset.card_powersetCard]

/-- A false positive on one point and a line set R forces a separate leaking
maximal input for every small subset of additional lines that miss the point. -/
theorem extensions_lower (I : Lines P L) (q t : ℕ) (A : Finset (Fin P) → Finset (Fin L) → Prop)
    (p : Fin P) (R pool : Finset (Fin L)) (d : Disjoint R pool)
    (off : ∀ w ∈ R ∪ pool, p ∉ I w) (room : R.card + t ≤ q) (leak : A {p} R)
    (mono : ∀ X X' Y Y', X ⊆ X' → Y ⊆ Y' → A X Y → A X' Y') :
    ∑ j ∈ Finset.range (t+1), pool.card.choose j ≤ (leaks I q A).card := by
  classical
  let S := pool.powerset.filter fun Z => Z.card ≤ t
  have memS (Z : Finset (Fin L)) : Z ∈ S ↔ Z ⊆ pool ∧ Z.card ≤ t := by simp [S]
  have sizeS := count_small_subsets pool t
  change S.card = _ at sizeS
  rw [← sizeS]
  apply Finset.card_le_card_of_injOn (fun Z => R ∪ Z)
  · intro Z hZ
    obtain ⟨sub,small⟩ := (memS Z).mp hZ
    apply (mem_leaks I q A _).mpr
    refine ⟨(Finset.card_union_le _ _).trans (by omega), mono _ _ _ _ ?_ Finset.subset_union_left leak⟩
    apply Finset.singleton_subset_iff.mpr
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
    intro hp
    obtain ⟨w,hw,pw⟩ := Finset.mem_biUnion.mp hp
    rcases Finset.mem_union.mp hw with wr | wz
    · exact off w (Finset.mem_union_left _ wr) pw
    · exact off w (Finset.mem_union_right _ (sub wz)) pw
  · intro Z hZ W hW eq
    have zs := ((memS Z).mp hZ).1
    have ws := ((memS W).mp hW).1
    ext w
    by_cases wr : w ∈ R
    · have nz : w ∉ Z := fun hw => Finset.disjoint_left.mp d wr (zs hw)
      have nw : w ∉ W := fun hw => Finset.disjoint_left.mp d wr (ws hw)
      simp [nz,nw]
    · have e := Finset.ext_iff.mp eq w
      simpa [wr] using e

#print axioms exact_minimum
#print axioms extensions_lower

/-- In a plane, a singleton point and r erroneous nonincident active lines
force the binomial sum on q^2-r possible additional lines. -/
theorem plane_witness_bound (I : Lines P L) (q : ℕ) (nlines : L = q^2+q+1)
    (A : Finset (Fin P) → Finset (Fin L) → Prop) (p : Fin P)
    (degree : (Finset.univ.filter fun w => p ∈ I w).card = q+1)
    (R : Finset (Fin L)) (small : R.card ≤ q) (off : ∀ w ∈ R, p ∉ I w) (leak : A {p} R)
    (mono : ∀ X X' Y Y', X ⊆ X' → Y ⊆ Y' → A X Y → A X' Y') :
    ∑ j ∈ Finset.range (q-R.card+1), (q^2-R.card).choose j ≤ (leaks I q A).card := by
  classical
  let pencil := Finset.univ.filter fun w => p ∈ I w
  let clear := Finset.univ \ pencil
  let pool := clear \ R
  have hclear (w : Fin L) : w ∈ clear ↔ p ∉ I w := by simp [clear,pencil]
  have sub : R ⊆ clear := fun w hw => (hclear w).mpr (off w hw)
  have nc : clear.card = q^2 := by
    change (Finset.univ \ pencil).card = _
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    have hpencil : pencil.card = q+1 := degree
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  have np : pool.card = q^2-R.card := by
    change (clear \ R).card = _
    rw [Finset.card_sdiff_of_subset sub, nc]
  have dj : Disjoint R pool := Finset.disjoint_left.mpr fun _ hr hp => (Finset.mem_sdiff.mp hp).2 hr
  have safe : ∀ w ∈ R ∪ pool, p ∉ I w := by
    intro w hw
    rcases Finset.mem_union.mp hw with hr | hp
    · exact off w hr
    · exact (hclear w).mp (Finset.mem_sdiff.mp hp).1
  rw [← np]
  exact extensions_lower I q (q-R.card) A p R pool dj safe (by omega) leak mono

#print axioms plane_witness_bound

end SparseNegatives
