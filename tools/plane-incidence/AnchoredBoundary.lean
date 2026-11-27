import RepairAnds

/-! Condition for a whole collection of reused upstream wires to preserve the
pairwise incompatibility of sparse negatives. On the subcube with a fixed set
of lines active, each upstream wire may be an arbitrary function of the points
or an arbitrary function of the lines. The choice can differ between wires. -/

namespace AnchoredBoundary

open PEqualNP.CircuitLowerBounds SparseNegatives AndTranscript RepairAnds

variable {P L d : ℕ}

abbrev Features (P L d : ℕ) := Finset (Fin P) → Finset (Fin L) → Fin d → Bool

def Monotone (B : Features P L d) : Prop :=
  ∀ X X' Y Y', X ⊆ X' → Y ⊆ Y' → ∀ i, B X Y i = true → B X' Y' i = true

def Splits (B : Features P L d) (R : Finset (Fin L)) : Prop :=
  ∀ i, (∀ X Y Z, R ⊆ Y → R ⊆ Z → B X Y i = B X Z i) ∨
       (∀ X X' Y, R ⊆ Y → B X Y i = B X' Y i)

def encode (B : Features P L d) (X : Finset (Fin P)) (Y : Finset (Fin L)) : List Bool :=
  inputs X Y (List.ofFn (B X Y))

/-- Every observation made on a positive incident pair is covered on one of
the two negative rows containing its endpoints, even when all upstream wires
are exported to the suffix. -/
theorem cross_covered (B : Features P L d) (R : Finset (Fin L))
    (mono : Monotone B) (split : Splits B R) (p : Fin P) (w : Fin L)
    (X X' : Finset (Fin P)) (Y Y' : Finset (Fin L)) (ry : R ⊆ Y) (ry' : R ⊆ Y')
    (px : p ∈ X ∨ p ∈ X') (wy : w ∈ Y ∨ w ∈ Y') :
    Covered (encode B {p} {w}) (encode B X Y) (encode B X' Y') := by
  apply covered_append
  · apply covered_append
    · exact bits_covered _ _ _ (Finset.singleton_subset_iff.mpr (Finset.mem_union.mpr px))
    · exact bits_covered _ _ _ (Finset.singleton_subset_iff.mpr (Finset.mem_union.mpr wy))
  · refine ⟨by simp,by simp,?_⟩
    intro j on
    by_cases valid : j < d
    · simp [List.getD_eq_getElem?_getD,valid] at on ⊢
      let i : Fin d := ⟨j,valid⟩
      change B {p} {w} i = true at on
      change B X Y i = true ∨ B X' Y' i = true
      let S := insert w R
      have rs : R ⊆ S := Finset.subset_insert _ _
      have ws : {w} ⊆ S := Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)
      have high := mono {p} {p} {w} S Finset.Subset.rfl ws i on
      rcases split i with point | line
      · have sat (U : Finset (Fin P)) (V : Finset (Fin L)) (rv : R ⊆ V) (pu : p ∈ U) : B U V i = true := by
          have h : B {p} V i = true := (point {p} S V rs rv).symm.trans high
          exact mono _ _ _ _ (Finset.singleton_subset_iff.mpr pu) Finset.Subset.rfl i h
        exact px.elim (fun h => Or.inl (sat X Y ry h)) (fun h => Or.inr (sat X' Y' ry' h))
      · have sat (U : Finset (Fin P)) (V : Finset (Fin L)) (rv : R ⊆ V) (wv : w ∈ V) : B U V i = true := by
          have h : B U S i = true := (line {p} U S rs).symm.trans high
          exact mono _ _ _ _ Finset.Subset.rfl (Finset.insert_subset wv rv) i h
        exact wy.elim (fun h => Or.inl (sat X Y ry h)) (fun h => Or.inr (sat X' Y' ry' h))
    · rw [List.getD_eq_default _ _ (by simp; omega)] at on
      contradiction

theorem family_bound (I : Lines P L) (t : ℕ) (long : ∀ w, t < (I w).card)
    (linear : ∀ w v, w ≠ v → (I w ∩ I v).card ≤ 1)
    (B : Features P L d) (R : Finset (Fin L)) (mono : Monotone B) (split : Splits B R)
    (C : Circuit) (mc : IsMonotoneCircuit C) (fan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (positive : ∀ p w, p ∈ I w → C.eval (encode B {p} {w}) = true)
    (F : Finset (Finset (Fin L))) (anchored : ∀ Y ∈ F, R ⊆ Y) (short : ∀ Y ∈ F, Y.card ≤ t)
    (negative : ∀ Y ∈ F, C.eval (encode B (outside I Y) Y) = false) :
    F.card ≤ 2 ^ count C.gates := by
  apply incompatible_count F (fun Y => encode B (outside I Y) Y) C mc fan negative
  intro Y hy Z hz ne
  obtain ⟨p,w,pw,px,wy⟩ := crossing_pair I t long linear Y Z (short Y hy) (short Z hz) ne
  exact ⟨_,positive p w pw,cross_covered B R mono split p w _ _ _ _ (anchored Y hy) (anchored Z hz) px wy⟩

def extensions (R : Finset (Fin L)) (t : ℕ) :=
  Finset.univ.filter fun Y : Finset (Fin L) => R ⊆ Y ∧ Y.card ≤ t

theorem count_extensions (R : Finset (Fin L)) (t : ℕ) (room : R.card ≤ t) :
    (extensions R t).card = ∑ j ∈ Finset.range (t-R.card+1), (L-R.card).choose j := by
  classical
  let pool := (Finset.univ : Finset (Fin L)) \ R
  let F := pool.powerset.filter fun Z => Z.card ≤ t-R.card
  have poolSize : pool.card = L-R.card := by simp [pool,Finset.card_sdiff_of_subset (Finset.subset_univ R)]
  rw [← poolSize,← count_small_subsets pool (t-R.card)]
  change (extensions R t).card = F.card
  have memF (Z : Finset (Fin L)) : Z ∈ F ↔ Z ⊆ pool ∧ Z.card ≤ t-R.card := by simp [F]
  have disj (Z : Finset (Fin L)) (sub : Z ⊆ pool) : Disjoint R Z :=
    Finset.disjoint_left.mpr fun _ r z => (Finset.mem_sdiff.mp (sub z)).2 r
  have recover (Z : Finset (Fin L)) (sub : Z ⊆ pool) : (R ∪ Z) \ R = Z := by
    ext w
    have avoid : w ∈ Z → w ∉ R := fun hw => (Finset.mem_sdiff.mp (sub hw)).2
    simp only [Finset.mem_sdiff,Finset.mem_union]
    tauto
  have image : F.image (fun Z => R ∪ Z) = extensions R t := by
    ext Y
    constructor
    · intro h
      obtain ⟨Z,hz,rfl⟩ := Finset.mem_image.mp h
      obtain ⟨sub,few⟩ := (memF Z).mp hz
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,Finset.subset_union_left,?_⟩
      rw [Finset.card_union_of_disjoint (disj Z sub)]
      omega
    · intro h
      obtain ⟨sub,few⟩ := (Finset.mem_filter.mp h).2
      refine Finset.mem_image.mpr ⟨Y\R,(memF _).mpr ⟨?_,?_⟩,?_⟩
      · exact fun w hw => Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,(Finset.mem_sdiff.mp hw).2⟩
      · rw [Finset.card_sdiff_of_subset sub]; omega
      · ext w
        have s : w ∈ R → w ∈ Y := fun h => sub h
        simp only [Finset.mem_union,Finset.mem_sdiff]
        tauto
  rw [← image,Finset.card_image_of_injOn]
  intro A ha D hd eq
  exact (recover A ((memF A).mp ha).1).symm.trans
    ((congrArg (fun S => S \ R) eq).trans (recover D ((memF D).mp hd).1))

/-- All ordinary lines of a plane, all affine points, and parameter t=q-1
give the lower bound with L=q², for any boundary that splits on its anchor. -/
theorem all_extensions (I : Lines P L) (t : ℕ) (long : ∀ w, t < (I w).card)
    (linear : ∀ w v, w ≠ v → (I w ∩ I v).card ≤ 1)
    (B : Features P L d) (R : Finset (Fin L)) (room : R.card ≤ t) (mono : Monotone B) (split : Splits B R)
    (C : Circuit) (mc : IsMonotoneCircuit C) (fan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (positive : ∀ p w, p ∈ I w → C.eval (encode B {p} {w}) = true)
    (negative : ∀ Y, R ⊆ Y → Y.card ≤ t → C.eval (encode B (outside I Y) Y) = false) :
    ∑ j ∈ Finset.range (t-R.card+1), (L-R.card).choose j ≤ 2 ^ count C.gates := by
  rw [← count_extensions R t room]
  exact family_bound I t long linear B R mono split C mc fan positive (extensions R t)
    (fun _ h => (Finset.mem_filter.mp h).2.1) (fun _ h => (Finset.mem_filter.mp h).2.2)
    (fun Y h => negative Y (Finset.mem_filter.mp h).2.1 (Finset.mem_filter.mp h).2.2)

#print axioms cross_covered
#print axioms all_extensions

end AnchoredBoundary
