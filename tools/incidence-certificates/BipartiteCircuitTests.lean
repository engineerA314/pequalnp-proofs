import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Max

/-! Extremal inputs for a monotone function on the vertices of a finite bipartite graph. -/

namespace BipartiteCircuitTests

variable {m n : ℕ}

abbrev Input (m n : ℕ) := Fin (m + n) → Bool

/-- The active coordinates of the first assignment are also active in the second. -/
def Below {ι : Type*} (x y : ι → Bool) : Prop :=
  ∀ i, x i = true → y i = true

/-- Some edge has both endpoints active. -/
def Hits (E : Fin m → Fin n → Prop) (x : Input m n) : Prop :=
  ∃ i j, E i j ∧ x (Fin.castAdd n i) = true ∧ x (Fin.natAdd m j) = true

def edgeInput (i : Fin m) (j : Fin n) : Input m n :=
  fun k => decide (k = Fin.castAdd n i ∨ k = Fin.natAdd m j)

def freeColumns (E : Fin m → Fin n → Prop) [DecidableRel E]
    (rows : Fin m → Bool) (j : Fin n) : Bool :=
  decide (∀ i, E i j → rows i = false)

def freeRows (E : Fin m → Fin n → Prop) [DecidableRel E]
    (cols : Fin n → Bool) (i : Fin m) : Bool :=
  decide (∀ j, E i j → cols j = false)

def rectangle (E : Fin m → Fin n → Prop) [DecidableRel E] (rows : Fin m → Bool) :
    Input m n :=
  Fin.append rows (freeColumns E rows)

def ClosedRows (E : Fin m → Fin n → Prop) [DecidableRel E] (rows : Fin m → Bool) : Prop :=
  freeRows E (freeColumns E rows) = rows

theorem edgeInput_hits {E : Fin m → Fin n → Prop} {i : Fin m} {j : Fin n} (h : E i j) :
    Hits E (edgeInput i j) :=
  ⟨i, j, h, by simp [edgeInput], by simp [edgeInput]⟩

theorem rectangle_misses (E : Fin m → Fin n → Prop) [DecidableRel E] (rows : Fin m → Bool) :
    ¬ Hits E (rectangle E rows) := by
  rintro ⟨i, j, edge, rowOn, colOn⟩
  have on : rows i = true := by simpa [rectangle] using rowOn
  have allowed : freeColumns E rows j = true := by simpa [rectangle] using colOn
  have off : rows i = false := (of_decide_eq_true allowed) i edge
  exact Bool.noConfusion (on.symm.trans off)

/-- Every independent input extends to a rectangle fixed by row-column closure. -/
theorem covered_by_closed_rectangle (E : Fin m → Fin n → Prop) [DecidableRel E]
    (x : Input m n) (miss : ¬ Hits E x) :
    ∃ rows, ClosedRows E rows ∧ Below x (rectangle E rows) := by
  let left : Fin m → Bool := fun i => x (Fin.castAdd n i)
  let rows := freeRows E (freeColumns E left)
  have grows (i : Fin m) (on : left i = true) : rows i = true := by
    apply decide_eq_true
    intro j edge
    cases col : freeColumns E left j with
    | false => rfl
    | true => exact Bool.noConfusion (on.symm.trans ((of_decide_eq_true col) i edge))
  have stable : freeColumns E rows = freeColumns E left := by
    funext j
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro col
      apply decide_eq_true
      intro i edge
      cases on : left i with
      | false => rfl
      | true => exact Bool.noConfusion ((grows i on).symm.trans ((of_decide_eq_true col) i edge))
    · intro col
      apply decide_eq_true
      intro i edge
      cases on : rows i with
      | false => rfl
      | true => exact Bool.noConfusion (col.symm.trans ((of_decide_eq_true on) j edge))
  refine ⟨rows, ?_, ?_⟩
  · change freeRows E (freeColumns E rows) = rows
    rw [stable]
  · intro k
    refine Fin.addCases (motive := fun k => x k = true → rectangle E rows k = true) ?_ ?_ k
    · intro i on
      simpa [rectangle] using grows i on
    · intro j on
      simp only [rectangle, Fin.append_right, stable]
      apply decide_eq_true
      intro i edge
      cases h : left i with
      | false => rfl
      | true => exact (miss ⟨i, j, edge, h, on⟩).elim

/-- A monotone output computes edge incidence exactly when it accepts each isolated edge pair
and rejects the rectangles indexed by the closed row supports. -/
theorem incidence_iff_extremal_tests (E : Fin m → Fin n → Prop) [DecidableRel E]
    (f : Input m n → Bool)
    (mono : ∀ x y, Below x y → f x = true → f y = true) :
    (∀ x, f x = true ↔ Hits E x) ↔
      (∀ i j, E i j → f (edgeInput i j) = true) ∧
      (∀ rows, ClosedRows E rows → f (rectangle E rows) = false) := by
  constructor
  · intro correct
    constructor
    · intro i j edge
      exact (correct _).2 (edgeInput_hits edge)
    · intro rows _
      cases hv : f (rectangle E rows) with
      | false => rfl
      | true => exact (rectangle_misses E rows ((correct _).1 hv)).elim
  · rintro ⟨positive, negative⟩ x
    constructor
    · intro accepted
      by_contra miss
      obtain ⟨rows, closed, bounded⟩ := covered_by_closed_rectangle E x miss
      exact Bool.noConfusion ((mono x _ bounded accepted).symm.trans (negative rows closed))
    · rintro ⟨i, j, edge, rowOn, colOn⟩
      apply mono (edgeInput i j) x ?_ (positive i j edge)
      intro k on
      rcases of_decide_eq_true on with rfl | rfl <;> assumption

theorem rectangle_injective (E : Fin m → Fin n → Prop) [DecidableRel E] :
    Function.Injective (rectangle E) := by
  intro rows other equal
  funext i
  simpa only [rectangle, Fin.append_left] using congrFun equal (Fin.castAdd n i)

theorem rectangle_maximal (E : Fin m → Fin n → Prop) [DecidableRel E]
    {rows : Fin m → Bool} (closed : ClosedRows E rows) {x : Input m n}
    (larger : Below (rectangle E rows) x) (miss : ¬ Hits E x) : x = rectangle E rows := by
  funext k
  refine Fin.addCases (motive := fun k => x k = rectangle E rows k) ?_ ?_ k
  · intro i
    apply Bool.eq_iff_iff.mpr
    refine ⟨?_, larger _⟩
    intro rowOn
    have allowed : freeRows E (freeColumns E rows) i = true := by
      apply decide_eq_true
      intro j edge
      cases h : freeColumns E rows j with
      | false => rfl
      | true =>
        have colOn : rectangle E rows (Fin.natAdd m j) = true := by
          simpa only [rectangle, Fin.append_right] using h
        exact (miss ⟨i, j, edge, rowOn, larger _ colOn⟩).elim
    rw [show freeRows E (freeColumns E rows) = rows from closed] at allowed
    simpa only [rectangle, Fin.append_left] using allowed
  · intro j
    apply Bool.eq_iff_iff.mpr
    refine ⟨?_, larger _⟩
    intro colOn
    simp only [rectangle, Fin.append_right]
    apply decide_eq_true
    intro i edge
    cases h : rows i with
    | false => rfl
    | true =>
      have rowOn : rectangle E rows (Fin.castAdd n i) = true := by
        simpa only [rectangle, Fin.append_left] using h
      exact (miss ⟨i, j, edge, larger _ rowOn, colOn⟩).elim

/-- For each closed negative input there exists a monotone Boolean function that agrees
with incidence on every other input and accepts this one. This quantifies over all
monotone functions and makes no assumption about the gate count of a candidate. -/
theorem closed_input_cannot_be_skipped (E : Fin m → Fin n → Prop) [DecidableRel E]
    {rows : Fin m → Bool} (closed : ClosedRows E rows) :
    ∃ f : Input m n → Bool,
      (∀ x y, Below x y → f x = true → f y = true) ∧
      (∀ x, x ≠ rectangle E rows → (f x = true ↔ Hits E x)) ∧
      f (rectangle E rows) = true := by
  classical
  let z := rectangle E rows
  let f := fun x : Input m n => decide (Hits E x ∨ Below z x)
  refine ⟨f, ?_, ?_, ?_⟩
  · intro x y grows accepted
    apply decide_eq_true
    rcases of_decide_eq_true accepted with ⟨i, j, edge, rowOn, colOn⟩ | larger
    · exact Or.inl ⟨i, j, edge, grows _ rowOn, grows _ colOn⟩
    · exact Or.inr (fun k on => grows k (larger k on))
  · intro x other
    change decide (Hits E x ∨ Below z x) = true ↔ Hits E x
    rw [decide_eq_true_eq]
    constructor
    · rintro (hit | larger)
      · exact hit
      · by_contra miss
        exact other (rectangle_maximal E closed larger miss)
    · exact Or.inl
  · exact decide_eq_true (Or.inr (fun _ on => on))

/-- On a perfect matching every row support is closed, so the negative test family has
one distinct rectangle for each of the 2^k possible row supports. -/
theorem matching_all_rows_closed {k : ℕ} (rows : Fin k → Bool) :
    ClosedRows (fun i j : Fin k => i = j) rows := by
  unfold ClosedRows
  funext i
  cases h : rows i <;> simp [freeRows, freeColumns, h]

/-- A marker output is constrained to be the OR of these coordinates on edge-free inputs. -/
def HasMarker (markers : Finset (Fin (m+n))) (x : Input m n) : Prop :=
  ∃ i ∈ markers, x i = true

def single {d : ℕ} (i : Fin d) : Fin d → Bool := fun j => decide (j = i)

def Allowed (E : Fin m → Fin n → Prop) (markers : Finset (Fin (m+n))) (x : Input m n) : Prop :=
  ¬ Hits E x ∧ ¬ HasMarker markers x

def MaximalAllowed (E : Fin m → Fin n → Prop) (markers : Finset (Fin (m+n))) (x : Input m n) :
    Prop :=
  Allowed E markers x ∧ ∀ y, Allowed E markers y → Below x y → y = x

theorem single_misses (E : Fin m → Fin n → Prop) (k : Fin (m+n)) : ¬ Hits E (single k) := by
  rintro ⟨i, j, _, hi, hj⟩
  have clash := (of_decide_eq_true hi).trans (of_decide_eq_true hj).symm
  have eq := congrArg Fin.val clash
  simp at eq
  have := i.isLt
  omega

/-- Extend an allowed input to one maximal in the graph obtained by deleting the markers. -/
theorem maximal_allowed_above (E : Fin m → Fin n → Prop) (markers : Finset (Fin (m+n)))
    {x : Input m n} (hx : Allowed E markers x) :
    ∃ z, Below x z ∧ MaximalAllowed E markers z := by
  classical
  let supports := fun (v : Input m n) => Finset.univ.filter fun i => v i = true
  let space : Finset (Input m n) := Finset.univ.filter (fun y => Allowed E markers y ∧ Below x y)
  have hxmem : x ∈ space := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx, fun _ h => h⟩
  obtain ⟨z, hzmem, largest⟩ := space.exists_max_image (fun v => (supports v).card) ⟨x, hxmem⟩
  obtain ⟨hz, hxz⟩ := (Finset.mem_filter.mp hzmem).2
  refine ⟨z, hxz, hz, ?_⟩
  intro y hy hzy
  have hymem : y ∈ space := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, hy, fun i hi => hzy i (hxz i hi)⟩
  have sub : supports z ⊆ supports y := by
    intro i h
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzy i (Finset.mem_filter.mp h).2⟩
  have eq := Finset.eq_of_subset_of_card_le sub (largest y hymem)
  funext i
  apply Bool.eq_iff_iff.mpr
  have memberships : i ∈ supports y ↔ i ∈ supports z := by rw [eq]
  simpa [supports] using memberships

/-- On independent inputs, the singleton positives and the maximal negatives after marker
deletion suffice to certify the marker output of any monotone candidate. -/
theorem marker_iff_extremal_tests (E : Fin m → Fin n → Prop) (markers : Finset (Fin (m+n)))
    (f : Input m n → Bool) (mono : ∀ x y, Below x y → f x = true → f y = true) :
    (∀ x, ¬ Hits E x → (f x = true ↔ HasMarker markers x)) ↔
      (∀ i ∈ markers, f (single i) = true) ∧
      (∀ z, MaximalAllowed E markers z → f z = false) := by
  constructor
  · intro correct
    constructor
    · intro i hi
      exact (correct _ (single_misses E i)).2 ⟨i, hi, by simp [single]⟩
    · intro z hz
      cases hv : f z with
      | false => rfl
      | true => exact (hz.1.2 ((correct z hz.1.1).1 hv)).elim
  · rintro ⟨yes, no⟩ x miss
    constructor
    · intro accepts
      by_contra unmarked
      obtain ⟨z, le, hz⟩ := maximal_allowed_above E markers ⟨miss, unmarked⟩
      exact Bool.noConfusion ((mono x z le accepts).symm.trans (no z hz))
    · rintro ⟨i, hi, on⟩
      apply mono (single i) x ?_ (yes i hi)
      intro j h
      obtain rfl := of_decide_eq_true h
      exact on

def clearMarkers (markers : Finset (Fin (m+n))) (x : Input m n) : Input m n :=
  fun i => if i ∈ markers then false else x i

theorem clear_allowed (E : Fin m → Fin n → Prop) (markers : Finset (Fin (m+n)))
    {x : Input m n} (independent : ¬ Hits E x) : Allowed E markers (clearMarkers markers x) := by
  have below : Below (clearMarkers markers x) x := by
    intro i active
    by_cases hi : i ∈ markers <;> simp_all [clearMarkers]
  constructor
  · rintro ⟨i, j, edge, hi, hj⟩
    exact independent ⟨i, j, edge, below _ hi, below _ hj⟩
  · rintro ⟨i, marked, on⟩
    simp [clearMarkers, marked] at on

/-- Direct bridge to the cleared-rectangle tests in the posted L-meta-7368 reduction. -/
theorem projected_negatives_iff (E : Fin m → Fin n → Prop) [DecidableRel E]
    (markers : Finset (Fin (m+n))) (f : Input m n → Bool)
    (mono : ∀ x y, Below x y → f x = true → f y = true) :
    (∀ rows, ClosedRows E rows → f (clearMarkers markers (rectangle E rows)) = false) ↔
      ∀ z, MaximalAllowed E markers z → f z = false := by
  constructor
  · intro projected z maximal
    obtain ⟨rows, closed, bound⟩ := covered_by_closed_rectangle E z maximal.1.1
    have below : Below z (clearMarkers markers (rectangle E rows)) := by
      intro i on
      by_cases hi : i ∈ markers
      · exact (maximal.1.2 ⟨i, hi, on⟩).elim
      · simpa [clearMarkers, hi] using bound i on
    have eq := maximal.2 _ (clear_allowed E markers (rectangle_misses E rows)) below
    rw [← eq]
    exact projected rows closed
  · intro reduced rows _
    let x := clearMarkers markers (rectangle E rows)
    obtain ⟨z, bound, maximal⟩ := maximal_allowed_above E markers
      (clear_allowed E markers (rectangle_misses E rows))
    change f x = false
    cases out : f x with
    | false => rfl
    | true => exact Bool.noConfusion ((mono x z bound out).symm.trans (reduced z maximal))

/-- Skipping a maximal negative allows a monotone candidate to be wrong there while
agreeing on all other independent inputs, with no imposed gate budget. -/
theorem maximal_marker_negative_is_necessary (E : Fin m → Fin n → Prop)
    (markers : Finset (Fin (m+n))) {z : Input m n} (maximal : MaximalAllowed E markers z) :
    ∃ f : Input m n → Bool,
      (∀ x y, Below x y → f x = true → f y = true) ∧
      (∀ x, x ≠ z → ¬ Hits E x → (f x = true ↔ HasMarker markers x)) ∧
      f z = true := by
  classical
  let f := fun x : Input m n => decide (HasMarker markers x ∨ Below z x)
  refine ⟨f, ?_, ?_, decide_eq_true (Or.inr (fun _ on => on))⟩
  · intro x y grows hx
    apply decide_eq_true
    rcases of_decide_eq_true hx with ⟨i, h, on⟩ | larger
    · exact Or.inl ⟨i, h, grows i on⟩
    · exact Or.inr (fun i on => grows i (larger i on))
  · intro x different miss
    change decide (HasMarker markers x ∨ Below z x) = true ↔ HasMarker markers x
    rw [decide_eq_true_eq]
    constructor
    · rintro (marked | larger)
      · exact marked
      · by_contra unmarked
        exact different (maximal.2 x ⟨miss, unmarked⟩ larger)
    · exact Or.inl

end BipartiteCircuitTests
