import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators

/-! A lower bound for an OR of separately built stars with auxiliary gate extensions. -/

namespace StarCoverBound

open scoped BigOperators

section TraceBudget

variable {α : Type*} [DecidableEq α]

/-- Each set records the singleton assignments on which a wire is true. -/
def Budget (wires : Set (Finset α)) (k : ℕ) : Prop :=
  ∀ picks : Finset (Finset α), (∀ s ∈ picks, s ∈ wires) →
    (picks.biUnion id).card ≤ picks.card + k

theorem initial_budget {wires : Set (Finset α)} (small : ∀ s ∈ wires, s.card ≤ 1) :
    Budget wires 0 := by
  intro picks h
  calc
    _ ≤ ∑ s ∈ picks, s.card := Finset.card_biUnion_le
    _ ≤ ∑ _s ∈ picks, 1 := Finset.sum_le_sum fun s hs => small s (h s hs)
    _ = _ := by simp

/-- Both AND and OR give a trace contained in the union of their two input traces. -/
theorem add_gate_budget {wires : Set (Finset α)} {k : ℕ} {a b c : Finset α}
    (before : Budget wires k) (ha : a ∈ wires) (hb : b ∈ wires) (hc : c ⊆ a ∪ b) :
    Budget (insert c wires) (k + 1) := by
  intro picks hp
  by_cases used : c ∈ picks
  · let rest := picks.erase c
    let sources := insert a (insert b rest)
    have old (s) (hs : s ∈ rest) : s ∈ wires :=
      (Set.mem_insert_iff.mp (hp s (Finset.mem_erase.mp hs).2)).resolve_left
        (Finset.mem_erase.mp hs).1
    have available : ∀ s ∈ sources, s ∈ wires := by
      intro s hs
      rcases Finset.mem_insert.mp hs with rfl | hs
      · exact ha
      rcases Finset.mem_insert.mp hs with rfl | hs
      · exact hb
      exact old s hs
    have incl : picks.biUnion id ⊆ sources.biUnion id := by
      intro v hv
      obtain ⟨s, hs, on⟩ := Finset.mem_biUnion.mp hv
      by_cases same : s = c
      · subst s
        rcases Finset.mem_union.mp (hc on) with h | h
        · exact Finset.mem_biUnion.mpr ⟨a, by simp [sources], h⟩
        · exact Finset.mem_biUnion.mpr ⟨b, by simp [sources], h⟩
      · have keep : s ∈ rest := Finset.mem_erase.mpr ⟨same, hs⟩
        exact Finset.mem_biUnion.mpr ⟨s, by simp [sources, keep], on⟩
    have covers := Finset.card_le_card incl
    have cost := before sources available
    have h1 : sources.card ≤ (insert b rest).card + 1 := Finset.card_insert_le ..
    have h2 := Finset.card_insert_le b rest
    have h3 : rest.card + 1 = picks.card := Finset.card_erase_add_one used
    omega
  · have old : ∀ s ∈ picks, s ∈ wires := by
      intro s hs
      exact (Set.mem_insert_iff.mp (hp s hs)).resolve_left (fun eq => used (eq ▸ hs))
    have := before picks old
    omega

/-- A separate value for constant true lets us give the extension both constants for
free. On the six singleton inputs the constant true value covers all six. -/
def Available (wires : Set (Finset α)) : Option (Finset α) → Prop
  | none => True
  | some s => s ∈ wires

def traceAnd : Option (Finset α) → Option (Finset α) → Option (Finset α)
  | none, b => b
  | a, none => a
  | some a, some b => some (a ∩ b)

def traceOr : Option (Finset α) → Option (Finset α) → Option (Finset α)
  | some a, some b => some (a ∪ b)
  | _, _ => none

def record (wires : Set (Finset α)) : Option (Finset α) → Set (Finset α)
  | none => wires
  | some s => insert s wires

/-- Nullary gates give constants, either unary gate copies its input. -/
inductive AuxGate (wires : Set (Finset α)) : Option (Finset α) → Prop
  | constTrue : AuxGate wires none
  | constFalse : AuxGate wires (some ∅)
  | copy (a) : Available wires a → AuxGate wires a
  | conj (a b) : Available wires a → Available wires b → AuxGate wires (traceAnd a b)
  | disj (a b) : Available wires a → Available wires b → AuxGate wires (traceOr a b)

theorem aux_gate_budget {wires : Set (Finset α)} {k : ℕ} {q : Option (Finset α)}
    (old : Budget wires k) (zero : ∅ ∈ wires) (gate : AuxGate wires q) :
    Budget (record wires q) (k+1) := by
  have stay : Budget wires (k+1) := fun p hp => (old p hp).trans (by omega)
  have keep (a : Option (Finset α)) (ha : Available wires a) : Budget (record wires a) (k+1) := by
    cases a with
    | none => exact stay
    | some a => exact add_gate_budget old ha ha Finset.subset_union_left
  cases gate with
  | constTrue => exact stay
  | constFalse => exact keep (some ∅) zero
  | copy _ ha => exact keep _ ha
  | conj a b ha hb =>
    cases a with
    | none => exact keep b hb
    | some a =>
      cases b with
      | none => exact keep (some a) ha
      | some b => exact add_gate_budget old ha hb (Finset.inter_subset_left.trans Finset.subset_union_left)
  | disj a b ha hb =>
    cases a with
    | none => cases b <;> exact stay
    | some a =>
      cases b with
      | none => exact stay
      | some b => exact add_gate_budget old ha hb (by rfl)

inductive Extension (base : Set (Finset α)) : ℕ → Set (Finset α) → Prop
  | nil : Extension base 0 (insert ∅ base)
  | gate {k wires q} : Extension base k wires → AuxGate wires q →
      Extension base (k+1) (record wires q)

theorem extension_invariant {base wires : Set (Finset α)} {k : ℕ}
    (small : ∀ s ∈ base, s.card ≤ 1) (run : Extension base k wires) :
    ∅ ∈ wires ∧ Budget wires k := by
  induction run with
  | nil =>
    refine ⟨Set.mem_insert _ _, initial_budget ?_⟩
    intro s hs
    rcases Set.mem_insert_iff.mp hs with rfl | hs
    · simp
    · exact small s hs
  | @gate k pool q _ gate ih =>
    refine ⟨?_, aux_gate_budget ih.2 ih.1 gate⟩
    cases q with
    | none => exact ih.1
    | some s => exact Set.mem_insert_of_mem _ ih.1

end TraceBudget

abbrev Edge := Fin 12 × Fin 12

/-- The coordinates and the two sets of marked inputs are those of L-meta-7368. -/
def incident (r c : Fin 12) : Bool :=
  decide (Fin.succAbove (9 : Fin 13) r + Fin.succAbove (0 : Fin 13) c ∈
    ({0, 1, 3, 9} : Finset (Fin 13)))

def edges : Finset Edge := Finset.univ.filter fun e => incident e.1 e.2

def matching : Finset Edge :=
  {(0,2), (1,1), (2,11), (3,10), (4,8), (5,7), (6,9), (7,6), (8,5), (9,3), (10,4), (11,0)}

theorem edge_count : edges.card = 45 := by decide +kernel
theorem matching_count : matching.card = 12 := by decide +kernel
theorem matching_edges : matching ⊆ edges := by decide +kernel

theorem matching_rows : ∀ r : Fin 12, (matching.filter (fun e => e.1 = r)).card ≤ 1 := by
  decide +kernel
theorem matching_cols : ∀ c : Fin 12, (matching.filter (fun e => e.2 = c)).card ≤ 1 := by
  decide +kernel

def IsStar (star : Finset Edge) : Prop :=
  (∃ r, ∀ e ∈ star, e.1 = r) ∨ (∃ c, ∀ e ∈ star, e.2 = c)

theorem matched_per_star {star : Finset Edge} (h : IsStar star) :
    (star ∩ matching).card ≤ 1 := by
  rcases h with ⟨r, hr⟩ | ⟨c, hc⟩
  · refine le_trans (Finset.card_le_card (t := matching.filter (fun e => e.1 = r)) ?_) (matching_rows r)
    intro e he
    obtain ⟨hs, hm⟩ := Finset.mem_inter.mp he
    exact Finset.mem_filter.mpr ⟨hm, hr e hs⟩
  · refine le_trans (Finset.card_le_card (t := matching.filter (fun e => e.2 = c)) ?_) (matching_cols c)
    intro e he
    obtain ⟨hs, hm⟩ := Finset.mem_inter.mp he
    exact Finset.mem_filter.mpr ⟨hm, hc e hs⟩

/-- Each star with d leaves uses d gates. The outer OR costs k − 1 more. -/
theorem star_formula_cost {k : ℕ} (stars : Fin k → Finset Edge) (shape : ∀ i, IsStar (stars i))
    (cover : edges ⊆ Finset.univ.biUnion stars) :
    56 ≤ (∑ i, (stars i).card) + k - 1 := by
  have edgeSum : edges.card ≤ ∑ i, (stars i).card :=
    (Finset.card_le_card cover).trans Finset.card_biUnion_le
  have matched : matching ⊆ Finset.univ.biUnion (fun i => stars i ∩ matching) := by
    intro e he
    obtain ⟨i, hi, inside⟩ := Finset.mem_biUnion.mp (cover (matching_edges he))
    exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_inter.mpr ⟨inside, he⟩⟩
  have starsNeeded : matching.card ≤ k := calc
    _ ≤ _ := Finset.card_le_card matched
    _ ≤ ∑ i, (stars i ∩ matching).card := Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin k, 1 := Finset.sum_le_sum fun i _ => matched_per_star (shape i)
    _ = k := by simp
  rw [edge_count] at edgeSum
  rw [matching_count] at starsNeeded
  omega

def rowMarker : Finset (Fin 24) := {0,1,3}
def colMarker : Finset (Fin 24) := {15,16,18}
def marked : Finset (Fin 24) := rowMarker ∪ colMarker

def colNeighbors (r : Fin 12) : Finset (Fin 24) :=
  (Finset.univ.filter (fun c => incident r c)).image (Fin.natAdd 12)
def rowNeighbors (c : Fin 12) : Finset (Fin 24) :=
  (Finset.univ.filter (fun r => incident r c)).image (Fin.castAdd 12)

theorem col_neighbors_trace : ∀ r, (colNeighbors r ∩ marked).card ≤ 1 := by decide +kernel
theorem row_neighbors_trace : ∀ c, (rowNeighbors c ∩ marked).card ≤ 1 := by decide +kernel

/-- Raw inputs have trace size at most one. Internal leaf ORs use neighbors of a
single center. Completed stars and their output ORs have empty singleton trace. -/
def BaseTrace (s : Finset (Fin 24)) : Prop :=
  s.card ≤ 1 ∨ (∃ r, s ⊆ colNeighbors r ∩ marked) ∨ (∃ c, s ⊆ rowNeighbors c ∩ marked)

theorem base_small (s : Finset (Fin 24)) (hs : BaseTrace s) : s.card ≤ 1 := by
  rcases hs with h | ⟨r, h⟩ | ⟨c, h⟩
  · exact h
  · exact (Finset.card_le_card h).trans (col_neighbors_trace r)
  · exact (Finset.card_le_card h).trans (row_neighbors_trace c)

inductive Hub
  | row (r : Fin 12)
  | col (c : Fin 12)

def Hub.center : Hub → Fin 24
  | .row r => Fin.castAdd 12 r
  | .col c => Fin.natAdd 12 c

def Hub.neighbors : Hub → Finset (Fin 24)
  | .row r => colNeighbors r
  | .col c => rowNeighbors c

theorem center_outside (h : Hub) : h.center ∉ h.neighbors := by
  cases h with
  | row r => exact (by decide +kernel : ∀ r, (Hub.row r).center ∉ (Hub.row r).neighbors) r
  | col c => exact (by decide +kernel : ∀ c, (Hub.col c).center ∉ (Hub.col c).neighbors) c

/-- The AND for one star, or an OR of completed star terms. -/
inductive Products
  | star (hub : Hub) (leaves : Finset (Fin 24)) (adjacent : leaves ⊆ hub.neighbors)
  | join (left right : Products)

def Products.on (x : Finset (Fin 24)) : Products → Prop
  | .star h leaves _ => h.center ∈ x ∧ ∃ v ∈ leaves, v ∈ x
  | .join left right => left.on x ∨ right.on x

theorem Products.off_single (p : Products) (v : Fin 24) : ¬ p.on {v} := by
  induction p with
  | star h leaves adj =>
    rintro ⟨center, u, hu, hit⟩
    have eq : h.center = u := (Finset.mem_singleton.mp center).trans (Finset.mem_singleton.mp hit).symm
    exact center_outside h (eq ▸ adj hu)
  | join _ _ hl hr => exact fun on => on.elim hl hr

/-- Any wire of the base formula is an input, an OR within one neighbor list,
or a completed star/product OR. Its position in the gate list does not matter. -/
inductive BaseWire
  | input (v : Fin 24)
  | leafOr (hub : Hub) (leaves : Finset (Fin 24)) (adjacent : leaves ⊆ hub.neighbors)
  | products (p : Products)

def BaseWire.on (x : Finset (Fin 24)) : BaseWire → Prop
  | .input v => v ∈ x
  | .leafOr _ leaves _ => ∃ v ∈ leaves, v ∈ x
  | .products p => p.on x

noncomputable def BaseWire.trace (w : BaseWire) : Finset (Fin 24) := by
  classical
  exact marked.filter fun v => w.on {v}

theorem BaseWire.trace_in_base (w : BaseWire) : BaseTrace w.trace := by
  classical
  cases w with
  | input u =>
    apply Or.inl
    have sub : (BaseWire.input u).trace ⊆ {u} := by
      intro v hv
      exact Finset.mem_singleton.mpr (Finset.mem_singleton.mp (Finset.mem_filter.mp hv).2).symm
    simpa using Finset.card_le_card sub
  | leafOr h leaves adj =>
    have sub : (BaseWire.leafOr h leaves adj).trace ⊆ h.neighbors ∩ marked := by
      intro v hv
      obtain ⟨mark, u, hu, hit⟩ := Finset.mem_filter.mp hv
      obtain rfl := Finset.mem_singleton.mp hit
      exact Finset.mem_inter.mpr ⟨adj hu, mark⟩
    cases h with
    | row r => exact Or.inr (Or.inl ⟨r, sub⟩)
    | col c => exact Or.inr (Or.inr ⟨c, sub⟩)
  | products p =>
    apply Or.inl
    have empty : (BaseWire.products p).trace = ∅ :=
      Finset.eq_empty_iff_forall_notMem.mpr fun v hv => p.off_single v (Finset.mem_filter.mp hv).2
    simp [empty]

theorem auxiliary_cost {t : ℕ} {base wires : Set (Finset (Fin 24))}
    (small : ∀ s ∈ base, s.card ≤ 1)
    (run : Extension base t wires) (ha : rowMarker ∈ wires) (hb : colMarker ∈ wires) :
    4 ≤ t := by
  let wants : Finset (Finset (Fin 24)) := {rowMarker, colMarker}
  have available : ∀ s ∈ wants, s ∈ wires := by
    simpa [wants] using And.intro ha hb
  have enough := (extension_invariant small run).2 wants available
  have two : wants.card = 2 := by decide +kernel
  have six : (wants.biUnion id).card = 6 := by decide +kernel
  omega

theorem star_plus_aux_lower_bound {k t : ℕ} (stars : Fin k → Finset Edge)
    (shape : ∀ i, IsStar (stars i)) (cover : edges ⊆ Finset.univ.biUnion stars)
    {base wires : Set (Finset (Fin 24))} (baseWires : ∀ s ∈ base, ∃ w : BaseWire, w.trace = s)
    (run : Extension base t wires)
    (ha : rowMarker ∈ wires) (hb : colMarker ∈ wires) :
    60 ≤ ((∑ i, (stars i).card) + k - 1) + t := by
  have := star_formula_cost stars shape cover
  have small (s) (hs : s ∈ base) : s.card ≤ 1 := by
    obtain ⟨w, rfl⟩ := baseWires s hs
    exact base_small _ w.trace_in_base
  have := auxiliary_cost small run ha hb
  omega

end StarCoverBound
