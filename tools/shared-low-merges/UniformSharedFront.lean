import PEqualNP.MetaComplexity.Helpers.Support
import PEqualNP.MetaComplexity.Helpers.LowMergeFacts
import Mathlib.Data.List.OfFn

/-! Shared low merges in a finite linear incidence system. The cost below counts
distinct gates in the union of the backward cones, including the selected roots.
Inputs cost zero. The proof uses the project's actual wire and low-merge semantics. -/

namespace UniformSharedFront

open PEqualNP.CircuitLowerBounds PEqualNP.LowMerge PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers
open LowMergeProof

/-- Replace an active gate by the valid earlier wires it reads. -/
def expand (j : ℕ) (g : Gate) (W : Finset ℕ) : Finset ℕ :=
  W.erase j ∪ g.inputs.toFinset.filter (· < j)

/-- Gates are supplied in reverse order. Each visited gate is charged once, even
when several selected roots or operands need it. -/
def coneCost (n : ℕ) : List Gate → Finset ℕ → ℕ
  | [], _ => 0
  | g :: gs, W =>
    let j := n + gs.length
    if j ∈ W then coneCost n gs (expand j g W) + 1 else coneCost n gs W

private theorem supp_length {n : ℕ} (gs : List Gate) (S : List (Finset (Fin n))) :
    (suppsFrom gs S).length = S.length + gs.length := by
  induction gs generalizing S with
  | nil => simp [suppsFrom]
  | cons g gs ih =>
    change (suppsFrom gs (S ++ [gateSupp S g])).length = _
    rw [ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

def joint {n : ℕ} (S : List (Finset (Fin n))) (W : Finset ℕ) : Finset (Fin n) :=
  W.biUnion fun j => S.getD j ∅

/-- The union of the supports of the chosen outputs costs only the distinct gates
that the backward traversal actually visits. -/
theorem cone_support_bound (n : ℕ) (gs : List Gate) (W : Finset ℕ)
    (fan : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (joint (suppsFrom gs.reverse (inputSupps n)) W).card ≤ coneCost n gs W + W.card := by
  induction gs generalizing W with
  | nil => simpa [coneCost, joint, suppsFrom] using (cnt_inputs (n := n) W)
  | cons g gs ih =>
    let S := suppsFrom gs.reverse (inputSupps n)
    let j := n + gs.length
    have len : S.length = j := by simp [S, supp_length, inputSupps, j]
    have tailFan : ∀ h ∈ gs, h.inputs.length ≤ 2 := fun h hh => fan h (by simp [hh])
    have step : suppsFrom (g :: gs).reverse (inputSupps n) = S ++ [gateSupp S g] := by
      simp [S, suppsFrom, List.foldl_append]
    rw [step]
    by_cases used : j ∈ W
    · have sub : joint (S ++ [gateSupp S g]) W ⊆ joint S (expand j g W) := by
        intro i hi
        obtain ⟨a, ha, hia⟩ := Finset.mem_biUnion.mp hi
        apply Finset.mem_biUnion.mpr
        by_cases e : a = j
        · subst a
          rw [← len, getD_snoc_eq] at hia
          obtain ⟨b, hb, hib⟩ := (mem_gateSupp S g i).mp hia
          have lt : b < j := by
            by_contra! bad
            rw [List.getD_eq_default _ _ (by omega)] at hib
            simp at hib
          exact ⟨b, Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hb, lt⟩), hib⟩
        · exact ⟨a, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨e, ha⟩),
            (getD_snoc_ne S _ _ a (by omega)) ▸ hia⟩
      have hc : (expand j g W).card ≤ W.card - 1 + 2 := calc
        _ ≤ (W.erase j).card + (g.inputs.toFinset.filter (· < j)).card := Finset.card_union_le _ _
        _ ≤ W.card - 1 + 2 := by
          rw [Finset.card_erase_of_mem used]
          exact Nat.add_le_add_left ((Finset.card_filter_le _ _).trans
            ((List.toFinset_card_le _).trans (fan g List.mem_cons_self))) _
      have h := ih (expand j g W) tailFan
      have hs := Finset.card_le_card sub
      have pos := Finset.card_pos.mpr ⟨j, used⟩
      change _ ≤ (if j ∈ W then _ else _) + W.card
      simp only [used, ite_true]
      change _ ≤ coneCost n gs (expand j g W) + 1 + W.card
      change (joint S (expand j g W)).card ≤ _ at h
      omega
    · have eq : joint (S ++ [gateSupp S g]) W = joint S W := by
        apply Finset.biUnion_congr rfl
        intro a ha
        exact getD_snoc_ne S _ _ a (fun e => used (by simpa [← len, ← e] using ha))
      change _ ≤ (if j ∈ W then _ else _) + W.card
      simp only [eq, used, ite_false]
      exact ih W tailFan

variable {P L : ℕ}

private def supp (n : ℕ) (C : Circuit) (g : ℕ) : Finset (Fin n) :=
  (suppsFrom C.gates (inputSupps n)).getD g ∅

private theorem agree_at {n : ℕ} (C : Circuit) (g : ℕ) (a b : Fin n → Bool)
    (agree : ∀ i ∈ supp n C g, a i = b i) :
    wireVal C (List.ofFn a) g = wireVal C (List.ofFn b) g :=
  (agree_wiresFrom a b C.gates _ _ _ (agree_inputs _ _)).2.2 g agree

private theorem ofFn_mono {n : ℕ} (C : Circuit) (mono : IsMonotoneCircuit C) (g : ℕ)
    (a b : Fin n → Bool) (h : ∀ i, a i = true → b i = true) :
    wireVal C (List.ofFn a) g = true → wireVal C (List.ofFn b) g = true := by
  apply wires_mono C mono _ _ (by simp)
  intro i on
  by_cases hi : i < n
  · simp [List.getD_eq_getElem?_getD, hi] at on ⊢
    exact h ⟨i, hi⟩ on
  · rw [List.getD_eq_default _ _ (by simp; omega)] at on
    contradiction

/-- A low merge accepts at least two different singleton points on its line. -/
theorem merge_points (inc : Fin P → Fin L → Bool) (C : Circuit) (g : ℕ) (w : Fin L)
    (m : IsLowMerge P L inc C g w) :
    ∃ p r : Fin P, p ≠ r ∧ p ∈ aliveSet P L C g w ∧ r ∈ aliveSet P L C g w := by
  obtain ⟨start, a, ha, b, hb, gate, _, left, right⟩ := m
  obtain ⟨p, hp, np⟩ := Finset.not_subset.mp left
  obtain ⟨r, hr, _⟩ := Finset.not_subset.mp right
  let j := g - (P + L)
  have hj : j < C.gates.length := by
    by_contra! bad
    change C.gates[j]? = _ at gate
    rw [List.getElem?_eq_none bad] at gate
    contradiction
  have op : C.gates[j] = ⟨.or, [a,b]⟩ := by
    change C.gates[j]? = _ at gate
    simpa only [List.getElem?_eq_getElem hj, Option.some.injEq] using gate
  have join (u : Fin P) : u ∈ aliveSet P L C g w ↔
      u ∈ aliveSet P L C a w ∨ u ∈ aliveSet P L C b w := by
    simp only [alive_mem]
    have ev := V_gate C w j hj (ind u)
    rw [show P + L + j = g by dsimp [j]; omega, op] at ev
    simp [ev, GateOp.eval, R, ha, hb]
  exact ⟨p, r, fun e => np (e ▸ hr), (join p).mpr (Or.inl hp), (join r).mpr (Or.inr hr)⟩

private def mask (p : Fin P) (y : Fin L → Bool) : Fin (P + L) → Bool :=
  Fin.append (ind p) y

private theorem mask_on (C : Circuit) (g : ℕ) (p : Fin P) (w : Fin L) :
    wireVal C (List.ofFn (mask p (ind w))) g = V C w g (ind p) := by
  unfold mask
  rw [List.ofFn_fin_append]
  rfl

private theorem low_of_merge {inc : Fin P → Fin L → Bool} {C : Circuit} {g : ℕ} {w : Fin L}
    (m : IsLowMerge P L inc C g w) : IsLow P L inc C g w := by
  obtain ⟨_, _, _, _, _, _, h, _, _⟩ := m
  exact h

/-- A point alive at a low wire is an essential primary input to that wire. -/
theorem point_input_mem (inc : Fin P → Fin L → Bool) (C : Circuit) (g : ℕ)
    (w : Fin L) (p : Fin P) (low : IsLow P L inc C g w) (alive : p ∈ aliveSet P L C g w) :
    Fin.castAdd L p ∈ supp (P + L) C g := by
  by_contra missing
  have eq := agree_at C g (mask p (ind w)) (Fin.append (fun _ : Fin P => false) (ind w)) (by
    intro i hi
    induction i using Fin.addCases with
    | left u =>
      have ne : u ≠ p := fun e => missing (e ▸ hi)
      simp [mask, ind, ne]
    | right v => simp [mask])
  rw [mask_on, show V C w g (ind p) = true from (alive_mem ..).mp alive] at eq
  have on : wireVal C (restrictInput P L w (fun _ => false)) g = true := by
    rw [List.ofFn_fin_append] at eq
    exact eq.symm
  have impossible := low _ on
  rw [lineSum_false] at impossible
  contradiction

/-- Switching off one of two lines sharing a merge changes the gate on some
singleton point input. The statement uses only the project's wire semantics. -/
theorem shared_line_flip (inc : Fin P → Fin L → Bool)
    (unique : ∀ {p r : Fin P} {w v : Fin L}, p ≠ r →
      inc p w = true → inc r w = true → inc p v = true → inc r v = true → w = v)
    (C : Circuit) (mono : IsMonotoneCircuit C) (g : ℕ) (w v : Fin L) (ne : w ≠ v)
    (mw : IsLowMerge P L inc C g w) (mv : IsLowMerge P L inc C g v) :
    ∃ u : Fin P, wireVal C (pointLineInput P L u w) g = true ∧
      wireVal C (List.ofFn (fun t : Fin P => decide (t = u)) ++
        List.ofFn (fun _ : Fin L => false)) g = false := by
  obtain ⟨p, r, diff, hp, hr⟩ := merge_points inc C g w mw
  have hw := alive_sub_line inc C g w (low_of_merge mw)
  have pick : ∃ u ∈ aliveSet P L C g w, inc u v ≠ true := by
    by_contra! all
    exact ne (unique diff (Finset.mem_filter.mp (hw hp)).2 (Finset.mem_filter.mp (hw hr)).2
      (all p hp) (all r hr))
  obtain ⟨u, hu, off⟩ := pick
  have zero : wireVal C (List.ofFn (mask u (fun _ : Fin L => false))) g = false := by
    apply Bool.eq_false_of_ne_true
    intro on
    have transfer := ofFn_mono C mono g (mask u (fun _ : Fin L => false)) (mask u (ind v)) (by
      intro i
      induction i using Fin.addCases with
      | left t => simp [mask]
      | right t => simp [mask]) on
    rw [mask_on] at transfer
    exact off (Finset.mem_filter.mp (alive_sub_line inc C g v (low_of_merge mv)
      ((alive_mem ..).mpr transfer))).2
  unfold mask at zero
  rw [List.ofFn_fin_append] at zero
  exact ⟨u, (alive_mem ..).mp hu, zero⟩

/-- Every charged line which shares its gate with another line belongs to
the support of that gate. -/
theorem line_input_mem (inc : Fin P → Fin L → Bool)
    (unique : ∀ {p r : Fin P} {w v : Fin L}, p ≠ r →
      inc p w = true → inc r w = true → inc p v = true → inc r v = true → w = v)
    (C : Circuit) (mono : IsMonotoneCircuit C) (g : ℕ) (w v : Fin L) (ne : w ≠ v)
    (mw : IsLowMerge P L inc C g w) (mv : IsLowMerge P L inc C g v) :
    Fin.natAdd P w ∈ supp (P + L) C g := by
  obtain ⟨u, yes, zero⟩ := shared_line_flip inc unique C mono g w v ne mw mv
  by_contra missing
  have eq := agree_at C g (mask u (ind w)) (mask u (fun _ : Fin L => false)) (by
    intro i hi
    induction i using Fin.addCases with
    | left t => simp [mask]
    | right t =>
      have ht : t ≠ w := fun e => missing (e ▸ hi)
      simp [mask, ind, ht])
  have hw : wireVal C (List.ofFn (mask u (ind w))) g = true := (mask_on C g u w).trans yes
  have h0 : wireVal C (List.ofFn (mask u (fun _ : Fin L => false))) g = false := by
    unfold mask
    rw [List.ofFn_fin_append]
    exact zero
  rw [hw, h0] at eq
  contradiction

/-- U is a set of distinct point inputs, T a set of distinct line inputs and D a
set of roots. Every charged point is alive at a low merge in D. Each charged
line shares a merge in D with some other line. No disjointness of cones is assumed. -/
theorem shared_front_bound (inc : Fin P → Fin L → Bool)
    (unique : ∀ {p r : Fin P} {w v : Fin L}, p ≠ r →
      inc p w = true → inc r w = true → inc p v = true → inc r v = true → w = v)
    (C : Circuit) (mono : IsMonotoneCircuit C) (fan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (D : Finset ℕ) (U : Finset (Fin P)) (T : Finset (Fin L))
    (points : ∀ p ∈ U, ∃ g ∈ D, ∃ w : Fin L, IsLow P L inc C g w ∧ p ∈ aliveSet P L C g w)
    (lines : ∀ w ∈ T, ∃ g ∈ D, ∃ v : Fin L, w ≠ v ∧
      IsLowMerge P L inc C g w ∧ IsLowMerge P L inc C g v) :
    U.card + T.card ≤ coneCost (P + L) C.gates.reverse D + D.card := by
  classical
  let A := U.image (Fin.castAdd L)
  let B := T.image (Fin.natAdd P)
  have dj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro i ha hb
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨w, _, eq⟩ := Finset.mem_image.mp hb
    have := congrArg Fin.val eq
    simp at this
    omega
  have ca : A.card = U.card := Finset.card_image_of_injective _ (Fin.castAdd_injective _ _)
  have cb : B.card = T.card := Finset.card_image_of_injective _ (Fin.natAdd_injective _ _)
  have sub : A ∪ B ⊆ joint (suppsFrom C.gates (inputSupps (P + L))) D := by
    intro i hi
    apply Finset.mem_biUnion.mpr
    rcases Finset.mem_union.mp hi with ha | hb
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨g, hg, w, low, alive⟩ := points p hp
      exact ⟨g, hg, point_input_mem inc C g w p low alive⟩
    · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hb
      obtain ⟨g, hg, v, ne, mw, mv⟩ := lines w hw
      exact ⟨g, hg, line_input_mem inc unique C mono g w v ne mw mv⟩
  have bound := cone_support_bound (P + L) C.gates.reverse D (by simpa using fan)
  rw [List.reverse_reverse] at bound
  have card := Finset.card_le_card sub
  rw [Finset.card_union_of_disjoint dj, ca, cb] at card
  exact card.trans bound

/-- In a plane of order q, a single gate shared by every line costs at least
the number of lines plus 2q gates in its cone, including the gate itself. Only
an upper bound q+1 on lines through a point is used in the incidence count. -/
theorem all_lines_front_bound (q : ℕ) (hq : 2 ≤ q) (size : L = q^2 + q + 1)
    (inc : Fin P → Fin L → Bool)
    (unique : ∀ {p r : Fin P} {w v : Fin L}, p ≠ r →
      inc p w = true → inc r w = true → inc p v = true → inc r v = true → w = v)
    (deg : ∀ p, (Finset.univ.filter fun w : Fin L => inc p w = true).card ≤ q + 1)
    (C : Circuit) (mono : IsMonotoneCircuit C) (fan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (g : ℕ) (merges : ∀ w : Fin L, IsLowMerge P L inc C g w) :
    L + 2*q ≤ coneCost (P + L) C.gates.reverse {g} := by
  classical
  let U := Finset.univ.biUnion fun w : Fin L => aliveSet P L C g w
  have memU (w : Fin L) (p : Fin P) (hp : p ∈ aliveSet P L C g w) : p ∈ U :=
    Finset.mem_biUnion.mpr ⟨w, Finset.mem_univ _, hp⟩
  have hits (w : Fin L) : 2 ≤ (U.filter fun p => inc p w = true).card := by
    obtain ⟨p, r, ne, hp, hr⟩ := merge_points inc C g w (merges w)
    have sub := alive_sub_line inc C g w (low_of_merge (merges w))
    apply Finset.one_lt_card.mpr
    exact ⟨p, Finset.mem_filter.mpr ⟨memU w p hp, (Finset.mem_filter.mp (sub hp)).2⟩,
      r, Finset.mem_filter.mpr ⟨memU w r hr, (Finset.mem_filter.mp (sub hr)).2⟩, ne⟩
  have count : 2*L ≤ U.card * (q+1) := calc
    2*L = ∑ _ : Fin L, 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ w : Fin L, (U.filter fun p => inc p w = true).card :=
      Finset.sum_le_sum (fun w _ => hits w)
    _ = ∑ p ∈ U, (Finset.univ.filter fun w : Fin L => inc p w = true).card := by
      simp only [Finset.card_filter]
      rw [Finset.sum_comm]
    _ ≤ ∑ _p ∈ U, (q+1) := Finset.sum_le_sum (fun p _ => deg p)
    _ = _ := by simp
  have pts : 2*q+1 ≤ U.card := by
    by_contra! small
    have le : U.card ≤ 2*q := by omega
    have bound := Nat.mul_le_mul_right (q+1) le
    rw [size] at count
    nlinarith
  have nontriv : 1 < L := by omega
  have other (w : Fin L) : ∃ v : Fin L, w ≠ v := by
    let a : Fin L := ⟨0, by omega⟩
    let b : Fin L := ⟨1, by omega⟩
    by_cases h : w = a
    · exact ⟨b, h ▸ (by simp [a,b])⟩
    · exact ⟨a, h⟩
  have h := shared_front_bound inc unique C mono fan {g} U Finset.univ (by
    intro p hp
    obtain ⟨w, _, alive⟩ := Finset.mem_biUnion.mp hp
    exact ⟨g, Finset.mem_singleton_self _, w, low_of_merge (merges w), alive⟩) (by
    intro w _
    obtain ⟨v, ne⟩ := other w
    exact ⟨g, Finset.mem_singleton_self _, v, ne, merges w, merges v⟩)
  simp only [Finset.card_singleton, Finset.card_univ, Fintype.card_fin] at h
  omega

#print axioms shared_line_flip
#print axioms shared_front_bound
#print axioms all_lines_front_bound

end UniformSharedFront
