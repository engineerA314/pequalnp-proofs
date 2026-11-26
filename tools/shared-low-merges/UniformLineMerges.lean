import PEqualNP.MetaComplexity.Helpers.EdgeUpperMono
import PEqualNP.MetaComplexity.L663
import PEqualNP.Defs.MetaComplexityLgpMono
import Mathlib.Data.List.OfFn

/-! For an arbitrary finite incidence system in which every line has at least two points,
construct an exact binary monotone circuit whose final OR is a low merge at every line,
in the sense used by the project's L663. This rules out a uniform constant bound on the
multiplicity of each individual plain low merge. The companion file UniformSharedFront
counts the distinct gates in the union of the cones of shared merges. -/

namespace UniformLineMerges

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.LowMerge
open PEqualNP.MetaComplexity.Helpers PEqualNP.MetaComplexity.Helpers.EdgeUpperMono

variable {P L : ℕ}

/-- Single-line soundness and acceptance of incident pairs suffice for the project's
per-line count. These restrictions are among the tests in L-meta-1629 when q ≥ 2. -/
theorem total_merge_uses (q : ℕ) (inc : Fin P → Fin L → Bool) (C : Circuit)
    (deg : ∀ w, (Finset.univ.filter fun p : Fin P => inc p w = true).card = q + 1)
    (mono : IsMonotoneCircuit C) (fan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (pairs : ∀ p w, inc p w = true → wireVal C (pointLineInput P L p w) C.output = true)
    (sound : ∀ w : Fin L, IsLow P L inc C C.output w) :
    L * q ≤ ∑ g ∈ Finset.range (P + L + C.gates.length),
      (Finset.univ.filter fun w : Fin L => IsLowMerge P L inc C g w).card := by
  have slice (w : Fin L) (pts : Fin P → Bool) :
      LowMergeProof.V C w C.output pts = lineSum P L inc w pts := by
    apply Bool.eq_iff_iff.mpr
    refine ⟨sound w pts, ?_⟩
    intro yes
    obtain ⟨p, edge, on⟩ := of_decide_eq_true yes
    apply LowMergeProof.V_mono C mono w C.output (LowMergeProof.ind p) pts ?_ (pairs p w edge)
    intro r hr
    obtain rfl := of_decide_eq_true hr
    exact on
  calc
    L * q = ∑ _ : Fin L, q := by simp
    _ ≤ ∑ w : Fin L, ((Finset.range (P + L + C.gates.length)).filter
        fun g => IsLowMerge P L inc C g w).card := by
      apply Finset.sum_le_sum
      intro w _
      have h := LowMergeProof.main inc C w mono fan (slice w)
      rw [deg w] at h
      omega
    _ = _ := by simp only [Finset.card_filter]; rw [Finset.sum_comm]

/-- Evaluate a set of incidence edges on the concatenated point and line input. -/
def hit (s : Finset (Fin P × Fin L)) (x : Fin (P + L) → Bool) : Bool :=
  decide (∃ e ∈ s, x (Fin.castAdd L e.1) = true ∧ x (Fin.natAdd P e.2) = true)

theorem build_edges (s : Finset (Fin P × Fin L)) :
    ∃ k, Bld (P + L) (hit s) k := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨1, ?_⟩
    intro m _
    refine ⟨[⟨.or, []⟩], m, ?_, ?_, by simp, by simp, ?_⟩
    · simp [Ok]
    · simp
    · intro w hw
      simp [wiresFrom, GateOp.eval, hit, ← hw]
  | insert e s _ ih =>
    obtain ⟨k, old⟩ := ih
    have pair := bld_and (bld_var (Fin.castAdd L e.1)) (bld_var (Fin.natAdd P e.2))
    refine ⟨_, bld_congr (bld_or pair old) ?_⟩
    intro x
    apply Bool.eq_iff_iff.mpr
    simp [hit]

/-- Retain the values of both operands of the final OR, as well as its output. -/
private theorem join_at_root {n k h : ℕ} {F H : (Fin n → Bool) → Bool}
    (hf : Bld n F k) (hh : Bld n H h) :
    ∃ (C : Circuit) (a b : ℕ), Monotone2 C ∧ n ≤ C.output ∧ a < C.output ∧ b < C.output ∧
      C.gates[C.output - n]? = some ⟨.or, [a,b]⟩ ∧
      ∀ x : Fin n → Bool, wireVal C (List.ofFn x) a = F x ∧ wireVal C (List.ofFn x) b = H x ∧
        C.eval (List.ofFn x) = (F x || H x) := by
  obtain ⟨u, a, ou, nu, _, au, eu⟩ := hf n le_rfl
  obtain ⟨v, b, ov, nv, _, bv, ev⟩ := hh (n + u.length) (by omega)
  let prefixGates := u ++ v
  let C : Circuit := ⟨prefixGates ++ [⟨.or, [a,b]⟩], n + prefixGates.length⟩
  have bound : C.output = n + u.length + v.length := by simp [C, prefixGates, Nat.add_assoc]
  refine ⟨C, a, b, ?_, by omega, by omega, by omega, ?_, ?_⟩
  · intro g hg
    change g ∈ (u ++ v) ++ [⟨.or, [a,b]⟩] at hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | rfl
    · have ok := ou g hg
      have nn := nu g hg
      simpa [Ok, nn] using ok
    · have ok := ov g hg
      have nn := nv g hg
      simpa [Ok, nn] using ok
    · simp
  · simp [C]
  · intro x
    let raw := List.ofFn x
    let first := wiresFrom u raw
    let both := wiresFrom v first
    have lr : raw.length = n := by simp [raw]
    have lf : first.length = n + u.length := by simp [first, length_wiresFrom, lr]
    have lb : both.length = C.output := by simp [both, length_wiresFrom, lf, bound]
    have original : (fun i : Fin n => raw.getD i false) = x := by
      funext i
      exact getD_ofFn x i
    have firstInputs : (fun i : Fin n => first.getD i false) = x := by
      funext i
      change (wiresFrom u raw).getD i false = _
      rw [getD_wiresFrom _ _ _ (by rw [lr]; exact i.isLt)]
      exact congrFun original i
    have va : both.getD a false = F x := by
      change (wiresFrom v first).getD a false = _
      rw [getD_wiresFrom _ _ _ (by omega), show first.getD a false = _ from eu raw lr, original]
    have vb : both.getD b false = H x := by rw [show both.getD b false = _ from ev first lf, firstInputs]
    have finalWires : C.wires raw = both ++ [F x || H x] := by
      change wiresFrom ((u ++ v) ++ [⟨.or, [a,b]⟩]) raw = _
      rw [wiresFrom_append, wiresFrom_append]
      change both ++ [GateOp.or.eval ([a,b].map (fun i => both.getD i false))] = _
      simp [GateOp.eval]
      exact congrArg₂ (fun i j : Bool => i || j) va vb
    change (C.wires raw).getD a false = _ ∧ (C.wires raw).getD b false = _ ∧
      (C.wires raw).getD C.output false = _
    rw [finalWires, List.getD_append _ _ _ _ (by omega : a < both.length),
      List.getD_append _ _ _ _ (by omega : b < both.length), ← lb, getD_snoc_eq]
    exact ⟨va, vb, rfl⟩

private theorem hit_single (s : Finset (Fin P × Fin L)) (p : Fin P) (w : Fin L) :
    hit s (Fin.append (fun i => decide (i = p)) (fun j => decide (j = w))) =
      decide ((p,w) ∈ s) := by
  apply Bool.eq_iff_iff.mpr
  simp [hit, Prod.exists]

/-- Split each line's incidences into a distinguished point and all its other points.
The top OR is simultaneously a low merge for every line, even with exact correctness
on inputs activating arbitrarily many points and lines. -/
theorem exists_root_merging_all_lines (inc : Fin P → Fin L → Bool)
    (two : ∀ w, ∃ p r, p ≠ r ∧ inc p w = true ∧ inc r w = true) :
    ∃ C : Circuit, Monotone2 C ∧
      (∀ (x : Fin P → Bool) (y : Fin L → Bool), C.eval (List.ofFn x ++ List.ofFn y) =
        decide (∃ p w, inc p w = true ∧ x p = true ∧ y w = true)) ∧
      ∀ w : Fin L, IsLowMerge P L inc C C.output w := by
  classical
  choose mark other different hm ho using two
  let lefts : Finset (Fin P × Fin L) := Finset.univ.filter fun e =>
    inc e.1 e.2 = true ∧ e.1 = mark e.2
  let rights : Finset (Fin P × Fin L) := Finset.univ.filter fun e =>
    inc e.1 e.2 = true ∧ e.1 ≠ mark e.2
  obtain ⟨_, leftBuilt⟩ := build_edges lefts
  obtain ⟨_, rightBuilt⟩ := build_edges rights
  obtain ⟨C, a, b, mono, base, ha, hb, gate, evals⟩ := join_at_root leftBuilt rightBuilt
  have correct (x : Fin P → Bool) (y : Fin L → Bool) :
      C.eval (List.ofFn x ++ List.ofFn y) = decide (∃ p w, inc p w = true ∧ x p = true ∧ y w = true) := by
    rw [← List.ofFn_fin_append, (evals _).2.2]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, hit, decide_eq_true_eq, Prod.exists, lefts, rights, Finset.mem_filter,
      Finset.mem_univ, true_and, Fin.append_left, Fin.append_right]
    constructor
    · rintro (⟨p,w,⟨i,_⟩,xv,yv⟩ | ⟨p,w,⟨i,_⟩,xv,yv⟩) <;> exact ⟨p,w,i,xv,yv⟩
    · rintro ⟨p,w,i,xv,yv⟩
      by_cases h : p = mark w
      · exact Or.inl ⟨p,w,⟨i,h⟩,xv,yv⟩
      · exact Or.inr ⟨p,w,⟨i,h⟩,xv,yv⟩
  refine ⟨C, mono, correct, ?_⟩
  intro w
  have aliveA (p : Fin P) : p ∈ aliveSet P L C a w ↔ (p,w) ∈ lefts := by
    simp only [aliveSet, Finset.mem_filter, Finset.mem_univ, true_and, pointLineInput, restrictInput,
      ← List.ofFn_fin_append, (evals _).1, hit_single, decide_eq_true_eq]
  have aliveB (p : Fin P) : p ∈ aliveSet P L C b w ↔ (p,w) ∈ rights := by
    simp only [aliveSet, Finset.mem_filter, Finset.mem_univ, true_and, pointLineInput, restrictInput,
      ← List.ofFn_fin_append, (evals _).2.1, hit_single, decide_eq_true_eq]
  refine ⟨base, a, ha, b, hb, gate, ?_, ?_, ?_⟩
  · intro pts on
    change C.eval (List.ofFn pts ++ List.ofFn (fun v => decide (v = w))) = true at on
    rw [correct, decide_eq_true_eq] at on
    obtain ⟨p, l, i, xp, yl⟩ := on
    obtain rfl := of_decide_eq_true yl
    exact decide_eq_true ⟨p, i, xp⟩
  · intro sub
    have yes := (aliveA (mark w)).2 (by simp [lefts, hm w])
    have no := (aliveB (mark w)).1 (sub yes)
    simp [rights] at no
  · intro sub
    have yes := (aliveB (other w)).2 (by simp [rights, ho w, (different w).symm])
    have no := (aliveA (other w)).1 (sub yes)
    simp [lefts, (different w).symm] at no

private theorem alive_or_union (C : Circuit) (g a b : ℕ) (w : Fin L)
    (start : P + L ≤ g) (ha : a < g) (hb : b < g)
    (gate : C.gates[g - (P + L)]? = some ⟨.or, [a,b]⟩) :
    aliveSet P L C g w = aliveSet P L C a w ∪ aliveSet P L C b w := by
  let j := g - (P + L)
  have hj : j < C.gates.length := by
    by_contra! oob
    change C.gates[j]? = _ at gate
    rw [List.getElem?_eq_none oob] at gate
    contradiction
  have gate' : C.gates[j] = ⟨.or, [a,b]⟩ := by
    change C.gates[j]? = _ at gate
    simpa only [List.getElem?_eq_getElem hj, Option.some.injEq] using gate
  have idx : P + L + j = g := by dsimp [j]; omega
  ext p
  simp only [Finset.mem_union, LowMergeProof.alive_mem]
  have ev := LowMergeProof.V_gate C w j hj (LowMergeProof.ind p)
  rw [idx, gate'] at ev
  simp [ev, GateOp.eval, LowMergeProof.R, ha, hb]

/-- On two different lines of a plane, a gate can be charged twice only if its
set of accepted singleton points changes when the active line changes. -/
theorem shared_merge_needs_different_points (inc : Fin P → Fin L → Bool)
    (unique : ∀ {p r : Fin P} {w v : Fin L}, p ≠ r →
      inc p w = true → inc r w = true → inc p v = true → inc r v = true → w = v)
    (C : Circuit) (g : ℕ) {w v : Fin L} (mw : IsLowMerge P L inc C g w)
    (mv : IsLowMerge P L inc C g v) (same : aliveSet P L C g w = aliveSet P L C g v) : w = v := by
  obtain ⟨start, a, ha, b, hb, gate, lowW, leftDiff, rightDiff⟩ := mw
  obtain ⟨_, _, _, _, _, _, lowV, _, _⟩ := mv
  obtain ⟨p, hp, notB⟩ := Finset.not_subset.mp leftDiff
  obtain ⟨r, hr, _⟩ := Finset.not_subset.mp rightDiff
  have ne : p ≠ r := by rintro rfl; exact notB hr
  have merged := alive_or_union C g a b w start ha hb gate
  have onP : p ∈ aliveSet P L C g w := merged ▸ Finset.mem_union_left _ hp
  have onR : r ∈ aliveSet P L C g w := merged ▸ Finset.mem_union_right _ hr
  have wSide := LowMergeProof.alive_sub_line inc C g w lowW
  have vSide := LowMergeProof.alive_sub_line inc C g v lowV
  exact unique ne (Finset.mem_filter.mp (wSide onP)).2 (Finset.mem_filter.mp (wSide onR)).2
    (Finset.mem_filter.mp (vSide (same ▸ onP))).2 (Finset.mem_filter.mp (vSide (same ▸ onR))).2

#print axioms total_merge_uses
#print axioms exists_root_merging_all_lines
#print axioms shared_merge_needs_different_points

end UniformLineMerges
