import RepairAnds
import OrSensitivity
import PEqualNP.MetaComplexity.Helpers.LowMergeWires
import PEqualNP.Defs.MetaComplexityLgpMono
import Mathlib.Data.Finset.Sum
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Log

/-! A total-size lower bound with precisely the plane and circuit-test
hypotheses in L-meta-1629. One q-line pencil yields the OR term. The family
of all sparse line sets yields the independent AND term. -/

namespace PlaneGateBound

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity SparseNegatives RepairAnds

def row {P L : ℕ} (X : Finset (Fin P)) (Y : Finset (Fin L)) : Fin (P+L) → Bool :=
  Fin.append (fun p => decide (p ∈ X)) (fun w => decide (w ∈ Y))

theorem singleton_row {P L : ℕ} (p : Fin P) (w : Fin L) :
    row {p} {w} = fun k => decide (k = Fin.castAdd L p ∨ k = Fin.natAdd P w) := by
  have apart (i : Fin P) (j : Fin L) : Fin.castAdd L i ≠ Fin.natAdd P j := by
    intro e
    have h := congrArg Fin.val e
    change i.val = P + j.val at h
    omega
  funext k
  induction k using Fin.addCases with
  | left i => simp [row,apart i w]
  | right j => simp [row,(apart p j).symm]

theorem accepts_pair {P L : ℕ} (C : Circuit) (mono : IsMonotoneCircuit C) (p : Fin P) (w : Fin L)
    (positive : circuitFun (P+L) C (row {p} {w}) = true) (z : Fin (P+L) → Bool)
    (px : z (Fin.castAdd L p) = true) (wy : z (Fin.natAdd P w) = true) :
    circuitFun (P+L) C z = true := by
  apply LowMergeProof.wires_mono C mono (List.ofFn (row {p} {w})) (List.ofFn z) (by simp) _ C.output positive
  intro i on
  by_cases valid : i < P+L
  · simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,valid,dite_eq_left,Option.getD_some] at on ⊢
    rw [singleton_row] at on
    have e := of_decide_eq_true on
    rcases e with e | e
    · rw [e]; exact px
    · rw [e]; exact wy
  · rw [List.getD_eq_default _ _ (by simp; omega)] at on
    contradiction

private theorem update_on {n : ℕ} (z : Fin n → Bool) (i j : Fin n) (on : z j = true) :
    Function.update z i true j = true := by
  by_cases e : j = i <;> simp [e,Function.update_of_ne,on]

/-- Any small line set supplies a sensitive zero assignment. Its point cost
is the size of the line union, and its line cost counts all missing lines. -/
theorem width {P L : ℕ} (I : Lines P L) (q : ℕ) (size : ∀ w, q < (I w).card)
    (linear : ∀ w v, w ≠ v → (I w ∩ I v).card ≤ 1) (Y : Finset (Fin L)) (few : Y.card ≤ q)
    (C : Circuit) (mono : IsMonotoneCircuit C) (fan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (positive : ∀ p w, p ∈ I w → circuitFun (P+L) C (row {p} {w}) = true)
    (negative : circuitFun (P+L) C (row (outside I Y) Y) = false) :
    (covered I Y).card + (L-Y.card) ≤ OrSensitivity.orCount C.gates + 1 := by
  classical
  let z := row (outside I Y) Y
  let missed := (Finset.univ : Finset (Fin L)) \ Y
  let T := ((covered I Y).disjSum missed).map finSumFinEquiv.toEmbedding
  have flips (i : Fin (P+L)) (hi : i ∈ T) : circuitFun (P+L) C (Function.update z i true) = true := by
    obtain ⟨k,hk,rfl⟩ := Finset.mem_map.mp hi
    cases k with
    | inl p =>
      have hp := Finset.inl_mem_disjSum.mp hk
      obtain ⟨w,hw,pw⟩ := Finset.mem_biUnion.mp hp
      apply accepts_pair C mono p w (positive p w pw)
      · exact Function.update_self _ _ _
      · apply update_on
        simpa [z,row] using hw
    | inr w =>
      have hw := (Finset.mem_sdiff.mp (Finset.inr_mem_disjSum.mp hk)).2
      obtain ⟨p,pw,px⟩ := private_point I q size linear Y few w hw
      apply accepts_pair C mono p w (positive p w pw)
      · apply update_on
        simpa [z,row] using px
      · exact Function.update_self _ _ _
  have bound := OrSensitivity.positive_sensitivity C mono fan z T negative flips
  simpa [T,missed,Finset.card_sdiff_of_subset (Finset.subset_univ Y)] using bound

private theorem pencil_count {N : ℕ} (I : Lines N N) (q : ℕ) (p : Fin N) (Y : Finset (Fin N))
    (size : ∀ w, (I w).card = q+1) (linear : ∀ w v, w ≠ v → (I w ∩ I v).card ≤ 1)
    (through : ∀ w ∈ Y, p ∈ I w) : ((covered I Y).erase p).card = Y.card*q := by
  classical
  have eq : (covered I Y).erase p = Y.biUnion fun w => (I w).erase p := by
    ext a
    simp only [Finset.mem_erase,covered,Finset.mem_biUnion]
    aesop
  rw [eq,Finset.card_biUnion]
  · apply Finset.sum_const_nat
    intro w hw
    rw [Finset.card_erase_of_mem (through w hw),size]
    omega
  · intro w hw v hv ne
    rw [Function.onFun,Finset.disjoint_left]
    intro a ha hb
    obtain ⟨ap,aw⟩ := Finset.mem_erase.mp ha
    have av := (Finset.mem_erase.mp hb).2
    exact ap ((Finset.card_le_one.mp (linear w v ne)) a (Finset.mem_inter.mpr ⟨aw,av⟩) p
      (Finset.mem_inter.mpr ⟨through w hw,through v hv⟩))

/-- q concurrent lines cover q²+1 points. The existence of such a pencil is
derived from point-pair existence and line sizes. -/
theorem wide_pencil {N q : ℕ} (I : Lines N N) (pos : 1 ≤ q) (nsize : N=q^2+q+1)
    (size : ∀ w, (I w).card = q+1) (linear : ∀ w v, w ≠ v → (I w ∩ I v).card ≤ 1)
    (joins : ∀ p r, p ≠ r → ∃ w, p ∈ I w ∧ r ∈ I w) :
    ∃ Y, Y.card=q ∧ (covered I Y).card=q^2+1 := by
  classical
  let p : Fin N := ⟨0,by omega⟩
  let pencil := Finset.univ.filter fun w => p ∈ I w
  have through : ∀ w ∈ pencil, p ∈ I w := fun _ h => (Finset.mem_filter.mp h).2
  have geom := pencil_count I q p pencil size linear through
  have eq : (covered I pencil).erase p = Finset.univ.erase p := by
    ext r
    simp only [Finset.mem_erase,Finset.mem_univ,and_true]
    constructor
    · exact And.left
    · intro rp
      obtain ⟨w,pw,rw⟩ := joins p r (Ne.symm rp)
      exact ⟨rp,Finset.mem_biUnion.mpr ⟨w,Finset.mem_filter.mpr ⟨Finset.mem_univ _,pw⟩,rw⟩⟩
  rw [eq,Finset.card_erase_of_mem (Finset.mem_univ p),Finset.card_univ,Fintype.card_fin] at geom
  have hn : N-1 = q^2+q := by omega
  rw [hn] at geom
  have le : q ≤ pencil.card := by
    exact Nat.le_of_mul_le_mul_right (show q*q ≤ pencil.card*q by nlinarith) pos
  obtain ⟨Y,sub,card⟩ := Finset.exists_subset_card_eq le
  have inside : ∀ w ∈ Y, p ∈ I w := fun w hw => through w (sub hw)
  have unionSize := pencil_count I q p Y size linear inside
  have nonempty : 0 < Y.card := by omega
  obtain ⟨w,hw⟩ := Finset.card_pos.mp nonempty
  have coveredP : p ∈ covered I Y := Finset.mem_biUnion.mpr ⟨w,hw,inside w hw⟩
  have unionPos := Finset.card_pos.mpr ⟨p,coveredP⟩
  rw [Finset.card_erase_of_mem coveredP,card,← pow_two] at unionSize
  exact ⟨Y,card,by omega⟩

/-- The hypotheses match L-meta-1629. Combining separate binary AND and OR
counts yields the additive lower bound for unrestricted sharing. -/
theorem total {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hq : 2 ≤ q) (nsize : N = q^2+q+1)
    (lengths : ∀ w, (Finset.univ.filter fun p => I p w).card = q+1)
    (unique : ∀ p r, p ≠ r → ∃! w, I p w ∧ I r w) (mc : Monotone2 C)
    (positive : ∀ p w, I p w → circuitFun (N+N) C (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N w)) = true)
    (negative : ∀ z : Fin (N+N) → Bool, (Finset.univ.filter fun w => z (Fin.natAdd N w) = true).card ≤ q →
      (¬ ∃ p w, I p w ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N w) = true) → circuitFun (N+N) C z = false) :
    2*q^2+1 + Nat.clog 2 (∑ j ∈ Finset.range (q+1), N.choose j) ≤ C.size := by
  classical
  let S (w : Fin N) := Finset.univ.filter fun p => I p w
  have memS (p w : Fin N) : p ∈ S w ↔ I p w := by simp [S]
  have size : ∀ w, q < (S w).card := by intro w; change q < (Finset.univ.filter _).card; rw [lengths]; omega
  have linear (w v : Fin N) (ne : w ≠ v) : (S w ∩ S v).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro p hp r hr
    by_contra diff
    obtain ⟨l,_,only⟩ := unique p r diff
    obtain ⟨pw,pv⟩ := Finset.mem_inter.mp hp
    obtain ⟨rw,rv⟩ := Finset.mem_inter.mp hr
    exact ne ((only w ⟨(memS _ _).mp pw,(memS _ _).mp rw⟩).trans
      (only v ⟨(memS _ _).mp pv,(memS _ _).mp rv⟩).symm)
  have mono : IsMonotoneCircuit C := fun g hg => (mc g hg).1
  have fan := fun g hg => (mc g hg).2
  have yes (p w : Fin N) (pw : p ∈ S w) : circuitFun (N+N) C (row {p} {w}) = true := by
    rw [singleton_row]
    exact positive p w ((memS _ _).mp pw)
  have no (Y : Finset (Fin N)) (few : Y.card ≤ q) : circuitFun (N+N) C (row (outside S Y) Y) = false := by
    apply negative
    · simpa only [row,Fin.append_right,decide_eq_true_eq,Finset.filter_mem_eq_inter,Finset.univ_inter] using few
    · rintro ⟨p,w,pw,px,wy⟩
      have hull : p ∈ outside S Y := by simpa [row] using px
      have selected : w ∈ Y := by simpa only [row,Fin.append_right,decide_eq_true_eq] using wy
      exact (Finset.mem_sdiff.mp hull).2 (Finset.mem_biUnion.mpr ⟨w,selected,(memS _ _).mpr pw⟩)
  obtain ⟨Y,card,hull⟩ := wide_pencil S (by omega) nsize lengths linear (by
    intro p r ne
    obtain ⟨w,⟨pw,rw⟩,_⟩ := unique p r ne
    exact ⟨w,(memS _ _).mpr pw,(memS _ _).mpr rw⟩)
  have few : Y.card ≤ q := by omega
  have ors := width S q size linear Y few C mono fan yes (no Y few)
  rw [card,hull,nsize] at ors
  have ands := whole_circuit S q size linear C mono fan
    (fun w p pw => by simpa [circuitFun,row,bits] using yes p w pw)
    (fun Y h => by simpa [circuitFun,row,bits] using no Y h)
  have bitsBound := Nat.clog_le_of_le_pow ands
  have sumBound := OrSensitivity.counts_disjoint C.gates
  change _ ≤ C.gates.length
  omega

#print axioms width
#print axioms total

end PlaneGateBound
