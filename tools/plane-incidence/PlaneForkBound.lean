import LineForks

/-! An all-order tradeoff on the exact L-meta-1629 hypotheses. The error
term counts distinct incidences that encounter simultaneous rises at an AND;
it can also be bounded by the sum of all individual gate-event counts. -/

namespace PlaneForkBound

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PartialSums ReversePath PlaneLineOnce LineForks

theorem raw_eval (n m : ℕ) (X : Finset (Fin n)) :
    (raw n m).map (fun f => f X)=List.ofFn (PlaneGateBound.row X (∅ : Finset (Fin m))) := by
  rw [raw,List.map_ofFn]
  congr 1
  funext i
  refine Fin.addCases (fun p => ?_) (fun w => ?_) i
  · simp [rawAt,PlaneGateBound.row,variableAt]
  · simp [rawAt,PlaneGateBound.row,zero]

def pairBits {n m : ℕ} (p : Fin n) (w : Fin m) := List.ofFn (PlaneGateBound.row {p} {w})
def simultaneous {n m : ℕ} (C : Circuit) (p : Fin n) (w : Fin m) :=
  anyFork C.gates (raw n m) (pairBits p w) {p}

theorem alternatives {n m : ℕ} (C : Circuit) (p : Fin n) (w : Fin m) (mc : Monotone2 C)
    (off : circuitFun (n+m) C (PlaneGateBound.row {p} (∅ : Finset (Fin m)))=false)
    (on : circuitFun (n+m) C (PlaneGateBound.row {p} {w})=true) :
    simultaneous C p w = true ∨ once n m C w {p}=true := by
  apply fork_or_flag C (raw n m) (pairBits p w) {p} (Fin.natAdd n w).val
    (fun g hg => (mc g hg).1) (fun g hg => (mc g hg).2) (by simp [raw,pairBits]) _ _ on
  · intro j
    have coord (i : Fin (n+m)) : PlaneGateBound.row {p} {w} i=true →
        rawAt n m i {p}=true ∨ i.val=(Fin.natAdd n w).val := by
      refine Fin.addCases (fun k => ?_) (fun k => ?_) i
      · simp [PlaneGateBound.row,rawAt,variableAt]; exact Or.inl
      · simp only [PlaneGateBound.row,Fin.append_right,decide_eq_true_eq,Finset.mem_singleton]
        rintro rfl; exact Or.inr rfl
    by_cases hi : j < n+m
    · simpa [pairBits,raw,List.getD_eq_getElem?_getD,hi] using coord ⟨j,hi⟩
    · simp [pairBits,List.getD_eq_getElem?_getD,hi]
  · rwa [raw_eval]

def rows {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (l : Fin N) :=
  Finset.univ.filter fun p => I p l

def forkedPairs {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit) :=
  ∑ l, ((rows I l).filter fun p => simultaneous C p l=true).card

theorem plane {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hq : 1≤q) (lengths : ∀ l, (rows I l).card=q+1)
    (unique : ∀ p r, p≠r → ∃! w, I p w ∧ I r w) (mc : Monotone2 C)
    (positive : ∀ p w, I p w → circuitFun (N+N) C (fun k => decide (k=Fin.castAdd N p ∨ k=Fin.natAdd N w))=true)
    (negative : ∀ z : Fin (N+N) → Bool, (Finset.univ.filter fun w => z (Fin.natAdd N w)=true).card≤q →
      (¬∃ p w, I p w ∧ z (Fin.castAdd N p)=true ∧ z (Fin.natAdd N w)=true) → circuitFun (N+N) C z=false) :
    N*q≤3*C.size+forkedPairs I C := by
  classical
  have off (p : Fin N) : circuitFun (N+N) C (PlaneGateBound.row {p} (∅ : Finset (Fin N)))=false := by
    apply negative
    · simp only [PlaneGateBound.row,Fin.append_right,decide_eq_true_eq,Finset.filter_mem_eq_inter,
        Finset.univ_inter,Finset.card_empty,Nat.zero_le]
    · rintro ⟨_,w,_,_,no⟩
      simp only [PlaneGateBound.row,Fin.append_right,decide_eq_true_eq,Finset.notMem_empty] at no
  have a := PlaneLineOnce.plane I C hq unique mc negative
  have each (l : Fin N) : (rows I l).card≤(single (once N N C l)).card+
      ((rows I l).filter fun p => simultaneous C p l=true).card := by
    apply le_trans (Finset.card_le_card (t := single (once N N C l) ∪ ((rows I l).filter fun p => simultaneous C p l=true)) ?_)
      (Finset.card_union_le _ _)
    intro p hp
    have edge : I p l := (Finset.mem_filter.mp hp).2
    have on : circuitFun (N+N) C (PlaneGateBound.row {p} {l})=true := by rw [PlaneGateBound.singleton_row]; exact positive p l edge
    rcases alternatives C p l mc (off p) on with forked | used
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp,forked⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,used⟩)
  have s := Finset.sum_le_sum (s := Finset.univ) (fun l _ => each l)
  simp only [lengths,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,Finset.sum_add_distrib] at s
  unfold forkedPairs
  rw [Nat.mul_add,Nat.mul_one] at s
  omega

def visits {P : Type} : List Gate → List (Signal P) → List Bool → Finset P → ℕ
  | [],_,_,_ => 0
  | g::gs,W,x,X => (fork g W x X).toNat + visits gs (W++[baseGate g W]) (x++[actualGate g x]) X

theorem indicator_le {P : Type} (gs : List Gate) (W : List (Signal P)) (x : List Bool) (X : Finset P) :
    (anyFork gs W x X).toNat≤visits gs W x X := by
  induction gs generalizing W x with
  | nil => rfl
  | cons g gs ih =>
    have h := ih (W++[baseGate g W]) (x++[actualGate g x])
    cases e : fork g W x X <;> simp [anyFork,visits,e]
    · exact h

def gateEvents {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit) :=
  ∑ l, ∑ p ∈ rows I l, visits C.gates (raw N N) (pairBits p l) {p}

theorem pairs_le_events {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit) :
    forkedPairs I C≤gateEvents I C := by
  apply Finset.sum_le_sum
  intro l _
  rw [Finset.card_eq_sum_ones,Finset.sum_filter]
  apply Finset.sum_le_sum
  intro p _
  have h := indicator_le C.gates (raw N N) (pairBits p l) {p}
  change (simultaneous C p l).toNat ≤ _ at h
  cases e : simultaneous C p l <;> simpa [e] using h

#print axioms plane
#print axioms pairs_le_events

end PlaneForkBound
