import ReverseCost
import PlaneGateBound

/-! Specialization to the raw point/line input convention in L-meta-1629.
Only the one-line negative tests and uniqueness of the line through two
points are required for the estimate. -/

namespace PlaneLineOnce

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity ReversePath PartialSums

def rawAt (n m : ℕ) : Fin (n+m) → Signal (Fin n) :=
  Fin.append (fun p : Fin n => variableAt p) (fun _ : Fin m => zero)
def raw (n m : ℕ) := List.ofFn (rawAt n m)
def once (n m : ℕ) (C : Circuit) (w : Fin m) : Signal (Fin n) :=
  pull C.gates (raw n m) C.output (Fin.natAdd n w).val

theorem raw_signals (n m : ℕ) (f : Signal (Fin n)) (h : f ∈ raw n m) : IsRaw f := by
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp h
  refine Fin.addCases (fun p => ?_) (fun w => ?_) i
  · simp only [rawAt,Fin.append_left]
    exact Or.inr (Or.inr ⟨p,rfl⟩)
  · simp only [rawAt,Fin.append_right]
    exact Or.inl rfl

theorem base_le (n m : ℕ) (X : Finset (Fin n)) (Y : Finset (Fin m)) (j : ℕ) :
    (raw n m).getD j zero X=true → (List.ofFn (PlaneGateBound.row X Y)).getD j false=true := by
  by_cases hj : j < n+m
  · have atIndex (i : Fin (n+m)) : rawAt n m i X=true → PlaneGateBound.row X Y i=true := by
      refine Fin.addCases (fun p => ?_) (fun w => ?_) i
      · simp [rawAt,PlaneGateBound.row,variableAt]
      · simp [rawAt,zero]
    simpa [raw,List.getD_eq_getElem?_getD,hj] using atIndex ⟨j,hj⟩
  · simp [raw,List.getD_eq_getElem?_getD,hj,zero]

theorem incidence {n m : ℕ} (I : Fin m → Finset (Fin n))
    (linear : ∀ l k, l≠k → (I l ∩ I k).card≤1) (C : Circuit)
    (mc : Monotone2 C) (reject : ∀ l,
      circuitFun (n+m) C (PlaneGateBound.row (outside I l) {l})=false) :
    (∑ l, (single (once n m C l)).card)≤3*C.size+m := by
  let neg (l : Fin m) := List.ofFn (PlaneGateBound.row (outside I l) {l})
  have left : IsMonotoneCircuit C := fun g hg => (mc g hg).1
  have right := fun g hg => (mc g hg).2
  have on (l : Fin m) : (neg l).getD (Fin.natAdd n l).val false=true := by
    simp [neg,List.getD_eq_getElem?_getD,PlaneGateBound.row]
  have bound := ReverseCost.line_once I linear C (raw n m) (raw_signals n m) (fun l => (Fin.natAdd n l).val) neg
    left right (by simp [raw,neg]) (fun l => by simp [neg]) on
    (fun l i => base_le n m (outside I l) {l} i) reject
  simpa [once] using bound

theorem plane {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hq : 1≤q) (unique : ∀ p r, p≠r → ∃! w, I p w ∧ I r w) (mc : Monotone2 C)
    (negative : ∀ z : Fin (N+N) → Bool, (Finset.univ.filter fun w => z (Fin.natAdd N w)=true).card≤q →
      (¬∃ p w, I p w ∧ z (Fin.castAdd N p)=true ∧ z (Fin.natAdd N w)=true) → circuitFun (N+N) C z=false) :
    (∑ l, (single (once N N C l)).card)≤3*C.size+N := by
  classical
  let S (w : Fin N) := Finset.univ.filter fun p => I p w
  have mem (p w : Fin N) : p ∈ S w ↔ I p w := by simp [S]
  have linear (l m : Fin N) (ne : l≠m) : (S l ∩ S m).card≤1 := by
    apply Finset.card_le_one.mpr
    intro p hp r hr
    by_contra diff
    obtain ⟨k,_,only⟩ := unique p r diff
    obtain ⟨pl,pm⟩ := Finset.mem_inter.mp hp
    obtain ⟨rl,rm⟩ := Finset.mem_inter.mp hr
    exact ne ((only l ⟨(mem _ _).mp pl,(mem _ _).mp rl⟩).trans
      (only m ⟨(mem _ _).mp pm,(mem _ _).mp rm⟩).symm)
  apply incidence S linear C mc
  intro l
  apply negative
  · simpa only [PlaneGateBound.row,Fin.append_right,decide_eq_true_eq,Finset.filter_mem_eq_inter,Finset.univ_inter,Finset.card_singleton] using hq
  · rintro ⟨p,w,pw,px,wy⟩
    have chosen : w=l := by simpa only [PlaneGateBound.row,Fin.append_right,decide_eq_true_eq,Finset.mem_singleton] using wy
    subst w
    have outsideP : p ∈ outside S l := by simpa [PlaneGateBound.row] using px
    exact (Finset.mem_sdiff.mp outsideP).2 ((mem p l).mpr pw)

#print axioms incidence
#print axioms plane

end PlaneLineOnce
