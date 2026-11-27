import ReverseAll
import PlaneHonestCost
import PlaneLineOnce

/-! A point may be marked once while the active line may recur arbitrarily.
Use sparse outside tests on the shared reverse outputs. -/

namespace PlanePointOnce

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PartialSums SparseRows SparsePlanes ReversePath PlaneAnchorBudget PlaneHonestCost

def pol (n m : ℕ) : Fin (n+m) → Signal (Fin m) :=
  Fin.append (fun _ : Fin n => zero) variableAt

def base (n m : ℕ) := List.ofFn (pol n m)

def once {n m : ℕ} (C : Circuit) (p : Fin n) : Signal (Fin m) :=
  pull C.gates (base n m) C.output (Fin.castAdd m p).val

theorem raw (n m : ℕ) (f : Signal (Fin m)) (inIt : f∈base n m) : IsRaw f := by
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp inIt
  refine Fin.addCases (fun _ => ?_) (fun w => ?_) i
  · exact Or.inl (by simp [pol])
  · exact Or.inr (Or.inr ⟨w,by simp [pol]⟩)

theorem base_le {n m : ℕ} (p : Fin n) (Y : Finset (Fin m)) (j : ℕ) :
    (base n m).getD j zero Y=true → (List.ofFn (PlaneGateBound.row {p} Y)).getD j false=true := by
  by_cases h : j<n+m
  · have atIndex (i : Fin (n+m)) : pol n m i Y=true → PlaneGateBound.row {p} Y i=true := by
      refine Fin.addCases (fun _ => ?_) (fun w => ?_) i
      · simp [pol,zero]
      · simp [pol,variableAt,PlaneGateBound.row]
    simpa [base,List.getD_eq_getElem?_getD,h] using atIndex ⟨j,h⟩
  · simp [base,List.getD_eq_getElem?_getD,h,zero]

theorem sound {n m : ℕ} (C : Circuit) (mc : Monotone2 C) (p : Fin n) (Y : Finset (Fin m)) :
    once C p Y=true → circuitFun (n+m) C (PlaneGateBound.row {p} Y)=true := by
  apply ReverseCost.flag_sound C (base n m) Y (List.ofFn (PlaneGateBound.row {p} Y)) (Fin.castAdd m p).val
    (fun g hg => (mc g hg).1) (fun g hg => (mc g hg).2) (by simp [base]) _ _ (base_le p Y)
  · simpa using (Nat.lt_of_lt_of_le p.isLt (Nat.le_add_right n m))
  · have within : (Fin.castAdd m p).val<n+m := (Fin.castAdd m p).isLt
    have atIndex : PlaneGateBound.row {p} Y (Fin.castAdd m p)=true := by simp [PlaneGateBound.row]
    rw [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left within]
    exact atIndex

theorem point_once {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit) (hq : 1≤q)
    (size : N=q^2+q+1) (lengths : ∀ w, (lineSet I w).card=q+1)
    (unique : ∀ p r, p≠r → ∃! w, I p w ∧ I r w) (mc : Monotone2 C) (neg : No I C q) :
    (∑ p : Fin N,(single (once (m := N) C p)).card)≤5*C.size+N := by
  obtain ⟨W,k,net,cost,flags⟩ := ReverseAll.outputs C (base N N) (raw N N)
  have rejects (p : Fin N) : Rejects (pencil I p) q (once C p) := by
    intro Y apart few
    cases h : once C p Y with
    | false => rfl
    | true =>
      have yes := sound C mc p Y h
      have no := p_off I C mc neg p Y apart few
      rw [p_eval C mc] at no
      rw [no] at yes; contradiction
  have cap (p : Fin N) : (single (once (m := N) C p)).card≤q+1 := by
    rw [← pencil_size I hq size lengths unique p]
    apply Finset.card_le_card
    exact SparseFrontier.off_inside (pencil I p) _ (fun Y apart few => rejects p Y apart (few.trans hq))
  have count := partial_count q (pencil I) (pencil_overlap I unique) W k net (fun p => once (m := N) C p)
    (fun p => flags (Fin.castAdd N p).val) rejects cap
  simp only [Fintype.card_fin] at count
  omega

theorem either_side {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit) (hq : 1≤q)
    (size : N=q^2+q+1) (lengths : ∀ w, (lineSet I w).card=q+1)
    (unique : ∀ p r, p≠r → ∃! w, I p w ∧ I r w) (mc : Monotone2 C) (neg : No I C q) :
    (∑ p : Fin N,(single (once (m := N) C p)).card)+(∑ w,(single (PlaneLineOnce.once N N C w)).card)≤8*C.size+2*N := by
  have p := point_once I C hq size lengths unique mc neg
  have w := PlaneLineOnce.plane I C hq unique mc neg
  omega

#print axioms point_once
#print axioms either_side

end PlanePointOnce
