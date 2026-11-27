import ThresholdCutScores
import ProfileThreshold

namespace ThresholdCutCount

open Finset ThresholdSplit ThresholdCutScores PEqualNP.CircuitLowerBounds
variable {c : ThrCircuit} {a b : ℕ}

def fits (z : Cut c a b) (m : Pattern z) (xy : (Fin a → Bool) × (Fin b → Bool)) :=
  (∀ i : Cross z,pCoord i.val (m i) xy.1≤qCoord i.val (m i) a xy.2) ∧
  -leftScore z xy.1≤rightScore z xy.2+crossScore z m-c.top

instance (z : Cut c a b) (m : Pattern z) (xy : (Fin a → Bool) × (Fin b → Bool)) :
    Decidable (fits z m xy) := by unfold fits; infer_instance

theorem fit_iff (z : Cut c a b) (m : Pattern z) (x : Fin a → Bool) (y : Fin b → Bool) :
    fits z m (x,y) ↔ c.eval (List.ofFn x++List.ofFn y)=true ∧ actual z x y=m := by
  rw [eval_mask,top_weights,decide_eq_true_eq,split_score z x y]
  change ((∀ i : Cross z,pCoord i.val (m i) x≤qCoord i.val (m i) a y) ∧
    -leftScore z x≤rightScore z y+crossScore z m-c.top) ↔ (_ ∧ _)
  rw [← matching]
  constructor
  · rintro ⟨eq,s⟩
    rw [← eq] at s
    exact ⟨by omega,eq⟩
  · rintro ⟨h,eq⟩
    refine ⟨eq,?_⟩
    rw [←eq]
    omega

theorem count (z : Cut c a b) (n : c.inputs=a+b) :
    c.satCount=∑ m : Pattern z,(univ.filter (fits z m)).card := by
  classical
  unfold ThrCircuit.satCount
  rw [n]
  let E := Fin.appendEquiv (α := Bool) a b
  let A := univ.filter fun xy : (Fin a → Bool) × (Fin b → Bool) => c.eval (List.ofFn xy.1++List.ofFn xy.2)=true
  have eq (xy : (Fin a → Bool) × (Fin b → Bool)) :
      c.eval (List.ofFn (E xy))=c.eval (List.ofFn xy.1++List.ofFn xy.2) := by simp [E,Fin.appendEquiv]
  let iso : {xy : (Fin a → Bool) × (Fin b → Bool) // c.eval (List.ofFn xy.1++List.ofFn xy.2)=true} ≃
      {x : Fin (a+b) → Bool // c.eval (List.ofFn x)=true} := E.subtypeEquiv fun xy => by rw [eq]
  rw [← Fintype.card_congr iso,Fintype.card_subtype]
  change A.card=_
  rw [Finset.card_eq_sum_card_fiberwise (f := fun xy => actual z xy.1 xy.2) (t := univ) (by simp)]
  apply sum_congr rfl
  intro m _
  congr 1
  ext xy
  simp [A,fit_iff z m xy.1 xy.2]

def quiet (w : List ℤ) (n : ℕ) := ∀ i : Fin n,w.getD i.val 0=0

instance (w : List ℤ) (n : ℕ) : Decidable (quiet w n) := by unfold quiet; infer_instance

theorem no_score (w : List ℤ) (x : Fin a → Bool) (h : quiet w a) : dot w (List.ofFn x)=0 := by
  rw [ProfileThreshold.dot_coord]
  apply Finset.sum_eq_zero
  intro i _
  rw [h i]
  simp

def classify (c : ThrCircuit) (a b : ℕ) : Cut c a b where
  side i := if quiet (c.gates[i].1.drop a) b then .left else
    if quiet (c.gates[i].1.take a) a then .right else .cross
  rightZero i h y := by
    split at h <;> rename_i v
    · exact no_score _ _ v
    · split at h <;> contradiction
  leftZero i h x := by
    split at h
    · contradiction
    · split at h <;> rename_i v
      · exact no_score _ _ v
      · contradiction

#print axioms count
#print axioms classify

end ThresholdCutCount
