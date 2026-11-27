import ProfileMass

namespace ProfileThreshold

open Finset ProfileMass ThresholdSplit PEqualNP.CircuitLowerBounds
variable {d : ℕ}

theorem dot_coord (n : ℕ) (w : List ℤ) (x : Fin n → Bool) :
    dot w (List.ofFn x)=∑ i, if x i then w.getD i.val 0 else 0 := by
  induction n generalizing w with
  | zero => simp [dot]
  | succ n ih =>
    rw [Fin.sum_univ_succ,List.ofFn_succ]
    cases w with
    | nil => simp [dot]
    | cons a w =>
      change (if x 0 then a else 0)+dot w (List.ofFn (fun j : Fin n => x j.succ))=_
      rw [ih]
      simp [List.getD_eq_getElem?_getD]

def signed (negative bit : Bool) := if negative then !bit else bit

theorem involution (s b : Bool) : signed s (signed s b)=b := by cases s <;> cases b <;> rfl

def blockEquivInputs (c : ThrCircuit) (width : Fin d → ℕ)
    (loc : (Σ j, Fin (width j)) ≃ Fin c.inputs) (flip : Assignment width) :
    (Fin c.inputs → Bool) ≃ Assignment width where
  toFun x := fun j i => signed (flip j i) (x (loc ⟨j,i⟩))
  invFun y := fun k => let q := loc.symm k; signed (flip q.1 q.2) (y q.1 q.2)
  left_inv x := by
    funext k
    obtain ⟨q,rfl⟩ := loc.surjective k
    simp [involution]
  right_inv y := by
    funext j i
    dsimp only
    rw [loc.symm_apply_apply,involution]

theorem sum_indicator {m : ℕ} (b : Fin m → Bool) :
    (∑ i, (if b i then (1 : ℤ) else 0))=((chosen b).card : ℤ) := by
  classical
  unfold chosen
  rw [Finset.card_filter,Nat.cast_sum]
  exact Finset.sum_congr rfl fun i _ => by cases b i <;> rfl

theorem bit_score (base : ℤ) (negative bit : Bool) :
    (if bit then (if negative then -base else base) else 0)=
      base*((if signed negative bit then 1 else 0)-(if negative then 1 else 0)) := by
  cases negative <;> cases bit <;> simp [signed]

def gateScore (width : Fin d → ℕ) (c : ThrCircuit) (rep : Fin d → GateId c → ℤ)
    (flip : Assignment width) (k : Sizes width) (g : GateId c) : ℤ :=
  ∑ j,rep j g*((k j).val-((chosen (flip j)).card : ℤ))

def agrees (width : Fin d → ℕ) (c : ThrCircuit) (rep : Fin d → GateId c → ℤ)
    (loc : (Σ j, Fin (width j)) ≃ Fin c.inputs) (flip : Assignment width) : Prop :=
  ∀ j i g, c.gates[g].1.getD (loc ⟨j,i⟩).val 0=if flip j i then -rep j g else rep j g

theorem score (width : Fin d → ℕ) (c : ThrCircuit) (rep : Fin d → GateId c → ℤ)
    (loc : (Σ j, Fin (width j)) ≃ Fin c.inputs) (flip : Assignment width)
    (h : agrees width c rep loc flip) (x : Fin c.inputs → Bool) (g : GateId c) :
    dot c.gates[g].1 (List.ofFn x)=gateScore width c rep flip (profile width (blockEquivInputs c width loc flip x)) g := by
  classical
  rw [dot_coord,← loc.sum_comp (fun i => if x i then c.gates[g].1.getD i.val 0 else 0),Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  change (∑ i : Fin (width j), if x (loc ⟨j,i⟩) then c.gates[g].1.getD (loc ⟨j,i⟩).val 0 else 0)=_
  simp_rw [h j _ g,bit_score]
  rw [← Finset.mul_sum,Finset.sum_sub_distrib,sum_indicator,sum_indicator]
  rfl

def accepts (width : Fin d → ℕ) (c : ThrCircuit) (rep : Fin d → GateId c → ℤ)
    (flip : Assignment width) (k : Sizes width) :=
  top c (fun g => decide (c.gates[g].2.1≤gateScore width c rep flip k g))

theorem count (width : Fin d → ℕ) (c : ThrCircuit) (rep : Fin d → GateId c → ℤ)
    (loc : (Σ j, Fin (width j)) ≃ Fin c.inputs) (flip : Assignment width)
    (h : agrees width c rep loc flip) :
    c.satCount=∑ k : Sizes width, if accepts width c rep flip k
      then ∏ j,(width j).choose (k j).val else 0 := by
  classical
  let e := blockEquivInputs c width loc flip
  have ident (x : Fin c.inputs → Bool) : c.eval (List.ofFn x)=accepts width c rep flip (profile width (e x)) := by
    rw [eval_mask]
    apply congrArg (top c)
    funext g
    simp only [mask,score width c rep loc flip h]
    rfl
  let iso := e.subtypeEquiv (p := fun x => c.eval (List.ofFn x)=true)
    (q := fun y => accepts width c rep flip (profile width y)=true) (fun x => by rw [ident])
  rw [ThrCircuit.satCount,Fintype.card_congr iso,Fintype.card_subtype,aggregate]

#print axioms count

end ProfileThreshold
