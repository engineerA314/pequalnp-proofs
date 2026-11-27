import PEqualNP.Defs.CircuitLowerBounds
import Mathlib

/-! Count a depth-two integer threshold circuit by the disjoint bottom
patterns and dominance between vectors from the two halves of its inputs. -/

namespace ThresholdSplit

open PEqualNP.CircuitLowerBounds
abbrev GateId (c : ThrCircuit) := Fin c.gates.length
abbrev Mask (c : ThrCircuit) := GateId c → Bool

def dot (w : List ℤ) (x : List Bool) : ℤ :=
  ((w.zip x).map (fun p => if p.2=true then p.1 else 0)).sum

theorem split_dot (w : List ℤ) (x y : List Bool) :
    dot w (x++y)=dot (w.take x.length) x+dot (w.drop x.length) y := by
  induction x generalizing w with
  | nil => simp [dot]
  | cons b x ih =>
    cases w with
    | nil => simp [dot]
    | cons a w =>
      simp only [List.cons_append,List.length_cons,List.take_succ_cons,List.drop_succ_cons]
      change (if b=true then a else 0)+dot w (x++y)=
        ((if b=true then a else 0)+dot (w.take x.length) x)+dot (w.drop x.length) y
      rw [ih,add_assoc]

def mask (c : ThrCircuit) (x : List Bool) : Mask c :=
  fun i => decide (c.gates[i].2.1≤dot c.gates[i].1 x)

def top (c : ThrCircuit) (m : Mask c) : Bool := decide (c.top≤
  (List.ofFn (fun i : GateId c => c.gates[i].2.2*(if m i then 1 else 0))).sum)

theorem eval_mask (c : ThrCircuit) (x : List Bool) : c.eval x=top c (mask c x) := by
  unfold ThrCircuit.eval top mask dot
  simp only [decide_eq_true_eq]
  congr 2
  let f := fun g : List ℤ × ℤ × ℤ => g.2.2*(if g.2.1≤((g.1.zip x).map (fun p => if p.2=true then p.1 else 0)).sum then 1 else 0)
  change (c.gates.map f).sum=(List.ofFn (f ∘ fun i : Fin c.gates.length => c.gates[i])).sum
  rw [← List.map_ofFn]
  simp

def point (c : ThrCircuit) (m : Mask c) (x : List Bool) (i : GateId c) : ℤ :=
  let partialSum := dot (c.gates[i].1.take x.length) x
  if m i then -partialSum else partialSum

def query (c : ThrCircuit) (m : Mask c) (cut : ℕ) (y : List Bool) (i : GateId c) : ℤ :=
  let partialSum := dot (c.gates[i].1.drop cut) y
  if m i then partialSum-c.gates[i].2.1 else c.gates[i].2.1-1-partialSum

theorem mask_iff (c : ThrCircuit) (m : Mask c) (x y : List Bool) :
    mask c (x++y)=m ↔ ∀ i, point c m x i≤query c m x.length y i := by
  rw [funext_iff]
  apply forall_congr'
  intro i
  cases b : m i <;> simp [mask,point,query,b,split_dot] <;> omega

variable {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]

theorem sum_by_mask (pattern : A → B) (pass : B → Bool) :
    (Finset.univ.filter (fun x => pass (pattern x)=true)).card =
    ∑ m : B, if pass m then (Finset.univ.filter (fun x => pattern x=m)).card else 0 := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := pattern) (t := Finset.univ) (by simp)]
  apply Finset.sum_congr rfl
  intro m _
  by_cases good : pass m=true
  · rw [ite_eq_left good]
    congr 1
    ext x
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨And.right,fun e => ⟨e ▸ good,e⟩⟩
  · rw [ite_eq_right good,Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨f,eq⟩ := Finset.mem_filter.mp hx
    exact good (eq ▸ (Finset.mem_filter.mp f).2)

def dominated (c : ThrCircuit) (m : Mask c) {a b : ℕ} (xy : (Fin a → Bool) × (Fin b → Bool)) :=
  ∀ i, point c m (List.ofFn xy.1) i≤query c m a (List.ofFn xy.2) i

instance (c : ThrCircuit) (m : Mask c) {a b : ℕ} (xy : (Fin a → Bool) × (Fin b → Bool)) :
    Decidable (dominated c m xy) := by unfold dominated; infer_instance

theorem count (c : ThrCircuit) (a b : ℕ) (h : c.inputs=a+b) :
    c.satCount = ∑ m : Mask c, if top c m then
      (Finset.univ.filter (fun xy : (Fin a → Bool) × (Fin b → Bool) => dominated c m xy)).card else 0 := by
  classical
  unfold ThrCircuit.satCount
  rw [h]
  let E := Fin.appendEquiv (α := Bool) a b
  let pattern := fun xy : (Fin a → Bool) × (Fin b → Bool) => mask c (List.ofFn xy.1++List.ofFn xy.2)
  have eq (xy : (Fin a → Bool) × (Fin b → Bool)) : c.eval (List.ofFn (E xy))=top c (pattern xy) := by
    simp [E,Fin.appendEquiv,pattern,eval_mask]
  let iso : {xy : (Fin a → Bool) × (Fin b → Bool) // top c (pattern xy)=true} ≃
      {x : Fin (a+b) → Bool // c.eval (List.ofFn x)=true} :=
    E.subtypeEquiv fun xy => by rw [eq]
  rw [← Fintype.card_congr iso,Fintype.card_subtype, sum_by_mask]
  apply Finset.sum_congr rfl
  intro m _
  split <;> rename_i hm
  · congr 1
    ext xy
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    simpa [pattern,dominated] using mask_iff c m (List.ofFn xy.1) (List.ofFn xy.2)
  · rfl

#print axioms count

end ThresholdSplit
