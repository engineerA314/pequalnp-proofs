import ThresholdSplit

namespace ThresholdCutScores

open ThresholdSplit PEqualNP.CircuitLowerBounds Finset

inductive Side | left | right | cross deriving DecidableEq

structure Cut (c : ThrCircuit) (a b : ℕ) where
  side : GateId c → Side
  rightZero : ∀ i,side i=.left → ∀ y : Fin b → Bool,dot (c.gates[i].1.drop a) (List.ofFn y)=0
  leftZero : ∀ i,side i=.right → ∀ x : Fin a → Bool,dot (c.gates[i].1.take a) (List.ofFn x)=0

variable {c : ThrCircuit} {a b : ℕ}

abbrev Cross (z : Cut c a b) := {i : GateId c // z.side i=.cross}
abbrev Pattern (z : Cut c a b) := Cross z → Bool

def leftPart (i : GateId c) (x : Fin a → Bool) := dot (c.gates[i].1.take a) (List.ofFn x)
def rightPart (i : GateId c) (a : ℕ) (y : Fin b → Bool) := dot (c.gates[i].1.drop a) (List.ofFn y)
def weight (i : GateId c) (on : Bool) : ℤ := if on then c.gates[i].2.2 else 0
def leftScore (z : Cut c a b) (x : Fin a → Bool) := ∑ i,if z.side i=.left then
  weight i (decide (c.gates[i].2.1≤leftPart i x)) else 0
def rightScore (z : Cut c a b) (y : Fin b → Bool) := ∑ i,if z.side i=.right then
  weight i (decide (c.gates[i].2.1≤rightPart i a y)) else 0
def crossScore (z : Cut c a b) (m : Pattern z) := ∑ i,if h : z.side i=.cross then weight i (m ⟨i,h⟩) else 0

def actual (z : Cut c a b) (x : Fin a → Bool) (y : Fin b → Bool) : Pattern z :=
  fun i => mask c (List.ofFn x++List.ofFn y) i.val

theorem sum_list {n : ℕ} (f : Fin n → ℤ) : (List.ofFn f).sum=∑ i,f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.ofFn_succ,Fin.sum_univ_succ,List.sum_cons,ih]

theorem top_weights (c : ThrCircuit) (m : Mask c) : top c m=decide (c.top≤∑ i,weight i (m i)) := by
  unfold top
  rw [sum_list]
  congr 2
  exact Finset.sum_congr rfl fun i _ => by cases m i <;> simp [weight]

theorem split_score (z : Cut c a b) (x : Fin a → Bool) (y : Fin b → Bool) :
    (∑ i,weight i (mask c (List.ofFn x++List.ofFn y) i))=
      leftScore z x+rightScore z y+crossScore z (actual z x y) := by
  unfold leftScore rightScore crossScore
  rw [← sum_add_distrib,← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  have both : dot c.gates[i].1 (List.ofFn x++List.ofFn y)=leftPart i x+rightPart i a y := by
    simpa only [leftPart,rightPart,List.length_ofFn] using split_dot c.gates[i].1 (List.ofFn x) (List.ofFn y)
  by_cases hl : z.side i=.left
  · have rz : rightPart i a y=0 := z.rightZero i hl y
    rw [rz,add_zero] at both
    have eq := congrArg (fun z : ℤ => decide (c.gates[i].2.1≤z)) both
    change mask c (List.ofFn x++List.ofFn y) i=decide (c.gates[i].2.1≤leftPart i x) at eq
    simp [hl,eq]
  · by_cases hr : z.side i=.right
    · have lz : leftPart i x=0 := z.leftZero i hr x
      rw [lz,zero_add] at both
      have eq := congrArg (fun z : ℤ => decide (c.gates[i].2.1≤z)) both
      change mask c (List.ofFn x++List.ofFn y) i=decide (c.gates[i].2.1≤rightPart i a y) at eq
      simp [hr,eq]
    · have hb : z.side i=.cross := by cases h : z.side i <;> simp_all
      simp [hl,hr,hb,actual]

def pCoord (i : GateId c) (on : Bool) (x : Fin a → Bool) : ℤ :=
  if on then -leftPart i x else leftPart i x
def qCoord (i : GateId c) (on : Bool) (a : ℕ) (y : Fin b → Bool) : ℤ :=
  if on then rightPart i a y-c.gates[i].2.1 else c.gates[i].2.1-1-rightPart i a y

theorem matching (z : Cut c a b) (m : Pattern z) (x : Fin a → Bool) (y : Fin b → Bool) :
    actual z x y=m ↔ ∀ i : Cross z,pCoord i.val (m i) x≤qCoord i.val (m i) a y := by
  rw [funext_iff]
  apply forall_congr'
  intro i
  cases hm : m i <;> simp [actual,mask,split_dot,pCoord,qCoord,leftPart,rightPart,hm] <;> omega

#print axioms split_score
#print axioms matching

end ThresholdCutScores
