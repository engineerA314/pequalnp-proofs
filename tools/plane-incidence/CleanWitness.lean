import SingleLevelStars
import AndTranscript

/-! Minimum number of variable occurrences in an accepting parse, truncated
above two. An OR chooses a parse, an AND concatenates two parses, and true
has a zero-leaf parse. Both reading positions of a reused wire count. -/

namespace CleanWitness

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.Helpers

inductive Weight | zero | one | two | many deriving Repr, DecidableEq

namespace Weight
def best : Weight → Weight → Weight
  | .zero,_ | _,.zero => .zero
  | .one,_ | _,.one => .one
  | .two,_ | _,.two => .two
  | .many,.many => .many
def add : Weight → Weight → Weight
  | .zero,b => b
  | a,.zero => a
  | .one,.one => .two
  | _,_ => .many
end Weight

variable {V : Type} [DecidableEq V]

abbrev Term (V : Type) := Finset V × Finset V

inductive Summary (V : Type) where
  | unit
  | data (atoms : Finset V) (terms : Finset (Term V))
deriving DecidableEq

namespace Summary
def bottom : Summary V := .data ∅ ∅
def atom (v : V) : Summary V := .data {v} ∅

def plus : Summary V → Summary V → Summary V
  | .unit,_ | _,.unit => .unit
  | .data A R,.data B T => .data (A∪B) (R∪T)
def times : Summary V → Summary V → Summary V
  | .unit,b => b
  | a,.unit => a
  | .data A _,.data B _ => .data ∅ {(A,B)}

def atoms : Summary V → Finset V
  | .unit => ∅
  | .data A _ => A
def terms : Summary V → Finset (Term V)
  | .unit => ∅
  | .data _ R => R
end Summary

def hits (A X : Finset V) : Bool := decide ((A ∩ X).Nonempty)
def fires (R : Finset (Term V)) (X : Finset V) : Bool :=
  decide (∃ t ∈ R, hits t.1 X = true ∧ hits t.2 X = true)

def weight (s : Summary V) (X : Finset V) : Weight := match s with
  | .unit => .zero
  | .data A R => if hits A X then .one else if fires R X then .two else .many

@[simp] theorem hits_empty (X : Finset V) : hits ∅ X = false := by simp [hits]
@[simp] theorem fires_empty (X : Finset V) : fires ∅ X = false := by simp [fires]
@[simp] theorem hits_union (A B X : Finset V) : hits (A∪B) X = (hits A X || hits B X) := by
  apply Bool.eq_iff_iff.mpr
  simp [hits,Finset.union_inter_distrib_right,Finset.union_nonempty]
@[simp] theorem fires_union (R T : Finset (Term V)) (X : Finset V) :
    fires (R∪T) X = (fires R X || fires T X) := by
  apply Bool.eq_iff_iff.mpr
  simp only [fires,decide_eq_true_eq,Bool.or_eq_true,Finset.mem_union]
  aesop
@[simp] theorem fires_singleton (A B X : Finset V) : fires {(A,B)} X = (hits A X && hits B X) := by
  apply Bool.eq_iff_iff.mpr
  simp [fires]

theorem plus_weight (a b : Summary V) (X : Finset V) :
    weight (a.plus b) X = (weight a X).best (weight b X) := by
  cases a with
  | unit => simp [weight,Summary.plus,Weight.best]
  | data A R =>
    cases b with
    | unit => cases hs : weight (.data A R) X <;> simp_all [Summary.plus,weight,Weight.best]
    | data B T =>
      cases hA : hits A X <;> cases hB : hits B X <;> cases hR : fires R X <;> cases hT : fires T X <;>
        simp [weight,Summary.plus,hA,hB,hR,hT,Weight.best]

theorem times_weight (a b : Summary V) (X : Finset V) :
    weight (a.times b) X = (weight a X).add (weight b X) := by
  cases a with
  | unit => simp [weight,Summary.times,Weight.add]
  | data A R =>
    cases b with
    | unit => cases hA : hits A X <;> cases hR : fires R X <;> simp [Summary.times,weight,hA,hR,Weight.add]
    | data B T =>
      cases hA : hits A X <;> cases hB : hits B X <;> cases hR : fires R X <;> cases hT : fires T X <;>
        simp [weight,Summary.times,hA,hB,hR,hT,Weight.add]

/-- The same gate dispatcher is used for the symbolic summary and numerical
weight. The last case supplies a fallback outside the promised basis. -/
def gate {α : Type} (zero one : α) (plus times : α → α → α) (g : Gate) (S : List α) : α :=
  match g.op,g.inputs with
  | .and,[] => one
  | .and,[i] | .or,[i] => S.getD i zero
  | .and,[i,j] => times (S.getD i zero) (S.getD j zero)
  | .or,[i,j] => plus (S.getD i zero) (S.getD j zero)
  | _,_ => zero

def scan {α : Type} (zero one : α) (plus times : α → α → α) : List Gate → List α → List α
  | [],S => S
  | g::gs,S => scan zero one plus times gs (S++[gate zero one plus times g S])

theorem getD_map {α β : Type} (f : α → β) (S : List α) (i : ℕ) (z : α) :
    (S.map f).getD i (f z) = f (S.getD i z) := by
  simp [List.getD_eq_getElem?_getD,Option.getD_map]

theorem gate_map {α β : Type} (f : α → β) (z o : α) (p m : α → α → α) (p' m' : β → β → β)
    (hp : ∀ a b, f (p a b)=p' (f a) (f b)) (hm : ∀ a b, f (m a b)=m' (f a) (f b))
    (g : Gate) (S : List α) :
    f (gate z o p m g S) = gate (f z) (f o) p' m' g (S.map f) := by
  obtain ⟨op,ins⟩ := g
  cases op <;> cases ins with
  | nil => rfl
  | cons i tail =>
    cases tail with
    | nil => simp [gate]
    | cons j tail => cases tail <;> simp [gate,hp,hm]

theorem scan_map {α β : Type} (f : α → β) (z o : α) (p m : α → α → α) (p' m' : β → β → β)
    (hp : ∀ a b, f (p a b)=p' (f a) (f b)) (hm : ∀ a b, f (m a b)=m' (f a) (f b))
    (gs : List Gate) (S : List α) :
    (scan z o p m gs S).map f = scan (f z) (f o) p' m' gs (S.map f) := by
  induction gs generalizing S with
  | nil => rfl
  | cons g gs ih =>
    simp only [scan,ih,List.map_append,List.map_cons,List.map_nil,gate_map f z o p m p' m' hp hm]

def summarize (C : Circuit) (inputs : List V) : Summary V :=
  (scan Summary.bottom .unit Summary.plus Summary.times C.gates (inputs.map Summary.atom)).getD C.output Summary.bottom

def minimum (C : Circuit) (inputs : List V) (X : Finset V) : Weight :=
  (scan .many .zero Weight.best Weight.add C.gates (inputs.map fun v => if v ∈ X then .one else .many)).getD C.output .many

theorem weight_eq_minimum (C : Circuit) (inputs : List V) (X : Finset V) : weight (summarize C inputs) X = minimum C inputs X := by
  let f (s : Summary V) := weight s X
  have bottom : f .bottom = .many := by simp [f,weight,Summary.bottom]
  have unit : f .unit = .zero := rfl
  have atom (v : V) : f (.atom v) = (if v ∈ X then .one else .many) := by
    by_cases hv : v ∈ X <;> simp [f,weight,Summary.atom,hits,hv]
  change f ((scan Summary.bottom .unit Summary.plus Summary.times C.gates (inputs.map Summary.atom)).getD C.output Summary.bottom) = _
  rw [← getD_map f]
  rw [scan_map f Summary.bottom .unit Summary.plus Summary.times Weight.best Weight.add
    (fun a b => plus_weight a b X) (fun a b => times_weight a b X)]
  simp only [bottom,unit,List.map_map,Function.comp_def,atom,minimum]

theorem gate_sound (g : Gate) (mono : g.op = .and ∨ g.op = .or) (fan : g.inputs.length ≤ 2)
    (W : List Weight) (x : List Bool) (old : ∀ j, W.getD j .many ≠ .many → x.getD j false = true) :
    gate .many .zero Weight.best Weight.add g W ≠ .many → AndTranscript.value g x = true := by
  obtain ⟨op,ins⟩ := g
  rcases mono with rfl | rfl <;> cases ins with
  | nil => simp [gate,AndTranscript.value,GateOp.eval]
  | cons i tail =>
    cases tail with
    | nil => simpa [gate,AndTranscript.value,GateOp.eval] using old i
    | cons j tail =>
      cases tail with
      | cons _ _ => simp at fan
      | nil =>
        cases h : W.getD i .many <;> cases k : W.getD j .many <;>
          simp_all [gate,Weight.add,Weight.best,AndTranscript.value,GateOp.eval]

theorem minimum_sound (C : Circuit) (inputs : List V) (X : Finset V)
    (mono : IsMonotoneCircuit C) (fan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (cheap : minimum C inputs X ≠ .many) : C.eval (inputs.map fun v => decide (v ∈ X)) = true := by
  have go (gs : List Gate) (W : List Weight) (x : List Bool) (length : W.length=x.length)
      (old : ∀ j, W.getD j .many ≠ .many → x.getD j false = true)
      (ops : ∀ g ∈ gs, g.op=.and ∨ g.op=.or) (fanin : ∀ g ∈ gs, g.inputs.length≤2) :
      ∀ j, (scan .many .zero Weight.best Weight.add gs W).getD j .many ≠ .many → (wiresFrom gs x).getD j false=true := by
    induction gs generalizing W x with
    | nil => exact old
    | cons g gs ih =>
      apply ih _ _ (by simp [length])
      · intro j
        by_cases last : j=W.length
        · subst j
          rw [getD_snoc_eq,length,getD_snoc_eq]
          exact gate_sound g (ops g (by simp)) (fanin g (by simp)) W x old
        · rw [getD_snoc_ne _ _ _ _ last,getD_snoc_ne _ _ _ _ (by omega)]
          exact old j
      · exact fun g hg => ops g (by simp [hg])
      · exact fun g hg => fanin g (by simp [hg])
  apply go C.gates _ _ (by simp) _ mono fan C.output cheap
  intro j
  by_cases hi : j < inputs.length
  · simp [List.getD_eq_getElem?_getD,hi]
  · simp [List.getD_eq_getElem?_getD,hi]

#print axioms weight_eq_minimum
#print axioms minimum_sound

end CleanWitness
