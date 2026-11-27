import PlaneGateBound
import AnchoredBoundary

/-! A gate can be pruned on every extension of any singleton anchor that
turns on one of its operands. Gate indices and missing-wire semantics are
preserved. Every original binary gate contributes one footprint. -/

namespace AnchorPruning

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.LowMergeProof AndTranscript OrSensitivity

variable {n : ℕ}

abbrev Probes (n : ℕ) := Fin n → List Bool

def next (W : Probes n) (g : Gate) : Probes n := fun u => emit g (W u)

def seen (W : Probes n) (R : Finset (Fin n)) (i : ℕ) : Bool :=
  decide (∃ u ∈ R, (W u).getD i false=true)

def footprint (W : Probes n) (i j : ℕ) :=
  Finset.univ.filter fun u => (W u).getD i false || (W u).getD j false

def simplify (g : Gate) (W : Probes n) (R : Finset (Fin n)) : Gate :=
  match g.op,g.inputs with
  | .and,[i,j] => if seen W R i then ⟨.or,[j]⟩ else if seen W R j then ⟨.or,[i]⟩ else g
  | .or,[i,j] => if seen W R i || seen W R j then ⟨.and,[]⟩ else g
  | _,_ => g

def reduce : List Gate → Probes n → Finset (Fin n) → List Gate
  | [],_,_ => []
  | g::gs,W,R => simplify g W R :: reduce gs (next W g) R

def Below (W : Probes n) (R : Finset (Fin n)) (x : List Bool) : Prop :=
  ∀ u ∈ R, (W u).length=x.length ∧ LeL (W u) x

theorem seen_on (W : Probes n) (R : Finset (Fin n)) (x : List Bool) (h : Below W R x) (i : ℕ) :
    seen W R i=true → x.getD i false=true := by
  intro a
  obtain ⟨u,hu,on⟩ := of_decide_eq_true a
  exact (h u hu).2 i on

theorem sound_step (g : Gate) (W : Probes n) (R : Finset (Fin n)) (x : List Bool) (h : Below W R x) :
    value (simplify g W R) x=value g x := by
  obtain ⟨op,inputs⟩ := g
  cases inputs with
  | nil => cases op <;> rfl
  | cons i rest =>
    cases rest with
    | nil => cases op <;> rfl
    | cons j rest =>
      cases rest with
      | cons k rest => cases op <;> rfl
      | nil =>
        have si := seen_on W R x h i
        have sj := seen_on W R x h j
        cases op <;> cases hi : seen W R i <;> cases hj : seen W R j <;>
          simp_all [simplify,value,GateOp.eval,List.getD_eq_getElem?_getD]

theorem next_below (W : Probes n) (R : Finset (Fin n)) (x : List Bool) (h : Below W R x)
    (g : Gate) (mono : g.op=.and ∨ g.op=.or) : Below (next W g) R (emit g x) := by
  intro u hu
  obtain ⟨len,le⟩ := h u hu
  exact ⟨by simp [next,emit,len], fold_mono [g] (by simpa using mono) (W u) x len le⟩

theorem wires_eq (gs : List Gate) (W : Probes n) (R : Finset (Fin n)) (x : List Bool)
    (h : Below W R x) (mono : ∀ g ∈ gs, g.op=.and ∨ g.op=.or) :
    wiresFrom (reduce gs W R) x=wiresFrom gs x := by
  induction gs generalizing W x with
  | nil => rfl
  | cons g gs ih =>
    change wiresFrom _ (x++[value (simplify g W R) x])=wiresFrom _ (emit g x)
    rw [sound_step g W R x h]
    exact ih _ _ (next_below W R x h g (mono g (by simp)))
      (fun g hg => mono g (by simp [hg]))

def Legal (g : Gate) := (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2

theorem simplify_legal (g : Gate) (W : Probes n) (R : Finset (Fin n)) (h : Legal g) :
    Legal (simplify g W R) := by
  obtain ⟨op,ins⟩ := g
  rcases h.1 with rfl | rfl <;> cases ins with
  | nil => exact h
  | cons i rest =>
    cases rest with
    | nil => exact h
    | cons j rest =>
      cases rest with
      | cons k rest => exact h
      | nil =>
        cases hi : seen W R i <;> cases hj : seen W R j <;> simp [simplify,hi,hj,Legal]

theorem reduce_legal (gs : List Gate) (W : Probes n) (R : Finset (Fin n)) (h : ∀ g ∈ gs, Legal g) :
    ∀ g ∈ reduce gs W R, Legal g := by
  induction gs generalizing W with
  | nil => simp [reduce]
  | cons a gs ih =>
    intro g hg
    rcases List.mem_cons.mp hg with rfl | tail
    · exact simplify_legal a W R (h a (by simp))
    · exact ih _ (fun g hg => h g (by simp [hg])) g tail

/-- The two flags distinguish binary ANDs and ORs. The list keeps gate
multiplicity even when several gates have exactly the same footprint. -/
def profiles (andSide : Bool) : List Gate → Probes n → List (Finset (Fin n))
  | [],_ => []
  | g::gs,W =>
    let tail := profiles andSide gs (next W g)
    match andSide,g.op,g.inputs with
    | true,.and,[i,j] | false,.or,[i,j] => footprint W i j :: tail
    | _,_,_ => tail

theorem seen_iff (W : Probes n) (R : Finset (Fin n)) (i j : ℕ) :
    Disjoint R (footprint W i j) ↔ seen W R i=false ∧ seen W R j=false := by
  simp only [seen,footprint,decide_eq_false_iff_not,Finset.disjoint_left,Finset.mem_filter,
    Finset.mem_univ,true_and,Bool.or_eq_true]
  grind

def surviving (A : List (Finset (Fin n))) (R : Finset (Fin n)) :=
  (A.filter fun D => decide (Disjoint R D)).length

theorem budgets (gs : List Gate) (W : Probes n) (R : Finset (Fin n)) :
    count (reduce gs W R)=surviving (profiles true gs W) R ∧
    orCount (reduce gs W R)=surviving (profiles false gs W) R := by
  induction gs generalizing W with
  | nil => simp [count,orCount,reduce,profiles,surviving]
  | cons g gs ih =>
    have ⟨a,o⟩ := ih (next W g)
    obtain ⟨op,ins⟩ := g
    cases ins with
    | nil => cases op <;> simp_all [reduce,count,orCount,profiles,simplify,tap,charge,surviving]
    | cons i rest =>
      cases rest with
      | nil => cases op <;> simp_all [reduce,count,orCount,profiles,simplify,tap,charge,surviving]
      | cons j rest =>
        cases rest with
        | cons k rest => cases op <;> simp_all [reduce,count,orCount,profiles,simplify,tap,charge,surviving]
        | nil =>
          cases op <;> cases hi : seen W R i <;> cases hj : seen W R j <;>
            simp_all [reduce,count,orCount,profiles,simplify,tap,charge,surviving,seen_iff,Nat.add_comm]

#print axioms wires_eq
#print axioms budgets

end AnchorPruning
