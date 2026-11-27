import PEqualNP.Defs.Search
import Mathlib

/-! Sum-product elimination for the project's CNF semantics. A factor has
a finite scope and a proof that its numerical value depends only on that scope. -/
namespace BucketCount

open PEqualNP.Search

structure Factor where
  vars : Finset ℕ
  read : Assignment → ℕ
  locality : ∀ x y, (∀ i∈vars, x i=y i) → read x=read y

def scope : List Factor → Finset ℕ
  | [] => ∅
  | f::F => f.vars∪scope F

def value : List Factor → Assignment → ℕ
  | [],_ => 1
  | f::F,x => f.read x * value F x

theorem local_value (F : List Factor) (x y : Assignment) (same : ∀ i∈scope F,x i=y i) :
    value F x=value F y := by
  induction F with
  | nil => rfl
  | cons f F ih =>
    exact congrArg₂ (·*·) (f.locality x y (fun i hi => same i (Finset.mem_union_left _ hi)))
      (ih (fun i hi => same i (Finset.mem_union_right _ hi)))

def clauseVars (c : Clause) : Finset ℕ := (c.map Prod.fst).toFinset

def clauseFactor (c : Clause) : Factor where
  vars := clauseVars c
  read := fun x => (c.eval x).toNat
  locality := by
    intro x y same
    apply congrArg Bool.toNat
    apply Bool.eq_iff_iff.mpr
    simp only [Clause.eval,List.any_eq_true,Literal.eval,beq_iff_eq]
    constructor <;> rintro ⟨l,hl,ok⟩ <;> refine ⟨l,hl,?_⟩
    · rw [← same l.1 (List.mem_toFinset.mpr (List.mem_map_of_mem hl))]
      exact ok
    · rw [same l.1 (List.mem_toFinset.mpr (List.mem_map_of_mem hl))]
      exact ok

theorem from_cnf (F : CNF) (x : Assignment) : value (F.map clauseFactor) x=(CNF.eval x F).toNat := by
  induction F with
  | nil => rfl
  | cons c F ih =>
    change (c.eval x).toNat*value (F.map clauseFactor) x=((c.eval x)&&(CNF.eval x F)).toNat
    rw [ih]
    cases c.eval x <;> cases CNF.eval x F <;> rfl

def active (v : ℕ) (F : List Factor) := F.filter fun f => decide (v∈f.vars)
def other (v : ℕ) (F : List Factor) := F.filter fun f => decide (v∉f.vars)

theorem split (v : ℕ) (F : List Factor) (x : Assignment) :
    value F x=value (active v F) x*value (other v F) x := by
  induction F with
  | nil => simp [active,other,value]
  | cons f F ih =>
    by_cases hv : v∈f.vars <;> simp [active,other,hv,value] at ih ⊢ <;> rw [ih] <;> ring

theorem outside (v : ℕ) (F : List Factor) : v∉scope (other v F) := by
  induction F with
  | nil => simp [other,scope]
  | cons f F ih =>
    by_cases h : v∈f.vars <;> simpa [other,h,scope] using ih

def put (x : Assignment) (v : ℕ) (b : Bool) : Assignment := Function.update x v b

theorem put_other (v : ℕ) (F : List Factor) (x : Assignment) (b : Bool) :
    value (other v F) (put x v b)=value (other v F) x := by
  apply local_value
  intro i hi
  have ne : i≠v := fun eq => outside v F (eq ▸ hi)
  simp [put,ne]

def sumOut (v : ℕ) (F : List Factor) : Factor where
  vars := (scope F).erase v
  read := fun x => value F (put x v false)+value F (put x v true)
  locality := by
    intro x y agree
    have hit (b : Bool) : value F (put x v b)=value F (put y v b) := by
      apply local_value
      intro i hi
      by_cases eq : i=v
      · simp [put,eq]
      · simpa [put,eq] using agree i (Finset.mem_erase.mpr ⟨eq,hi⟩)
    rw [hit false,hit true]

def eliminate (v : ℕ) (F : List Factor) := sumOut v (active v F)::other v F

theorem project (v : ℕ) (F : List Factor) (x : Assignment) :
    value (eliminate v F) x=value F (put x v false)+value F (put x v true) := by
  change (_+_)*value (other v F) x=_
  rw [add_mul,split v F (put x v false),split v F (put x v true),put_other,put_other]

def marginal : List ℕ → (Assignment → ℕ) → Assignment → ℕ
  | [],f => f
  | v::vs,f => marginal vs (fun x => f (put x v false)+f (put x v true))

def compile : List ℕ → List Factor → List Factor
  | [],F => F
  | v::vs,F => compile vs (eliminate v F)

theorem exact_count (vs : List ℕ) (F : List Factor) (x : Assignment) :
    value (compile vs F) x=marginal vs (value F) x := by
  induction vs generalizing F with
  | nil => rfl
  | cons v vs ih =>
    change value (compile vs (eliminate v F)) x=_
    rw [ih]
    exact congrArg (fun f => marginal vs f x) (funext (project v F))

#print axioms from_cnf
#print axioms exact_count

end BucketCount
