import BucketCount

namespace BucketWitness

open PEqualNP.Search BucketCount

def possible (vs : List ℕ) (F : List Factor) (x : Assignment) : Prop :=
  ∃ y : Assignment, (∀ i, i∉vs → y i=x i) ∧ 0<value F y

theorem choose_bit (v : ℕ) (F : List Factor) (y : Assignment) :
    0<value (eliminate v F) y ↔ ∃ b : Bool,0<value F (put y v b) := by
  rw [project]
  constructor
  · intro hn
    by_cases h : 0<value F (put y v false)
    · exact ⟨false,h⟩
    · exact ⟨true,by omega⟩
  · rintro ⟨(_|_),h⟩ <;> omega

theorem undo (y : Assignment) (v : ℕ) (b : Bool) : put (put y v b) v (y v)=y := by
  funext i
  by_cases h : i=v <;> simp [put,h]

theorem step (v : ℕ) (vs : List ℕ) (F : List Factor) (x : Assignment) :
    possible (v::vs) F x ↔ possible vs (eliminate v F) x := by
  constructor
  · rintro ⟨y,agree,on⟩
    refine ⟨put y v (x v),?_,(choose_bit v F _).mpr ⟨y v,?_⟩⟩
    · intro i out
      by_cases eq : i=v
      · simp [put,eq]
      · simpa [put,eq] using agree i (by simp [eq,out])
    · simpa [undo] using on
  · rintro ⟨z,agree,on⟩
    obtain ⟨b,hit⟩ := (choose_bit v F z).mp on
    refine ⟨put z v b,?_,hit⟩
    intro i out
    have neq : i≠v := fun eq => out (eq ▸ List.mem_cons_self)
    have off : i∉vs := fun hin => out (List.mem_cons_of_mem _ hin)
    simpa [put,neq] using agree i off

theorem support_search (vs : List ℕ) (F : List Factor) (x : Assignment) :
    possible vs F x ↔ 0<value (compile vs F) x := by
  induction vs generalizing F with
  | nil =>
    constructor
    · rintro ⟨y,h,on⟩
      have eq : y=x := funext fun i => h i (by simp)
      exact eq ▸ on
    · intro on
      exact ⟨x,fun _ _ => rfl,on⟩
  | cons v vs ih =>
    exact (step v vs F x).trans (ih (eliminate v F))

def best (v : ℕ) (F : List Factor) (y : Assignment) : Assignment :=
  put y v (decide (value F (put y v false)=0))

theorem best_valid (v : ℕ) (F : List Factor) (y : Assignment) (h : 0<value (eliminate v F) y) :
    0<value F (best v F y) := by
  rw [project] at h
  by_cases z : value F (put y v false)=0 <;> simp [best,z] <;> omega

def recover : List ℕ → List Factor → Assignment → Option Assignment
  | [],F,x => if value F x=0 then none else some x
  | v::vs,F,x => (recover vs (eliminate v F) x).map (best v F)

theorem succeeds (vs : List ℕ) (F : List Factor) (x : Assignment) :
    (recover vs F x).isSome=true ↔ 0<value (compile vs F) x := by
  induction vs generalizing F with
  | nil =>
    by_cases z : value F x=0 <;> simp [recover,compile,z]
    omega
  | cons v vs ih =>
    simpa [recover,compile] using ih (eliminate v F)

theorem sound (vs : List ℕ) (F : List Factor) (x y : Assignment) (h : recover vs F x=some y) :
    0<value F y := by
  induction vs generalizing F y with
  | nil =>
    by_cases z : value F x=0
    · simp [recover,z] at h
    · simp [recover,z] at h
      subst y
      omega
  | cons v vs ih =>
    cases rest : recover vs (eliminate v F) x with
    | none => simp [recover,rest] at h
    | some z =>
      simp [recover,rest] at h
      subst y
      exact best_valid v F z (ih _ _ rest)

theorem full (vs : List ℕ) (F : CNF) (covers : ∀ i∈scope (F.map clauseFactor),i∈vs)
    (x : Assignment) : (recover vs (F.map clauseFactor) x).isSome=true ↔ Satisfiable F := by
  rw [succeeds,← support_search]
  constructor
  · rintro ⟨y,_,good⟩
    rw [from_cnf] at good
    refine ⟨y,?_⟩
    cases h : CNF.eval y F <;> simp_all
  · rintro ⟨y,hy⟩
    let z : Assignment := fun i => if i∈vs then y i else x i
    refine ⟨z,fun i hi => by simp [z,hi],?_⟩
    have eq := local_value (F.map clauseFactor) z y (fun i hi => by simp [z,covers i hi])
    simp [eq,from_cnf,hy]

def order (F : CNF) := (scope (F.map clauseFactor)).sort (·≤·)
def solve (F : CNF) := recover (order F) (F.map clauseFactor) (fun _ => false)

theorem solve_iff (F : CNF) : (solve F).isSome=true ↔ Satisfiable F :=
  full (order F) F (by simp [order]) _

theorem model (F : CNF) (y : Assignment) (h : solve F=some y) : CNF.eval y F=true := by
  have on := sound _ _ _ _ h
  rw [from_cnf] at on
  cases eq : CNF.eval y F <;> simp_all

#print axioms solve_iff
#print axioms model

end BucketWitness
