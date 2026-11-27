import BucketWitness
import CNFReader

namespace BucketBits

open BucketCount BucketWitness PEqualNP.Search

def assignment : (vs : List ℕ) → Assignment → (Fin vs.length → Bool) → Assignment
  | [],x,_ => x
  | v::vs,x,bits => put (assignment vs x (Fin.tail bits)) v (bits 0)

theorem sum_bits (vs : List ℕ) (f : Assignment → ℕ) (x : Assignment) :
    marginal vs f x=∑ bits : Fin vs.length → Bool, f (assignment vs x bits) := by
  classical
  induction vs generalizing f with
  | nil => simp [marginal,assignment]
  | cons v vs ih =>
    change marginal vs (fun y => f (put y v false)+f (put y v true)) x=_
    rw [ih,Finset.sum_add_distrib]
    let e := Fin.consEquiv (fun _ : Fin (vs.length+1) => Bool)
    calc
      _ = ∑ p : Bool × (Fin vs.length → Bool), f (assignment (v::vs) x (e p)) := by
        rw [Fintype.sum_prod_type]
        simp [e,assignment,add_comm]
      _ = _ := e.sum_comp (fun bits => f (assignment (v::vs) x bits))

theorem agrees (vs : List ℕ) (x : Assignment) (bits : Fin vs.length → Bool)
    (i : Fin vs.length) (distinct : vs.Nodup) : assignment vs x bits vs[i]=bits i := by
  induction vs with
  | nil => exact i.elim0
  | cons v vs ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · change Function.update (assignment vs x (Fin.tail bits)) v (bits 0) v=bits 0
      exact Function.update_self ..
    · have neq : vs[j]≠v := fun eq => (List.nodup_cons.mp distinct).1 (eq ▸ List.getElem_mem _)
      change Function.update (assignment vs x (Fin.tail bits)) v (bits 0) vs[j]=Fin.tail bits j
      rw [Function.update_of_ne neq]
      exact ih (Fin.tail bits) j (List.nodup_cons.mp distinct).2

theorem count_cnf (F : CNF) :
    value (compile (order F) (F.map clauseFactor)) (fun _ => false)=
      ((Finset.univ : Finset (Fin (order F).length → Bool)).filter
        (fun bits => CNF.eval (assignment (order F) (fun _ => false) bits) F=true)).card := by
  rw [exact_count,sum_bits]
  simp_rw [from_cnf]
  classical
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro b _
  cases CNF.eval (assignment (order F) (fun _ => false) b) F <;> rfl

def onWord (w : List Bool) : Option Assignment := (CNFReader.parse w).bind solve

theorem accepts (w : List Bool) : (onWord w).isSome=true ↔ w∈SAT := by
  cases parse : CNFReader.parse w with
  | none =>
    simp only [onWord,parse,Option.bind_none,Option.isSome_none,Bool.false_eq_true,false_iff]
    rintro ⟨F,eq,_⟩
    exact (CNFReader.rejects _).mp parse F eq
  | some F =>
    simp only [onWord,parse,Option.bind_some,solve_iff]
    constructor
    · intro sat
      exact ⟨F,(CNFReader.parse_iff _ _).mp parse,sat⟩
    · rintro ⟨G,eq,sat⟩
      have same := (CNFReader.parse_iff _ _).mpr eq
      rw [parse] at same
      exact (Option.some.inj same).symm ▸ sat

#print axioms count_cnf
#print axioms accepts

end BucketBits
