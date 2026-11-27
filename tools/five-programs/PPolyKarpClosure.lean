import CircuitQueryFamily
import GraphMatrixComplete

namespace PPolyKarpClosure

open CircuitPortBlock CircuitPortCompose CircuitPortBoolean CircuitQueryFamily
open PEqualNP.CircuitLowerBounds PEqualNP.Library PEqualNP.Library.Machines

def padded (v : W) (m : ℕ) := List.ofFn (fun i : Fin m => v.getD i.val false)

theorem padded_exact (v : W) : padded v v.length=v := by
  apply List.ext_getElem
  · simp [padded]
  · intro i _ hi
    simp only [padded,List.getElem_ofFn,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some]

theorem closure (A B : Language Bool) (reduction : PolyTimeReducible A B) (nonuniform : B∈PPoly) : A∈PPoly := by
  classical
  obtain ⟨f,hf,tr⟩ := reduction
  obtain ⟨q,length⟩ := output_length_poly f hf
  obtain ⟨p,feed⟩ := transduction f hf
  obtain ⟨r,family⟩ := nonuniform
  choose D gate sz dec using family
  let u := p.comp (2*q+Polynomial.X+1)
  let v := r.comp q
  let one := u+(q*(u+1)+v+1)+4
  refine ⟨1+(q+1)*(one+4),?_⟩
  intro n
  let limit := q.eval n
  let b := u.eval n
  have valU : b=p.eval (2*limit+n+1) := by simp [b,u,limit]
  have inputCost (j : ℕ) (hj : j ≤ limit) : p.eval (2*j+n+1) ≤ b := by
    rw [valU]
    exact eval_mono p (by omega)
  have downstream (j : ℕ) (hj : j ≤ limit) : (D j).size ≤ v.eval n := by
    change (D j).size ≤ (r.comp q).eval n
    rw [Polynomial.eval_comp]
    exact (sz j).trans (eval_mono r hj)
  let term := fun j x => decide ((f x).length=j) && (D j).eval (padded (f x) j)
  have candidate (j : ℕ) (hj : j ≤ limit) : Small n (one.eval n) (term j) := by
    have test := mono (feed n j).2 (inputCost j hj)
    have outputs (i : Fin j) : Small n b (fun x => (f x).getD i.val false) :=
      mono (feed n i.val).1 (inputCost _ (i.isLt.le.trans hj))
    have attach := many n j (fun _ => b) _ outputs (D j) (gate j)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at attach
    have joined := conjunction test attach
    apply mono joined
    have lim := Nat.mul_le_mul_right (b+1) hj
    have d := downstream j hj
    change b+(j*(b+1)+(D j).size+1)+4 ≤ (u+(q*(u+1)+v+1)+4).eval n
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_one,Polynomial.eval_ofNat]
    change b+(j*(b+1)+(D j).size+1)+4 ≤ b+(limit*(b+1)+v.eval n+1)+4
    omega
  obtain ⟨C,leg,cap,reads⟩ := any_list n (one.eval n) (List.range (limit+1)) term
    (fun i hi => candidate i (Nat.le_of_lt_succ (List.mem_range.mp hi)))
  refine ⟨C,leg,?_,?_⟩
  · simpa [limit] using cap
  · intro x hx
    rw [reads x hx]
    change (List.range (limit+1)).any (fun i => term i x)=true ↔ x∈A
    rw [List.any_eq_true,tr x]
    have available : (f x).length ≤ limit := by simpa [limit,hx] using length x
    constructor
    · rintro ⟨j,_,h⟩
      obtain ⟨eq,hits⟩ := Bool.and_eq_true_iff.mp h
      have same : (f x).length=j := of_decide_eq_true eq
      subst j
      rw [padded_exact] at hits
      exact (dec _ (f x) rfl).mp hits
    · intro yes
      refine ⟨(f x).length,List.mem_range.mpr (Nat.lt_succ_of_le available),?_⟩
      simp only [term,decide_true,Bool.true_and,padded_exact]
      exact (dec _ (f x) rfl).mpr yes

theorem graph_consequence :
    ({w : W | ThreeColourMatrix.Accepted w} : Language Bool)∈PPoly → NP⊆PPoly := by
  intro graphs L member
  exact closure _ _ (GraphMatrixComplete.complete.2 L member) graphs

#print axioms closure
#print axioms graph_consequence

end PPolyKarpClosure
