import CircuitPortBoolean
import WordMachine
import PEqualNP.CircuitLowerBounds.L006

namespace CircuitQueryFamily

open CircuitPortBlock CircuitPortCompose CircuitPortBoolean PEqualNP.CircuitLowerBounds
open PEqualNP.Library PEqualNP.Library.Universal PEqualNP.Library.Machines

def pre (j : ℕ) := un j++false::un j

theorem pre_length (j : ℕ) : (pre j).length=2*j+1 := by simp [pre,un]; omega

theorem pair_eq (j : ℕ) (x : W) : pre j++x=pairB (un j) x := by simp [pre,pairB,un_length,List.append_assoc]

theorem queries (predicate : ℕ → W → Bool) (effective : WordMachine.Effective
    (fun e => predicate (unpairB e).1.length (unpairB e).2)) :
    ∃ p : Polynomial ℕ, ∀ n j, Small n (p.eval (2*j+n+1)) (predicate j) := by
  let test := fun e : W => predicate (unpairB e).1.length (unpairB e).2
  let L : Language Bool := {e | test e=true}
  have uniform : L∈P := ⟨test,fun _ => Iff.rfl,WordMachine.decideBit effective⟩
  obtain ⟨p,budget⟩ := PEqualNP.CircuitLowerBounds.L006 uniform
  refine ⟨p+2*Polynomial.X+1,?_⟩
  intro n j
  let k := 2*j+n+1
  obtain ⟨D,ok,cost,read⟩ := budget k
  obtain ⟨E,good,sz,hard⟩ := prefixed n (pre j) D ok
  have len : (pre j).length+n=k := by rw [pre_length]; dsimp [k]; omega
  refine ⟨E,good,?_,?_⟩
  · rw [len] at sz
    change D.size ≤ p.eval k at cost
    change E.size ≤ (p+2*Polynomial.X+1).eval k
    simp; omega
  · intro x hx
    rw [hard x hx]
    apply Bool.eq_iff_iff.mpr
    have result := read (pre j++x) (by simp only [List.length_append,hx,len])
    change D.eval (pre j++x)=true ↔ predicate j x=true
    rw [pair_eq] at result ⊢
    change D.eval (pairB (un j) x)=true ↔ predicate (unpairB (pairB (un j) x)).1.length (unpairB (pairB (un j) x)).2=true at result
    simpa only [unpairB_pairB,un_length] using result

theorem transduction (f : W → W) (hf : WordMachine.CPT f) :
    ∃ p : Polynomial ℕ, ∀ n j,
      Small n (p.eval (2*j+n+1)) (fun x => (f x).getD j false) ∧
      Small n (p.eval (2*j+n+1)) (fun x => decide ((f x).length=j)) := by
  have machine := cpt_comp cpt_unpairB2 hf
  obtain ⟨p,bit⟩ := queries (fun j x => (f x).getD j false) (WordMachine.query cpt_unpairB1 machine)
  obtain ⟨q,len⟩ := queries (fun j x => decide ((f x).length=j)) (WordMachine.lenEq machine cpt_unpairB1)
  refine ⟨p+q,fun n j => ⟨mono (bit n j) ?_,mono (len n j) ?_⟩⟩ <;> simp

#print axioms transduction

end CircuitQueryFamily
