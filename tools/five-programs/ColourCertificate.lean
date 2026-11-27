import ThreeColourMatrix
import PEqualNP.Library.Universal.Pair
import Mathlib

namespace ColourCertificate

open PEqualNP.Library.Universal ThreeColourMatrix

def pigment (a b : Bool) : Fin 3 := if a then 0 else if b then 1 else 2
def same (a b c d : Bool) := (a==c) && (a || (b==d))

theorem palette : ∀ a b c d, same a b c d=true ↔ pigment a b=pigment c d := by decide

def tint (a b : List Bool) (i : ℕ) := pigment (a.getD i false) (b.getD i false)

def good (w a b : List Bool) (i j : ℕ) :=
  !(w.getD (i*a.length+j) false) ||
    !(same (a.getD i false) (b.getD i false) (a.getD j false) (b.getD j false))

theorem edge (w a b : List Bool) (i j : ℕ) :
    good w a b i j=true ↔ (w.getD (i*a.length+j) false=true → tint a b i≠tint a b j) := by
  unfold good tint
  cases h : w.getD (i*a.length+j) false <;> simp [← palette]

def check (w witness : List Bool) :=
  let a := (unpairB witness).1
  let b := (unpairB witness).2
  decide (w.length=a.length*a.length) &&
    (List.range a.length).all (fun i => (List.range a.length).all (fun j => good w a b i j))

theorem check_iff (w cert : List Bool) :
    check w cert=true ↔ let a := (unpairB cert).1
                        let b := (unpairB cert).2
                        w.length=a.length*a.length ∧
                        ∀ i j, i<a.length → j<a.length →
                        w.getD (i*a.length+j) false=true → tint a b i≠tint a b j := by
  simp only [check,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,List.mem_range,edge]
  tauto

def channel (n : ℕ) (c : ℕ → Fin 3) (label : Fin 3) : List Bool :=
  List.ofFn (fun i : Fin n => decide (c i=label))

theorem bit (n : ℕ) (c : ℕ → Fin 3) (k : Fin 3) (i : ℕ) (hi : i<n) :
    (channel n c k).getD i false=decide (c i=k) := by
  simp [channel,List.getD_eq_getElem?_getD,hi]

theorem decode (n : ℕ) (c : ℕ → Fin 3) (i : ℕ) (hi : i<n) :
    tint (channel n c 0) (channel n c 1) i=c i := by
  simp only [tint,bit _ _ _ _ hi]
  generalize c i=u
  fin_cases u <;> decide

theorem spec (w : List Bool) : Accepted w ↔
    ∃ cert : List Bool, cert.length≤3*w.length+1 ∧ check w cert=true := by
  constructor
  · rintro ⟨n,len,c,hc⟩
    let a := channel n c 0
    let b := channel n c 1
    have la : a.length=n := by simp [a,channel]
    have lb : b.length=n := by simp [b,channel]
    refine ⟨pairB a b,?_,(check_iff _ _).mpr ?_⟩
    · simp [pairB,un,la,lb,len]
      nlinarith [Nat.le_mul_self n]
    · simp only [unpairB_pairB,la]
      refine ⟨len,fun i j hi hj e => ?_⟩
      simpa only [a,b,decode _ _ i hi,decode _ _ j hj] using hc i j hi hj e
  · rintro ⟨cert,_,valid⟩
    obtain ⟨len,okay⟩ := (check_iff _ _).mp valid
    exact ⟨_,len,tint (unpairB cert).1 (unpairB cert).2,okay⟩

#print axioms spec

end ColourCertificate
