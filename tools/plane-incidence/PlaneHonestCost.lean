import WireFrontier
import SparsePlanes

/-! Counts computed on each original gate under a singleton-point cofactor.
The radius varies: a charged gate rejects every small enough set of outside
lines, while recognizing more than b distinct lines through this point. -/

namespace PlaneHonestCost

open PartialSums SparseFrontier SparseRows SparsePlanes WireFrontier
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity ReversePath PlaneAnchorBudget

def atPoint {P : ℕ} (L : ℕ) (p : Fin P) : Fin (P+L) → Signal (Fin L) :=
  Fin.append (fun r => if r=p then one else zero) variableAt

def pointW {P : ℕ} (L : ℕ) (p : Fin P) := List.ofFn (atPoint L p)

theorem p_raw {P : ℕ} (L : ℕ) (p : Fin P) (f : Signal (Fin L)) (hf : f∈pointW L p) : IsRaw f := by
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hf
  refine Fin.addCases (fun r => ?_) (fun w => ?_) i
  · by_cases h : r=p <;> simp [atPoint,h,IsRaw]
  · exact Or.inr (Or.inr ⟨w,by simp [atPoint]⟩)

theorem p_eval {P L : ℕ} (C : Circuit) (mc : Monotone2 C) (p : Fin P) (Y : Finset (Fin L)) :
    finalSignal C (pointW L p) Y=circuitFun (P+L) C (PlaneGateBound.row {p} Y) := by
  rw [finalSignal,LineForks.base_output C _ _ (fun g hg => (mc g hg).1) (fun g hg => (mc g hg).2)]
  unfold circuitFun pointW
  rw [List.map_ofFn]
  congr 2
  funext i
  refine Fin.addCases (fun r => ?_) (fun w => ?_) i
  · by_cases h : r=p <;> simp [atPoint,PlaneGateBound.row,h,one,zero]
  · simp [atPoint,PlaneGateBound.row,variableAt]

variable {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)

abbrev Yes := ∀ p w, I p w → circuitFun (N+N) C (fun k => decide (k=Fin.castAdd N p ∨ k=Fin.natAdd N w))=true
abbrev No (q : ℕ) := ∀ z : Fin (N+N) → Bool, (Finset.univ.filter fun w => z (Fin.natAdd N w)=true).card≤q →
      (¬∃ p w, I p w ∧ z (Fin.castAdd N p)=true ∧ z (Fin.natAdd N w)=true) → circuitFun (N+N) C z=false

theorem p_off (mc : Monotone2 C) (neg : No I C q) (p : Fin N) :
    Rejects (pencil I p) q (finalSignal C (pointW N p)) := by
  intro Y apart few
  rw [p_eval C mc]
  apply neg
  · simpa only [PlaneGateBound.row,Fin.append_right,decide_eq_true_eq,Finset.filter_mem_eq_inter,Finset.univ_inter] using few
  · rintro ⟨r,w,rw,pr,wy⟩
    have eq : r=p := by simpa [PlaneGateBound.row] using pr
    subst r
    have sel : w∈Y := by simpa only [PlaneGateBound.row,Fin.append_right,decide_eq_true_eq] using wy
    exact Finset.disjoint_left.mp apart sel (Finset.mem_filter.mpr ⟨Finset.mem_univ _,rw⟩)

theorem point (hq : 0<q) (size : N=q^2+q+1) (lengths : ∀ w, (lineSet I w).card=q+1)
    (unique : ∀ p r, p≠r → ∃! w, I p w ∧ I r w) (mc : Monotone2 C) (pos : Yes I C) (neg : No I C q)
    (p : Fin N) (b radius z : ℕ) (hb : 1≤b) (capacity : b*z≤q) (budget : radius*z≤q) :
    z ≤ WireFrontier.total b radius (pencil I p) C.gates (pointW N p) := by
  let c := WireFrontier.total b radius (pencil I p) C.gates (pointW N p)
  by_contra! small
  have a : c+1≤z := by omega
  have enough := (Nat.mul_le_mul_left radius a).trans budget
  have bound := physical b radius q hb (pencil I p) C (pointW N p) (p_raw N p) (p_off I C mc neg p) enough
  have sub : pencil I p ⊆ single (finalSignal C (pointW N p)) := by
    intro w hw
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rw [p_eval C mc,PlaneGateBound.singleton_row]
    exact pos p w (Finset.mem_filter.mp hw).2
  have higher := (Finset.card_le_card sub).trans (bound.trans ((Nat.mul_le_mul_left b a).trans capacity))
  rw [pencil_size I hq size lengths unique p] at higher
  omega

noncomputable def gateSum {n : ℕ} {P : Type} [Fintype P] [DecidableEq P] (b radius : ℕ)
    (R : Fin n → Finset P) : List Gate → (Fin n → List (Signal P)) → ℕ
  | [],_ => 0
  | g::gs,W => (∑ p, bill b radius (R p) g (W p)) + gateSum b radius R gs (fun p => W p++[baseGate g (W p)])

theorem exchange {n : ℕ} {P : Type} [Fintype P] [DecidableEq P] (b radius : ℕ)
    (R : Fin n → Finset P) (gs : List Gate) (W : Fin n → List (Signal P)) :
    (∑ p,WireFrontier.total b radius (R p) gs (W p))=gateSum b radius R gs W := by
  induction gs generalizing W with
  | nil => simp [WireFrontier.total,gateSum]
  | cons g gs ih => simp [WireFrontier.total,gateSum,Finset.sum_add_distrib,ih]

theorem whole (hq : 0<q) (size : N=q^2+q+1) (lengths : ∀ w, (lineSet I w).card=q+1)
    (unique : ∀ p r, p≠r → ∃! w, I p w ∧ I r w) (mc : Monotone2 C) (pos : Yes I C) (neg : No I C q)
    (b radius z : ℕ) (hb : 1≤b) (capacity : b*z≤q) (budget : radius*z≤q) :
    N*z≤gateSum b radius (pencil I) C.gates (pointW N) := by
  have each := Finset.sum_le_sum (s := Finset.univ) (fun p _ => point I C hq size lengths unique mc pos neg p b radius z hb capacity budget)
  simpa [smul_eq_mul,exchange] using each

theorem harmonic (hq : 0<q) (size : N=q^2+q+1) (lengths : ∀ w, (lineSet I w).card=q+1)
    (unique : ∀ p r, p≠r → ∃! w, I p w ∧ I r w) (mc : Monotone2 C) (pos : Yes I C) (neg : No I C q) :
    N*(∑ b∈Finset.Icc 1 q,q/b)≤∑ b∈Finset.Icc 1 q,gateSum b 1 (pencil I) C.gates (pointW N) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b mem
  apply whole I C hq size lengths unique mc pos neg b 1 (q/b) (Finset.mem_Icc.mp mem).1
  · simpa [Nat.mul_comm] using Nat.div_mul_le_self q b
  · simpa using Nat.div_le_self q b

#print axioms point
#print axioms whole
#print axioms harmonic

end PlaneHonestCost
