import ProofWitnessKraft
import IntegerPigeonProof

namespace ProofWitnessIncidence

open ProofDagBudget ProofWitnessScale ProofWitnessKraft
variable {L X I : Type} [DecidableEq L] [DecidableEq I]

theorem secant (m t : ℕ) : ((m+3 : ℕ) : ℚ) ≤ t+(2:ℚ)^(m+2)*(1/2 : ℚ)^t := by
  by_cases h : t ≤ m+2
  · let d := m+2-t
    have eq : m+2=d+t := by dsimp [d]; omega
    have power : (2:ℚ)^(m+2)*(1/2:ℚ)^t=2^d := by
      rw [eq,pow_add,one_div,inv_pow]
      field_simp
    have bound : (d:ℚ)+1≤(2:ℚ)^d := by exact_mod_cast Nat.succ_le_of_lt (Nat.lt_two_pow_self (n:=d))
    have value : (m:ℚ)+2=(d:ℚ)+t := by exact_mod_cast eq
    rw [power]
    push_cast
    linarith
  · have big : ((m+3:ℕ):ℚ)≤t := by exact_mod_cast (show m+3≤t by omega)
    exact le_trans big (le_add_of_nonneg_right (by positivity))

theorem incidence (H : L → X → Prop) (ids : Finset I) (x : I → X) (A : Finset L)
    (light : ∀ l∈A,(failures H ids x l).card≤1) (W : List L) (run : Derives H A W)
    (z : L) (last : z∈W) (bad : ∀ k∈ids,¬H z (x k)) (m : ℕ) :
    (m+3)*ids.card ≤ (∑ k ∈ ids,count (failures H ids x) W k)+2^(m+1) := by
  classical
  let F := failures H ids x
  have k := kraft H ids x A light W run z last bad
  have upper : (2:ℚ)^(m+2)*(∑ k ∈ ids,weight F W k) ≤ (2:ℚ)^(m+1) := by
    calc _ ≤ (2:ℚ)^(m+2)*(1/2) := mul_le_mul_of_nonneg_left k (by positivity)
         _ = _ := by rw [show m+2=m+1+1 by omega,pow_succ]; ring
  have sum : ∑ _k ∈ ids,((m+3:ℕ):ℚ) ≤
      ∑ k ∈ ids,((count F W k:ℚ)+(2:ℚ)^(m+2)*weight F W k) :=
    Finset.sum_le_sum (fun i _ => secant m (count F W i))
  rw [Finset.sum_add_distrib,← Finset.mul_sum] at sum
  simp only [Finset.sum_const,nsmul_eq_mul] at sum
  have desired : ((m+3:ℕ):ℚ)*ids.card ≤ (∑ k ∈ ids,(count F W k : ℚ))+2^(m+1) := by
    nlinarith
  exact_mod_cast desired

theorem critical_incidence (H : L → X → Prop) (A : Finset L) (crit : Critical H A) (W : List L)
    (run : Derives H A W) (z : L) (last : z∈W) (bad : ∀ x,¬H z x) (m : ℕ) :
    (m+3)*A.card ≤ (∑ k : A,count (failures H Finset.univ (witnesses crit)) W k)+2^(m+1) := by
  simpa using incidence H Finset.univ (witnesses crit) A (source_light H A crit) W run z last (fun k _ => bad _) m

theorem parity (l : ℕ) (hl : 0<l) (π : List (PEqualNP.ProofComplexity.LinClause (ParityProofBudget.VBit l)))
    (proof : PEqualNP.ProofComplexity.IsLinRefutation (PEqualNP.ProofComplexity.BPHP (2^l+1) l) π) (m : ℕ) :
    (m+3)*(2^l*(2^l+1).choose 2) ≤
      (∑ k : ParityProofBudget.axioms l,count (failures ParityProofBudget.truth Finset.univ
        (witnesses (ParityProofBudget.critical l))) π k)+2^(m+1) := by
  open PEqualNP.ProofComplexity ParityProofBudget in
    have eq : (↑(axioms l) : Set (LinClause (VBit l)))=linOfClause '' BPHP (2^l+1) l := Set.ext (source_iff l)
    have d := proof.1
    rw [← eq] at d
    have bad : ∀ x,¬truth (∅ : LinClause (VBit l)) x := by simp [truth,LinClauseSat]
    rw [← source_card l hl]
    exact critical_incidence _ _ (critical l) _ (sound_steps _ _ d) _ proof.2 bad m

open PEqualNP.Search PEqualNP.ProofComplexity IntegerPigeonAxioms in
theorem integer (l : ℕ) (hl : 0<l) (π : List (QLine (ParityProofBudget.VBit l)))
    (h : IsResLinQSynRefutation (BPHP (2^l+1) l) π) (m : ℕ) :
    (m+3)*(2^l*(2^l+1).choose 2) ≤
      (∑ k : axioms l,count (failures Holds Finset.univ (witnesses (critical l))) (π.map List.toFinset) k)+2^(m+1) := by
  classical
  have eq : (↑(raw l) : Set (Clause (ParityProofBudget.VBit l)))=BPHP (2^l+1) l := Set.ext (raw_mem _)
  have d := h.1
  rw [← eq] at d
  have last : (∅ : Finset (QEq (ParityProofBudget.VBit l)))∈π.map List.toFinset :=
    List.mem_map.mpr ⟨[],h.2,rfl⟩
  have bad : ∀ x,¬Holds (∅ : Finset (QEq (ParityProofBudget.VBit l))) x := by simp [Holds]
  rw [← card_axioms l hl]
  exact critical_incidence _ _ (critical l) _ (IntegerPigeonProof.run _ _ d) _ last bad m

#print axioms integer
#print axioms incidence
#print axioms parity

end ProofWitnessIncidence
