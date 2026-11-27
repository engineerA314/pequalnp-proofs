import ProofTwoThirds
import IntegerMatchingWidth

namespace BitMatchingBound

open Finset MatchingExtension ProofTwoThirds PEqualNP.ProofComplexity PEqualNP.Search
open ParityProofBudget (VBit)
open ParityMatchingWidth (Hole readBits)

theorem parity (l : ℕ) (hl : 0<l) (W : List (LinClause (VBit l))) (refutes : IsLinRefutation (BPHP (2^l+1) l) W) :
    ∃ C∈W,2*(2^l+1)≤3*(ParityMatchingWidth.scope C).card := by
  classical
  have eq : (↑(ParityProofBudget.axioms l) : Set (LinClause (VBit l)))=linOfClause '' BPHP (2^l+1) l :=
    Set.ext (ParityProofBudget.source_iff l)
  have d := refutes.1
  rw [←eq] at d
  have proof := lift_derivation ParityProofBudget.truth readBits _ _ (ParityProofBudget.sound_steps _ _ d)
  let f : Fin (2^l+1) → Hole l := fun _ _ => false
  have bad : ¬localValid ParityMatchingWidth.scope (fun C g => LinClauseSat (readBits g) C) (∅ : LinClause (VBit l)) := by
    intro valid
    have z := valid f (by simp [ParityMatchingWidth.scope])
    simp [LinClauseSat] at z
  simpa [Hole] using forced _ _ (ParityMatchingWidth.depends _ _) _ (ParityMatchingWidth.local_source l hl) proof refutes.2 bad

theorem integer (l : ℕ) (hl : 0<l) (W : List (QLine (VBit l))) (refutes : IsResLinQSynRefutation (BPHP (2^l+1) l) W) :
    ∃ C∈W,2*(2^l+1)≤3*(IntegerMatchingWidth.scope C.toFinset).card := by
  classical
  have eq : (↑(IntegerPigeonAxioms.raw l) : Set (Clause (VBit l)))=BPHP (2^l+1) l := Set.ext (IntegerPigeonAxioms.raw_mem _)
  have d := refutes.1
  rw [←eq] at d
  have proof := lift_derivation IntegerPigeonAxioms.Holds readBits _ _ (IntegerPigeonProof.run _ _ d)
  have endIn : (∅ : Finset (QEq (VBit l)))∈W.map List.toFinset := List.mem_map.mpr ⟨[],refutes.2,rfl⟩
  let f : Fin (2^l+1) → Hole l := fun _ _ => false
  have bad : ¬localValid IntegerMatchingWidth.scope (fun C g => IntegerPigeonAxioms.Holds C (readBits g))
      (∅ : Finset (QEq (VBit l))) := by
    intro valid
    have z := valid f (by simp [IntegerMatchingWidth.scope])
    simp [IntegerPigeonAxioms.Holds] at z
  obtain ⟨C,mem,large⟩ := forced _ _ (IntegerMatchingWidth.depends _ _) _ (IntegerMatchingWidth.local_source l hl) proof endIn bad
  obtain ⟨D,hd,rfl⟩ := List.mem_map.mp mem
  exact ⟨D,hd,by simpa [Hole] using large⟩

#print axioms parity
#print axioms integer

end BitMatchingBound
