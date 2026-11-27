import ParityMatchingWidth
import IntegerPigeonProof

namespace IntegerMatchingWidth

open Finset PEqualNP.Search PEqualNP.ProofComplexity PEqualNP.ProofComplexity.Helpers
open IntegerPigeonAxioms IntegerPigeonProof
open ParityMatchingWidth (Hole readBits bax_holds)
open MatchingExtension ProofMatchingBottleneck ProofDagBudget
open ParityProofBudget (VBit)

noncomputable def vars {m l : ℕ} (e : QEq (Fin m × Fin l)) := Finset.univ.filter (fun v => e.1 v≠0)
noncomputable def scope {m l : ℕ} (C : Finset (QEq (Fin m × Fin l))) :=
  C.biUnion fun e => (vars e).image Prod.fst

theorem present {m l : ℕ} {C : Finset (QEq (Fin m × Fin l))} {e} (he : e∈C)
    {v : Fin m × Fin l} (h : e.1 v≠0) : v.1∈scope C :=
  Finset.mem_biUnion.mpr ⟨e,he,Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)⟩

theorem depends (m l : ℕ) : localEval (@scope m l) (fun C f => Holds C (readBits f)) := by
  intro C f g eq yes
  obtain ⟨e,he,ok⟩ := yes
  refine ⟨e,he,?_⟩
  unfold QEq.Holds at ok ⊢
  rw [←ok]
  apply Finset.sum_congr rfl
  intro v _
  by_cases zero : e.1 v=0
  · simp [zero]
  · exact congrArg (fun b : Bool => e.1 v*(if b then (1 : ℤ) else 0))
      (congrFun (eq v.1 (present he zero)).symm v.2)

theorem in_encoded {m l : ℕ} {C : Clause (Fin m × Fin l)} {v : Literal (Fin m × Fin l)}
    (h : v∈C) : v.1.1∈scope (encode C) := by
  have inside : litQEq v∈encode C := Finset.mem_image_of_mem _ h
  exact present (v := v.1) inside (by simp [litQEq])

theorem local_source (l : ℕ) (hl : 0<l) (D : Finset (QEq (VBit l))) (src : D∈axioms l) :
    localValid scope (fun C f => Holds C (readBits f)) D := by
  classical
  obtain ⟨C,hC,rfl⟩ := Finset.mem_image.mp src
  obtain ⟨i,j,α,ne,rfl⟩ := (raw_mem _ _).mp hC
  intro f inj
  let b : Fin l := ⟨0,hl⟩
  have iocc : ((i,b),!α b)∈bax i j α := Finset.mem_union_left _ (Finset.mem_image_of_mem _ (mem_univ b))
  have jocc : ((j,b),!α b)∈bax i j α := Finset.mem_union_right _ (Finset.mem_image_of_mem _ (mem_univ b))
  exact encoded_true _ _ (bax_holds i j α f (fun h => ne (inj (in_encoded iocc) (in_encoded jocc) h)))

theorem certificate (l : ℕ) (hl : 0<l) (π : List (QLine (VBit l))) (refutes : IsResLinQSynRefutation (BPHP (2^l+1) l) π) :
    event scope (fun C f => Holds C (readBits f)) (π.map List.toFinset) := by
  classical
  have eq : (↑(raw l) : Set (Clause (VBit l)))=BPHP (2^l+1) l := Set.ext (raw_mem _)
  have d := refutes.1
  rw [←eq] at d
  have proof := lift_derivation Holds readBits _ _ (run _ _ d)
  rcases first scope _ (depends _ _) _ (local_source l hl) proof with all|found
  · let f : Fin (2^l+1) → Hole l := fun _ _ => false
    have endIn : (∅ : Finset (QEq (VBit l)))∈π.map List.toFinset := List.mem_map.mpr ⟨[],refutes.2,rfl⟩
    have z := all ∅ endIn f (by simp [scope])
    simpa [Holds] using z
  · exact found

theorem bound (l : ℕ) (hl : 0<l) (π : List (QLine (VBit l))) (refutes : IsResLinQSynRefutation (BPHP (2^l+1) l) π) :
    ∃ C∈π,2^l < 2*(scope C.toFinset).card := by
  obtain ⟨D,hd,big⟩ := wide _ _ (certificate l hl π refutes)
  obtain ⟨C,hc,rfl⟩ := List.mem_map.mp hd
  exact ⟨C,hc,by simpa [Hole] using big⟩

#print axioms certificate
#print axioms bound

end IntegerMatchingWidth
