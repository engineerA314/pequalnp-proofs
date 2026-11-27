import PigeonResolutionBoundary

namespace PigeonExactSupport

open Finset PEqualNP.ProofComplexity PigeonLocalMatching PigeonResolutionBoundary

theorem complete_formula (m n : ℕ) : axioms (fun _ : Fin m => (Finset.univ : Finset (Fin n)))=PHP m n := by
  ext C
  rfl

theorem exact_support (m n : ℕ) (hn : 0<n) {π : List (Line (Fin m) (Fin n))} (proof : IsRefutation (PHP m n) π) :
    ∃ R∈π, ∃ p : Fin m, p∉support R ∧ (support R).card=n ∧
      ∃ f : Fin m → Fin n,Set.InjOn f (support R) ∧ (support R).image f=univ ∧ ¬ClauseSat (assign f) R := by
  classical
  let E := fun _ : Fin m => (Finset.univ : Finset (Fin n))
  have : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  obtain ⟨C,_,D,_,R,hr,p,_,_,_,_,_,_,outside,invalid,blocked'⟩ :=
    extraction E (fun _ => Finset.univ_nonempty) ((complete_formula m n).symm ▸ proof)
  have missed : ∃ f,good E (support R) f ∧ ¬ClauseSat (assign f) R := by
    by_contra absent
    apply invalid
    intro f hf
    by_contra bad
    exact absent ⟨f,hf,bad⟩
  obtain ⟨f,hf,bad⟩ := missed
  have full : (support R).image f=univ := Finset.univ_subset_iff.mp (blocked' f hf bad)
  have count := Finset.card_image_of_injOn hf.1
  rw [full,Finset.card_univ,Fintype.card_fin] at count
  exact ⟨R,hr,p,outside,count.symm,f,hf.1,full,bad⟩

#print axioms exact_support

end PigeonExactSupport
