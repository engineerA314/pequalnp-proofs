import ProofDagBudget
import PEqualNP.ProofComplexity.Helpers.SizeBound

namespace ParityProofBudget

open PEqualNP.ProofComplexity PEqualNP.ProofComplexity.Helpers ProofDagBudget

variable {V : Type} [DecidableEq V]

def truth (C : LinClause V) (x : V → Bool) := LinClauseSat x C

theorem sound_steps (A : Finset (LinClause V)) (W : List (LinClause V)) (legal : IsLinDerivation (↑A) W) :
    Derives truth A W := by
  induction legal with
  | nil => exact .nil
  | ax _ src ih => exact .step ih _ (Or.inl src)
  | @res π C D R _ hc hd rule ih =>
    refine .step ih R (Or.inr ⟨{C,D},Finset.card_le_two,?_,?_⟩)
    · intro f hf
      rcases Finset.mem_insert.mp hf with rfl | h
      · exact hc
      · exact Finset.mem_singleton.mp h ▸ hd
    · intro x hx t ht
      rw [Finset.mem_singleton.mp ht]
      exact lin_resolvent_sound x rule (hx _ (by simp)) (hx _ (by simp))
  | @weak π C D _ hc rule ih =>
    refine .step ih D (Or.inr ⟨{C},by simp,by simpa,?_⟩)
    intro x hx t ht
    rw [Finset.mem_singleton.mp ht]
    exact rule x (hx _ (by simp))

abbrev VBit (l : ℕ) := Fin (2^l+1) × Fin l
def indices (l : ℕ) :=
  (Finset.univ : Finset (Fin (2^l+1))).powersetCard 2 ×ˢ (Finset.univ : Finset (Fin l → Bool))
def axioms (l : ℕ) : Finset (LinClause (VBit l)) := (indices l).image setClause

theorem source_iff (l : ℕ) (C : LinClause (VBit l)) :
    C∈axioms l ↔ C∈linOfClause '' BPHP (2^l+1) l := by
  classical
  constructor
  · intro h
    obtain ⟨⟨S,α⟩,hs,rfl⟩ := Finset.mem_image.mp h
    have two : S.card=2 := (Finset.mem_powersetCard.mp (Finset.mem_product.mp hs).1).2
    obtain ⟨i,j,ne,rfl⟩ := Finset.card_eq_two.mp two
    exact ⟨bax i j α,⟨i,j,α,ne,rfl⟩,(setClause_pair _ _ _).symm⟩
  · rintro ⟨C,⟨i,j,α,ne,rfl⟩,rfl⟩
    refine Finset.mem_image.mpr ⟨({i,j},α),?_,setClause_pair _ _ _⟩
    simp [indices,Finset.mem_powersetCard,ne]

theorem source_card (l : ℕ) (hl : 0<l) : (axioms l).card=2^l*(2^l+1).choose 2 := by
  classical
  have inj : Set.InjOn setClause (indices l : Set (Finset (Fin (2^l+1)) × (Fin l → Bool))) := by
    intro p hp p' _ h
    have two : p.1.card=2 := (Finset.mem_powersetCard.mp (Finset.mem_product.mp hp).1).2
    exact setClause_inj hl (Finset.card_pos.mp (by omega)) h
  rw [axioms,Finset.card_image_of_injOn inj]
  simp [indices,Finset.card_powersetCard,Nat.mul_comm]

theorem critical (l : ℕ) : Critical truth (axioms l) := by
  intro L hL
  obtain ⟨z,⟨i,j,α,ne,rfl⟩,rfl⟩ := (source_iff l L).mp hL
  obtain ⟨x,hx⟩ := bphp_critical i j ne α
  refine ⟨x,?_⟩
  intro B hb other
  obtain ⟨D,hD,rfl⟩ := (source_iff l B).mp hb
  exact (linOfClause_sat _ _).mpr (hx D hD (fun eq => other (congrArg linOfClause eq)))

theorem bit_php (l : ℕ) (hl : 0<l) (π : List (LinClause (VBit l)))
    (refutes : IsLinRefutation (BPHP (2^l+1) l) π) :
    2*(2^l*(2^l+1).choose 2)≤π.length+1 ∧
    2^l*(2^l+1).choose 2≤paid (axioms l) π+1 := by
  have eq : (↑(axioms l) : Set (LinClause (VBit l)))=linOfClause '' BPHP (2^l+1) l :=
    Set.ext (source_iff l)
  have d := refutes.1
  rw [← eq] at d
  have run := sound_steps _ _ d
  have bad : ∀ x, ¬truth (∅ : LinClause (VBit l)) x := by simp [truth,LinClauseSat]
  rw [← source_card l hl]
  exact ⟨length_bound _ _ _ run ∅ refutes.2 bad (critical l),
    (essential _ _ _ run ∅ refutes.2 bad (critical l)).2⟩

#print axioms bit_php

end ParityProofBudget
