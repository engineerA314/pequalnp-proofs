import ParityProofBudget
import PEqualNP.Defs.SearchQSyn
import PEqualNP.Search.Helpers.ResLinQ

/-! The distinct input equations in the integer bit-pigeonhole proof
system, including the cost of writing the literals in a source line. -/

namespace IntegerPigeonAxioms

open ProofDagBudget PEqualNP.Search PEqualNP.ProofComplexity
open PEqualNP.ProofComplexity.Helpers PEqualNP.Search.Helpers
open ParityProofBudget (VBit)

variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem lin_inj : Function.Injective (@linOfClause V _) := by
  apply Finset.image_injective
  rintro ⟨i,b⟩ ⟨j,c⟩ eq
  simpa [Prod.ext_iff] using eq

omit [Fintype V] in
theorem literal_inj : Function.Injective (@litQEq V _) := by
  rintro ⟨i,b⟩ ⟨j,c⟩ eq
  have co := congrArg (fun e : QEq V => e.1 i) eq
  have right := congrArg (fun e : QEq V => e.2) eq
  by_cases same : i=j
  · subst j
    cases b <;> cases c <;> simp_all [litQEq]
  · simp [litQEq,same] at co

noncomputable def raw (l : ℕ) : Finset (Clause (VBit l)) := by
  classical
  exact Finset.univ.filter (fun C => C∈BPHP (2^l+1) l)

theorem raw_mem (l : ℕ) (C : Clause (VBit l)) : C∈raw l ↔ C∈BPHP (2^l+1) l := by
  classical
  simp [raw]

theorem raw_card (l : ℕ) (hl : 0<l) : (raw l).card=2^l*(2^l+1).choose 2 := by
  classical
  have eq : (raw l).image linOfClause=ParityProofBudget.axioms l := by
    ext C
    simp [ParityProofBudget.source_iff,raw_mem,Set.mem_image]
  rw [← Finset.card_image_of_injective _ lin_inj,eq,ParityProofBudget.source_card l hl]

noncomputable def encode (C : Clause V) : Finset (QEq V) := by
  classical
  exact C.image litQEq

theorem encode_inj : Function.Injective (@encode V _ _) := by
  classical
  exact Finset.image_injective literal_inj

noncomputable def axioms (l : ℕ) := (raw l).image encode

theorem card_axioms (l : ℕ) (hl : 0<l) : (axioms l).card=2^l*(2^l+1).choose 2 := by
  classical
  rw [axioms,Finset.card_image_of_injective _ encode_inj,raw_card l hl]

def Holds (L : Finset (QEq V)) (x : V → Bool) := ∃ e∈L,QEq.Holds x e

theorem encoded_true (x : V → Bool) (C : Clause V) (s : ClauseSat x C) : Holds (encode C) x := by
  classical
  obtain ⟨v,hv,on⟩ := s
  exact ⟨litQEq v,Finset.mem_image_of_mem _ hv,litQEq_holds x v on⟩

theorem critical (l : ℕ) : Critical Holds (axioms l) := by
  classical
  intro L hL
  obtain ⟨C,hC,rfl⟩ := Finset.mem_image.mp hL
  obtain ⟨i,j,α,ne,rfl⟩ := (raw_mem _ _).mp hC
  obtain ⟨x,hx⟩ := bphp_critical i j ne α
  refine ⟨x,?_⟩
  intro D hD diff
  obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hD
  exact encoded_true x B (hx B ((raw_mem _ _).mp hB) (fun eq => diff (congrArg encode eq)))

theorem literal_size (v : V × Bool) : (litQEq v).size=2+(if v.2 then 1 else 0) := by
  classical
  have coeff : (∑ i : V,Nat.size (if i=v.1 then (1 : ℤ) else 0).natAbs)=1 := by
    rw [Finset.sum_eq_single v.1]
    · simp
    · intro i _ diff
      simp [diff]
    · simp
  cases s : v.2 <;> simp [QEq.size,litQEq,coeff,s]

theorem number_literals (l : ℕ) (C : Clause (VBit l)) (h : C∈raw l) : C.card=2*l := by
  classical
  obtain ⟨i,j,α,ne,rfl⟩ := (raw_mem l C).mp h
  let f := fun (k : Fin (2^l+1)) (b : Fin l) => ((k,b),!α b)
  have inj (k : Fin (2^l+1)) : Function.Injective (f k) := fun b c eq =>
    congrArg (fun x : (Fin (2^l+1) × Fin l) × Bool => x.1.2) eq
  have dis : Disjoint (Finset.univ.image (f i)) (Finset.univ.image (f j)) := by
    apply Finset.disjoint_left.mpr
    intro v hi hj
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨b,_,eq⟩ := Finset.mem_image.mp hj
    exact ne (congrArg (fun x : (Fin (2^l+1) × Fin l) × Bool => x.1.1) eq).symm
  change ((Finset.univ.image (f i))∪(Finset.univ.image (f j))).card=_
  rw [Finset.card_union_of_disjoint dis,Finset.card_image_of_injective _ (inj i),
    Finset.card_image_of_injective _ (inj j)]
  simp [two_mul]

#print axioms card_axioms
#print axioms number_literals

end IntegerPigeonAxioms
