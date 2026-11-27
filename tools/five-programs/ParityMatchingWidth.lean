import ProofMatchingBottleneck
import ParityProofBudget

namespace ParityMatchingWidth

open Finset PEqualNP.ProofComplexity PEqualNP.ProofComplexity.Helpers
open MatchingExtension ProofMatchingBottleneck ProofDagBudget ParityProofBudget

abbrev Pid (l : ℕ) := Fin (2^l+1)
abbrev Hole (l : ℕ) := Fin l → Bool
def readBits {m l : ℕ} (f : Fin m → Hole l) : Fin m × Fin l → Bool := fun v => f v.1 v.2

def scope {m l : ℕ} (C : LinClause (Fin m × Fin l)) : Finset (Fin m) :=
  C.biUnion fun q => q.1.image Prod.fst

theorem present {m l : ℕ} {C : LinClause (Fin m × Fin l)} {q : LinEq (Fin m × Fin l)}
    (hq : q∈C) {v} (hv : v∈q.1) : v.1∈scope C :=
  Finset.mem_biUnion.mpr ⟨q,hq,Finset.mem_image_of_mem _ hv⟩

theorem depends (m l : ℕ) : localEval (@scope m l) (fun C f => LinClauseSat (readBits f) C) := by
  intro C f g eq yes
  obtain ⟨q,hq,ok⟩ := yes
  refine ⟨q,hq,?_⟩
  have same : q.1.filter (fun v => readBits g v=true)=q.1.filter (fun v => readBits f v=true) := by
    apply Finset.filter_congr
    intro v hv
    simp [readBits,eq v.1 (present hq hv)]
  unfold LinEqSat at ok ⊢
  rwa [same] at ok

theorem bax_holds {m l : ℕ} (i j : Fin m) (α : Hole l) (f : Fin m → Hole l) (distinct : f i≠f j) :
    ClauseSat (readBits f) (bax i j α) := by
  classical
  by_contra bad
  have agree (p : Fin m) (inside : ∀ b : Fin l,((p,b),!α b)∈bax i j α) : f p=α := by
    funext b
    by_contra disagree
    apply bad
    refine ⟨((p,b),!α b),inside b,?_⟩
    change f p b= !α b
    cases e : f p b <;> cases a : α b <;> simp_all
  exact distinct ((agree i (fun b => Finset.mem_union_left _ (Finset.mem_image_of_mem _ (mem_univ b)))).trans
    (agree j (fun b => Finset.mem_union_right _ (Finset.mem_image_of_mem _ (mem_univ b)))).symm)

theorem in_encoded {m l : ℕ} {C : Clause (Fin m × Fin l)} {v : Literal (Fin m × Fin l)}
    (h : v∈C) : v.1.1∈scope (linOfClause C) := by
  have inside : (({v.1} : Finset _),v.2)∈linOfClause C :=
    Finset.mem_image_of_mem (fun l : Literal (Fin m × Fin l) => (({l.1} : Finset _),l.2)) h
  exact present (v := v.1) inside (Finset.mem_singleton_self _)

theorem local_source (l : ℕ) (hl : 0<l) (C : LinClause (VBit l)) (src : C∈axioms l) :
    localValid scope (fun D f => LinClauseSat (readBits f) D) C := by
  rintro f inj
  obtain ⟨_,⟨i,j,α,ne,rfl⟩,rfl⟩ := (source_iff l C).mp src
  let b : Fin l := ⟨0,hl⟩
  have iocc : ((i,b),!α b)∈bax i j α := Finset.mem_union_left _ (Finset.mem_image_of_mem _ (mem_univ b))
  have jocc : ((j,b),!α b)∈bax i j α := Finset.mem_union_right _ (Finset.mem_image_of_mem _ (mem_univ b))
  exact (linOfClause_sat _ _).mpr (bax_holds i j α f (fun h => ne (inj (in_encoded iocc) (in_encoded jocc) h)))

theorem certificate (l : ℕ) (hl : 0<l) (W : List (LinClause (VBit l))) (refutes : IsLinRefutation (BPHP (2^l+1) l) W) :
    event scope (fun C f => LinClauseSat (readBits f) C) W := by
  classical
  have d := refutes.1
  have eq : (↑(axioms l) : Set (LinClause (VBit l)))=linOfClause '' BPHP (2^l+1) l := Set.ext (source_iff l)
  rw [←eq] at d
  have proof := lift_derivation truth readBits _ _ (sound_steps _ _ d)
  rcases first scope _ (depends _ _) _ (local_source l hl) proof with all|found
  · let f : Pid l → Hole l := fun _ _ => false
    have z := all ∅ refutes.2 f (by simp [scope])
    simpa [LinClauseSat] using z
  · exact found

theorem bound (l : ℕ) (hl : 0<l) (W : List (LinClause (VBit l))) (refutes : IsLinRefutation (BPHP (2^l+1) l) W) :
    ∃ C∈W,2^l < 2*(scope C).card := by
  simpa [Hole] using wide _ _ (certificate l hl W refutes)

#print axioms certificate
#print axioms bound

end ParityMatchingWidth
