import PigeonLocalMatching

namespace PigeonResolutionBoundary

open Finset PEqualNP.ProofComplexity PigeonLocalMatching

variable {P H : Type} [DecidableEq P] [DecidableEq H]

def blocked (E : P → Finset H) (R : Line P H) (p : P) :=
  p∉support R ∧ (¬valid E R) ∧ ∀ f,good E (support R) f → ¬ClauseSat (assign f) R →
    E p ⊆ (support R).image f

theorem parents {C D R : Line P H} {p : P} {j : H}
    (split : R=C.erase ((p,j),true) ∪ D.erase ((p,j),false)) :
    support C ⊆ insert p (support R) ∧ support D ⊆ insert p (support R) := by
  constructor
  · intro x hx
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hx
    by_cases e : l=((p,j),true)
    · simp [e]
    · exact Finset.mem_insert_of_mem <| belongs <| split ▸ Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨e,hl⟩)
  · intro x hx
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hx
    by_cases e : l=((p,j),false)
    · simp [e]
    · exact Finset.mem_insert_of_mem <| belongs <| split ▸ Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨e,hl⟩)

theorem obstruction (E : P → Finset H) {C D R : Line P H} (left : valid E C) (right : valid E D)
    (bad : ¬valid E R) (res : IsResolvent C D R) :
    ∃ p j,((p,j),true)∈C ∧ ((p,j),false)∈D ∧ blocked E R p := by
  classical
  obtain ⟨⟨p,j⟩,pos,neg,split⟩ := res
  have parentsGood := parents split
  have combine (f : P → H) (hf : good E (insert p (support R)) f) : ClauseSat (assign f) R :=
    Helpers.resolvent_sound _ ⟨(p,j),pos,neg,split⟩
      (left f (good_mono hf parentsGood.1)) (right f (good_mono hf parentsGood.2))
  have outside : p∉support R := by
    intro hp
    apply bad
    intro f hf
    apply combine f
    simpa [Finset.insert_eq_of_mem hp] using hf
  refine ⟨p,j,pos,neg,outside,bad,?_⟩
  intro f hf miss h e
  by_contra absent
  apply miss
  apply sat_ext (g := Function.update f p h)
  · intro i hi
    exact Function.update_of_ne (show i≠p from fun eq => outside (eq ▸ hi)) _ _
  · exact combine _ (extend hf outside e absent)

def evidence (E : P → Finset H) (π : List (Line P H)) :=
  ∃ C∈π,∃ D∈π,∃ R∈π,∃ p j,valid E C ∧ valid E D ∧
    ((p,j),true)∈C ∧ ((p,j),false)∈D ∧ IsResolvent C D R ∧ blocked E R p

theorem keep {E : P → Finset H} {π : List (Line P H)} (X : Line P H) (h : evidence E π) :
    evidence E (X::π) := by
  obtain ⟨C,hC,D,hD,R,hR,tail⟩ := h
  exact ⟨C,List.mem_cons_of_mem _ hC,D,List.mem_cons_of_mem _ hD,R,List.mem_cons_of_mem _ hR,tail⟩

theorem first_failure (E : P → Finset H) (live : ∀ p,(E p).Nonempty) {π : List (Line P H)}
    (proof : IsDerivation (axioms E) π) : (∀ C∈π,valid E C) ∨ evidence E π := by
  classical
  induction proof with
  | nil => left; simp
  | ax prev axiomMem ih =>
    rcases ih with all | old
    · exact Or.inl (fun _ mem => (List.mem_cons.mp mem).elim
        (fun e => e ▸ ax_valid E live axiomMem) (fun m => all _ m))
    · exact Or.inr (keep _ old)
  | @res π C D R prev hc hd step ih =>
    rcases ih with all | old
    · by_cases vr : valid E R
      · exact Or.inl (fun _ mem => (List.mem_cons.mp mem).elim (fun e => e ▸ vr) (fun m => all _ m))
      · obtain ⟨p,j,cp,dp,ob⟩ := obstruction E (all C hc) (all D hd) vr step
        exact Or.inr ⟨C,List.mem_cons_of_mem _ hc,D,List.mem_cons_of_mem _ hd,
          R,List.mem_cons_self,p,j,all C hc,all D hd,cp,dp,step,ob⟩
    · exact Or.inr (keep _ old)

theorem extraction [Nonempty H] (E : P → Finset H) (live : ∀ p,(E p).Nonempty)
    {π : List (Line P H)} (proof : IsRefutation (axioms E) π) : evidence E π := by
  classical
  rcases first_failure E live proof.1 with all | found
  · let f : P → H := fun _ => Classical.choice ‹Nonempty H›
    have h := all ∅ proof.2 f (by simp [good,support])
    simpa [ClauseSat] using h
  · exact found

#print axioms obstruction
#print axioms extraction

end PigeonResolutionBoundary
