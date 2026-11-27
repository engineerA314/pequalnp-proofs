import PigeonLocalMatching
import ProofDagBudget

namespace MatchingExtension

open Finset PigeonLocalMatching ProofDagBudget

variable {P H L X : Type} [DecidableEq P] [DecidableEq H] [Fintype H] [DecidableEq L]

theorem grow (S : Finset P) (f : P → H) (initial : Set.InjOn f (↑S : Set P)) (T : Finset P)
    (cap : (S∪T).card≤Fintype.card H) :
    ∃ g : P → H,Set.InjOn g (↑(S∪T) : Set P) ∧ ∀ p∈S,g p=f p := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨f,by simpa using initial,fun _ _ => rfl⟩
  | @insert p T hp ih =>
    have united : S∪insert p T=insert p (S∪T) := by ext; simp
    rw [united] at cap ⊢
    obtain ⟨g,inj,old⟩ := ih ((Finset.card_le_card (Finset.subset_insert _ _)).trans cap)
    by_cases used : p∈S∪T
    · exact ⟨g,by simpa [Finset.insert_eq_of_mem used] using inj,old⟩
    · have small : (S∪T).card<Fintype.card H := by rw [Finset.card_insert_of_notMem used] at cap; omega
      have free : ∃ j : H,j∉(S∪T).image g := by
        by_contra! covers
        have eq : (S∪T).image g=univ := Finset.univ_subset_iff.mp (fun j _ => covers j)
        have card := Finset.card_image_of_injOn inj
        rw [eq,Finset.card_univ] at card
        omega
      obtain ⟨j,fresh⟩ := free
      let E := fun _ : P => (univ : Finset H)
      have m : good E (S∪T) g := ⟨inj,fun _ _ => mem_univ _⟩
      refine ⟨Function.update g p j,(extend m used (mem_univ _) fresh).1,?_⟩
      intro q hq
      have ne : q≠p := fun eq => used (eq ▸ (mem_union_left T hq))
      exact (Function.update_of_ne ne _ _).trans (old q hq)

def localValid (scope : L → Finset P) (truth : L → (P → H) → Prop) (l : L) :=
  ∀ f,Set.InjOn f (↑(scope l) : Set P) → truth l f

def localEval (scope : L → Finset P) (truth : L → (P → H) → Prop) :=
  ∀ l f g,(∀ p∈scope l,g p=f p) → truth l g → truth l f

def parentScope (scope : L → Finset P) (parents : Finset L) := parents.biUnion scope

theorem loss (scope : L → Finset P) (truth : L → (P → H) → Prop) (depends : localEval scope truth)
    (l : L) (B : Finset L) (old : ∀ t∈B,localValid scope truth t)
    (rule : ∀ g,(∀ t∈B,truth t g) → truth l g) (bad : ¬localValid scope truth l) :
    Fintype.card H < (parentScope scope B).card := by
  classical
  by_contra! small
  apply bad
  intro f inj
  let U := parentScope scope B
  let K := scope l ∩ U
  have fixed : K ∪ U = U := Finset.union_eq_right.mpr Finset.inter_subset_right
  have ik : Set.InjOn f (↑K : Set P) := inj.mono (fun _ hp => (Finset.mem_inter.mp hp).1)
  obtain ⟨g,gi,eq⟩ := grow K f ik U (by rw [fixed]; exact small)
  rw [fixed] at gi
  let z := fun p => if p∈U then g p else f p
  apply depends l f z
  · intro p hp
    by_cases inside : p∈U
    · exact (ite_eq_left inside).trans (eq p (Finset.mem_inter.mpr ⟨hp,inside⟩))
    · exact ite_eq_right inside
  · apply rule z
    intro t ht
    apply old t ht z
    have inside {p} (hp : p∈scope t) : p∈U := Finset.mem_biUnion.mpr ⟨t,ht,hp⟩
    intro p hp q hq same
    apply gi (inside hp) (inside hq)
    simpa only [z,ite_eq_left (inside hp),ite_eq_left (inside hq)] using same

theorem lift_derivation (T : L → X → Prop) (read : (P → H) → X) (A : Finset L) (W : List L)
    (legal : Derives T A W) : Derives (fun l f => T l (read f)) A W := by
  induction legal with
  | nil => exact .nil
  | step prev l rule ih =>
    apply Derives.step ih l
    rcases rule with ax|⟨B,arity,seen,sound⟩
    · exact Or.inl ax
    · exact Or.inr ⟨B,arity,seen,fun f => sound (read f)⟩

#print axioms loss

end MatchingExtension
