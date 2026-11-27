import MatchingTwoParents

namespace MatchingThreeBlocks

open Finset MatchingExtension

variable {P H : Type} [Fintype P] [DecidableEq P] [Fintype H] [DecidableEq H]

def region (tag : P → Fin 3) (i : Fin 3) := univ.filter (fun p => tag p≠i)

theorem covering (tag : P → Fin 3) (p q : P) :
    ∃ i : Fin 3,p∈region tag i ∧ q∈region tag i := by
  have ex : ∀ a b : Fin 3,∃ i : Fin 3,a≠i ∧ b≠i := by decide
  obtain ⟨i,x,y⟩ := ex (tag p) (tag q)
  exact ⟨i,by simp [region,x],by simp [region,y]⟩

theorem incompatible (tag : P → Fin 3) (big : Fintype.card H < Fintype.card P) (f : P → H)
    (a : Set.InjOn f (↑(region tag 0) : Set P)) (b : Set.InjOn f (↑(region tag 1) : Set P)) :
    ¬Set.InjOn f (↑(region tag 2) : Set P) := by
  intro c
  have inj : Function.Injective f := by
    intro p q same
    obtain ⟨i,pi,qi⟩ := covering tag p q
    fin_cases i
    · exact a pi qi same
    · exact b pi qi same
    · exact c pi qi same
  exact (Nat.not_lt_of_ge (Fintype.card_le_of_injective f inj)) big

theorem local_failure [Nonempty H] (tag : P → Fin 3) (small : (region tag 2).card≤Fintype.card H) :
    ∃ f : P → H,Set.InjOn f (↑(region tag 2) : Set P) := by
  classical
  let f := fun _ : P => Classical.choice ‹Nonempty H›
  obtain ⟨g,inj,_⟩ := grow ∅ f (by simp) (region tag 2) (by simpa using small)
  exact ⟨g,by simpa using inj⟩

theorem card_region (tag : P → Fin 3) (i : Fin 3) :
    (region tag i).card+(univ.filter (fun p => tag p=i)).card=Fintype.card P := by
  have part := Finset.card_filter_add_card_filter_not (s := (univ : Finset P)) (p := fun p => tag p=i)
  simpa [region,Nat.add_comm] using part

#print axioms incompatible
#print axioms local_failure

end MatchingThreeBlocks
