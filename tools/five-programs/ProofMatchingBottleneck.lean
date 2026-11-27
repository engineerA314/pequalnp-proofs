import MatchingExtension

namespace ProofMatchingBottleneck

open Finset MatchingExtension ProofDagBudget

variable {P H L : Type} [DecidableEq P] [DecidableEq H] [Fintype H] [DecidableEq L]

def event (S : L → Finset P) (T : L → (P → H) → Prop) (W : List L) :=
  ∃ l∈W,∃ B : Finset L,B.card≤2 ∧ (∀ t∈B,t∈W ∧ localValid S T t) ∧
    ¬localValid S T l ∧ Fintype.card H < (parentScope S B).card

theorem preserve {S : L → Finset P} {T : L → (P → H) → Prop} {W : List L} (r : L) (h : event S T W) :
    event S T (r::W) := by
  obtain ⟨l,hl,B,arity,parents,bad,large⟩ := h
  exact ⟨l,List.mem_cons_of_mem _ hl,B,arity,fun t ht => ⟨List.mem_cons_of_mem _ (parents t ht).1,(parents t ht).2⟩,bad,large⟩

theorem first (S : L → Finset P) (T : L → (P → H) → Prop) (dep : localEval S T)
    (A : Finset L) (start : ∀ l∈A,localValid S T l) {W : List L} (legal : Derives T A W) :
    (∀ l∈W,localValid S T l) ∨ event S T W := by
  classical
  induction legal with
  | nil => left; simp
  | @step W prev l rule ih =>
    rcases ih with all | found
    · by_cases loc : localValid S T l
      · left
        intro t ht
        rcases List.mem_cons.mp ht with rfl|old
        · exact loc
        · exact all t old
      · right
        rcases rule with input|⟨B,arity,earlier,sound⟩
        · exact (loc (start l input)).elim
        · have validB := fun t ht => all t (earlier t ht)
          have joinedLarge := loss S T dep l B validB (fun g passed => sound g passed l (by simp)) loc
          exact ⟨l,List.mem_cons_self,B,arity,fun t ht => ⟨List.mem_cons_of_mem _ (earlier t ht),validB t ht⟩,loc,joinedLarge⟩
    · right; exact preserve _ found

theorem wide (S : L → Finset P) (T : L → (P → H) → Prop) {W : List L} (h : event S T W) :
    ∃ l∈W,Fintype.card H < 2*(S l).card := by
  classical
  by_contra! small
  obtain ⟨l,hl,B,arity,earlier,_,large⟩ := h
  let w := Fintype.card H/2
  have lim (t : L) (ht : t∈W) : (S t).card≤w := by have := small t ht; dsimp [w]; omega
  have sum := Finset.card_biUnion_le (s := B) (t := S)
  have cap : ∑ t∈B,(S t).card≤∑ _t∈B,w := Finset.sum_le_sum fun t ht => lim t (earlier t ht).1
  simp only [sum_const,nsmul_eq_mul] at cap
  have span := Nat.mul_le_mul_right w arity
  unfold parentScope at large
  dsimp [w] at *
  omega

#print axioms first
#print axioms wide

end ProofMatchingBottleneck
