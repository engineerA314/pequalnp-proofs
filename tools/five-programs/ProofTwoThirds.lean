import MatchingTwoParents
import ProofMatchingBottleneck

namespace ProofTwoThirds

open Finset MatchingExtension MatchingTwoParents ProofDagBudget

variable {P H L : Type} [DecidableEq P] [DecidableEq H] [Fintype H] [DecidableEq L]

theorem pair_step (S : L → Finset P) (T : L → (P → H) → Prop) (dep : localEval S T) (a b r : L)
    (va : localValid S T a) (vb : localValid S T b) (rule : ∀ f,T a f → T b f → T r f)
    (ca : 3*(S a).card≤2*Fintype.card H+1) (cb : 3*(S b).card≤2*Fintype.card H+1)
    (cr : 3*(S r).card≤2*Fintype.card H+1) : localValid S T r := by
  intro f inj
  have mid := budget (S a) (S b) (S r)
  obtain ⟨g,ga,gb,gr⟩ := couple (S a) (S b) (S r) f inj (by omega) (by omega) (by omega)
  exact dep r f g gr (rule g (va g ga) (vb g gb))

theorem small_all (S : L → Finset P) (T : L → (P → H) → Prop) (dep : localEval S T)
    (A : Finset L) (start : ∀ l∈A,localValid S T l) {W : List L} (proof : Derives T A W)
    (small : ∀ l∈W,3*(S l).card≤2*Fintype.card H+1) : ∀ l∈W,localValid S T l := by
  classical
  induction proof with
  | nil => simp
  | @step W prev l step ih =>
    have prevSmall (t : L) (ht : t∈W) := small t (List.mem_cons_of_mem _ ht)
    have all := ih prevSmall
    have on : localValid S T l := by
      rcases step with ax|⟨B,arity,seen,sound⟩
      · exact start l ax
      · by_cases empty : B.card=0
        · have e := Finset.card_eq_zero.mp empty
          exact fun f _ => sound f (by simp [e]) l (by simp)
        by_cases single : B.card=1
        · obtain ⟨p,rfl⟩ := Finset.card_eq_one.mp single
          have mem := seen p (by simp)
          apply pair_step S T dep p p l (all p mem) (all p mem) _ (prevSmall p mem) (prevSmall p mem) (small l List.mem_cons_self)
          intro f h _
          exact sound f (by simpa using h) l (by simp)
        · obtain ⟨p,q,_,rfl⟩ := Finset.card_eq_two.mp (by omega : B.card=2)
          have hp := seen p (by simp)
          have hq := seen q (by simp)
          apply pair_step S T dep p q l (all p hp) (all q hq) _ (prevSmall p hp) (prevSmall q hq) (small l List.mem_cons_self)
          intro f h k
          apply sound f _ l (by simp)
          intro t ht
          rcases Finset.mem_insert.mp ht with rfl|eq
          · exact h
          · exact Finset.mem_singleton.mp eq ▸ k
    intro t ht
    rcases List.mem_cons.mp ht with rfl|mem
    · exact on
    · exact all t mem

theorem forced (S : L → Finset P) (T : L → (P → H) → Prop) (dep : localEval S T) (A : Finset L)
    (start : ∀ l∈A,localValid S T l) {W : List L} (proof : Derives T A W) {r : L} (hr : r∈W)
    (bad : ¬localValid S T r) : ∃ l∈W,2*(Fintype.card H+1) ≤ 3*(S l).card := by
  by_contra! small
  have cap (t : L) (ht : t∈W) : 3*(S t).card≤2*Fintype.card H+1 := by have := small t ht; omega
  exact bad (small_all S T dep A start proof cap r hr)

#print axioms forced

end ProofTwoThirds
