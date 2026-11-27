import Mathlib

/-! A minimally inconsistent set of K input lines requires at least K-1
non-input steps in a sound derivation of fan-in two, even with shared lines. -/

namespace ProofDagBudget

variable {L X : Type} [DecidableEq L]
def Entails (H : L → X → Prop) (S T : Finset L) :=
  ∀ x, (∀ a ∈ S, H a x) → ∀ t ∈ T, H t x

inductive Derives (H : L → X → Prop) (A : Finset L) : List L → Prop
  | nil : Derives H A []
  | step {W : List L} (built : Derives H A W) (l : L)
      (rule : l∈A ∨ ∃ P : Finset L, P.card≤2 ∧ (∀ f∈P, f∈W) ∧ Entails H P {l}) :
      Derives H A (l::W)

def sources (A : Finset L) (W : List L) := (W.filter fun x => decide (x∈A)).toFinset
def paid (A : Finset L) (W : List L) := (W.filter fun x => decide (x∉A)).length

theorem frontier (H : L → X → Prop) (A : Finset L) (W : List L) (legal : Derives H A W) :
    ∀ T : Finset L, (∀ f∈T,f∈W) →
    ∃ D : Finset L, D⊆A ∧ D⊆sources A W ∧ D.card≤paid A W+T.card ∧ Entails H D T := by
  induction legal with
  | nil =>
    intro T raw
    have ht : T=∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun t ht => by simpa using raw t ht)
    subst T
    exact ⟨∅,by simp,by simp,by simp,fun _ _ _ h => by simp at h⟩
  | @step W old l rule ih =>
    intro T raw
    have sub : sources A W⊆sources A (l::W) := by
      intro f hf
      simp only [sources,List.mem_toFinset,List.mem_filter,decide_eq_true_eq] at hf ⊢
      exact ⟨List.mem_cons_of_mem _ hf.1,hf.2⟩
    have rate : paid A W≤paid A (l::W) := by by_cases hl : l∈A <;> simp [paid,hl]
    by_cases hit : l∈T
    · let U := T.erase l
      have card : U.card+1=T.card := Finset.card_erase_add_one hit
      have prev : ∀ f∈U,f∈W := by
        intro f hf
        exact (List.mem_cons.mp (raw f (Finset.mem_erase.mp hf).2)).resolve_left (Finset.mem_erase.mp hf).1
      by_cases ax : l∈A
      · obtain ⟨D,inA,record,cap,ent⟩ := ih U prev
        refine ⟨insert l D,Finset.insert_subset ax inA,Finset.insert_subset ?_ (record.trans sub),?_,?_⟩
        · simp [sources,ax]
        · have h := Finset.card_insert_le l D
          omega
        · intro x hx t ht
          by_cases eq : t=l
          · exact eq ▸ hx l (Finset.mem_insert_self _ _)
          · exact ent x (fun d hd => hx _ (Finset.mem_insert_of_mem hd)) t (Finset.mem_erase.mpr ⟨eq,ht⟩)
      · obtain ⟨P,two,avail,rule⟩ := rule.resolve_left ax
        obtain ⟨D,inA,record,cap,ent⟩ := ih (U∪P) (fun f hf => (Finset.mem_union.mp hf).elim (prev f) (avail f))
        refine ⟨D,inA,record.trans sub,?_,?_⟩
        · have cost : paid A (l::W)=paid A W+1 := by simp [paid,ax]
          have h := Finset.card_union_le U P
          omega
        · intro x hx t ht
          by_cases eq : t=l
          · subst t
            exact rule x (fun p hp => ent x hx p (Finset.mem_union_right _ hp)) _ (by simp)
          · exact ent x hx t (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq,ht⟩))
    · have prev (f : L) (hf : f∈T) : f∈W :=
        (List.mem_cons.mp (raw f hf)).resolve_left (fun e => hit (e ▸ hf))
      obtain ⟨D,inA,record,cap,ent⟩ := ih T prev
      exact ⟨D,inA,record.trans sub,cap.trans (Nat.add_le_add_right rate _),ent⟩

def Critical (H : L → X → Prop) (A : Finset L) :=
  ∀ a∈A, ∃ x, ∀ b∈A, b≠a → H b x

theorem essential (H : L → X → Prop) (A : Finset L) (W : List L) (legal : Derives H A W)
    (z : L) (last : z∈W) (bad : ∀ x, ¬ H z x) (critical : Critical H A) :
    A⊆sources A W ∧ A.card≤paid A W+1 := by
  obtain ⟨D,inA,record,cap,ent⟩ := frontier H A W legal {z} (by simpa)
  have back : A⊆D := by
    intro a ha
    by_contra absent
    obtain ⟨x,hx⟩ := critical a ha
    exact bad x (ent x (fun b hb => hx b (inA hb) (fun eq => absent (eq ▸ hb))) z (by simp))
  have eq := Finset.Subset.antisymm back inA
  rw [← eq] at record cap
  exact ⟨record,by simpa using cap⟩

theorem split_length (A : Finset L) (W : List L) :
    (W.filter fun x => decide (x∈A)).length+paid A W=W.length := by
  induction W with
  | nil => rfl
  | cons l W ih =>
    by_cases h : l∈A <;> simp [paid] at ih <;> simp [paid,h] <;> omega

theorem length_bound (H : L → X → Prop) (A : Finset L) (W : List L) (legal : Derives H A W)
    (z : L) (last : z∈W) (bad : ∀ x, ¬ H z x) (critical : Critical H A) :
    2*A.card≤W.length+1 := by
  obtain ⟨allAx,nonAx⟩ := essential H A W legal z last bad critical
  have count := (Finset.card_le_card allAx).trans (List.toFinset_card_le _)
  have length := split_length A W
  omega

#print axioms length_bound

end ProofDagBudget
