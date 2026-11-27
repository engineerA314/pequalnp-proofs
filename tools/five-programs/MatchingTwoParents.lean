import MatchingExtension

namespace MatchingTwoParents

open Finset MatchingExtension

variable {P H : Type} [DecidableEq P] [DecidableEq H] [Fintype H]

def middle (A B R : Finset P) := (A∩B) ∪ (R∩(A∪B))

theorem budget (A B R : Finset P) : 2*(middle A B R).card ≤ A.card+B.card+R.card := by
  have sub : middle A B R ⊆ A∪B := by
    intro p h
    rcases Finset.mem_union.mp h with h|h
    · exact Finset.mem_union_left _ (Finset.mem_inter.mp h).1
    · exact (Finset.mem_inter.mp h).2
  have a := Finset.card_le_card sub
  have b := Finset.card_union_le (A∩B) (R∩(A∪B))
  have r := Finset.card_le_card (Finset.inter_subset_left : R∩(A∪B) ⊆ R)
  have c := Finset.card_union_add_card_inter A B
  unfold middle at *
  omega

theorem finish (S A : Finset P) (f : P → H) (inj : Set.InjOn f (↑S : Set P))
    (available : A.card≤Fintype.card H) : ∃ g : P → H,
      Set.InjOn g (↑A : Set P) ∧ ∀ p∈S∩A,g p=f p := by
  have eq : (S∩A)∪A=A := Finset.union_eq_right.mpr Finset.inter_subset_right
  have ini : Set.InjOn f (↑(S∩A) : Set P) := inj.mono (fun _ h => (Finset.mem_inter.mp h).1)
  obtain ⟨g,gi,same⟩ := grow (S∩A) f ini A (by rw [eq]; exact available)
  rw [eq] at gi
  exact ⟨g,gi,same⟩

theorem couple (A B R : Finset P) (f : P → H) (verified : Set.InjOn f (↑R : Set P))
    (a : A.card≤Fintype.card H) (b : B.card≤Fintype.card H) (room : (middle A B R).card≤Fintype.card H) :
    ∃ g : P → H,Set.InjOn g (↑A : Set P) ∧ Set.InjOn g (↑B : Set P) ∧ ∀ p∈R,g p=f p := by
  classical
  let K := middle A B R
  obtain ⟨core,ci,cr⟩ := finish R K f verified room
  obtain ⟨left,li,la⟩ := finish K A core ci a
  obtain ⟨right,ri,rb⟩ := finish K B core ci b
  let g := fun p => if p∈A then left p else if p∈B then right p else f p
  have useA (p) (pa : p∈A) : g p=left p := by simp [g,pa]
  have useB (p) (pb : p∈B) : g p=right p := by
    by_cases pa : p∈A
    · have pk : p∈K := Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨pa,pb⟩)
      rw [useA p pa,la p (Finset.mem_inter.mpr ⟨pk,pa⟩),rb p (Finset.mem_inter.mpr ⟨pk,pb⟩)]
    · simp [g,pa,pb]
  refine ⟨g,?_,?_,?_⟩
  · intro x hx y hy h
    exact li hx hy ((useA _ hx).symm.trans (h.trans (useA _ hy)))
  · intro x hx y hy h
    exact ri hx hy ((useB _ hx).symm.trans (h.trans (useB _ hy)))
  · intro p pr
    by_cases pa : p∈A
    · have pk : p∈K := Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨pr,Finset.mem_union_left _ pa⟩)
      rw [useA _ pa,la p (Finset.mem_inter.mpr ⟨pk,pa⟩),cr p (Finset.mem_inter.mpr ⟨pr,pk⟩)]
    · by_cases pb : p∈B
      · have pk : p∈K := Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨pr,Finset.mem_union_right _ pb⟩)
        rw [useB _ pb,rb p (Finset.mem_inter.mpr ⟨pk,pb⟩),cr p (Finset.mem_inter.mpr ⟨pr,pk⟩)]
      · simp [g,pa,pb]

#print axioms couple

end MatchingTwoParents
