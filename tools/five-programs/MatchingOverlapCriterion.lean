import MatchingTwoParents

namespace MatchingOverlapCriterion

open Finset MatchingTwoParents
variable {P H : Type} [DecidableEq P] [DecidableEq H] [Fintype H]

theorem middle_inj (A B R : Finset P) (g : P → H) (ga : Set.InjOn g (↑A : Set P))
    (gb : Set.InjOn g (↑B : Set P)) (gr : Set.InjOn g (↑R : Set P)) :
    Set.InjOn g (↑(middle A B R) : Set P) := by
  intro p hp q hq eq
  rcases Finset.mem_union.mp hp with pab|pr
  · obtain ⟨pa,pb⟩ := Finset.mem_inter.mp pab
    rcases Finset.mem_union.mp hq with qab|qr
    · exact ga pa (Finset.mem_inter.mp qab).1 eq
    · rcases Finset.mem_union.mp (Finset.mem_inter.mp qr).2 with qa|qb
      · exact ga pa qa eq
      · exact gb pb qb eq
  · obtain ⟨pr,pu⟩ := Finset.mem_inter.mp pr
    rcases Finset.mem_union.mp hq with qab|qr
    · obtain ⟨qa,qb⟩ := Finset.mem_inter.mp qab
      rcases Finset.mem_union.mp pu with pa|pb
      · exact ga pa qa eq
      · exact gb pb qb eq
    · exact gr pr (Finset.mem_inter.mp qr).1 eq

theorem capacity {S : Finset P} {g : P → H} (inj : Set.InjOn g (↑S : Set P)) : S.card≤Fintype.card H := by
  rw [← Finset.card_image_of_injOn inj]
  exact Finset.card_le_univ _

theorem iff_capacity (A B R : Finset P) (f : P → H) (verified : Set.InjOn f (↑R : Set P)) :
    (∃ g : P → H,Set.InjOn g (↑A : Set P) ∧ Set.InjOn g (↑B : Set P) ∧ ∀ p∈R,g p=f p) ↔
      A.card≤Fintype.card H ∧ B.card≤Fintype.card H ∧ (middle A B R).card≤Fintype.card H := by
  constructor
  · rintro ⟨g,ga,gb,agree⟩
    have gr : Set.InjOn g (↑R : Set P) := fun p hp q hq eq =>
      verified hp hq ((agree p hp).symm.trans (eq.trans (agree q hq)))
    exact ⟨capacity ga,capacity gb,capacity (middle_inj A B R g ga gb gr)⟩
  · rintro ⟨a,b,room⟩
    exact couple A B R f verified a b room

#print axioms iff_capacity

end MatchingOverlapCriterion
