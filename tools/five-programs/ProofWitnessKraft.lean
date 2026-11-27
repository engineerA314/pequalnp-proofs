import ProofWitnessScale

/-! A Kraft bound on the numbers of lines falsified by individual witnesses. -/
namespace ProofWitnessKraft

open ProofDagBudget ProofWitnessScale
variable {L X I : Type} [DecidableEq L] [DecidableEq I]

noncomputable def count (F : L → Finset I) (W : List L) (k : I) :=
  W.countP (fun l => decide (k∈F l))

noncomputable def weight (F : L → Finset I) (W : List L) (k : I) : ℚ :=
  (1/2 : ℚ)^(count F W k)

omit [DecidableEq L] in
theorem nonnegW (F : L → Finset I) (W : List L) (k : I) : 0≤weight F W k := by
  unfold weight
  positivity

omit [DecidableEq L] in
theorem le_oneW (F : L → Finset I) (W : List L) (k : I) : weight F W k≤1 := by
  exact pow_le_one₀ (by norm_num) (by norm_num)

omit [DecidableEq L] in
theorem hit (F : L → Finset I) (W : List L) (l : L) (k : I) (h : k∈F l) :
    weight F (l::W) k=weight F W k*(1/2) := by simp [weight,count,h,pow_succ]

omit [DecidableEq L] in
theorem decreases (F : L → Finset I) (W : List L) (l : L) (k : I) :
    weight F (l::W) k≤weight F W k := by
  by_cases h : k∈F l
  · rw [hit F W l k h]
    linarith [nonnegW F W k]
  · simp [weight,count,h]

theorem unionSum (P : Finset L) (F : L → Finset I) (w : I → ℚ) (pos : ∀ i,0≤w i) :
    ∑ i ∈ P.biUnion F,w i ≤ ∑ p ∈ P, ∑ i ∈ F p,w i := by
  induction P using Finset.induction_on with
  | empty => simp
  | insert l P hp ih =>
    rw [Finset.biUnion_insert,Finset.sum_insert hp]
    have total := Finset.sum_union_inter (s₁ := F l) (s₂ := P.biUnion F) (f := w)
    have inter : 0 ≤ ∑ i ∈ F l ∩ P.biUnion F,w i := Finset.sum_nonneg fun i _ => pos i
    linarith

theorem line_bound (H : L → X → Prop) (ids : Finset I) (x : I → X) (A : Finset L)
    (light : ∀ l∈A,(failures H ids x l).card≤1) (W : List L) (run : Derives H A W) :
    ∀ l∈W, ∑ k ∈ failures H ids x l, weight (failures H ids x) W k ≤ (1/2 : ℚ) := by
  classical
  let F := failures H ids x
  induction run with
  | nil => simp
  | @step W _ l legal ih =>
    intro z hz
    rcases List.mem_cons.mp hz with rfl | prev
    · change ∑ k ∈ F z, weight F (z::W) k ≤ _
      have factor : ∑ k ∈ F z, weight F (z::W) k = (∑ k ∈ F z,weight F W k)*(1/2 : ℚ) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun k hk => hit F W z k hk
      rw [factor]
      suffices small : ∑ k ∈ F z,weight F W k ≤ 1 by linarith
      rcases legal with ax | ⟨P,two,prev,sound⟩
      · have n : (F z).card≤1 := light z ax
        calc _ ≤ ∑ _k ∈ F z, (1:ℚ) := Finset.sum_le_sum fun k _ => le_oneW F W k
             _ = (F z).card := by simp
             _ ≤ 1 := by exact_mod_cast n
      · have cover : F z ⊆ P.biUnion F := by
          intro k hk
          obtain ⟨inI,wrong⟩ := (mem_failures _ _ _ _ _).mp hk
          by_contra missed
          apply wrong (sound (x k) _ z (by simp))
          intro p hp
          by_contra no
          exact missed (Finset.mem_biUnion.mpr ⟨p,hp,(mem_failures _ _ _ _ _).mpr ⟨inI,no⟩⟩)
        calc _ ≤ ∑ k ∈ P.biUnion F,weight F W k :=
                   Finset.sum_le_sum_of_subset_of_nonneg cover (fun k _ _ => nonnegW F W k)
             _ ≤ ∑ p ∈ P,∑ k ∈ F p,weight F W k := unionSum P F _ (nonnegW F W)
             _ ≤ ∑ _p ∈ P,(1/2:ℚ) := Finset.sum_le_sum fun p hp => ih p (prev p hp)
             _ = (P.card : ℚ)*(1/2) := by simp
             _ ≤ 1 := by have h : (P.card : ℚ)≤2 := by exact_mod_cast two
                         linarith
    · calc _ ≤ ∑ k ∈ F z,weight F W k := Finset.sum_le_sum fun k _ => decreases F W l k
           _ ≤ _ := ih z prev

theorem kraft (H : L → X → Prop) (ids : Finset I) (x : I → X) (A : Finset L)
    (light : ∀ l∈A,(failures H ids x l).card≤1) (W : List L) (run : Derives H A W)
    (z : L) (last : z∈W) (bad : ∀ k∈ids,¬H z (x k)) :
    ∑ k ∈ ids,weight (failures H ids x) W k ≤ (1/2 : ℚ) := by
  have eq : failures H ids x z=ids := by
    ext k
    rw [mem_failures]
    exact ⟨And.left,fun h => ⟨h,bad k h⟩⟩
  simpa only [eq] using line_bound H ids x A light W run z last

#print axioms kraft

end ProofWitnessKraft
