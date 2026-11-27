import ScaledWidth

/-! Partial recognition of sums with bounded pairwise overlap. Monotone ANDs
are unrestricted. Only wide OR gates are allocated to individual outputs. -/

namespace OverlapSums

open PartialSums CleanPreparation

variable {P L : Type} [Fintype P] [DecidableEq P] [Fintype L]

def cost (b : ℕ) (A F : Finset P) : ℕ := if F⊆A ∧ b<F.card then 1 else 0

theorem cost_once (b : ℕ) (I : L → Finset P) (linear : ∀ l m, l≠m → (I l ∩ I m).card≤b)
    (F : Finset P) : (∑ l, cost b (I l) F)≤1 := by
  classical
  let owners := Finset.univ.filter fun l => F⊆I l ∧ b<F.card
  have one : owners.card≤1 := by
    apply Finset.card_le_one.mpr
    intro l hl m hm
    by_contra ne
    obtain ⟨sl,big⟩ := (Finset.mem_filter.mp hl).2
    have sm := (Finset.mem_filter.mp hm).2.1
    have sub : F⊆I l ∩ I m := fun p hp => Finset.mem_inter.mpr ⟨sl hp,sm hp⟩
    exact (Nat.not_le_of_lt big) ((Finset.card_le_card sub).trans (linear l m ne))
  simpa [cost,owners,Finset.sum_boole] using one

def Ledger (b : ℕ) (I : L → Finset P) (W : List (Signal P)) (k : ℕ) : Prop :=
  ∃ c : L → ℕ, (∑ l,c l)≤k ∧ ∀ l, ScaledWidth.Wide b (c l) (W.map (low I l))

theorem budget (b : ℕ) (pos : 1≤b) (I : L → Finset P) (linear : ∀ l m, l≠m → (I l ∩ I m).card≤b)
    (W : List (Signal P)) (k : ℕ) (net : Built W k) : Ledger b I W k := by
  classical
  induction net with
  | raw W raw =>
    refine ⟨fun _ => 0,by simp,?_⟩
    intro l
    apply ScaledWidth.initial
    intro j
    by_cases hj : j<W.length
    · have mem := List.getElem_mem (l := W) hj
      simpa [List.getD_eq_getElem?_getD,hj] using (raw_low I l W[j] (raw _ mem)).trans pos
    · simp [List.getD_eq_getElem?_getD,hj]
  | @sum W k net f g hf hg ih =>
    obtain ⟨c,old,widths⟩ := ih
    let h := plus f g
    let F := single h
    refine ⟨fun l => c l+cost b (I l) F,?_,?_⟩
    · simp only [Finset.sum_add_distrib]
      exact Nat.add_le_add old (cost_once b I linear F)
    · intro l
      simp only [List.map_append,List.map_cons,List.map_nil]
      change ScaledWidth.Wide b _ ((W.map (low I l))++[low I l h])
      by_cases small : (low I l h).card≤b
      · exact ScaledWidth.widen (Nat.le_add_right _ _) (ScaledWidth.small b _ _ (widths l) _ small)
      · have off : h (outside I l)=false := by
          cases q : h (outside I l) <;> first | rfl | simp [low,q] at small
        have mon := mono _ _ (Built.sum net f g hf hg) h (by simp [h])
        have insideF : F⊆I l := inside I l h mon off
        have big : b<F.card := by simpa [low,off,F,h] using (show b<(low I l h).card by omega)
        have feeOne : cost b (I l) F=1 := by simp [cost,insideF,big]
        rw [feeOne]
        obtain ⟨i,hi⟩ := get_of_mem (W.map (low I l)) _ (List.mem_map_of_mem hf)
        obtain ⟨j,hj⟩ := get_of_mem (W.map (low I l)) _ (List.mem_map_of_mem hg)
        apply ScaledWidth.join b _ _ (widths l) _ i j
        rw [hi,hj]
        have both : f (outside I l)=false ∧ g (outside I l)=false := Bool.or_eq_false_iff.mp off
        intro p hp
        simp only [low,off,both.1,both.2,Bool.false_eq_true,ite_false,single,Finset.mem_filter,
          Finset.mem_univ,true_and,Finset.mem_union] at hp ⊢
        exact Bool.or_eq_true_iff.mp hp
  | @prod W k net f g hf hg ih =>
    obtain ⟨c,old,widths⟩ := ih
    refine ⟨c,old,?_⟩
    intro l
    simp only [List.map_append,List.map_cons,List.map_nil]
    let h := times f g
    change ScaledWidth.Wide b _ ((W.map (low I l))++[low I l h])
    by_cases on : h (outside I l)=true
    · exact ScaledWidth.small b _ _ (widths l) _ (by simp [low,on])
    · have off : h (outside I l)=false := by simpa using on
      have side : f (outside I l)=false ∨ g (outside I l)=false := Bool.and_eq_false_iff.mp off
      rcases side with left | right
      · obtain ⟨i,hi⟩ := get_of_mem (W.map (low I l)) _ (List.mem_map_of_mem hf)
        apply ScaledWidth.dominated b _ _ (widths l) _ i
        rw [hi]
        intro p hp
        simp only [low,off,left,Bool.false_eq_true,ite_false,single,Finset.mem_filter,Finset.mem_univ,true_and] at hp ⊢
        exact (Bool.and_eq_true_iff.mp hp).1
      · obtain ⟨i,hi⟩ := get_of_mem (W.map (low I l)) _ (List.mem_map_of_mem hg)
        apply ScaledWidth.dominated b _ _ (widths l) _ i
        rw [hi]
        intro p hp
        simp only [low,off,right,Bool.false_eq_true,ite_false,single,Finset.mem_filter,Finset.mem_univ,true_and] at hp ⊢
        exact (Bool.and_eq_true_iff.mp hp).2

/-- One can recognize a subset of the singleton variables of each row and
accept other non-singleton inputs. Rejection on its full complement suffices. -/
theorem total (b : ℕ) (pos : 1≤b) (I : L → Finset P) (linear : ∀ l m, l≠m → (I l ∩ I m).card≤b)
    (W : List (Signal P)) (k : ℕ) (net : Built W k) (out : L → Signal P)
    (outputs : ∀ l, out l ∈ W) (reject : ∀ l, out l (outside I l)=false) :
    (∑ l, (single (out l)).card)≤b*(k+Fintype.card L) := by
  obtain ⟨c,spent,width⟩ := budget b pos I linear W k net
  calc
    _ ≤ ∑ l, b*(c l+1) := by
      apply Finset.sum_le_sum
      intro l _
      obtain ⟨j,hj⟩ := get_of_mem (W.map (low I l)) _ (List.mem_map_of_mem (outputs l))
      simpa only [hj,low,reject,Bool.false_eq_true,ite_false] using ScaledWidth.each b _ _ (width l) j
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      apply Nat.mul_le_mul_left
      simpa [Finset.sum_add_distrib] using Nat.add_le_add_right spent (Fintype.card L)

#print axioms total

end OverlapSums
