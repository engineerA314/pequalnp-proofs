import SparsePencilChart

namespace SparsePencilRoots

open Polynomial SparseNegativeRoots SparsePencilChart

noncomputable def zeros (S : Finset ℝ) (p : Polynomial ℝ) : Finset ℝ := by
  classical exact S.filter (fun x => p.eval x=0)

theorem in_zeros (S : Finset ℝ) (p : Polynomial ℝ) (x : ℝ) : x∈zeros S p ↔ x∈S ∧ p.eval x=0 := by
  classical simp [zeros]

theorem few (S : Finset ℝ) (neg : ∀ x∈S,x<0) (p : Polynomial ℝ) (nz : p≠0)
    (U : Finset ℕ) (inc : p.support⊆U) : (zeros S p).card≤U.card-1 := by
  have r := negative p nz (zeros S p) (fun x hx =>
    ⟨neg x ((in_zeros _ _ _).mp hx).1,((in_zeros _ _ _).mp hx).2⟩)
  have cap := Finset.card_le_card inc
  omega

theorem pencil_support (A B : Polynomial ℝ) (r : ℝ) :
    (A-C r*B).support⊆A.support∪B.support := by
  classical
  intro n hn
  simp only [mem_support_iff,coeff_sub,coeff_C_mul] at hn
  by_contra missed
  simp only [Finset.mem_union,not_or] at missed
  have a := notMem_support_iff.mp missed.1
  have b := notMem_support_iff.mp missed.2
  simp [a,b] at hn

theorem pencil {ι : Type} [Fintype ι] (s a b : ι → ℝ) (d : ℕ) (hd : 0<d)
    (A B : Polynomial ℝ) (hb : B≠0) (indep : ∀ r : ℝ,A-C r*B≠0)
    (live : mix s a b d A B≠0) (S : Finset ℝ) (neg : ∀ x∈S,x<0)
    (all : ∀ x∈S,(mix s a b d A B).eval x=0) :
    S.card≤d*((A.support∪B.support).card-1) := by
  classical
  let P := chart s a b d
  let R := P.roots.toFinset
  let M := (A.support∪B.support).card-1
  let fibres := fun r : ℝ => zeros S (A-C r*B)
  let poles := zeros S B
  have pn : P≠0 := chart_ne s a b d A B hb live
  have num : R.card≤P.natDegree := (Multiset.toFinset_card_le _).trans P.card_roots'
  have bound : P.natDegree≤d := chart_degree s a b d
  have bp : poles.card≤M := few S neg B hb _ Finset.subset_union_right
  have each (r : ℝ) : (fibres r).card≤M := few S neg _ (indep r) _ (pencil_support A B r)
  have cover_fibres : (R.biUnion fibres).card≤R.card*M := by
    calc _ ≤ ∑ r ∈ R,(fibres r).card := Finset.card_biUnion_le
         _ ≤ ∑ _r ∈ R,M := Finset.sum_le_sum fun r _ => each r
         _ = _ := by simp
  have contained (x : ℝ) (hx : x∈S) (out : B.eval x≠0) : x∈R.biUnion fibres := by
    have h := all x hx
    rw [nonpole s a b d A B x out] at h
    have z := (mul_eq_zero.mp h).resolve_right (pow_ne_zero _ out)
    refine Finset.mem_biUnion.mpr ⟨A.eval x/B.eval x,Multiset.mem_toFinset.mpr ((mem_roots pn).mpr z),?_⟩
    refine (in_zeros _ _ _).mpr ⟨hx,?_⟩
    simp [eval_sub,eval_mul,out]
  have general : S⊆poles∪R.biUnion fibres := by
    intro x hx
    by_cases out : B.eval x=0
    · exact Finset.mem_union_left _ ((in_zeros _ _ _).mpr ⟨hx,out⟩)
    · exact Finset.mem_union_right _ (contained x hx out)
  by_cases full : P.natDegree=d
  · by_cases nonempty : R.Nonempty
    · obtain ⟨r,hr⟩ := nonempty
      have top : P.coeff d≠0 := by rw [← full,coeff_natDegree]; exact leadingCoeff_ne_zero.mpr pn
      have subset : S⊆R.biUnion fibres := by
        intro x hx
        by_cases out : B.eval x=0
        · have h := all x hx
          rw [pole s a b d A B x out] at h
          have va : A.eval x=0 := by by_contra na; exact (mul_ne_zero top (pow_ne_zero _ na)) h
          exact Finset.mem_biUnion.mpr ⟨r,hr,(in_zeros _ _ _).mpr ⟨hx,by simp [out,va]⟩⟩
        · exact contained x hx out
      exact (Finset.card_le_card subset).trans (cover_fibres.trans (Nat.mul_le_mul_right _ (num.trans bound)))
    · have empty := Finset.not_nonempty_iff_eq_empty.mp nonempty
      have subset : S⊆poles := by simpa [empty] using general
      exact (Finset.card_le_card subset).trans (bp.trans (by simpa using Nat.mul_le_mul_right M hd))
  · have small : 1+R.card≤d := by omega
    calc S.card ≤ (poles∪R.biUnion fibres).card := Finset.card_le_card general
         _ ≤ poles.card+(R.biUnion fibres).card := Finset.card_union_le _ _
         _ ≤ M+R.card*M := Nat.add_le_add bp cover_fibres
         _ = (1+R.card)*M := by ring
         _ ≤ d*M := Nat.mul_le_mul_right _ small

#print axioms pencil

end SparsePencilRoots
