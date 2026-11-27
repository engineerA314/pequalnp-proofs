import PermanentRealWitness

namespace PermanentLineProbes

open Finset Polynomial PermanentJetOnes ConjugateRankTest Module PEqualNP.Gct

noncomputable def line {n : ℕ} (t : Mat n n) : Polynomial ℂ :=
  ∑ σ : Equiv.Perm (Fin n),∏ i,(1+Polynomial.C (t (σ i,i))*X)

theorem evaluation {n : ℕ} (t : Mat n n) (s : ℂ) :
    (line t).eval s = MvPolynomial.eval (fun p => 1+s*t p) (permPoly ℂ n) := by
  simp only [line,permPoly,Matrix.permanent,Matrix.mvPolynomialX_apply,
    Polynomial.eval_finsetSum,Polynomial.eval_prod,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_one,Polynomial.eval_C,Polynomial.eval_X,MvPolynomial.eval_sum,
    MvPolynomial.eval_prod,MvPolynomial.eval_X]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.prod_congr rfl
  intro i _
  rw [mul_comm]

theorem degree {n : ℕ} (t : Mat n n) : (line t).natDegree≤n := by
  unfold line
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ _
  apply (Polynomial.natDegree_prod_le _ _).trans
  calc
    _ ≤ ∑ _i : Fin n,1 := by
      apply Finset.sum_le_sum
      intro i _
      apply (Polynomial.natDegree_add_le _ _).trans
      exact max_le (by simp) ((Polynomial.natDegree_mul_le).trans (by simp))
    _ = n := by simp

theorem all_of_grid {n : ℕ} (t : Mat n n) (pass : ∀ i : Fin (n+1),
    MvPolynomial.eval (fun p => 1+(i.val : ℂ)*t p) (permPoly ℂ n)=(n.factorial : ℂ)) :
    ∀ s : ℂ,MvPolynomial.eval (fun p => 1+s*t p) (permPoly ℂ n)=(n.factorial : ℂ) := by
  have inj : Function.Injective (fun i : Fin (n+1) => (i.val : ℂ)) := fun i j h => Fin.ext (by change (i.val : ℂ)=(j.val : ℂ) at h; exact_mod_cast h)
  have poly := Polynomial.eq_of_natDegree_lt_card_of_eval_eq (line t) (C (n.factorial : ℂ)) inj
    (fun i => by simpa only [Polynomial.eval_C,evaluation] using pass i)
    (by have := degree t; simp only [Polynomial.natDegree_C,_root_.max_zero,Fintype.card_fin]; omega)
  intro s
  rw [←evaluation,poly,Polynomial.eval_C]

theorem span_flat {n : ℕ} (t : Mat n n) (constant : ∀ s : ℂ,MvPolynomial.eval (fun p => 1+s*t p)
    (permPoly ℂ n)=(n.factorial : ℂ)) : flat (Submodule.span ℂ {t}) := by
  intro w hw
  obtain ⟨s,rfl⟩ := Submodule.mem_span_singleton.mp hw
  exact constant s

theorem find {k : ℕ} (t : Mat (k+2) (k+2)) (jet : total t≠0 ∨ disjointSum t≠0) :
    ∃ i : Fin (k+3), MvPolynomial.eval (fun p => 1+(i.val : ℂ)*t p) (permPoly ℂ (k+2))≠((k+2).factorial : ℂ) := by
  by_contra! none
  let S := Submodule.span ℂ ({t} : Set _)
  have mem : t∈S := Submodule.subset_span (by simp)
  have flatS := span_flat t (all_of_grid t none)
  exact jet.elim (fun h => h (linear_condition (k+1) S flatS t mem)) (fun h => h (quadratic_condition k S flatS t mem))

theorem rank_witness (k : ℕ) (L : Submodule ℂ (Mat (k+2) (k+2)))
    (fail : finrank ℂ (L⊔imageBar L : Submodule ℂ _)+2*(k+1)<2*finrank ℂ L) :
    ∃ t∈L,∃ i : Fin (k+3),MvPolynomial.eval (fun p => 1+(i.val : ℂ)*t p)
      (permPoly ℂ (k+2))≠((k+2).factorial : ℂ) := by
  rcases PermanentRealWitness.certificate (k+1) L fail with ⟨t,ht,one⟩|⟨t,ht,_,_,a,ha,eq⟩
  · exact ⟨t,ht,find t (Or.inl one)⟩
  · exact ⟨t,ht,find t (Or.inr (eq ▸ (Complex.ofReal_ne_zero.mpr ha.ne')))⟩

#print axioms all_of_grid
#print axioms rank_witness

end PermanentLineProbes
