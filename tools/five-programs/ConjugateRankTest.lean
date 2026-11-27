import PermanentConjugateBound

namespace ConjugateRankTest

open Module ConjugateMatrixCore PermanentJetOnes ComplexConjugate

variable {p q : ℕ}

@[simp] theorem bar_bar (x : Mat p q) : bar (bar x)=x := by funext a; simp [bar]

def imageBar (L : Submodule ℂ (Mat p q)) : Submodule ℂ (Mat p q) where
  carrier := {x | bar x∈L}
  zero_mem' := by change bar (0 : Mat p q)∈L; simp
  add_mem' := by intro x y hx hy; change bar (x+y)∈L; rw [bar_add]; exact L.add_mem hx hy
  smul_mem' := by intro c x hx; change bar (c • x)∈L; rw [bar_smul]; exact L.smul_mem _ hx

theorem core_inter (L : Submodule ℂ (Mat p q)) : core L=L⊓imageBar L := rfl

noncomputable def asReal (L : Submodule ℂ (Mat p q)) : L ≃ₗ[ℝ] imageBar L where
  toFun x := ⟨bar x,by change bar (bar x.val)∈L; simpa using x.property⟩
  invFun x := ⟨bar x,x.property⟩
  left_inv x := Subtype.ext (bar_bar _)
  right_inv x := Subtype.ext (bar_bar _)
  map_add' x y := Subtype.ext (bar_add _ _)
  map_smul' c x := by
    apply Subtype.ext
    funext a
    change conj (c • x.val a)=c • conj (x.val a)
    simp [Complex.real_smul]

theorem same_dimension (L : Submodule ℂ (Mat p q)) : finrank ℂ (imageBar L)=finrank ℂ L := by
  have real := (asReal L).finrank_eq
  have x := Module.finrank_mul_finrank ℝ ℂ L
  have y := Module.finrank_mul_finrank ℝ ℂ (imageBar L)
  rw [Complex.finrank_real_complex] at x y
  omega

theorem rank_identity (L : Submodule ℂ (Mat p q)) :
    finrank ℂ (L⊔imageBar L : Submodule ℂ _)+finrank ℂ (core L)=2*finrank ℂ L := by
  rw [core_inter,Submodule.finrank_sup_add_finrank_inf_eq,same_dimension,two_mul]

theorem flat_rank (n : ℕ) (L : Submodule ℂ (Mat (n+1) (n+1))) (h : flat L) :
    2*finrank ℂ L≤finrank ℂ (L⊔imageBar L : Submodule ℂ _)+2*n := by
  have id := rank_identity L
  have cap := PermanentConjugateBound.core_bound n L h
  omega

#print axioms rank_identity
#print axioms flat_rank

end ConjugateRankTest
