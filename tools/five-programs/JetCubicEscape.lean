import JetMaximalExample
import PermutationPairAverage

namespace JetCubicEscape

open Finset PermanentJetOnes ConjugateMatrixCore JetIsotropicFrame JetFrameCoefficients
open JetMaximalExample PEqualNP.Gct.Helpers.LevelLow PEqualNP.Gct MvPolynomial

def a (k : ℕ) := three k 1 1 (-2)
noncomputable def direction (k : ℕ) : Mat (k+3) (k+3) := fun p => a k p.1+u k p.1*a k p.2

theorem sum_a (k : ℕ) : ∑ i,a k i=0 := by rw [a,sum_three]; norm_num
theorem square_a (k : ℕ) : ∑ i,(a k i)^2=6 := by
  simp only [pow_two]
  change innerV (a k) (a k)=6
  rw [a,inner_three]; norm_num

theorem restrict_exact {k : ℕ} (x : Vec (k+1)) (h : ∑ i,x i=0) :
    rowPart (fun j => x j.castSucc)=x := by
  funext i
  induction i using Fin.lastCases with
  | last =>
    rw [Fin.sum_univ_castSucc] at h
    rw [rowPart_last]
    linear_combination -h
  | cast j => simp

theorem member (k : ℕ) : direction k∈exampleSpace k := by
  refine ⟨⟨fun j => a k j.castSucc,0⟩,?_⟩
  have zero : rowPart (0 : Vec (k+2))=0 := restrict_exact (0 : Vec (k+3)) (by simp)
  funext ⟨i,j⟩
  simp [embed,array,outer,direction,restrict_exact _ (sum_a k),zero]

theorem at_row (k : ℕ) (σ : Equiv.Perm (Fin (k+3))) (x : ℂ) :
    (Finset.prod Finset.univ (fun i : Fin (k+3) => (1+x*direction k (σ i,i)))) =
      (1-2*x)*((1+x)+x*scale k 2*a k (σ.symm 0))*((1+x)-x*scale k 2*a k (σ.symm 1)) := by
  rw [← Equiv.prod_comp σ.symm]
  simp only [Equiv.apply_symm_apply,direction,Fin.prod_univ_succ]
  have row0 : a k 0=1 := rfl
  have row1 : a k (0 : Fin (k+2)).succ=1 := rfl
  have row2 : a k (0 : Fin (k+1)).succ.succ= -2 := rfl
  have rowOther (i : Fin k) : a k i.succ.succ.succ=0 := rfl
  have u0 : u k 0=scale k 2 := rfl
  have u1 : u k (0 : Fin (k+2)).succ= -scale k 2 := rfl
  have u2 : u k (0 : Fin (k+1)).succ.succ=0 := rfl
  have uOther (i : Fin k) : u k i.succ.succ.succ=0 := rfl
  simp only [row0,row1,row2,rowOther,u0,u1,u2,uOther,zero_mul,add_zero,mul_zero,
    Finset.prod_const_one,mul_one]
  change _ = (1-2*x)*((1+x)+x*scale k 2*a k (σ.symm 0))*((1+x)-x*scale k 2*a k (σ.symm (0 : Fin (k+2)).succ))
  ring

theorem exact_line (k : ℕ) (x : ℂ) :
    eval (fun p => 1+x*direction k p) (permPoly ℂ (k+3)) =
      ((k+3).factorial : ℂ)*(1-8*x^3) := by
  classical
  simp only [permPoly,Matrix.permanent,Matrix.mvPolynomialX_apply,eval_sum,eval_prod,eval_X]
  simp_rw [at_row, mul_assoc (1-2*x)]
  rw [← mul_sum]
  let f := fun (i j : Fin (k+3)) => ((1+x)+x*scale k 2*a k i)*((1+x)-x*scale k 2*a k j)
  change (1-2*x)*(∑ σ : Equiv.Perm (Fin (k+3)), f (σ⁻¹ 0) (σ⁻¹ 1))=_
  have inv := Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin (k+3)))) (fun σ : Equiv.Perm (Fin (k+3)) => f (σ 0) (σ 1))
  rw [show (∑ σ : Equiv.Perm (Fin (k+3)), f (σ⁻¹ 0) (σ⁻¹ 1))=∑ σ : Equiv.Perm (Fin (k+3)), f (σ 0) (σ 1) from inv]
  rw [PermutationPairAverage.two_positions (k+1) 0 1 (by intro e; have bad := congrArg Fin.val e; simpa using bad)]
  unfold f
  rw [PermutationPairAverage.off_diag (k+1) (a k) (sum_a k),square_a]
  have half := scale_eq k 2 (by norm_num)
  rw [Nat.factorial_succ (k+2),Nat.factorial_succ (k+1)]
  push_cast at *
  linear_combination (1-2*x)*((k+1).factorial : ℂ)*3*x^2*half

theorem never_flat (k : ℕ) : ¬flat (exampleSpace k) := by
  intro level
  have z := level _ ((exampleSpace k).smul_mem (1/2 : ℂ) (member k))
  change eval (fun p => 1+(1/2 : ℂ)*direction k p) (permPoly ℂ (k+3))=_ at z
  rw [exact_line] at z
  norm_num at z
  exact (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _) : ((k+3).factorial : ℂ)≠0) z.symm

#print axioms exact_line
#print axioms never_flat

end JetCubicEscape
