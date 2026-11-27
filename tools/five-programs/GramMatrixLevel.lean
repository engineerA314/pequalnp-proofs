import GramPermanent
import Mathlib.Analysis.Matrix.Order

namespace GramMatrixLevel

open scoped MatrixOrder ComplexOrder ComplexConjugate
open MvPolynomial PermanentSupport GramPermanent
variable {n : ℕ}

noncomputable def along (A : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) : ℂ :=
  eval (fun p : Fin n × Fin n => 1+(t : ℂ)*A p.1 p.2) (PEqualNP.Gct.permPoly ℂ n)

theorem gram_along (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    along (star X*X) t=value (fun i j => conj (X i j)) (dual (fun i j => conj (X i j)))
      (fun _ => (t : ℂ)) := by
  apply congrArg (fun g => eval g (PEqualNP.Gct.permPoly ℂ n))
  funext p
  simp [Matrix.mul_apply,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,
    dual,Finset.mul_sum,mul_assoc]

theorem strict_psd (A : Matrix (Fin n) (Fin n) ℂ) (hp : A.PosSemidef) (nz : A≠0)
    (t : ℝ) (ht : 0<t) : (n.factorial : ℝ)<(along A t).re := by
  obtain ⟨X,hX⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hp.nonneg
  have some_entry : ∃ i j,X i j≠0 := by
    by_contra! zero
    have z : X=0 := by ext i j; exact zero i j
    exact nz (by simp [hX,z])
  obtain ⟨i,j,entry⟩ := some_entry
  rw [hX,gram_along]
  exact GramPermanent.strict _ _ (fun _ => ht) i j (by simpa using entry)

theorem real_value (A : Matrix (Fin n) (Fin n) ℂ) (hp : A.PosSemidef) (t : ℝ) :
    (along A t).im=0 := by
  obtain ⟨X,rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hp.nonneg
  rw [gram_along,GramPermanent.square_sum]
  rfl

theorem one_probe (A : Matrix (Fin n) (Fin n) ℂ) (hp : A.PosSemidef) (t : ℝ) (ht : 0<t) :
    along A t=(n.factorial : ℂ) ↔ A=0 := by
  constructor
  · intro eq
    by_contra nz
    have bound := strict_psd A hp nz t ht
    rw [eq] at bound
    simp at bound
  · rintro rfl
    change MvPolynomial.eval _ _=_
    simp [PEqualNP.Gct.permPoly,Matrix.permanent,Matrix.mvPolynomialX_apply,Fintype.card_perm]

#print axioms strict_psd
#print axioms one_probe

end GramMatrixLevel
