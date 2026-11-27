import JetIsotropicFrame

namespace JetFrameCoefficients

open JetIsotropicFrame Finset ComplexConjugate

def three (k : ℕ) (a b c : ℂ) : Vec (k+3) :=
  Fin.cases a (Fin.cases b (Fin.cases c (fun _ => 0)))

theorem sum_three (k : ℕ) (a b c : ℂ) : ∑ i,three k a b c i=a+b+c := by
  simp [three,Fin.sum_univ_succ]; ring

theorem inner_three (k : ℕ) (a b c x y z : ℂ) :
    innerV (three k a b c) (three k x y z)=a*x+b*y+c*z := by
  simp [three,innerV,Fin.sum_univ_succ]; ring

noncomputable def scale (k : ℕ) (d : ℝ) : ℂ := ↑(Real.sqrt (((k : ℝ)+3)*(k+2)/d))
noncomputable def u (k : ℕ) := three k (scale k 2) (-scale k 2) 0
noncomputable def v (k : ℕ) := three k (scale k 6) (scale k 6) (-2*scale k 6)

theorem scale_eq (k : ℕ) (d : ℝ) (hd : 0<d) :
    (d : ℂ)*scale k d^2=((k : ℂ)+3)*(k+2) := by
  have h := Real.sq_sqrt (show 0 ≤ ((k : ℝ)+3)*(k+2)/d by positivity)
  have realEq : d*Real.sqrt (((k : ℝ)+3)*(k+2)/d)^2=((k : ℝ)+3)*(k+2) := by
    rw [h]; field_simp
  unfold scale
  exact_mod_cast realEq

theorem instance_frame (k : ℕ) : Frame (k+3) (u k) (v k) := by
  constructor
  · rw [u,sum_three]; ring
  · rw [v,sum_three]; ring
  · rw [u,v,inner_three]; ring
  · rw [u,inner_three]
    have h := scale_eq k 2 (by norm_num)
    push_cast at *
    linear_combination h
  · rw [v,inner_three]
    have h := scale_eq k 6 (by norm_num)
    push_cast at *
    linear_combination h

theorem conj_three (k : ℕ) (a b c : ℂ) (i : Fin (k+3)) :
    conj (three k a b c i)=three k (conj a) (conj b) (conj c) i := by
  induction i using Fin.cases with
  | zero => rfl
  | succ i => induction i using Fin.cases with
    | zero => rfl
    | succ i => induction i using Fin.cases with
      | zero => rfl
      | succ i => simp [three]

@[simp] theorem real_u (k : ℕ) (i) : conj (u k i)=u k i := by simp [u,conj_three,scale]
@[simp] theorem real_v (k : ℕ) (i) : conj (v k i)=v k i := by simp [v,conj_three,scale,map_ofNat]

#print axioms instance_frame

end JetFrameCoefficients
