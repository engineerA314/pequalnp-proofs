import ModulusAmplifier

namespace ModulusConverse

open Polynomial ModulusAmplifier

theorem all_dvd (z : ℤ) (h : ∀ m : ℕ,0 < m → (m:ℤ)∣z) : z=0 := by
  by_contra ne
  have d := Int.natCast_dvd.mp (h (z.natAbs+1) (by omega))
  have hsize := Nat.le_of_dvd (Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr ne)) d
  omega

theorem at_zero (a : ℕ) (F : ZPoly) (sample : ∀ m : ℕ,0 < m → (m:ℤ)^a∣F.eval (m:ℤ)) : X^a∣F := by
  induction a generalizing F with
  | zero => simp
  | succ a ih =>
    have c : F.coeff 0=0 := by
      apply all_dvd
      intro m hm
      have d : (m:ℤ)∣F.eval (m:ℤ) := (by simp : (m:ℤ)∣(m:ℤ)^(a+1)).trans (sample m hm)
      have diff : (m:ℤ)∣F.eval (m:ℤ)-F.coeff 0 := by simpa [coeff_zero_eq_eval_zero] using sub_dvd_eval_sub (m:ℤ) 0 F
      simpa using dvd_sub d diff
    obtain ⟨Q,eq⟩ := X_dvd_iff.mpr c
    have smaller (m : ℕ) (hm : 0 < m) : (m:ℤ)^a∣Q.eval (m:ℤ) := by
      have larger := sample m hm
      rw [eq,eval_mul,eval_X,pow_succ'] at larger
      exact (mul_dvd_mul_iff_left (by exact_mod_cast hm.ne' : (m:ℤ)≠0)).mp larger
    obtain ⟨R,hR⟩ := ih Q smaller
    exact ⟨R,by rw [eq,hR,pow_succ']; ring⟩

theorem necessary (a b : ℕ) (F : ZPoly) (amp : Amplifies a b F) :
    X^a∣F ∧ (1-X)^b∣1-F := by
  refine ⟨at_zero a F (fun m _ => (amp m m).1 dvd_rfl),?_⟩
  let G := (1-F).comp (1-X)
  have h : X^b∣G := by
    apply at_zero
    intro m _
    have d := (amp m (1-m)).2 (by simp)
    have dd := dvd_neg.mpr d
    simpa [G,eval_comp,neg_sub] using dd
  obtain ⟨R,eq⟩ := h
  refine ⟨R.comp (1-X),?_⟩
  have sr : (1-X : ZPoly).comp (1-X)=X := by simp
  have e := congrArg (fun P : ZPoly => P.comp (1-X)) eq
  simpa [G,comp_assoc,sr,mul_comp,pow_comp] using e

theorem iff_multiplicity (a b : ℕ) (F : ZPoly) :
    Amplifies a b F ↔ X^a∣F ∧ (1-X)^b∣1-F :=
  ⟨necessary _ _ _,fun h => sufficient _ _ _ h.1 h.2⟩

theorem endpoints (a b : ℕ) (F : ZPoly) (amp : Amplifies (a+1) (b+1) F) :
    F.eval 0=0 ∧ F.eval 1=1 := by
  obtain ⟨left,right⟩ := necessary _ _ _ amp
  have z := eval_dvd (x:=(0:ℤ)) left
  have o := eval_dvd (x:=(1:ℤ)) right
  simp at z o
  exact ⟨z,by omega⟩

theorem min_degree (a b : ℕ) (F : ZPoly) (amp : Amplifies (a+1) (b+1) F) :
    a+b+1≤F.natDegree := by
  obtain ⟨left,right⟩ := necessary _ _ _ amp
  obtain ⟨zero,one⟩ := endpoints _ _ _ amp
  have deriv : F.derivative≠0 := by
    intro z
    have con := eq_C_of_derivative_eq_zero z
    have f0 := congrArg (eval (0:ℤ)) con
    have f1 := congrArg (eval (1:ℤ)) con
    simp only [eval_C,zero,one] at f0 f1
    omega
  have l : X^a∣F.derivative := by simpa using pow_sub_one_dvd_derivative_of_pow_dvd left
  have r : (1-X)^b∣F.derivative := by simpa using pow_sub_one_dvd_derivative_of_pow_dvd right
  have cop : IsCoprime (X : ZPoly) (1-X) := ⟨1,1,by ring⟩
  have all := natDegree_le_of_dvd (cop.pow.mul_dvd l r) deriv
  have nz : (1-X : ZPoly)≠0 := by intro h; have hh:=one_sub_X_degree; rw [h] at hh; simp at hh
  rw [natDegree_mul (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ nz),natDegree_pow,natDegree_pow,natDegree_X,one_sub_X_degree] at all
  have lt := natDegree_derivative_lt (derivative_ne_zero.mp deriv)
  omega

theorem optimal (a b : ℕ) : (blend (a+1) (b+1)).natDegree=a+b+1 := by
  have lo := min_degree a b _ (universal _ _)
  have hi := (interpolate (a+1) (b+1)).2.2
  omega

#print axioms iff_multiplicity
#print axioms min_degree
#print axioms optimal

end ModulusConverse
