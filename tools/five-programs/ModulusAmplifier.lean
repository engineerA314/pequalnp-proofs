import Mathlib

namespace ModulusAmplifier

open Polynomial

abbrev ZPoly := Polynomial ℤ

noncomputable def blend : ℕ → ℕ → ZPoly
  | 0,_ => 1
  | _+1,0 => 0
  | a+1,b+1 => X*blend a (b+1)+(1-X)*blend (a+1) b
termination_by a b => a+b

theorem one_sub_X_degree : (1-X : ZPoly).natDegree=1 := by
  have h : (1-X : ZPoly)=-(X-C 1) := by simp
  rw [h,natDegree_neg,natDegree_X_sub_C]

theorem interpolate : ∀ a b : ℕ, X^a ∣ blend a b ∧ (1-X)^b ∣ 1-blend a b ∧
    (blend a b).natDegree≤a+b-1
  | 0,b => by simp [blend]
  | a+1,0 => by simp [blend]
  | a+1,b+1 => by
    obtain ⟨la,lb,ld⟩ := interpolate a (b+1)
    obtain ⟨ra,rb,rd⟩ := interpolate (a+1) b
    rw [blend]
    refine ⟨?_,?_,?_⟩
    · apply dvd_add
      · obtain ⟨u,hu⟩ := la
        exact ⟨u,by rw [hu,pow_succ]; ring⟩
      · exact dvd_mul_of_dvd_right ra _
    · have one : 1-(X*blend a (b+1)+(1-X)*blend (a+1) b)=
          X*(1-blend a (b+1))+(1-X)*(1-blend (a+1) b) := by ring
      rw [one]
      apply dvd_add
      · exact dvd_mul_of_dvd_right lb _
      · obtain ⟨v,hv⟩ := rb
        exact ⟨v,by rw [hv,pow_succ]; ring⟩
    · apply natDegree_add_le_of_degree_le
      · have h := natDegree_mul_le (p:=X) (q:=blend a (b+1))
        rw [natDegree_X] at h
        omega
      · have h := natDegree_mul_le (p:=(1-X:ZPoly)) (q:=blend (a+1) b)
        rw [one_sub_X_degree] at h
        omega
termination_by a b => a+b

def Amplifies (a b : ℕ) (F : ZPoly) := ∀ (m : ℕ) (x : ℤ),
  ((m:ℤ)∣x → (m:ℤ)^a∣F.eval x) ∧ ((m:ℤ)∣x-1 → (m:ℤ)^b∣F.eval x-1)

theorem sufficient (a b : ℕ) (F : ZPoly) (left : X^a ∣ F) (right : (1-X)^b ∣ 1-F) :
    Amplifies a b F := by
  intro m x
  constructor
  · intro hx
    obtain ⟨u,hu⟩ := left
    have eq := congrArg (Polynomial.eval x) hu
    simp only [eval_mul,eval_pow,eval_X] at eq
    rw [eq]
    exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd hx _) _
  · intro hx
    obtain ⟨v,hv⟩ := right
    have eq := congrArg (Polynomial.eval x) hv
    simp only [eval_mul,eval_pow,eval_sub,eval_X,eval_one] at eq
    have div : (m:ℤ)∣1-x := by simpa [neg_sub] using (dvd_neg.mpr hx)
    have he : (m:ℤ)^b ∣ 1-F.eval x := eq ▸ dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd div _) _
    simpa [neg_sub] using (dvd_neg.mpr he)

theorem universal (a b : ℕ) : Amplifies a b (blend a b) :=
  sufficient _ _ _ (interpolate a b).1 (interpolate a b).2.1

theorem equal_precision (m k : ℕ) (_ : 1≤k) : ∃ F : ZPoly,F.natDegree≤2*k-1 ∧
    ∀ x : ℤ, ((m:ℤ)∣x → (m:ℤ)^k∣F.eval x) ∧ ((m:ℤ)∣x-1 → (m:ℤ)^k∣F.eval x-1) :=
  ⟨blend k k,by simpa [two_mul] using (interpolate k k).2.2,universal k k m⟩

#print axioms equal_precision

end ModulusAmplifier
