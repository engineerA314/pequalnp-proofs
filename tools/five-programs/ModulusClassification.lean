import ModulusConverse

namespace ModulusClassification

open Polynomial ModulusAmplifier ModulusConverse

theorem all_solutions (a b : ℕ) (F : ZPoly) : Amplifies a b F ↔
    ∃ H : ZPoly,F=blend a b+X^a*(1-X)^b*H := by
  let U := blend a b
  have v := interpolate a b
  have cop : IsCoprime (X : ZPoly) (1-X) := ⟨1,1,by ring⟩
  constructor
  · intro h
    obtain ⟨left,right⟩ := necessary a b F h
    have la : X^a∣F-U := dvd_sub left v.1
    have rb : (1-X)^b∣F-U := by
      have w := dvd_sub v.2.1 right
      simpa only [sub_sub_sub_cancel_left] using w
    obtain ⟨H,hH⟩ := cop.pow.mul_dvd la rb
    exact ⟨H,by change F=U+_; rw [← hH]; ring⟩
  · rintro ⟨H,rfl⟩
    apply sufficient
    · exact dvd_add v.1 ((dvd_mul_right _ _).mul_right H)
    · have eq : 1-(U+X^a*(1-X)^b*H)=(1-U)-(X^a*(1-X)^b*H) := by ring
      rw [show blend a b=U from rfl,eq]
      exact dvd_sub v.2.1 ((dvd_mul_left _ _).mul_right H)

theorem unique (a b : ℕ) (F : ZPoly) (amp : Amplifies a b F) (short : F.natDegree<a+b) :
    F=blend a b := by
  obtain ⟨H,eq⟩ := (all_solutions a b F).mp amp
  by_contra different
  have nz : F-blend a b≠0 := sub_ne_zero.mpr different
  have dvd : X^a*(1-X)^b∣F-blend a b := ⟨H,by rw [eq]; ring⟩
  have bound := natDegree_le_of_dvd dvd nz
  have ne : (1-X : ZPoly)≠0 := by intro h; have n:=one_sub_X_degree; rw [h] at n; simp at n
  rw [natDegree_mul (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ ne),natDegree_pow,natDegree_pow,natDegree_X,one_sub_X_degree] at bound
  have upper := natDegree_sub_le F (blend a b)
  have size := (interpolate a b).2.2
  omega

theorem modulus_two (x : ℤ) : (2∣x → 4∣x^2) ∧ (2∣x-1 → 4∣x^2-1) := by
  constructor
  · rintro ⟨k,rfl⟩
    exact ⟨k^2,by ring⟩
  · rintro ⟨k,h⟩
    have eq : x=2*k+1 := by omega
    exact ⟨k^2+k,by rw [eq]; ring⟩

#print axioms all_solutions
#print axioms unique

end ModulusClassification
