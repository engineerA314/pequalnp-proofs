import ConjugateMatrixCore

namespace JetIsotropicFrame

open Finset PermanentJetOnes ConjugateMatrixCore

abbrev Vec (n : ℕ) := Fin n → ℂ
variable {n : ℕ}

def innerV (a b : Vec n) := ∑ i,a i*b i
def outer (a b : Vec n) : Mat n n := fun p => a p.1*b p.2

theorem dot_outer (a b c d : Vec n) : dot (outer a b) (outer c d)=innerV a c*innerV b d := by
  unfold dot outer innerV
  rw [Finset.sum_mul]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum]
  exact sum_congr rfl fun j _ => by ring

theorem dot_add_left (x y z : Mat n n) : dot (x+y) z=dot x z+dot y z := by
  simp [dot,add_mul,sum_add_distrib]
theorem dot_add_right (x y z : Mat n n) : dot x (y+z)=dot x y+dot x z := by
  simp [dot,mul_add,sum_add_distrib]

@[simp] theorem innerV_one (a : Vec n) : innerV a 1=∑ i,a i := by simp [innerV]
@[simp] theorem one_innerV (a : Vec n) : innerV 1 a=∑ i,a i := by simp [innerV]
theorem innerV_comm (a b : Vec n) : innerV a b=innerV b a := by simp [innerV,mul_comm]

def array (u v a b : Vec n) := outer a 1+outer 1 b+outer u a+outer v b

structure Frame (n : ℕ) (u v : Vec n) : Prop where
  usum : ∑ i,u i=0
  vsum : ∑ i,v i=0
  cross : innerV u v=0
  uu : innerV u u=(n : ℂ)*((n : ℂ)-1)
  vv : innerV v v=(n : ℂ)*((n : ℂ)-1)

theorem row_sum (u v a b : Vec n) (ha : ∑ i,a i=0) (hb : ∑ i,b i=0) (i : Fin n) :
    ∑ j,array u v a b (i,j)=(n : ℂ)*a i := by
  simp [array,outer,Finset.sum_add_distrib,← Finset.mul_sum,ha,hb]

theorem col_sum (u v a b : Vec n) (fr : Frame n u v) (ha : ∑ i,a i=0) (j : Fin n) :
    ∑ i,array u v a b (i,j)=(n : ℂ)*b j := by
  simp [array,outer,Finset.sum_add_distrib,← Finset.sum_mul,ha,fr.usum,fr.vsum]

theorem energy (u v a b : Vec n) (fr : Frame n u v) (ha : ∑ i,a i=0) (hb : ∑ i,b i=0) :
    dot (array u v a b) (array u v a b)=(n : ℂ)^2*(innerV a a+innerV b b) := by
  have hvu : innerV v u=0 := (innerV_comm v u).trans fr.cross
  simp [array,dot_add_left,dot_add_right,dot_outer,ha,hb,fr.usum,fr.vsum,fr.cross,hvu,fr.uu,fr.vv]
  ring

theorem conditions (u v a b : Vec n) (fr : Frame n u v) (ha : ∑ i,a i=0) (hb : ∑ i,b i=0) :
    total (array u v a b)=0 ∧ disjointSum (array u v a b)=0 := by
  let t := array u v a b
  have ht : total t=0 := by simp [t,total,row_sum _ _ _ _ ha hb,← Finset.mul_sum,ha]
  refine ⟨ht,?_⟩
  change disjointSum t=0
  unfold disjointSum
  rw [PEqualNP.Gct.Helpers.RealLevel.ident]
  have et : (∑ i,∑ j,t (i,j)^2)=(n : ℂ)^2*(innerV a a+innerV b b) := by
    simpa only [t,dot,pow_two] using energy u v a b fr ha hb
  change (total t)^2 - _ - _ + _ = 0
  rw [ht,et]
  simp only [t,row_sum _ _ _ _ ha hb,col_sum _ _ _ _ fr ha,mul_pow,← Finset.mul_sum]
  simp only [innerV,← pow_two]
  ring

#print axioms conditions

end JetIsotropicFrame
