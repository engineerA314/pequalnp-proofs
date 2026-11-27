import ConjugateRankTest

namespace PermanentRealWitness

open Finset PermanentJetOnes ConjugateMatrixCore PermanentConjugateBound ConjugateRankTest
open ComplexConjugate Module

variable {p q : ℕ}

theorem centered_smul {x : Mat p q} (h : centered x) (c : ℂ) : centered (c • x) := by
  constructor <;> intro i <;> simp [Pi.smul_apply,smul_eq_mul,← Finset.mul_sum,h.1,h.2]

theorem real_center {L : Submodule ℂ (Mat p q)} {x : Mat p q} (hx : x∈core L)
    (z : x≠0) (cx : centered x) :
    ∃ t∈L,t≠0 ∧ bar t=t ∧ centered t := by
  have sum : x+bar x∈L := L.add_mem hx.1 hx.2
  by_cases on : x+bar x=0
  · have bx : bar x= -x := eq_neg_of_add_eq_zero_left (add_comm x (bar x) ▸ on)
    refine ⟨Complex.I • x,L.smul_mem _ hx.1,smul_ne_zero Complex.I_ne_zero z,?_,centered_smul cx _⟩
    rw [bar_smul,bx]
    simp
  · exact ⟨_,sum,on,by rw [bar_add,bar_bar,add_comm],centered_add cx (centered_bar cx)⟩

theorem energy {x : Mat p q} (cx : centered x) (real : bar x=x) :
    disjointSum x = ↑(∑ i,∑ j,Complex.normSq (x (i,j))) := by
  unfold disjointSum
  rw [PEqualNP.Gct.Helpers.RealLevel.ident]
  simp only [cx.1,cx.2,Finset.sum_const_zero,zero_pow (by decide : 2≠0),sub_zero,zero_add]
  simp only [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← Complex.mul_conj,pow_two]
  exact congrArg (x (i,j)*·) (congrFun real (i,j)).symm

theorem positive_energy {x : Mat p q} (nz : x≠0) :
    0<∑ i,∑ j,Complex.normSq (x (i,j)) := by
  have nonneg : 0≤∑ i,∑ j,Complex.normSq (x (i,j)) := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  by_contra! nonpos
  have zero := le_antisymm nonpos nonneg
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _)] at zero
  apply nz
  funext ⟨i,j⟩
  have row := zero i (mem_univ _)
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg _)] at row
  exact Complex.normSq_eq_zero.mp (row j (mem_univ _))

theorem certificate (n : ℕ) (L : Submodule ℂ (Mat (n+1) (n+1)))
    (rankFail : finrank ℂ (L⊔imageBar L : Submodule ℂ _)+2*n < 2*finrank ℂ L) :
    (∃ t∈L,total t≠0) ∨ ∃ t∈L,centered t ∧ bar t=t ∧
      ∃ a : ℝ,0<a ∧ disjointSum t=(a : ℂ) := by
  classical
  by_cases one : ∃ t∈L,total t≠0
  · exact Or.inl one
  · right
    push Not at one
    let F := (projection n n).domRestrict (core L)
    have high : 2*n<finrank ℂ (core L) := by have e := rank_identity L; omega
    have no : ¬Function.Injective F := by
      intro injects
      have bound := LinearMap.finrank_le_finrank_of_injective injects
      have short : finrank ℂ (core L)≤n+n := by simpa [finrank_prod] using bound
      omega
    rw [← LinearMap.ker_eq_bot,LinearMap.ker_eq_bot'] at no
    push Not at no
    obtain ⟨⟨t,ht⟩,h,nz⟩ := no
    have row (i : Fin n) : ∑ j,t (i.castSucc,j)=0 := congrFun (congrArg Prod.fst h) i
    have col (j : Fin n) : ∑ i,t (i,j.castSucc)=0 := congrFun (congrArg Prod.snd h) j
    have tot : ∑ i,∑ j,t (i,j)=0 := one _ ht.1
    have swap : ∑ j,∑ i,t (i,j)=0 := by rw [sum_comm]; exact tot
    obtain ⟨w,hw,wz,real,cw⟩ := real_center ht (fun z => nz (Subtype.ext z))
      ⟨all_zero _ tot row,all_zero _ swap col⟩
    exact ⟨w,hw,cw,real,_,positive_energy wz,energy cw real⟩

#print axioms certificate

end PermanentRealWitness
