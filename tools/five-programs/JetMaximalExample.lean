import JetFrameCoefficients
import PermanentConjugateBound
import PEqualNP.Gct.Helpers.LevelLow

namespace JetMaximalExample

open Finset PermanentJetOnes ConjugateMatrixCore JetIsotropicFrame JetFrameCoefficients
open PEqualNP.Gct.Helpers.LevelLow ComplexConjugate Module

theorem ext_add {k : ℕ} (x y : Vec k) : rowPart (x+y)=rowPart x+rowPart y := by
  funext i
  induction i using Fin.lastCases with
  | last => simp [sum_add_distrib,add_comm]
  | cast j => simp

theorem ext_smul {k : ℕ} (c : ℂ) (x : Vec k) : rowPart (c • x)=c • rowPart x := by
  funext i
  induction i using Fin.lastCases with
  | last => simp [mul_sum]
  | cast j => simp

theorem ext_bar {k : ℕ} (x : Vec k) (i : Fin (k+1)) :
    rowPart (fun j => conj (x j)) i=conj (rowPart x i) := by
  induction i using Fin.lastCases with
  | last => simp
  | cast j => simp

noncomputable def embed (k : ℕ) : Vec (k+2) × Vec (k+2) →ₗ[ℂ] Mat (k+3) (k+3) where
  toFun x := array (u k) (v k) (rowPart x.1) (rowPart x.2)
  map_add' x y := by
    funext ⟨i,j⟩
    simp [array,outer,ext_add]
    ring
  map_smul' c x := by
    funext ⟨i,j⟩
    simp [array,outer,ext_smul]
    ring

theorem embed_inj (k : ℕ) : Function.Injective (embed k) := by
  rw [← LinearMap.ker_eq_bot,LinearMap.ker_eq_bot']
  rintro ⟨a,b⟩ h
  change array (u k) (v k) (rowPart a) (rowPart b)=0 at h
  have nn : ((k+3 : ℕ) : ℂ)≠0 := by exact_mod_cast (by omega : k+3≠0)
  have nn' : (k : ℂ)+3≠0 := by simpa only [Nat.cast_add,Nat.cast_ofNat] using nn
  apply Prod.ext
  · funext i
    have s := row_sum (u k) (v k) (rowPart a) (rowPart b) (sum_rowPart _) (sum_rowPart _) i.castSucc
    rw [h] at s
    simpa [nn'] using s.symm
  · funext j
    have s := col_sum (u k) (v k) (rowPart a) (rowPart b) (instance_frame _) (sum_rowPart _) j.castSucc
    rw [h] at s
    simpa [nn'] using s.symm

noncomputable def exampleSpace (k : ℕ) := LinearMap.range (embed k)

theorem dimension (k : ℕ) : finrank ℂ (exampleSpace k)=2*(k+2) := by
  rw [exampleSpace,LinearMap.finrank_range_of_inj (embed_inj _)]
  simp [finrank_prod,two_mul]

theorem jets (k : ℕ) (t : Mat (k+3) (k+3)) (ht : t∈exampleSpace k) : total t=0 ∧ disjointSum t=0 := by
  obtain ⟨⟨a,b⟩,rfl⟩ := ht
  exact conditions _ _ _ _ (instance_frame k) (sum_rowPart _) (sum_rowPart _)

theorem closed (k : ℕ) (t : Mat (k+3) (k+3)) (ht : t∈exampleSpace k) : bar t∈exampleSpace k := by
  obtain ⟨⟨a,b⟩,rfl⟩ := ht
  refine ⟨⟨fun j => conj (a j),fun j => conj (b j)⟩,?_⟩
  funext ⟨i,j⟩
  simp [embed,bar,array,outer,ext_bar]

#print axioms dimension
#print axioms closed

end JetMaximalExample
