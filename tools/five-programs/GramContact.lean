import GramMatrixLevel
import PEqualNP.Gct.Helpers.RankOne
import PEqualNP.Gct.Helpers.MincExpansion
import PEqualNP.Gct.Helpers.Rung.RootsEsymm

/-! Every sub-leading Taylor coefficient can vanish on a nonzero rank-one PSD ray. -/
namespace GramContact

open Finset MvPolynomial
open scoped ComplexConjugate
open PEqualNP.Gct.Helpers.Minc (Mk)
open PEqualNP.Gct.Helpers.RankOne (KSub)
variable {n : ℕ}

noncomputable def elem (k : ℕ) (u : Fin n → ℂ) :=
  ∑ S : KSub n k, ∏ i∈S.1, u i

theorem scaled (k : ℕ) (u : Fin n → ℂ) (t : ℂ) :
    elem k (fun i => t*u i)=t^k * elem k u := by
  classical
  simp only [elem,Finset.prod_mul_distrib,Finset.prod_const,Finset.mul_sum]
  exact Finset.sum_congr rfl fun S _ => by rw [S.2]

theorem conjugated (k : ℕ) (u : Fin n → ℂ) :
    elem k (fun i => conj (u i))=conj (elem k u) := by simp [elem]

theorem roots (n k : ℕ) (hn : 0<n) (z : ℂ) (hz : IsPrimitiveRoot z n) :
    elem k (fun i : Fin n => z^i.val) = if k=0 then 1 else if k=n then (-1)^(n+1) else 0 := by
  classical
  rw [← PEqualNP.Gct.Rung.esymm_roots_of_unity n hn z hz k]
  symm
  exact Finset.sum_subtype _ (by simp [Finset.mem_powersetCard]) _

theorem root_sq (n k : ℕ) (hn : 0<n) (z : ℂ) (hz : IsPrimitiveRoot z n) :
    elem k (fun i : Fin n => z^i.val) * conj (elem k (fun i : Fin n => z^i.val)) =
      if k=0 ∨ k=n then 1 else 0 := by
  rw [roots n k hn z hz]
  by_cases h : k=0
  · simp [h]
  by_cases f : k=n
  · subst k
    simp [hn.ne',← mul_pow]
  · simp [h,f]

theorem coefficient (k : ℕ) (u : Fin n → ℂ) (t : ℂ) :
    Mk n k (fun p => t*u p.1*conj (u p.2)) =
      (k.factorial : ℂ)*t^k*(elem k u*conj (elem k u)) := by
  change PEqualNP.Gct.Helpers.RankOne.Mk n k (fun p => t*u p.1*conj (u p.2))=_
  rw [PEqualNP.Gct.Helpers.RankOne.Mk_rankOne n k (fun i => t*u i) (fun i => conj (u i))]
  change (k.factorial : ℂ)*elem k (fun i => t*u i)*elem k (fun i => conj (u i))=_
  rw [scaled,conjugated]
  ring

theorem exact_ray (n : ℕ) (hn : 0<n) (z : ℂ) (hz : IsPrimitiveRoot z n) (t : ℂ) :
    eval (fun p : Fin n × Fin n => 1+t*z^p.1.val*conj (z^p.2.val)) (PEqualNP.Gct.permPoly ℂ n)
      =(n.factorial : ℂ)*(1+t^n) := by
  classical
  rw [PEqualNP.Gct.Helpers.Minc.minc_Mk]
  simp_rw [coefficient (u := fun i : Fin n => z^i.val),root_sq n _ hn z hz]
  rw [Finset.sum_range_succ]
  have rest : (∑ k∈Finset.range n,(((n-k).factorial : ℂ)*
      ((k.factorial : ℂ)*t^k*(if k=0 ∨ k=n then 1 else 0))))=(n.factorial : ℂ) := by
    rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr hn)]
    · simp
    · intro b hb notzero
      have diff : b≠n := (Finset.mem_range.mp hb).ne
      simp [diff,notzero]
  rw [rest]
  simp
  ring

#print axioms exact_ray

end GramContact
