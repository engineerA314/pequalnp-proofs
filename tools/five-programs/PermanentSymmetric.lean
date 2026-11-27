import PermanentGrid

namespace PermanentSymmetric

open Finset MvPolynomial PermanentSupport PermanentGrid
variable {n d : ℕ}

theorem nonconstant (u : Fin d → Fin n → ℂ) (i : Fin d) (j : Fin n) (nz : u i j≠0) :
    forms u ≠ 1 := by
  classical
  intro equal
  let c : Fin d → ℂ := Pi.single i (-(u i j)⁻¹)
  have vanishes : eval c (forms u)=0 := by
    rw [forms,map_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [c,Pi.single_apply,mul_ite,nz]
  rw [equal,map_one] at vanishes
  exact one_ne_zero vanishes

theorem symmetric_witness (u : Fin d → Fin n → ℂ) (i : Fin d) (j : Fin n) (nz : u i j≠0) :
    ∃ c : Fin d → ℂ, (∀ i,c i∈grid n) ∧ value u u c≠(n.factorial : ℂ) := by
  classical
  have support : ∃ a : Fin d →₀ ℕ, a≠0 ∧ a∈(forms u).support := by
    by_contra! h
    apply nonconstant u i j nz
    ext a
    by_cases ha : a=0
    · subst a
      simp [forms,PEqualNP.Gct.Helpers.Support.coeff_zero_prod]
    · rw [notMem_support_iff.mp (h a ha)]
      rw [MvPolynomial.coeff_one]
      simp [Ne.symm ha]
  obtain ⟨a,az,inP⟩ := support
  exact integer_witness u u a az inP inP

theorem single_direction (u : Fin n → ℂ) (j : Fin n) (nz : u j≠0) :
    ∃ t∈grid n, MvPolynomial.eval (fun p : Fin n × Fin n => 1+t*u p.1*u p.2)
      (PEqualNP.Gct.permPoly ℂ n)≠(n.factorial : ℂ) := by
  obtain ⟨c,hc,off⟩ := symmetric_witness (d := 1) (fun _ => u) 0 j nz
  refine ⟨c 0,hc 0,?_⟩
  simpa [value,Fin.sum_univ_one] using off

#print axioms single_direction

end PermanentSymmetric
