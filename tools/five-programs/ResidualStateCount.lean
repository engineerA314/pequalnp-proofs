import ResidualAntichain

namespace ResidualStateCount

open Finset ResidualAntichain
abbrev Form (n : ℕ) := F (Fin n)
abbrev Hist (n : ℕ) := Form n →₀ ℕ

instance {V : Type} [Fintype V] [DecidableEq V] (x : V → Bool) (c : C V) : Decidable (hit x c) := by
  unfold hit; infer_instance
instance {V : Type} [Fintype V] [DecidableEq V] (x : V → Bool) (f : F V) : Decidable (sat x f) := by
  unfold sat; infer_instance

def count {n : ℕ} (f : Form n) : ℕ := ∑ x : Fin n → Bool,if sat x f then 1 else 0

theorem split {n : ℕ} (f : Form (n+1)) : count f=count (branch f false)+count (branch f true) := by
  unfold count
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n+1) => Bool)),Fintype.sum_prod_type]
  simp only [Fin.consEquiv_apply,← branch_sat,Fintype.sum_bool]
  omega

def multiply (k : ℕ) : ℕ →+ ℕ where
  toFun x := x*k
  map_zero' := by simp
  map_add' _ _ := add_mul ..

noncomputable def value (n : ℕ) : Hist n →+ ℕ :=
  Finsupp.liftAddHom fun f => multiply (count f)
noncomputable def step (n : ℕ) : Hist (n+1) →+ Hist n :=
  Finsupp.liftAddHom fun f => Finsupp.singleAddHom (branch f false)+Finsupp.singleAddHom (branch f true)

theorem value_one (n : ℕ) (f : Form n) (k : ℕ) :
    value n (Finsupp.single f k)=k*count f := by simp [value,multiply]

theorem step_one (n : ℕ) (f : Form (n+1)) (k : ℕ) :
    step n (Finsupp.single f k)=Finsupp.single (branch f false) k+Finsupp.single (branch f true) k := by
  simp [step]

theorem conserve (n : ℕ) : (value n).comp (step n)=value (n+1) := by
  apply Finsupp.addHom_ext
  intro f k
  simp only [AddMonoidHom.comp_apply,step_one,map_add,value_one,split f,Nat.mul_add]

noncomputable def run : (n : ℕ) → Hist n → ℕ
  | 0,h => value 0 h
  | n+1,h => run n (step n h)

theorem invariant (n : ℕ) (h : Hist n) : run n h=value n h := by
  induction n with
  | zero => rfl
  | succ n ih => exact (ih (step n h)).trans (DFunLike.congr_fun (conserve n) h)

theorem exact_count {n : ℕ} (f : Form n) : run n (Finsupp.single (normal f) 1)=count f := by
  rw [invariant,value_one,one_mul]
  unfold count
  apply Finset.sum_congr rfl
  intro x _
  simp only [normalized]

#print axioms exact_count

end ResidualStateCount
