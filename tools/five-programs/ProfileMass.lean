import ThresholdSplit

namespace ProfileMass

open Finset
variable {d : ℕ}

def chosen {m : ℕ} (x : Fin m → Bool) : Finset (Fin m) := univ.filter fun i => x i

def size {m : ℕ} (x : Fin m → Bool) : Fin (m+1) :=
  ⟨(chosen x).card,Nat.lt_succ_of_le ((Finset.card_le_univ _).trans_eq (Fintype.card_fin _))⟩

def blockEquiv (m k : ℕ) : {x : Fin m → Bool // (chosen x).card=k} ≃ {S : Finset (Fin m) // S.card=k} where
  toFun x := ⟨chosen x.1,x.2⟩
  invFun S := ⟨fun i => decide (i∈S.1),by simpa [chosen] using S.2⟩
  left_inv x := by apply Subtype.ext; funext i; simp [chosen]
  right_inv S := by apply Subtype.ext; simp [chosen]

abbrev Assignment (width : Fin d → ℕ) := ∀ j,Fin (width j) → Bool
abbrev Sizes (width : Fin d → ℕ) := ∀ j,Fin (width j+1)
def profile (width : Fin d → ℕ) (x : Assignment width) : Sizes width := fun j => size (x j)

def fiber (width : Fin d → ℕ) (k : Sizes width) :
    {x : Assignment width // profile width x=k} ≃
      ∀ j,{b : Fin (width j) → Bool // (chosen b).card=(k j).val} where
  toFun x := fun j => ⟨x.1 j,congrArg Fin.val (congrFun x.2 j)⟩
  invFun b := ⟨fun j => (b j).1,funext fun j => Fin.ext (b j).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem mass (width : Fin d → ℕ) (k : Sizes width) :
    (univ.filter fun x : Assignment width => profile width x=k).card=∏ j, (width j).choose (k j).val := by
  classical
  rw [← Fintype.card_subtype,Fintype.card_congr (fiber width k),Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro j _
  rw [Fintype.card_congr (blockEquiv (width j) (k j).val),Fintype.card_finset_len,Fintype.card_fin]

theorem aggregate (width : Fin d → ℕ) (pass : Sizes width → Bool) :
    (univ.filter fun x : Assignment width => pass (profile width x)=true).card=
      ∑ k : Sizes width, if pass k then ∏ j,(width j).choose (k j).val else 0 := by
  classical
  rw [ThresholdSplit.sum_by_mask]
  simp_rw [mass]

/-- Integer form of (m+1)/2^m ≤ (3/4)^(m-1), for every nonempty group. -/
theorem compression (s : ℕ) : (s+2)*2^s≤2*3^s := by
  induction s with
  | zero => decide
  | succ s ih =>
    simp only [pow_succ]
    have h := Nat.mul_le_mul_right 3 ih
    have small : (s+3)*2≤(s+2)*3 := by omega
    have a := Nat.mul_le_mul_right (2^s) small
    nlinarith

#print axioms aggregate
#print axioms compression

end ProfileMass
