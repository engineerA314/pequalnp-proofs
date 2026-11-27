import ResidualStateCount

namespace ResidualModel

open ResidualAntichain ResidualStateCount

noncomputable def model : (n : ℕ) → Form n → (Fin n → Bool)
  | 0,_ => Fin.elim0
  | n+1,f =>
    if 0 < run n (Finsupp.single (normal (branch f false)) 1) then
      Fin.cons false (model n (branch f false))
    else Fin.cons true (model n (branch f true))

theorem correct (n : ℕ) (f : Form n) (positive : 0<count f) : sat (model n f) f := by
  induction n with
  | zero =>
    by_contra fail
    have none (x : Fin 0 → Bool) : ¬sat x f := by
      have eq : x=model 0 f := Subsingleton.elim _ _
      simpa only [eq] using fail
    simp [count,none] at positive
  | succ n ih =>
    rw [split] at positive
    unfold model
    rw [exact_count]
    split <;> rename_i h
    · exact (branch_sat _ _ _).mp (ih _ h)
    · exact (branch_sat _ _ _).mp (ih _ (by omega))

#print axioms correct

end ResidualModel
