import GridResidualLower

namespace GridRectangleLower

open Finset ResidualInducedMatching GridStripMatching GridOrderCut GridResidualLower

def rect (r c : ℕ) : SimpleGraph (Fin r × Fin c) where
  Adj u v := (u.1=v.1 ∧ near u.2 v.2) ∨ (u.2=v.2 ∧ near u.1 v.1)
  symm := ⟨by
    rintro a b (h|h)
    · exact Or.inl ⟨h.1.symm,h.2.symm⟩
    · exact Or.inr ⟨h.1.symm,h.2.symm⟩⟩
  loopless := ⟨by intro a; simp [near]⟩

def includeGrid {m r c : ℕ} (hr : m≤r) (hc : m≤c) (v : Fin m × Fin m) : Fin r × Fin c :=
  (v.1.castLE hr,v.2.castLE hc)

theorem faithful {m r c : ℕ} (hr : m≤r) (hc : m≤c) (u v : Fin m × Fin m) :
    (rect r c).Adj (includeGrid hr hc u) (includeGrid hr hc v) ↔ (grid m).Adj u v := by
  simp [rect,grid,includeGrid,near,Fin.ext_iff]

def cut {r c : ℕ} (time : Fin r × Fin c → ℕ) (t : ℕ) := univ.filter (fun u => time u ≤ t)

def lower (r c : ℕ) (time : Fin r × Fin c → ℕ) (size : ℕ) :=
  ∃ t,∀ (Q : Type) [Fintype Q] (write : Finset (Fin r × Fin c) → Q) (read : Q → Finset (Fin r × Fin c) → Prop),
    correct (rect r c) (cut time t) write read → size≤Fintype.card Q

theorem subgrid (r c k : ℕ) (hr : 2*k+2≤r) (hc : 2*k+2≤c) (time : Fin r × Fin c → ℕ)
    (unique : Function.Injective time) : lower r c time (2^(k+1)) := by
  classical
  let embed := includeGrid hr hc
  have inj : Function.Injective embed := by
    intro u v eq
    apply Prod.ext <;> apply Fin.ext
    · exact congrArg (fun p : Fin r × Fin c => p.1.val) eq
    · exact congrArg (fun p : Fin r × Fin c => p.2.val) eq
  obtain ⟨t,⟨M⟩⟩ := any_order k (time ∘ embed) (unique.comp inj)
  let M' : CutMatching (rect r c) (cut time t) (k+1) :=
    { left := fun i => embed (M.left i)
      right := fun i => embed (M.right i)
      before := fun i => by simpa [cut,beforeTime] using M.before i
      afterCut := fun i => by simpa [cut,beforeTime] using M.afterCut i
      edge := fun i => (faithful hr hc _ _).mpr (M.edge i)
      noLeft := fun i j e => M.noLeft i j ((faithful hr hc _ _).mp e)
      onlyPair := fun i j e => M.onlyPair i j ((faithful hr hc _ _).mp e) }
  exact ⟨t,fun Q _ enc read accurate => on_cut _ _ M' Q enc read accurate⟩

theorem all_rectangles (r c : ℕ) (time : Fin r × Fin c → ℕ) (unique : Function.Injective time) :
    lower r c time (2^(min r c/2)) := by
  cases h : min r c/2 with
  | zero =>
    refine ⟨0,fun Q _ enc _ _ => ?_⟩
    have : Nonempty Q := ⟨enc ∅⟩
    have positive := Fintype.card_pos (α := Q)
    rw [pow_zero]
    omega
  | succ k =>
    apply subgrid r c k _ _ time unique <;> omega

#print axioms all_rectangles

end GridRectangleLower
