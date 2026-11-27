import ResidualInducedMatching

namespace GridStripMatching

open Finset ResidualInducedMatching

def near {m : ℕ} (i j : Fin m) := i.val+1=j.val ∨ j.val+1=i.val

def grid (m : ℕ) : SimpleGraph (Fin m × Fin m) where
  Adj u v := (u.1=v.1 ∧ near u.2 v.2) ∨ (u.2=v.2 ∧ near u.1 v.1)
  symm := ⟨by
    rintro a b (h|h)
    · exact Or.inl ⟨h.1.symm,h.2.symm⟩
    · exact Or.inr ⟨h.1.symm,h.2.symm⟩⟩
  loopless := ⟨by intro a; simp [near]⟩

def pos {m : ℕ} (vertical : Bool) (i j : Fin m) := if vertical then (j,i) else (i,j)

theorem adj {m : ℕ} (v : Bool) (i j s t : Fin m) :
    (grid m).Adj (pos v i s) (pos v j t) ↔ (i=j ∧ near s t) ∨ (s=t ∧ near i j) := by
  cases v <;> simp [grid,pos,or_comm]

def mixed {m : ℕ} (p : Fin m → Prop) := (∃ j,p j) ∧ (∃ j,¬p j)

theorem transition {m : ℕ} (p : Fin (m+1) → Prop) (mix : mixed p) :
    ∃ i j,p i ∧ ¬p j ∧ near i j := by
  classical
  by_contra! no
  have same (i : Fin m) : p i.castSucc ↔ p i.succ := by
    constructor
    · intro h
      by_contra hn
      exact no i.castSucc i.succ h hn (Or.inl rfl)
    · intro h
      by_contra hn
      exact no i.succ i.castSucc h hn (Or.inr rfl)
  have constant (i : Fin (m+1)) : p i ↔ p 0 := by
    induction i using Fin.induction with
    | zero => rfl
    | succ i ih => exact (same i).symm.trans ih
  obtain ⟨⟨i,hi⟩,⟨j,hj⟩⟩ := mix
  exact hj ((constant j).mpr ((constant i).mp hi))

noncomputable def matching {m k : ℕ} (S : Finset (Fin (m+1) × Fin (m+1))) (v : Bool)
    (rows : Fin k → Fin (m+1)) (apart : ∀ i j,i≠j → rows i≠rows j ∧ ¬near (rows i) (rows j))
    (many : ∀ i,mixed (fun j => pos v (rows i) j∈S)) : CutMatching (grid (m+1)) S k := by
  classical
  choose l r inside outside consecutive using fun i => transition _ (many i)
  refine ⟨fun i => pos v (rows i) (l i),fun i => pos v (rows i) (r i),inside,outside,?_,?_,?_⟩
  · intro i
    exact (adj ..).mpr (Or.inl ⟨rfl,consecutive i⟩)
  · intro i j edge
    by_cases same : i=j
    · subst j; exact (grid _).loopless.irrefl _ edge
    · rcases (adj ..).mp edge with e|e
      · exact (apart i j same).1 e.1
      · exact (apart i j same).2 e.2
  · intro i j edge
    by_contra diff
    rcases (adj ..).mp edge with e|e
    · exact (apart i j diff).1 e.1
    · exact (apart i j diff).2 e.2

#print axioms matching

end GridStripMatching
