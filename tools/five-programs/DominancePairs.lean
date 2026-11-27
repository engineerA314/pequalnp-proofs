import Mathlib

/-! A count-preserving split for weighted offline dominance queries. Input
points are ordered before queries at ties in the splitting coordinate. -/

namespace DominancePairs

variable {P Q : Type}

def total (R : P → Q → Bool) (w : P → ℕ) (v : Q → ℕ) (points : List P) (queries : List Q) : ℕ :=
  (points.map fun p => w p * (queries.map fun q => if R p q then v q else 0).sum).sum

theorem append_left (R : P → Q → Bool) (w : P → ℕ) (v : Q → ℕ) (l h : List P) (q : List Q) :
    total R w v (l++h) q = total R w v l q + total R w v h q := by simp [total]

theorem append_right (R : P → Q → Bool) (w : P → ℕ) (v : Q → ℕ) (p : List P) (l h : List Q) :
    total R w v p (l++h) = total R w v p l + total R w v p h := by
  induction p with
  | nil => simp [total]
  | cons a p ih =>
    simp only [total,List.map_cons,List.sum_cons,List.map_append,List.sum_append,Nat.mul_add] at ih ⊢
    omega

theorem agrees (R S : P → Q → Bool) (w : P → ℕ) (v : Q → ℕ) (p : List P) (q : List Q)
    (same : ∀ x∈p, ∀ y∈q,R x y=S x y) : total R w v p q=total S w v p q := by
  unfold total
  congr 1
  apply List.map_congr_left
  intro x hx
  congr 2
  apply List.map_congr_left
  intro y hy
  rw [same _ hx _ hy]

theorem split (R : P → Q → Bool) (w : P → ℕ) (v : Q → ℕ)
    (coordP : P → ℤ) (coordQ : Q → ℤ) (pLow pHigh : List P) (qLow qHigh : List Q)
    (forward : ∀ p∈pLow, ∀ q∈qHigh,coordP p≤coordQ q)
    (backward : ∀ p∈pHigh, ∀ q∈qLow,coordQ q<coordP p) :
    let both := fun p q => decide (coordP p≤coordQ q) && R p q
    total both w v (pLow++pHigh) (qLow++qHigh) =
      total both w v pLow qLow+total both w v pHigh qHigh+total R w v pLow qHigh := by
  dsimp only
  rw [append_left,append_right,append_right]
  have good := agrees (fun p q => decide (coordP p≤coordQ q) && R p q) R w v pLow qHigh
    (fun p hp q hq => by simp [forward p hp q hq])
  have bad := agrees (fun p q => decide (coordP p≤coordQ q) && R p q) (fun _ _ => false) w v pHigh qLow
    (fun p hp q hq => by simp [not_le_of_gt (backward p hp q hq)])
  rw [good,bad]
  have z : total (fun _ _ => false) w v pHigh qLow=0 := by simp [total]
  omega

#print axioms split

end DominancePairs
