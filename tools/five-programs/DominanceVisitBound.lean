import Mathlib

namespace DominanceVisitBound

/-- Per-record budget for a geometric split and a drop in dimension. -/
def visits : ℕ → ℕ → ℕ
  | 0, _ => 1
  | _+1, 0 => 1
  | s+1, d+1 => 1+visits s (d+1)+visits (s+1) d

theorem visits_pos (s d : ℕ) : 1≤visits s d := by cases s <;> cases d <;> simp [visits] <;> omega

theorem exactVisits (s d : ℕ) : visits s d+1=2*(s+d).choose d := by
  induction s generalizing d with
  | zero => simp [visits]
  | succ s ih =>
    induction d with
    | zero => simp [visits]
    | succ d ihd =>
      have e := ih (d+1)
      have H : (s+1+(d+1)).choose (d+1)=(s+1+d).choose d+(s+(d+1)).choose (d+1) := by
        rw [show s+1+(d+1)=(s+1+d)+1 by omega,Nat.choose_succ_succ]
        rw [show s+1+d=s+(d+1) by omega]
      rw [H]
      simp only [visits]
      omega

/-- Cost counts the number of records present at each call. The same-dimensional
children partition the records; the projected cross query uses a subset. -/
inductive Charged : ℕ → ℕ → ℕ → ℕ → Prop
  | leaf (s d n : ℕ) : Charged s d n n
  | split {s d a b c wa wb wc : ℕ} (bounded : c≤a+b)
      (left : Charged s (d+1) a wa) (right : Charged s (d+1) b wb)
      (cross : Charged (s+1) d c wc) :
      Charged (s+1) (d+1) (a+b) (a+b+wa+wb+wc)

theorem charge {s d n w : ℕ} (tree : Charged s d n w) : w≤n*visits s d := by
  induction tree with
  | leaf s d n => simpa only [Nat.mul_one] using Nat.mul_le_mul_left n (visits_pos s d)
  | @split s d a b c wa wb wc cap left right cross li ri ci =>
    have projected := ci.trans (Nat.mul_le_mul_right _ cap)
    calc
      a+b+wa+wb+wc ≤ a+b+a*visits s (d+1)+b*visits s (d+1)+(a+b)*visits (s+1) d := by omega
      _ = (a+b)*visits (s+1) (d+1) := by rw [visits]; ring

theorem binomial_bound {s d n w : ℕ} (tree : Charged s d n w) : w+n≤2*n*(s+d).choose d := by
  have cap := charge tree
  calc
    w+n ≤ n*(visits s d+1) := by simpa [Nat.mul_add] using Nat.add_le_add_right cap n
    _ = _ := by rw [exactVisits]; ring

#print axioms binomial_bound

end DominanceVisitBound
