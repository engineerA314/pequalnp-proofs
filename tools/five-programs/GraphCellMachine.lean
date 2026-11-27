import GraphStreamRoles
import GraphStreamCPT

namespace GraphCellMachine

open WordMachine GraphStreamWords GraphStreamForm GraphStreamRoles GraphStreamCPT
open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal

theorem constEff (b : Bool) : Effective (fun _ => b) := cpt_const _

theorem normCPT (r : Shape) {i : W → W} (hi : CPT i) :
    CPT (fun s => un (norm r (i s).length)) := by
  cases r with
  | pal c => exact cpt_const []
  | var a b => exact unary hi
  | tri t p => exact unary hi

theorem sameCPT (r s : Shape) {i j : W → W} (hi : CPT i) (hj : CPT j) :
    Effective (fun e => same r (i e).length s (j e).length) := by
  simpa only [same,un_length] using both (constEff (decide (r=s))) (lenEq (normCPT r hi) (normCPT s hj))

theorem hitCPT (ref : Ref) (s : Shape) {w i j : W → W} (hw : CPT w) (hi : CPT i) (hj : CPT j) :
    Effective (fun e => hit (w e) (i e).length ref s (j e).length) := by
  cases ref with
  | fixed r => exact sameCPT s r hj hi
  | orig p =>
    have a := varCPT hw hi p
    have test (b : Bool) : Effective (fun e => same s (j e).length (.var false b) (pos (w e) (i e).length p).1.val) := by
      simpa only [un_length] using sameCPT s (.var false b) hj a
    refine changeF (branch (polarityCPT hw hi p) (test true) (test false)) ?_
    intro e
    cases h : (pos (w e) (i e).length p).2 <;> simp [h,hit,target]

theorem directionCPT (r s : Shape) {w i j : W → W} (hw : CPT w) (hi : CPT i) (hj : CPT j) :
    Effective (fun e => direction (w e) r (i e).length s (j e).length) := by
  cases r with
  | pal a => cases s <;> exact constEff _
  | var a b => exact either (sameCPT s (.pal 2) hj hi) (both (constEff b) (sameCPT s (.var a false) hj hi))
  | tri t p =>
    apply either (hitCPT (feedRef t p) s hw hi hj)
    cases s with
    | pal a => exact constEff false
    | var a b => exact constEff false
    | tri u q => exact both (lenEq hi hj) (constEff (decide (t=u ∧ p≠q)))

def adjacent (w : W) (r : Shape) (i : ℕ) (s : Shape) (j : ℕ) :=
  direction w r i s j || direction w s j r i

theorem adjacentCPT (r s : Shape) {w i j : W → W} (hw : CPT w) (hi : CPT i) (hj : CPT j) :
    CPT (fun e => [adjacent (w e) r (i e).length s (j e).length]) :=
  oneBit (either (directionCPT r s hw hi hj) (directionCPT s r hw hj hi))

#print axioms adjacentCPT

end GraphCellMachine
