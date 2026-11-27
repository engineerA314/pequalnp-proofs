import PEqualNP.Library.SearchHelpers.TableauStepWLoop
import PEqualNP.Library.SearchHelpers.SatVerifierCPT
import Mathlib

/-! Finite-index loops and bit queries proved polynomial time in the project's TM2 model. -/
namespace WordMachine

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.Tab.StepW

abbrev W := List Bool
abbrev CPT (f : W → W) := ComputableInPolyTime (fun x : W => x) (fun x : W => x) f
def flag (b : Bool) : W := if b then [true] else []
abbrev Effective (p : W → Bool) := CPT (fun s => flag (p s))

theorem changeF {f g : W → W} (h : CPT f) (eq : ∀ s, f s=g s) : CPT g := funext eq ▸ h

theorem eqWords {f g : W → W} (hf : CPT f) (hg : CPT g) : Effective (fun s => decide (f s=g s)) :=
  cpt_bitFlag (cpt_comp (cpt_pair hf hg) (PEqualNP.MetaComplexity.Helpers.Machines.strEq_polyTime (A := Bool)))

theorem neg {p : W → Bool} (hp : Effective p) : Effective (fun s => !p s) := by
  refine changeF (cpt_sel hp (cpt_const [true]) (cpt_const [])) ?_
  intro s
  dsimp only
  cases p s <;> rfl

theorem both {p q : W → Bool} (hp : Effective p) (hq : Effective q) : Effective (fun s => p s && q s) := by
  refine changeF (cpt_sel hp (cpt_const []) hq) ?_
  intro s
  dsimp only
  cases p s <;> cases q s <;> rfl

theorem either {p q : W → Bool} (hp : Effective p) (hq : Effective q) : Effective (fun s => p s || q s) := by
  refine changeF (cpt_sel hp hq (cpt_const [true])) ?_
  intro s
  dsimp only
  cases p s <;> cases q s <;> rfl

theorem equalBits {p q : W → Bool} (hp : Effective p) (hq : Effective q) :
    Effective (fun s => p s == q s) := by
  refine changeF (eqWords hp hq) ?_
  intro s
  dsimp only
  cases p s <;> cases q s <;> rfl

theorem query {offset word : W → W} (hi : CPT offset) (hw : CPT word) :
    Effective (fun s => (word s).getD (offset s).length false) := by
  have d : CPT (fun s => (word s).drop (offset s).length) :=
    changeF (cpt_iterLen cpt_tail (fun s => by simp) hi hw) (fun s => List.tail_iterate _ _)
  have h := eqWords (cpt_tk (cpt_const [true]) d) (cpt_const [true])
  refine changeF h ?_
  intro s
  have head : ((word s).drop (offset s).length).head?=(word s)[(offset s).length]? := by simp
  dsimp only
  rw [List.getD_eq_getElem?_getD,← head,tk_eq]
  cases (word s).drop (offset s).length with
  | nil => rfl
  | cons b xs => cases b <;> rfl

theorem lenEq {f g : W → W} (hf : CPT f) (hg : CPT g) : Effective (fun s => decide ((f s).length=(g s).length)) := by
  refine changeF (eqWords (cpt_mulU2 hf (cpt_const [true])) (cpt_mulU2 hg (cpt_const [true]))) ?_
  intro s
  simp [mulU,un]

theorem all_flags (xs : List ℕ) (p : ℕ → Bool) :
    (xs.flatMap fun i => flag (!(p i))).isEmpty=xs.all p := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    cases h : p i
    · simp [flag,h]
    · simpa [flag,h] using ih

theorem allBelow (bound : W → W) (p : ℕ → W → Bool) (hb : CPT bound)
    (hp : Effective (fun s => p (unpairB s).1.length (unpairB s).2)) :
    Effective (fun s => (List.range (bound s).length).all (fun i => p i s)) := by
  have loop := cpt_flatMapRange (neg hp) hb cpt_id
  refine changeF (cpt_sel loop (cpt_const [true]) (cpt_const [])) ?_
  intro s
  simp only [unpairB_pairB,un_length]
  let bad := (List.range (bound s).length).flatMap fun i => flag (!(p i s))
  change sel bad [true] []=flag _
  rw [← all_flags]
  change sel bad [true] []=flag bad.isEmpty
  cases bad <;> rfl

theorem decideBit {p : W → Bool} (hp : Effective p) :
    ComputableInPolyTime (fun s : W => s) Computability.encodeBool p := by
  have h := cpt_comp (cpt_pair hp (cpt_const [true])) (PEqualNP.MetaComplexity.Helpers.Machines.strEq_polyTime (A := Bool))
  have eq : (fun s => decide (flag (p s)=[true]))=p := by funext s; cases p s <;> rfl
  exact eq ▸ h

#print axioms allBelow
#print axioms query

end WordMachine
