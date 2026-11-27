import GraphStreamForm

namespace GraphStreamCPT

open WordMachine GraphStreamWords GraphStreamForm PEqualNP.Library PEqualNP.Library.Machines
open PEqualNP.Library.Universal PEqualNP.Library.SearchHelpers.SatV ThreeColourGadgets
open PEqualNP.Library.SearchHelpers.KSat.Hard (cpt_dropI cpt_headI cpt_isEndF)

theorem branch {p : W → Bool} {yes no : W → W} (hp : Effective p) (hy : CPT yes) (hn : CPT no) :
    CPT (fun s => if p s then yes s else no s) := by
  refine changeF (cpt_sel hp hn hy) ?_
  intro s
  cases p s <;> rfl

theorem unary {w : W → W} (hw : CPT w) : CPT (fun s => un (w s).length) := by
  simpa [mulU] using cpt_mulU2 hw (cpt_const [true])

theorem skipTwo {w : W → W} (hw : CPT w) : CPT (fun s => (w s).drop 2) := by
  refine changeF (cpt_tail1 (cpt_tail1 hw)) ?_
  intro s
  cases w s with
  | nil => rfl
  | cons h t => cases t <;> rfl

theorem rawCPT {r : W → W} (hr : CPT r) (p : Fin 3) : CPT (fun s => rawAt (r s) p) := by
  have d1 := cpt_comp hr cpt_dropI
  have d2 := cpt_comp d1 cpt_dropI
  have a := cpt_comp hr cpt_headI
  have e1 : Effective (fun s => isEnd (dropI (r s))) := changeF (cpt_comp d1 cpt_isEndF) (fun _ => rfl)
  have e2 : Effective (fun s => isEnd (dropI (dropI (r s)))) := changeF (cpt_comp d2 cpt_isEndF) (fun _ => rfl)
  have b := branch e1 a (cpt_comp d1 cpt_headI)
  have c := branch (either e1 e2) b (cpt_comp d2 cpt_headI)
  fin_cases p
  · exact a
  · exact b
  · exact c

def wire {n : ℕ} (l : Fin n × Bool) := pairB (un l.1.val) (flag l.2)

theorem parsedCPT {w raw : W → W} (hw : CPT w) (hr : CPT raw) :
    CPT (fun s => wire (parsed (w s) (raw s))) := by
  have polarity := query (cpt_const [true]) hr
  exact cpt_pairB2 (addrCPT hw (skipTwo hr)) polarity

theorem posCPT {w i : W → W} (hw : CPT w) (hi : CPT i) (p : Fin 3) :
    CPT (fun s => wire (pos (w s) (i s).length p)) := by
  have r := clauseCPT hi hw
  have d (b : Bool) : CPT (fun s => wire (dummy (w s),b)) := cpt_pairB2 (unary hw) (cpt_const (flag b))
  have l := parsedCPT hw (rawCPT r p)
  have stop : Effective (fun s => isEnd (clauseAt (i s).length (w s))) := changeF (cpt_comp r cpt_isEndF) (fun _ => rfl)
  have total := branch (lenEq hi hw) (d false) (branch (eqWords r (cpt_const [])) (d (decide (p=1)))
    (branch stop (d true) l))
  refine changeF total ?_
  intro s
  simp only [pos,decide_eq_true_eq]
  split_ifs <;> rfl

theorem varCPT {w i : W → W} (hw : CPT w) (hi : CPT i) (p : Fin 3) :
    CPT (fun s => un (pos (w s) (i s).length p).1.val) := by
  simpa [wire,unpairB_pairB] using cpt_unpairB1_1 (posCPT hw hi p)

theorem polarityCPT {w i : W → W} (hw : CPT w) (hi : CPT i) (p : Fin 3) :
    Effective (fun s => (pos (w s) (i s).length p).2) := by
  simpa [wire,unpairB_pairB] using cpt_unpairB2_1 (posCPT hw hi p)

#print axioms posCPT

end GraphStreamCPT
