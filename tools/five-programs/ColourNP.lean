import WordMachine
import ColourCertificate
import PEqualNP.Library.L032

namespace ColourNP

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal WordMachine ColourCertificate
open ThreeColourMatrix (Accepted)

abbrev first (s : W) := (unpairB s).1
abbrev second (s : W) := (unpairB s).2

theorem sameEffective {a b c d : W → Bool} (ha : Effective a) (hb : Effective b)
    (hc : Effective c) (hd : Effective d) :
    Effective (fun s => same (a s) (b s) (c s) (d s)) :=
  both (equalBits ha hc) (either ha (equalBits hb hd))

theorem cell {w a b i j : W → W} (hw : CPT w) (ha : CPT a) (hb : CPT b) (hi : CPT i) (hj : CPT j) :
    Effective (fun s => good (w s) (a s) (b s) (i s).length (j s).length) := by
  have e := query (cpt_app2 (cpt_mulU2 hi ha) hj) hw
  have edgeBit : Effective (fun s => (w s).getD ((i s).length*(a s).length+(j s).length) false) := by
    simpa [mulU,un] using e
  exact either (neg edgeBit) (neg (sameEffective (query hi ha) (query hi hb) (query hj ha) (query hj hb)))

theorem row {w a b i : W → W} (hw : CPT w) (ha : CPT a) (hb : CPT b) (hi : CPT i) :
    Effective (fun s => (List.range (a s).length).all (fun j => good (w s) (a s) (b s) (i s).length j)) :=
  allBelow a _ ha (cell (cpt_comp cpt_unpairB2 hw) (cpt_comp cpt_unpairB2 ha)
    (cpt_comp cpt_unpairB2 hb) (cpt_comp cpt_unpairB2 hi) cpt_unpairB1)

theorem table {w a b : W → W} (hw : CPT w) (ha : CPT a) (hb : CPT b) :
    Effective (fun s => (List.range (a s).length).all (fun i => (List.range (a s).length).all
      (fun j => good (w s) (a s) (b s) i j))) :=
  allBelow a _ ha (row (cpt_comp cpt_unpairB2 hw) (cpt_comp cpt_unpairB2 ha)
    (cpt_comp cpt_unpairB2 hb) cpt_unpairB1)

theorem checkMachine :
    ComputableInPolyTime encodePair Computability.encodeBool (fun p : W × W => check p.1 p.2) := by
  let a := fun s : W => first (second s)
  let b := fun s : W => second (second s)
  have ha : CPT a := cpt_unpairB1_1 cpt_unpairB2
  have hb : CPT b := cpt_unpairB2_1 cpt_unpairB2
  have sz : Effective (fun s => decide ((first s).length=(a s).length*(a s).length)) := by
    simpa [mulU,un] using lenEq cpt_unpairB1 (cpt_mulU2 ha ha)
  have efficient : Effective (fun s => check (first s) (second s)) :=
    both sz (table cpt_unpairB1 ha hb)
  have h := cpt_comp cpt_pairB (decideBit efficient)
  have eq : ((fun s => check (first s) (second s)) ∘ (fun p : W × W => pairB p.1 p.2))=
      (fun p => check p.1 p.2) := by
    funext p
    simp [first,second,unpairB_pairB]
  exact eq ▸ h

theorem inNP : ({w : W | Accepted w} : Language Bool)∈NP := by
  let R : Set (W × W) := {p | check p.1 p.2=true}
  refine ⟨R,3*Polynomial.X+1,⟨fun p => check p.1 p.2,fun _ => Iff.rfl,checkMachine⟩,?_⟩
  intro x
  change Accepted x ↔ ∃ w : W, w.length≤(3*Polynomial.X+1 : Polynomial ℕ).eval x.length ∧ check x w=true
  simpa using spec x

#print axioms checkMachine
#print axioms inNP

end ColourNP
