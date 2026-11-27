import GraphMatrixLoops
import GraphStreamCorrect
import ColourNP
import PEqualNP.Library.L032
import PEqualNP.Library.L018

namespace GraphMatrixComplete

open WordMachine GraphStreamForm GraphStreamRoles GraphCellMachine GraphMatrixLoops ThreeColourGadgets
open PEqualNP.Library PEqualNP.Library.SearchHelpers PEqualNP.Library.SearchHelpers.SatV PEqualNP.Search

theorem entry_read (w : W) (i j : Fin (width w)) :
    (word w).getD (i.val*width w+j.val) false=entry w i j := by
  let k : Fin (width w*width w) := finProdFinEquiv (i,j)
  have h : k.val=i.val*width w+j.val := by simp [k,finProdFinEquiv,Nat.mul_comm,Nat.add_comm]
  rw [← h,List.getD_eq_getElem?_getD]
  unfold word
  rw [List.getElem?_ofFn,dite_eq_left k.isLt]
  change entry w (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2=_
  rw [show finProdFinEquiv.symm k=(i,j) from finProdFinEquiv.symm_apply_apply _]

theorem entry_graph (w : W) (i j : Fin (width w)) :
    entry w i j=true ↔ Edge (streamed w) (project w i) (project w j) ∨ Edge (streamed w) (project w j) (project w i) := by
  simp only [entry,adjacent,direction_arc,Bool.or_eq_true,ThreeColourMatrix.arcs_iff,project]

theorem word_iff (w : W) : ThreeColourMatrix.Accepted (word w) ↔ Sat (streamed w) := by
  rw [graph_iff]
  have length : (word w).length=width w*width w := by simp only [word,List.length_ofFn]
  constructor
  · rintro ⟨d,len,c,good⟩
    have eq : d=width w := by nlinarith
    subst d
    choose rep inv using onto w
    refine ⟨fun v => c (rep v).val,?_⟩
    intro u v edge
    apply good _ _ (rep u).isLt (rep v).isLt
    rw [entry_read w (rep u) (rep v),entry_graph,inv,inv]
    exact Or.inl edge
  · rintro ⟨c,good⟩
    refine ⟨width w,length,fun i => if h : i<width w then c (project w ⟨i,h⟩) else 0,?_⟩
    intro i j hi hj edge
    rw [entry_read w ⟨i,hi⟩ ⟨j,hj⟩,entry_graph] at edge
    simp only [hi,hj,dite_true]
    rcases edge with h | h
    · exact good _ _ h
    · exact Ne.symm (good _ _ h)

def valid (w : W) := wfB w && KSat.Mem.wt 0 w

theorem valid_iff (w : W) : valid w=true ↔ ∃ F : CNF,encodeCNF F=w ∧ IsKCNF 3 F := by
  constructor
  · intro h
    obtain ⟨wf,sz⟩ := Bool.and_eq_true_iff.mp h
    obtain ⟨F,rfl⟩ := (wfB_iff w).mp wf
    exact ⟨F,rfl,(KSat.Mem.wt_cnf F).mp sz⟩
  · rintro ⟨F,rfl,small⟩
    exact Bool.and_eq_true_iff.mpr ⟨(wfB_iff _).mpr ⟨F,rfl⟩,(KSat.Mem.wt_cnf F).mpr small⟩

def reduce (w : W) := if valid w then word w else ThreeColourWord.rejectWord

theorem language (w : W) : w∈KSAT 3 ↔ ThreeColourMatrix.Accepted (reduce w) := by
  by_cases hv : valid w=true
  · obtain ⟨F,rfl,hF⟩ := (valid_iff w).mp hv
    rw [reduce,ite_eq_left hv,word_iff,GraphStreamCorrect.corresponds F hF]
    constructor
    · rintro ⟨G,_,eq,sat⟩
      have same := CNFReader.parse_iff (encodeCNF F) G
      have eq2 : F=G := Option.some.inj (((CNFReader.parse_iff _ F).mpr rfl).symm.trans (same.mpr eq))
      exact eq2 ▸ sat
    · exact fun sat => ⟨F,hF,rfl,sat⟩
  · rw [reduce,ite_eq_right hv]
    constructor
    · rintro ⟨F,small,eq,_⟩
      exact False.elim (hv ((valid_iff w).mpr ⟨F,eq,small⟩))
    · exact fun h => False.elim (ThreeColourWord.rejected h)

theorem reduceCPT : CPT reduce := by
  have wf : Effective wfB := changeF KSat.Hard.cpt_wfF (fun _ => rfl)
  have sz : Effective (KSat.Mem.wt 0) := changeF KSat.Mem.cpt_wtF (fun _ => rfl)
  exact GraphStreamCPT.branch (both wf sz) wordCPT (PEqualNP.Library.Universal.cpt_const _)

theorem hardness : PolyTimeReducible (KSAT 3) {w : W | ThreeColourMatrix.Accepted w} :=
  ⟨reduce,reduceCPT,language⟩

theorem complete : NPComplete {w : W | ThreeColourMatrix.Accepted w} :=
  L020 _ _ L032 ColourNP.inNP hardness

theorem consequence : ({w : W | ThreeColourMatrix.Accepted w} : Language Bool)∈P → P=NP :=
  (L018 _ complete).mp

theorem output_bound (w : W) : (reduce w).length ≤ (13*(w.length+1))^2 := by
  by_cases h : valid w=true
  · simp only [reduce,ite_eq_left h,word,List.length_ofFn,pow_two]
    exact le_rfl
  · simp only [reduce,ite_eq_right h,ThreeColourWord.rejectWord,List.length_cons,List.length_nil]
    nlinarith [Nat.zero_le w.length]

#print axioms consequence
#print axioms reduceCPT
#print axioms complete

end GraphMatrixComplete
