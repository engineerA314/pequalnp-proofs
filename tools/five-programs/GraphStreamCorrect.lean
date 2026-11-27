import GraphStreamForm
import ThreeColourWord

namespace GraphStreamCorrect

open PEqualNP.Search PEqualNP.Library.SearchHelpers.SatV GraphStreamWords GraphStreamForm
open ThreeColourGadgets WordMachine

def rowValue (w : W) (x : Fin (B w) → Bool) (i : ℕ) :=
  ev x (pos w i 0)||ev x (pos w i 1)||ev x (pos w i 2)

def pull (w : W) (x : Fin (B w) → Bool) : Assignment := fun v => x (label w (vcode v))

theorem at_clause (F : CNF) (i : ℕ) (hi : i<F.length) :
    clauseAt i (encodeCNF F)=encodeClause F[i]++encodeCNF (F.drop (i+1)) := by
  rw [clause_drop,List.drop_eq_getElem_cons hi]
  rfl

theorem clauses_fit (F : CNF) : 2*F.length≤(encodeCNF F).length := by
  have cost := ThreeColourWord.input_cost F
  omega

theorem end_row (w : W) (x : Fin (B w) → Bool) :
    rowValue w x w.length=!(x (dummy w)) := by
  cases h : x (dummy w) <;> simp [rowValue,pos,ev,h]

theorem extra_row (F : CNF) (i : ℕ) (out : F.length ≤ i) (ne : i ≠ (encodeCNF F).length)
    (x : Fin (B (encodeCNF F)) → Bool) : rowValue (encodeCNF F) x i=true := by
  have d : F.drop i=[] := List.drop_eq_nil_of_le out
  have blank : clauseAt i (encodeCNF F)=[] := by rw [clause_drop,d]; rfl
  cases h : x (dummy (encodeCNF F)) <;> simp [rowValue,pos,blank,ne,ev,h]

theorem real_row (F : CNF) (i : ℕ) (hi : i<F.length) (len : F[i].length≤3)
    (x : Fin (B (encodeCNF F)) → Bool) (hd : x (dummy (encodeCNF F))=false) :
    rowValue (encodeCNF F) x i=Clause.eval (pull (encodeCNF F) x) F[i] := by
  have below := clauses_fit F
  have ne : i≠(encodeCNF F).length := by omega
  rw [rowValue]
  simp only [pos,ne,ite_false,at_clause F i hi]
  generalize eq : F[i]=c at len ⊢
  cases c with
  | nil => simp [encodeClause,isEnd,ev,hd,Clause.eval]
  | cons l c =>
    let tail := encodeCNF (List.drop (i+1) F)
    have enc : encodeClause (l::c)++tail=encodeLiteral l++(encodeClause c++tail) := by
      simp [encodeClause,List.append_assoc]
    have nempty : encodeClause (l::c)++tail≠[] := by rw [enc,encodeLiteral_eq]; simp
    have nend : isEnd (encodeClause (l::c)++tail)=false := by rw [enc,isEnd_lit]
    dsimp only [tail] at nempty nend
    simp only [nempty,nend,ite_false,Bool.false_eq_true]
    dsimp only [tail] at *
    simp_rw [clause_word (l::c) (encodeCNF (F.drop (i+1))) len (by simp),typed]
    exact PackedThreeSAT.padded (l::c) (by simp) len (Literal.eval (pull (encodeCNF F) x))

theorem layout (F : CNF) (small : IsKCNF 3 F) (x : Fin (B (encodeCNF F)) → Bool) :
    (∀ i : Fin (B (encodeCNF F)),rowValue (encodeCNF F) x i=true) ↔
      x (dummy (encodeCNF F))=false ∧ CNF.eval (pull (encodeCNF F) x) F=true := by
  constructor
  · intro h
    have final := h (dummy (encodeCNF F))
    change rowValue _ _ (encodeCNF F).length=true at final
    rw [end_row,Bool.not_eq_true'] at final
    refine ⟨final,List.all_eq_true.mpr ?_⟩
    intro c hc
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hc
    have limit := clauses_fit F
    have valid := h ⟨i,by unfold B; omega⟩
    exact (real_row F i hi (small _ hc) x final) ▸ valid
  · rintro ⟨final,okay⟩ i
    by_cases last : i.val=(encodeCNF F).length
    · rw [last,end_row,final]; rfl
    · by_cases hi : i.val<F.length
      · rw [real_row F i.val hi (small _ (List.getElem_mem _)) x final]
        exact List.all_eq_true.mp okay _ (List.getElem_mem _)
      · exact extra_row F i.val (Nat.le_of_not_gt hi) last x

noncomputable def lift (w : W) (A : Assignment) (k : Fin (B w)) : Bool := by
  classical
  exact if k=dummy w then false else
    if h : ∃ v : ℕ,vcode v=(keys w).getD k.val [] then A (Classical.choose h) else false

theorem read_lift (w : W) (A : Assignment) (v : ℕ) (hv : vcode v∈keys w) :
    pull w (lift w A) v=A v := by
  classical
  have bound := List.idxOf_lt_length_of_mem hv
  have small : (label w (vcode v)).val<w.length := by simpa [label,addr,keys] using bound
  have diff : label w (vcode v)≠dummy w := fun e => small.ne (congrArg Fin.val e)
  have get : (keys w).getD (label w (vcode v)).val []=vcode v := by
    simp [label,addr,List.getD_eq_getElem?_getD,List.getElem?_idxOf hv]
  simp only [pull,lift,diff,ite_false,get]
  split
  next h => exact congrArg A (vcode_injective (Classical.choose_spec h))
  next no => exact False.elim (no ⟨v,rfl⟩)

theorem corresponds (F : CNF) (small : IsKCNF 3 F) :
    Sat (streamed (encodeCNF F)) ↔ Satisfiable F := by
  constructor
  · rintro ⟨x,ok⟩
    exact ⟨pull _ x,((layout F small x).mp ok).2⟩
  · rintro ⟨A,yes⟩
    let w := encodeCNF F
    refine ⟨lift w A,(layout F small _).mpr ⟨by simp [w,lift],?_⟩⟩
    apply List.all_eq_true.mpr
    intro c hc
    obtain ⟨l,hl,t⟩ := List.any_eq_true.mp (List.all_eq_true.mp yes c hc)
    refine List.any_eq_true.mpr ⟨l,hl,?_⟩
    change (pull w (lift w A) l.1==l.2)=true
    rw [read_lift w A l.1 (occurs F c l hc hl)]
    exact t

#print axioms corresponds

end GraphStreamCorrect
