import PEqualNP.Defs.Search
import ThreeColourGadgets

namespace PackedThreeSAT

open PEqualNP.Search ThreeColourGadgets

def names (F : CNF) := (F.flatMap fun c => c.map Prod.fst).dedup

def code (F : CNF) (x : ℕ) : Fin ((names F).length+1) :=
  ⟨(names F).idxOf x,Nat.lt_succ_of_le List.idxOf_le_length⟩

theorem named (F : CNF) (c : Clause) (l : Literal) (hc : c∈F) (hl : l∈c) : l.1∈names F := by
  simp only [names,List.mem_dedup,List.mem_flatMap,List.mem_map]
  exact ⟨c,hc,l,hl,rfl⟩

theorem unpack (F : CNF) (x : ℕ) (h : x∈names F) : (names F).getD (code F x).val 0=x := by
  simp [code,List.getD_eq_getElem?_getD,List.getElem?_idxOf h]

def pad : Clause → Fin 3 → Literal
  | [] => three (0,false) (0,false) (0,false)
  | [a] => three a a a
  | [a,b] => three a b b
  | a::b::c::_ => three a b c

theorem padded (c : Clause) (nonempty : c≠[]) (short : c.length≤3) (on : Literal → Bool) :
    (on (pad c 0)||on (pad c 1)||on (pad c 2))=c.any on := by
  rcases c with _|⟨a,_|⟨b,_|⟨d,_|⟨e,tail⟩⟩⟩⟩
  · exact False.elim (nonempty rfl)
  · simp [pad,three]
  · simp [pad,three]
  · simp [pad,three,Bool.or_assoc]
  · simp at short
    omega

theorem pad_mem (c : Clause) (nonempty : c≠[]) (j : Fin 3) : pad c j∈c := by
  rcases c with _|⟨a,_|⟨b,_|⟨d,tail⟩⟩⟩
  · contradiction
  all_goals fin_cases j <;> simp [pad,three]

def form (F : CNF) : Form ((names F).length+1) F.length := fun i j =>
  let l := pad F[i] j
  (code F l.1,l.2)

def regular (F : CNF) := F.all fun c => !c.isEmpty && decide (c.length≤3)

theorem regular_iff (F : CNF) : regular F=true ↔ ∀ c∈F,c≠[] ∧ c.length≤3 := by
  simp [regular,List.all_eq_true]

theorem sat_regular (F : CNF) (short : IsKCNF 3 F) (on : Satisfiable F) : regular F=true := by
  obtain ⟨x,hx⟩ := on
  apply (regular_iff F).mpr
  intro c hc
  refine ⟨?_,short c hc⟩
  rintro rfl
  have off := List.all_eq_true.mp hx _ hc
  simp [Clause.eval] at off

theorem formal (F : CNF) (ok : regular F=true) : Satisfiable F ↔ Sat (form F) := by
  have shape := (regular_iff F).mp ok
  constructor
  · rintro ⟨A,all⟩
    let B := fun i : Fin ((names F).length+1) => A ((names F).getD i.val 0)
    refine ⟨B,?_⟩
    intro i
    have hc : F[i]∈F := List.getElem_mem _
    have h := shape _ hc
    have agree (j : Fin 3) : ev B (form F i j)=Literal.eval A (pad F[i] j) := by
      change (A ((names F).getD (code F (pad F[i] j).1).val 0) == _)=_
      rw [unpack F _ (named F _ _ hc (pad_mem _ h.1 j))]
      rfl
    rw [agree,agree,agree,padded _ h.1 h.2]
    exact List.all_eq_true.mp all _ hc
  · rintro ⟨B,all⟩
    let A : Assignment := fun v => B (code F v)
    refine ⟨A,List.all_eq_true.mpr ?_⟩
    intro c hc
    obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp hc
    let j : Fin F.length := ⟨i,hi⟩
    have h := shape c hc
    subst c
    change F[i].any (Literal.eval A)=true
    rw [← padded _ h.1 h.2]
    exact all j

#print axioms formal

end PackedThreeSAT
