import GraphStreamWords
import PackedThreeSAT

namespace GraphStreamForm

open ThreeColourGadgets PEqualNP.Search GraphStreamWords WordMachine PEqualNP.Library.SearchHelpers.SatV

def tokens (F : CNF) : List (Option Literal) := F.flatMap fun c => c.map some++[none]
def tokenWord : Option Literal → W
  | none => [false,false]
  | some l => encodeLiteral l

theorem token_code (F : CNF) : (tokens F).flatMap tokenWord=encodeCNF F := by
  induction F with
  | nil => rfl
  | cons c F ih =>
    change ((c.map some++[none])++tokens F).flatMap tokenWord=encodeClause c++encodeCNF F
    simp [List.flatMap_append,List.flatMap_map,ih,tokenWord,encodeClause]

theorem progress (l : Option Literal) (rest : W) : dropI (tokenWord l++rest)=rest := by
  cases l with
  | none => rfl
  | some l => exact dropI_lit l rest

theorem drop_tokens (j : ℕ) (ts : List (Option Literal)) :
    dropI^[j] (ts.flatMap tokenWord)=(ts.drop j).flatMap tokenWord := by
  induction j generalizing ts with
  | zero => simp
  | succ j ih =>
    cases ts with
    | nil => simpa using dropI_iter_nil (j+1)
    | cons l ts => rw [Function.iterate_succ_apply,List.flatMap_cons,progress,ih]; rfl

theorem count_tokens (ts : List (Option Literal)) : ts.length≤(ts.flatMap tokenWord).length := by
  induction ts with
  | nil => simp
  | cons o ts ih =>
    have one : 1≤(tokenWord o).length := by cases o <;> simp [tokenWord,encodeLiteral]
    simp only [List.length_cons,List.flatMap_cons,List.length_append]; omega

theorem occurs (F : CNF) (c : Clause) (l : Literal) (hc : c∈F) (hl : l∈c) :
    vcode l.1∈keys (encodeCNF F) := by
  have ht : some l∈tokens F :=
    List.mem_flatMap.mpr ⟨c,hc,List.mem_append_left _ (List.mem_map_of_mem hl)⟩
  obtain ⟨j,hj,atJ⟩ := List.mem_iff_getElem.mp ht
  have bound := count_tokens (tokens F)
  rw [token_code] at bound
  refine List.mem_map.mpr ⟨j,List.mem_range.mpr (by omega),?_⟩
  rw [key,item,← token_code,drop_tokens,List.drop_eq_getElem_cons hj,atJ,List.flatMap_cons]
  change (headI (encodeLiteral l++_)).drop 2=_
  rw [headI_lit,encodeLiteral_eq]
  rfl

abbrev B (w : W) := w.length+1
def dummy (w : W) : Fin (B w) := ⟨w.length,Nat.lt_succ_self _⟩
def label (w code : W) : Fin (B w) := ⟨addr w code,Nat.lt_succ_of_le (by
  have h : (keys w).idxOf code≤(keys w).length := List.idxOf_le_length
  simpa [addr,keys] using h)⟩

def parsed (w raw : W) : Fin (B w) × Bool := (label w (raw.drop 2),raw.getD 1 false)
def rawAt (r : W) (p : Fin 3) : W :=
  let a := headI r
  let r1 := dropI r
  let b := if isEnd r1 then a else headI r1
  let r2 := dropI r1
  let c := if isEnd r1 || isEnd r2 then b else headI r2
  three a b c p

def pos (w : W) (i : ℕ) (p : Fin 3) : Fin (B w) × Bool :=
  let r := clauseAt i w
  if i=w.length then (dummy w,false)
  else if r=[] then (dummy w,decide (p=1))
  else if isEnd r then (dummy w,true)
  else parsed w (rawAt r p)

def streamed (w : W) : Form (B w) (B w) := fun i p => pos w i.val p

theorem typed (w : W) (l : Literal) :
    parsed w (encodeLiteral l)=(label w (vcode l.1),l.2) := by rw [encodeLiteral_eq]; rfl

theorem good_end (tail : W) : isEnd (false::false::tail)=true := rfl

theorem clause_word (c : Clause) (tail : W) (short : c.length≤3) (live : c≠[]) :
    ∀ p,rawAt (encodeClause c++tail) p=encodeLiteral (PackedThreeSAT.pad c p) := by
  rcases c with _|⟨a,_|⟨b,_|⟨k,_|⟨e,l⟩⟩⟩⟩
  · contradiction
  · intro p
    simp [rawAt,encodeClause,List.append_assoc,headI_lit,dropI_lit,good_end,PackedThreeSAT.pad]
    fin_cases p <;> rfl
  · intro p
    simp [rawAt,encodeClause,List.append_assoc,headI_lit,dropI_lit,isEnd_lit,good_end,PackedThreeSAT.pad]
    fin_cases p <;> rfl
  · intro p
    simp [rawAt,encodeClause,List.append_assoc,headI_lit,dropI_lit,isEnd_lit,PackedThreeSAT.pad]
    fin_cases p <;> rfl
  · simp at short; omega

end GraphStreamForm
