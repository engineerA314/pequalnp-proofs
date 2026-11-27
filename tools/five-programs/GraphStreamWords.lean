import WordMachine
import PEqualNP.Library.SearchHelpers.KSatHard
import PEqualNP.Library.SearchHelpers.KSatNP

namespace GraphStreamWords

open PEqualNP.Search PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.SatV PEqualNP.Library.SearchHelpers.Tab.StepW WordMachine
open PEqualNP.Library.SearchHelpers.KSat.Hard (cpt_dropI cpt_headI)

def skip : W → W
  | false::false::r => r
  | _::_::r => skip r
  | _ => []

inductive ScanState | edge | data | mark | copy
  deriving DecidableEq

instance : Fintype ScanState := ⟨{.edge,.data,.mark,.copy},by intro s; cases s <;> simp⟩

def transition : ScanState → Bool → ScanState × Option Bool
  | .edge,true => (.data,none)
  | .edge,false => (.mark,none)
  | .data,_ => (.edge,none)
  | .mark,true => (.edge,none)
  | .mark,false => (.copy,none)
  | .copy,b => (.copy,some b)

theorem copies (w : W) : fstRun transition (fun _ => none) .copy w=w := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [fstRun,transition,ih]

theorem skip_machine : ∀ w : W, fstRun transition (fun _ => none) .edge w=skip w
  | [] => rfl
  | [b] => by cases b <;> rfl
  | false::false::w => by simp [fstRun,transition,skip,copies]
  | false::true::w => by simp [fstRun,transition,skip,skip_machine w]
  | true::b::w => by simp [fstRun,transition,skip,skip_machine w]

theorem skipCPT : CPT skip := fst_polyTime _ _ _ transition (fun _ => none) .edge (fun w => (skip_machine w).symm)

theorem skip_length : ∀ w : W, (skip w).length≤w.length
  | [] => by decide
  | [a] => by cases a <;> decide
  | false::false::r => by simp [skip]; omega
  | false::true::r => by have := skip_length r; simp [skip]; omega
  | true::a::r => by have := skip_length r; simp [skip]; omega

theorem skip_digits (ds r : W) : skip ((ds.flatMap fun b => [true,b])++r)=skip r := by
  induction ds with
  | nil => rfl
  | cons b ds ih => simp [skip,ih]

theorem skip_literal (l : Literal) (rest : W) : skip (encodeLiteral l++rest)=skip rest := by
  simp [encodeLiteral,List.append_assoc,skip,skip_digits]

theorem skip_clause (c : Clause) (tail : W) : skip (encodeClause c++tail)=tail := by
  induction c with
  | nil => simp [encodeClause,skip]
  | cons l c ih =>
    have eq : encodeClause (l::c)++tail=encodeLiteral l++(encodeClause c++tail) := by simp [encodeClause,List.append_assoc]
    rw [eq,skip_literal,ih]

def clauseAt (i : ℕ) (w : W) := skip^[i] w
def item (i : ℕ) (w : W) := headI (dropI^[i] w)
def key (i : ℕ) (w : W) := (item i w).drop 2
def keys (w : W) := (List.range w.length).map fun i => key i w
def addr (w tag : W) := (keys w).idxOf tag

theorem clause_drop : ∀ i (F : CNF), clauseAt i (encodeCNF F)=encodeCNF (F.drop i)
  | 0,F => by simp [clauseAt]
  | i+1,[] => by simp [clauseAt,encodeCNF,Function.iterate_succ_apply,skip]
                 simpa [clauseAt,encodeCNF] using clause_drop i []
  | i+1,c::F => by
    rw [clauseAt,Function.iterate_succ_apply]
    change skip^[i] (skip (encodeClause c++encodeCNF F))=_
    rw [skip_clause]
    exact clause_drop i F

theorem clauseCPT {idx w : W → W} (hi : CPT idx) (hw : CPT w) :
    CPT (fun s => clauseAt (idx s).length (w s)) := cpt_iterLen skipCPT skip_length hi hw

theorem itemCPT {idx w : W → W} (hi : CPT idx) (hw : CPT w) :
    CPT (fun s => item (idx s).length (w s)) := cpt_comp (cpt_iterLen cpt_dropI dropI_length hi hw) cpt_headI

theorem keyCPT {idx w : W → W} (hi : CPT idx) (hw : CPT w) :
    CPT (fun s => key (idx s).length (w s)) := by
  refine changeF (cpt_tail1 (cpt_tail1 (itemCPT hi hw))) ?_
  intro s
  unfold key
  cases item (idx s).length (w s) with
  | nil => rfl
  | cons h t => cases t <;> rfl

theorem oneBit {p : W → Bool} (h : Effective p) : CPT (fun s => [p s]) := by
  refine changeF (cpt_sel h (cpt_const [false]) (cpt_const [true])) ?_
  intro s
  cases p s <;> rfl

theorem until_eq (xs : List W) (tag : W) :
    hd (xs.map fun a => decide (a≠tag))=un (xs.idxOf tag) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    by_cases eq : a=tag
    · subst a
      simp [hd,un]
    · simpa [hd,un,eq,List.replicate_succ] using congrArg (List.cons true) ih

theorem flatOne {A B : Type} (xs : List A) (f : A → B) :
    xs.flatMap (fun a => [f a])=xs.map f := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [ih]

theorem addrCPT {w tag : W → W} (hw : CPT w) (ht : CPT tag) :
    CPT (fun s => un (addr (w s) (tag s))) := by
  have test := neg (eqWords (keyCPT cpt_unpairB1 (cpt_comp cpt_unpairB2 hw)) (cpt_comp cpt_unpairB2 ht))
  have list := cpt_flatMapRange (oneBit test) hw cpt_id
  refine changeF (cpt_comp list cpt_hd) ?_
  intro s
  simp only [unpairB_pairB,un_length,flatOne]
  simpa [addr,keys,List.map_map,Function.comp_def] using until_eq (keys (w s)) (tag s)

end GraphStreamWords
