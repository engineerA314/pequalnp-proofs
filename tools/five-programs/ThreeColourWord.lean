import CNFReader
import PackedThreeSAT
import ThreeColourMatrix

/-! Functions on raw bit strings for the project's two languages. -/
namespace ThreeColourWord

open PEqualNP.Search PackedThreeSAT ThreeColourMatrix

def rejectWord : List Bool := [true]

theorem rejected : ¬Accepted rejectWord := by
  rintro ⟨n,len,c,good⟩
  change 1=n*n at len
  have one : n=1 := by nlinarith
  subst n
  exact (good 0 0 (by decide) (by decide) rfl) rfl

def encodeGraph (F : CNF) := if regular F then word (form F) else rejectWord
def reduce (w : List Bool) := ((CNFReader.parse w).map encodeGraph).getD rejectWord

theorem formula (F : CNF) : (IsKCNF 3 F ∧ Satisfiable F) ↔ Accepted (encodeGraph F) := by
  by_cases ok : regular F=true
  · simp only [encodeGraph,ok,ite_true,← matrix_iff,← formal F ok]
    exact and_iff_right (fun c hc => ((regular_iff F).mp ok c hc).2)
  · have off : regular F=false := Bool.eq_false_iff.mpr ok
    simp only [encodeGraph,off,Bool.false_eq_true,ite_false]
    exact ⟨fun h => False.elim (ok (sat_regular F h.1 h.2)),fun h => False.elim (rejected h)⟩

theorem language (w : List Bool) : w∈KSAT 3 ↔ Accepted (reduce w) := by
  cases read : CNFReader.parse w with
  | none =>
    have invalid := (CNFReader.rejects w).mp read
    simp only [reduce,read,Option.map_none,Option.getD_none]
    constructor
    · rintro ⟨F,_,eq,_⟩
      exact False.elim (invalid F eq)
    · exact fun h => False.elim (rejected h)
  | some F =>
    simp only [reduce,read,Option.map_some,Option.getD_some,← formula]
    constructor
    · rintro ⟨G,small,eq,sat⟩
      have same := (CNFReader.parse_iff w G).mpr eq
      rw [read] at same
      exact Option.some.inj same ▸ ⟨small,sat⟩
    · rintro ⟨small,sat⟩
      exact ⟨F,small,(CNFReader.parse_iff w F).mp read,sat⟩

def occurrences (F : CNF) := (F.flatMap fun c => c.map Prod.fst).length

theorem literals_cost (c : Clause) : 4*c.length≤(c.flatMap encodeLiteral).length := by
  induction c with
  | nil => simp
  | cons l c ih =>
    have four : 4≤(encodeLiteral l).length := by simp [encodeLiteral]
    simp only [List.length_cons,List.flatMap_cons,List.length_append]
    omega

theorem input_cost (F : CNF) : 4*occurrences F+2*F.length≤(encodeCNF F).length := by
  induction F with
  | nil => simp [occurrences,encodeCNF]
  | cons c F ih =>
    have cost := literals_cost c
    simp only [occurrences,List.flatMap_cons,List.length_append,List.length_map] at ih ⊢
    simp only [encodeCNF,List.flatMap_cons,List.length_append,encodeClause,List.length_cons,List.length_nil] at ih ⊢
    omega

theorem output_bound (w : List Bool) : (reduce w).length≤(5+4*w.length)^2 := by
  cases read : CNFReader.parse w with
  | none => simp [reduce,read,rejectWord]; nlinarith [Nat.zero_le w.length]
  | some F =>
    have input := input_cost F
    have eq := (CNFReader.parse_iff w F).mp read
    rw [eq] at input
    have den : (names F).length≤occurrences F := List.Sublist.length_le (List.dedup_sublist _)
    by_cases good : regular F=true
    · simp only [reduce,read,Option.map_some,Option.getD_some,encodeGraph,good,ite_true,word_length]
      have linear : side ((names F).length+1) F.length≤5+4*w.length := by unfold side; omega
      simpa only [pow_two] using Nat.mul_le_mul linear linear
    · simp [reduce,read,encodeGraph,good,rejectWord]; nlinarith [Nat.zero_le w.length]

#print axioms language
#print axioms output_bound

end ThreeColourWord
