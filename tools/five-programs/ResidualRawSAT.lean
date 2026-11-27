import ResidualStateCount
import ClauseCliqueSAT

namespace ResidualRawSAT

open Finset PEqualNP.Search ResidualAntichain ResidualStateCount ClauseCliqueSAT

variable {n : ℕ}

def clause (formula : CNF) (e : ↥(vars formula) ≃ Fin n) (c : Clause) : C (Fin n) :=
  univ.filter (fun l => ((e.symm l.1).val,l.2)∈c)

def indexed (formula : CNF) (e : ↥(vars formula) ≃ Fin n) : Form n :=
  (formula.map (clause formula e)).toFinset

theorem equiv_sat (formula : CNF) (e : ↥(vars formula) ≃ Fin n) (x : Fin n → Bool) :
    sat x (indexed formula e) ↔ CNF.eval (ClauseCliqueSAT.extend formula (fun v => x (e v))) formula=true := by
  constructor
  · intro h
    apply List.all_eq_true.mpr
    intro c hc
    have inF : clause formula e c∈indexed formula e := List.mem_toFinset.mpr (List.mem_map_of_mem hc)
    obtain ⟨⟨i,s⟩,mem,yes⟩ := h _ inF
    have occ : ((e.symm i).val,s)∈c := (Finset.mem_filter.mp mem).2
    apply List.any_eq_true.mpr
    refine ⟨_,occ,?_⟩
    simpa [Literal.eval,ClauseCliqueSAT.extend,(e.symm i).property] using (show decide (x i=s)=true from decide_eq_true yes)
  · intro h C hc
    obtain ⟨c,inc,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hc)
    obtain ⟨⟨v,s⟩,mem,yes⟩ := List.any_eq_true.mp (List.all_eq_true.mp h c inc)
    have confirmed : v∈vars formula := occurs formula inc mem
    let i := e ⟨v,confirmed⟩
    refine ⟨(i,s),Finset.mem_filter.mpr ⟨mem_univ _,?_⟩,?_⟩
    · simpa [i] using mem
    · simpa [i,Literal.eval,ClauseCliqueSAT.extend,confirmed] using yes

theorem count_card (f : Form n) :
    ResidualStateCount.count f=(univ.filter (fun x : Fin n → Bool => sat x f)).card := by
  classical
  simp [ResidualStateCount.count,Finset.sum_boole]

theorem word_count (formula : CNF) (e : ↥(vars formula) ≃ Fin n) :
    run n (Finsupp.single (normal (indexed formula e)) 1)=(modelsF formula).card := by
  classical
  rw [exact_count,count_card]
  let b : (Fin n → Bool) ≃ (↥(vars formula) → Bool) :=
    { toFun := fun x v => x (e v)
      invFun := fun y i => y (e.symm i)
      left_inv := fun x => by funext i; simp
      right_inv := fun y => by funext v; simp }
  let iso := b.subtypeEquiv (p := fun x => sat x (indexed formula e))
    (q := fun y => CNF.eval (ClauseCliqueSAT.extend formula y) formula=true) (equiv_sat formula e)
  simpa only [Fintype.card_subtype,modelsF] using Fintype.card_congr iso

noncomputable def result (formula : CNF) : ℕ :=
  let e := Fintype.equivFin ↥(vars formula)
  run _ (Finsupp.single (normal (indexed formula e)) 1)

theorem word (w : List Bool) :
    (∃ formula,CNFReader.parse w=some formula ∧ 0<result formula) ↔ w∈SAT := by
  have id (formula : CNF) : result formula=(modelsF formula).card := word_count _ _
  simp only [id]
  exact ClauseCliqueSAT.word w

#print axioms word_count
#print axioms word

end ResidualRawSAT
