import ClauseCliqueBound
import CNFReader

namespace ClauseCliqueSAT

open PEqualNP.Search ClauseSubcubes

def vars (F : CNF) : Finset ℕ := (F.flatMap (fun c => c.map Prod.fst)).toFinset

theorem occurs (F : CNF) {c : Clause} {l : Literal} (hc : c∈F) (hl : l∈c) : l.1∈vars F := by
  simp only [vars,List.mem_toFinset,List.mem_flatMap,List.mem_map]
  exact ⟨c,hc,l,hl,rfl⟩

def extend (F : CNF) (x : ↥(vars F) → Bool) (v : ℕ) : Bool :=
  if h : v∈vars F then x ⟨v,h⟩ else false

def mask (F : CNF) (i : Fin F.length) : Cube ↥(vars F) :=
  Finset.univ.filter (fun p => (p.1.val,!p.2)∈F[i])

theorem fits_false (F : CNF) (i : Fin F.length) (x : ↥(vars F) → Bool) :
    Fits (mask F i) x ↔ Clause.eval (extend F x) F[i]=false := by
  constructor
  · intro fits
    apply List.any_eq_false.mpr
    intro l hl
    have mem := occurs F (List.getElem_mem _) hl
    have eq := fits ⟨l.1,mem⟩ (!l.2) (by simpa [mask] using hl)
    simp [Literal.eval,extend,mem,eq]
  · intro no v b h
    have pair : (v.val,!b)∈F[i] := (Finset.mem_filter.mp h).2
    have e := List.any_eq_false.mp no _ pair
    simp only [Literal.eval,extend,v.property,dite_true] at e
    cases b <;> cases val : x v <;> simp_all

noncomputable def modelsF (F : CNF) : Finset (↥(vars F) → Bool) := by
  classical exact Finset.univ.filter (fun x => CNF.eval (extend F x) F=true)

theorem surviving (F : CNF) : modelsF F=(Finset.univ : Finset (Fin F.length)).inf
    (fun i => (models (mask F i))ᶜ) := by
  classical
  ext x
  simp only [modelsF,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_inf,
    Finset.mem_compl,mem_models,fits_false,Bool.not_eq_false]
  constructor
  · intro h i _
    exact List.all_eq_true.mp h F[i] (List.getElem_mem _)
  · intro h
    apply List.all_eq_true.mpr
    intro c hc
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hc
    exact h ⟨i,hi⟩ trivial

theorem count (F : CNF) : ((modelsF F).card : ℤ)=
    ∑ t ∈ ClauseCliqueBound.cliques (mask F) Finset.univ,
      (-1:ℤ)^t.card*(2^((vars F).card-(coords (t.biUnion (mask F))).card):ℕ) := by
  classical
  rw [surviving]
  simpa [ClauseCliqueBound.cliques] using ClauseSubcubes.count (mask F) Finset.univ

theorem nonempty (F : CNF) : (modelsF F).Nonempty ↔ Satisfiable F := by
  classical
  constructor
  · rintro ⟨x,h⟩
    exact ⟨extend F x,(Finset.mem_filter.mp h).2⟩
  · rintro ⟨A,on⟩
    let x := fun v : ↥(vars F) => A v.val
    refine ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,List.all_eq_true.mpr ?_⟩⟩
    intro c hc
    obtain ⟨l,hl,yes⟩ := List.any_eq_true.mp (List.all_eq_true.mp on c hc)
    refine List.any_eq_true.mpr ⟨l,hl,?_⟩
    simpa [Literal.eval,extend,x,occurs F hc hl] using yes

noncomputable def accepts (w : List Bool) : Prop := ∃ F,CNFReader.parse w=some F ∧ 0<(modelsF F).card

theorem word (w : List Bool) : accepts w ↔ w∈SAT := by
  constructor
  · rintro ⟨F,read,n⟩
    exact ⟨F,(CNFReader.parse_iff _ _).mp read,(nonempty F).mp (Finset.card_pos.mp n)⟩
  · rintro ⟨F,eq,sat⟩
    exact ⟨F,(CNFReader.parse_iff _ _).mpr eq,Finset.card_pos.mpr ((nonempty F).mpr sat)⟩

#print axioms count
#print axioms word

end ClauseCliqueSAT
