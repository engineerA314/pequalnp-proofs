import CleanPreparation

/-! Count all incident pairs admitting a two-variable-leaf accepting parse
in an arbitrary shared DAG. A positive parse may repeat input occurrences,
and different parses at the same edge can have different costs. -/

namespace CleanEdges

open CleanWitness CleanPreparation SharedOrStars SingleLevelStars
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.Helpers

variable {V : Type} [Fintype V] [DecidableEq V]

def shortEdges (E : Finset (Finset V)) (C : Circuit) (inputs : List V) :=
  E.filter fun e => minimum C inputs e = .two

def pairs (R : Finset (Term V)) : Finset (Finset V) :=
  R.biUnion fun t => t.1.biUnion fun a => t.2.image fun b => ({a,b} : Finset V)

omit [Fintype V] in
theorem mem_pairs (R : Finset (Term V)) (e : Finset V) : e ∈ pairs R ↔
    ∃ t ∈ R, ∃ a ∈ t.1, ∃ b ∈ t.2, ({a,b} : Finset V) = e := by simp [pairs]

theorem count_terms (G : Finset (Finset V)) (linear : ∀ c d, c≠d → (neighbors G c ∩ neighbors G d).card≤1)
    (raw : List (Finset V)) (atomic : ∀ j, (raw.getD j ∅).card≤1) (prep : List OrGate)
    (R : Finset (Term V)) (present : ∀ t ∈ R, t.1 ∈ run prep raw ∧ t.2 ∈ run prep raw)
    (valid : ∀ t ∈ R, ∀ a ∈ t.1, ∀ b ∈ t.2, {a,b} ∈ G) :
    (pairs R).card ≤ prep.length+R.card := by
  classical
  let T := R.filter fun t => t.1.Nonempty ∧ t.2.Nonempty
  have star (i : {j // j ∈ T}) : ∃ c j, (run prep raw).getD j ∅ ⊆ neighbors G c ∧
      ∀ a ∈ i.val.1, ∀ b ∈ i.val.2, ∃ v ∈ (run prep raw).getD j ∅, ({a,b} : Finset V)={c,v} := by
    obtain ⟨inR,A,B⟩ := Finset.mem_filter.mp i.property
    obtain ⟨hasA,hasB⟩ := present i.val inR
    rcases rectangle_is_star G linear _ _ A B (valid i.val inR) with ⟨c,eq,sub⟩ | ⟨c,eq,sub⟩
    · obtain ⟨j,hj⟩ := get_of_mem _ _ hasB
      refine ⟨c,j,hj ▸ sub,?_⟩
      intro a ha b hb
      rw [eq,Finset.mem_singleton] at ha
      exact ⟨b,hj ▸ hb,by rw [ha]⟩
    · obtain ⟨j,hj⟩ := get_of_mem _ _ hasA
      refine ⟨c,j,hj ▸ sub,?_⟩
      intro a ha b hb
      rw [eq,Finset.mem_singleton] at hb
      exact ⟨a,hj ▸ ha,by rw [hb,Finset.pair_comm a c]⟩
  choose center arm contained includes using star
  have cover (e : Finset V) (he : e ∈ pairs R) : ∃ i ∈ (Finset.univ : Finset {j // j ∈ T}),
      ∃ v ∈ (run prep raw).getD (arm i) ∅, e={center i,v} := by
    obtain ⟨t,ht,a,ha,b,hb,rfl⟩ := (mem_pairs R e).mp he
    let i : {j // j ∈ T} := ⟨t,Finset.mem_filter.mpr ⟨ht,⟨a,ha⟩,⟨b,hb⟩⟩⟩
    exact ⟨i,Finset.mem_univ _,includes i a ha b hb⟩
  have cost := cover_cost (neighbors G) linear (pairs R) prep raw atomic Finset.univ center arm (fun i _ => contained i) cover
  have size : T.card≤R.card := Finset.card_le_card (Finset.filter_subset _ _)
  simp only [Finset.card_univ,Fintype.card_coe] at cost
  omega

omit [Fintype V] in
theorem hits_of_mem (A X : Finset V) {v : V} (ha : v ∈ A) (hx : v ∈ X) : hits A X = true :=
  decide_eq_true ⟨v,Finset.mem_inter.mpr ⟨ha,hx⟩⟩

/-- Under just the singleton and nonedge-pair rejections, the binary gate
count bounds how many actual edges can have a two-leaf parse. All wire
sharing, arbitrary AND depth, nullary constants and missing reads are allowed. -/
theorem bound (G : Finset (Finset V)) (simple : ∀ e ∈ G, e.card=2)
    (linear : ∀ c d, c≠d → (neighbors G c ∩ neighbors G d).card≤1)
    (C : Circuit) (inputs : List V) (mono : IsMonotoneCircuit C) (fan : ∀ g ∈ C.gates, g.inputs.length≤2)
    (sound : ∀ a b : V, {a,b} ∉ G → C.eval (inputs.map fun v => decide (v ∈ ({a,b} : Finset V))) = false) :
    (shortEdges G C inputs).card ≤ C.size := by
  classical
  obtain ⟨prep,present,cost⟩ := extract C inputs
  cases h : summarize C inputs with
  | unit =>
    have empty : shortEdges G C inputs = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      have good := (Finset.mem_filter.mp he).2
      rw [← weight_eq_minimum,h] at good
      contradiction
    simp [empty]
  | data A R =>
    have valid (t : Term V) (ht : t ∈ R) (a : V) (ha : a ∈ t.1) (b : V) (hb : b ∈ t.2) : {a,b} ∈ G := by
      by_contra negative
      have on : fires R {a,b}=true := decide_eq_true ⟨t,ht,hits_of_mem _ _ ha (by simp),hits_of_mem _ _ hb (by simp)⟩
      have cheap : minimum C inputs {a,b} ≠ .many := by
        rw [← weight_eq_minimum,h]
        cases atLeastOne : hits A {a,b} <;> simp [weight,atLeastOne,on]
      have yes := minimum_sound C inputs {a,b} mono fan cheap
      rw [sound a b negative] at yes
      contradiction
    have sub : shortEdges G C inputs ⊆ pairs R := by
      intro e he
      obtain ⟨inG,cheap⟩ := Finset.mem_filter.mp he
      rw [← weight_eq_minimum,h] at cheap
      have on : fires R e = true := by
        cases ha : hits A e <;> cases hh : fires R e <;> simp_all [weight]
      obtain ⟨t,ht,oa,ob⟩ := of_decide_eq_true on
      obtain ⟨a,ha⟩ := of_decide_eq_true oa
      obtain ⟨b,hb⟩ := of_decide_eq_true ob
      obtain ⟨aA,ae⟩ := Finset.mem_inter.mp ha
      obtain ⟨bB,be⟩ := Finset.mem_inter.mp hb
      have small : ({a,b} : Finset V)⊆e := Finset.insert_subset ae (Finset.singleton_subset_iff.mpr be)
      have equal := Finset.eq_of_subset_of_card_le small (by rw [simple e inG,simple _ (valid t ht a aA b bB)])
      exact (mem_pairs R e).mpr ⟨t,ht,a,aA,b,bB,equal⟩
    rw [h] at present cost
    exact (Finset.card_le_card sub).trans ((count_terms G linear _ (atomic inputs) prep R present valid).trans cost)

#print axioms bound

end CleanEdges
