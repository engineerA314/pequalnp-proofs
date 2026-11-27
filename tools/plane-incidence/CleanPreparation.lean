import CleanWitness

/-! A shared Boolean circuit can prepare the operands of all its two-leaf
products in one OR network. Each original gate creates at most one preparation
OR or adds one product to the pool, even in the presence of constants. -/

namespace CleanPreparation

open CleanWitness SharedOrStars PEqualNP.CircuitLowerBounds

variable {V : Type} [DecidableEq V]

omit [DecidableEq V] in
theorem get_of_mem (S : List (Finset V)) (A : Finset V) (h : A ∈ S) : ∃ i, S.getD i ∅=A := by
  obtain ⟨i,e⟩ := List.mem_iff_get.mp h
  exact ⟨i,by simpa [List.getD_eq_getElem?_getD,i.isLt] using e⟩

theorem run_append (a b : List OrGate) (S : List (Finset V)) : run (a++b) S=run b (run a S) := by
  induction a generalizing S with
  | nil => rfl
  | cons g gs ih => exact ih (S++[joined S g])

def Ready (S : List (Finset V)) (P : Finset (Term V)) (w : Summary V) : Prop :=
  w.atoms ∈ S ∧ w.terms ⊆ P

structure Inventory (raw : List (Finset V)) (W : List (Summary V)) (spent : ℕ) where
  prep : List OrGate
  pool : Finset (Term V)
  empty : ∅ ∈ run prep raw
  wires : ∀ w ∈ W, Ready (run prep raw) pool w
  arms : ∀ t ∈ pool, t.1 ∈ run prep raw ∧ t.2 ∈ run prep raw
  cost : prep.length+pool.card ≤ spent

variable {raw : List (Finset V)} {W : List (Summary V)} {spent : ℕ}

theorem read (inv : Inventory raw W spent) (j : ℕ) : Ready (run inv.prep raw) inv.pool (W.getD j .bottom) := by
  by_cases hj : j < W.length
  · apply inv.wires
    simp [List.getD_eq_getElem?_getD,hj]
  · simpa [List.getD_eq_getElem?_getD,hj,Ready,Summary.bottom,Summary.atoms,Summary.terms] using inv.empty

theorem reuse (inv : Inventory raw W spent) (w : Summary V) (hw : Ready (run inv.prep raw) inv.pool w) :
    Nonempty (Inventory raw (W++[w]) (spent+1)) := by
  refine ⟨{inv with wires := ?_, cost := inv.cost.trans (Nat.le_succ _)}⟩
  intro u hu
  rcases List.mem_append.mp hu with h | h
  · exact inv.wires u h
  · have e : u=w := by simpa using h
    exact e ▸ hw

theorem sum (inv : Inventory raw W spent) (a b : Summary V)
    (ha : Ready (run inv.prep raw) inv.pool a) (hb : Ready (run inv.prep raw) inv.pool b) :
    Nonempty (Inventory raw (W++[a.plus b]) (spent+1)) := by
  cases a with
  | unit => exact reuse inv _ ha
  | data A R =>
    cases b with
    | unit => exact reuse inv _ hb
    | data B T =>
      obtain ⟨i,hi⟩ := get_of_mem _ A ha.1
      obtain ⟨j,hj⟩ := get_of_mem _ B hb.1
      let prep := inv.prep++[(i,j)]
      have eq : run prep raw = run inv.prep raw ++ [A∪B] := by simp only [prep,run_append,run,joined,hi,hj]
      have keep (U : Finset V) (mem : U ∈ run inv.prep raw) : U ∈ run prep raw := by simp [eq,mem]
      refine ⟨⟨prep,inv.pool,keep _ inv.empty,?_,?_,?_⟩⟩
      · intro w hw
        rcases List.mem_append.mp hw with old | new
        · exact ⟨keep _ (inv.wires w old).1,(inv.wires w old).2⟩
        · simp only [List.mem_singleton] at new
          subst w
          exact ⟨by simp [eq,Summary.plus,Summary.atoms],Finset.union_subset ha.2 hb.2⟩
      · exact fun t ht => ⟨keep _ (inv.arms t ht).1,keep _ (inv.arms t ht).2⟩
      · have h := inv.cost
        simp [prep]; omega

theorem product (inv : Inventory raw W spent) (a b : Summary V)
    (ha : Ready (run inv.prep raw) inv.pool a) (hb : Ready (run inv.prep raw) inv.pool b) :
    Nonempty (Inventory raw (W++[a.times b]) (spent+1)) := by
  cases a with
  | unit => exact reuse inv _ hb
  | data A R =>
    cases b with
    | unit => exact reuse inv _ ha
    | data B T =>
      let pool := insert (A,B) inv.pool
      have older : inv.pool ⊆ pool := Finset.subset_insert _ _
      refine ⟨⟨inv.prep,pool,inv.empty,?_,?_,?_⟩⟩
      · intro w hw
        rcases List.mem_append.mp hw with old | new
        · exact ⟨(inv.wires w old).1,(inv.wires w old).2.trans older⟩
        · simp only [List.mem_singleton] at new
          subst w
          exact ⟨inv.empty,by simp [pool,Summary.times,Summary.terms]⟩
      · intro t ht
        rcases Finset.mem_insert.mp ht with rfl | h
        · exact ⟨ha.1,hb.1⟩
        · exact inv.arms t h
      · have h := inv.cost
        have : pool.card ≤ inv.pool.card+1 := Finset.card_insert_le _ _
        omega

theorem step (inv : Inventory raw W spent) (g : Gate) :
    Nonempty (Inventory raw (W++[gate Summary.bottom .unit Summary.plus Summary.times g W]) (spent+1)) := by
  have bot : Ready (run inv.prep raw) inv.pool .bottom := ⟨inv.empty,Finset.empty_subset _⟩
  have unit : Ready (run inv.prep raw) inv.pool .unit := ⟨inv.empty,Finset.empty_subset _⟩
  obtain ⟨op,ins⟩ := g
  cases op <;> cases ins with
  | nil => exact reuse inv _ unit
  | cons i tail =>
    cases tail with
    | nil => first | exact reuse inv _ (read inv i) | exact reuse inv _ bot
    | cons j tail =>
      cases tail with
      | nil => first | exact sum inv _ _ (read inv i) (read inv j) | exact product inv _ _ (read inv i) (read inv j) | exact reuse inv _ bot
      | cons _ _ => exact reuse inv _ bot

theorem advance (gs : List Gate) (inv : Inventory raw W spent) :
    Nonempty (Inventory raw (scan Summary.bottom .unit Summary.plus Summary.times gs W) (spent+gs.length)) := by
  induction gs generalizing W spent with
  | nil => exact ⟨inv⟩
  | cons g gs ih =>
    obtain ⟨next⟩ := step inv g
    simpa [scan,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih next

def rawOf (inputs : List V) : List (Finset V) := ∅ :: inputs.map fun v => {v}

omit [DecidableEq V] in
theorem atomic (inputs : List V) (j : ℕ) : ((rawOf inputs).getD j ∅).card≤1 := by
  cases j with
  | zero => simp [rawOf,List.getD]
  | succ j =>
    simp only [rawOf,List.getD_cons_succ]
    cases h : inputs[j]? with
    | none => simp [List.getD_eq_getElem?_getD,h]
    | some v => simp [List.getD_eq_getElem?_getD,h]

def initial (inputs : List V) : Inventory (rawOf inputs) (inputs.map Summary.atom) 0 where
  prep := []
  pool := ∅
  empty := by simp [run,rawOf]
  wires := by
    intro w hw
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
    exact ⟨by simp [run,rawOf,Summary.atom,Summary.atoms,hv],Finset.empty_subset _⟩
  arms := by simp
  cost := by simp

/-- One shared preparation and the output products fit in the original gate budget. -/
theorem extract (C : Circuit) (inputs : List V) :
    ∃ prep : List OrGate, (∀ t ∈ (summarize C inputs).terms,
      t.1 ∈ run prep (rawOf inputs) ∧ t.2 ∈ run prep (rawOf inputs)) ∧
      prep.length+(summarize C inputs).terms.card ≤ C.size := by
  obtain ⟨inv⟩ := advance C.gates (initial inputs)
  have ready := read inv C.output
  have bound := Finset.card_le_card ready.2
  have cost := inv.cost
  refine ⟨inv.prep,fun t ht => inv.arms t (ready.2 ht),?_⟩
  change inv.prep.length + (summarize C inputs).terms.card ≤ C.gates.length
  change (summarize C inputs).terms.card ≤ inv.pool.card at bound
  omega

#print axioms extract

end CleanPreparation
