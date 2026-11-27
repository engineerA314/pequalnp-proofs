import SparseRows
import LineForks

/-! Row-specific accounting on the original circuit. Constants, copies and any
gate having the same cofactor function as an earlier wire have zero cost. -/

namespace WireFrontier

open PartialSums SparseFrontier SparseRows ReversePath CleanWitness
open PEqualNP.CircuitLowerBounds

variable {P : Type} [Fintype P] [DecidableEq P]

def palette (W : List (Signal P)) := zero :: one :: W

noncomputable def bill (b radius : ℕ) (R : Finset P) (g : Gate) (W : List (Signal P)) : ℕ := by
  classical
  let h := baseGate g W
  exact if h∈palette W then 0 else fee b R h radius

noncomputable def total (b radius : ℕ) (R : Finset P) : List Gate → List (Signal P) → ℕ
  | [],_ => 0
  | g::gs,W => bill b radius R g W + total b radius R gs (W++[baseGate g W])

theorem read_available (W : List (Signal P)) (i : ℕ) : W.getD i zero∈palette W := by
  by_cases hi : i<W.length
  · simp [palette,List.getD_eq_getElem?_getD,hi,List.getElem_mem]
  · simp [palette,List.getD_eq_getElem?_getD,hi]

theorem new_binary (g : Gate) (W : List (Signal P)) (fresh : baseGate g W ∉ palette W) :
    ∃ d a e, a∈palette W ∧ e∈palette W ∧ baseGate g W=combine d a e := by
  have z : zero∈palette W := by simp [palette]
  have o : one∈palette W := by simp [palette]
  obtain ⟨op,ins⟩ := g
  cases op <;> cases ins with
  | nil => first | exact False.elim (fresh z) | exact False.elim (fresh o)
  | cons i more =>
    cases more with
    | nil => first | exact False.elim (fresh z) | exact False.elim (fresh (read_available W i))
    | cons j tail =>
      cases tail with
      | nil =>
        first
        | exact False.elim (fresh z)
        | exact ⟨true,_,_,read_available W i,read_available W j,rfl⟩
        | exact ⟨false,_,_,read_available W i,read_available W j,rfl⟩
      | cons _ _ => exact False.elim (fresh z)

def State (b radius : ℕ) (R : Finset P) (W : List (Signal P)) (c : ℕ) :=
  Frontier b R (palette W) c radius ∧ ∀ h ∈ palette W, Mono h

theorem advance (b radius : ℕ) (R : Finset P) (W : List (Signal P)) (c : ℕ) (g : Gate)
    (old : State b radius R W c) :
    State b radius R (W++[baseGate g W]) (c+bill b radius R g W) := by
  classical
  let h := baseGate g W
  have eq : palette (W++[h]) = palette W ++ [h] := rfl
  change Frontier b R (palette (W++[h])) (c+bill b radius R g W) radius ∧ _
  rw [eq]
  by_cases haveH : h ∈ palette W
  · have cost : bill b radius R g W=0 := if_pos haveH
    rw [cost,Nat.add_zero]
    constructor
    · intro T avail
      have prev : Available (palette W) T := by
        intro f hf
        rcases List.mem_append.mp (avail f hf) with existing | last
        · exact existing
        · exact (List.mem_singleton.mp last) ▸ haveH
      obtain ⟨F,af,remaining,cap,rel⟩ := old.1 T prev
      exact ⟨F,fun f hf => List.mem_append_left _ (af f hf),remaining,cap,rel⟩
    · intro f hf
      rcases List.mem_append.mp hf with earlier | last
      · exact old.2 f earlier
      · exact (List.mem_singleton.mp last) ▸ old.2 h haveH
  · obtain ⟨d,a,e,aa,ee,hEq⟩ := new_binary g W haveH
    have cost : bill b radius R g W=fee b R h radius := if_neg haveH
    change h=combine d a e at hEq
    rw [cost,hEq]
    constructor
    · exact SparseFrontier.step b radius R (palette W) c old.1 d a e aa ee
    · intro f hf
      rcases List.mem_append.mp hf with earlier | last
      · exact old.2 f earlier
      · rw [List.mem_singleton.mp last]
        intro X Y sub
        exact combine_mono d a e X Y (old.2 a aa X Y sub) (old.2 e ee X Y sub)

theorem propagate (b radius : ℕ) (R : Finset P) (gs : List Gate) (W : List (Signal P)) (c : ℕ)
    (old : State b radius R W c) :
    State b radius R (scan zero one plus times gs W) (c+total b radius R gs W) := by
  induction gs generalizing W c with
  | nil => simpa [scan,total] using old
  | cons g gs ih =>
    have later := ih _ _ (advance b radius R W c g old)
    simpa only [scan,total,Nat.add_assoc,baseGate] using later

theorem start (b radius : ℕ) (pos : 1≤b) (R : Finset P) (W : List (Signal P))
    (raw : ∀ f∈W, IsRaw f) : State b radius R W 0 := by
  classical
  have allRaw : ∀ f∈palette W, IsRaw f := by
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact Or.inl rfl
    rcases List.mem_cons.mp hf with rfl | hf
    · exact Or.inr (Or.inl rfl)
    · exact raw f hf
  refine ⟨?_,mono _ 0 (Built.raw _ allRaw)⟩
  intro T av
  exact ⟨T,av,fun f hf => raw_terminal b pos R f (allRaw f (av f hf)) radius,by simp,fun _ _ z => z⟩

def finalSignal (C : Circuit) (W : List (Signal P)) := (scan zero one plus times C.gates W).getD C.output zero

theorem physical (b radius t : ℕ) (pos : 1≤b) (R : Finset P) (C : Circuit) (W : List (Signal P))
    (raw : ∀ f ∈ W, IsRaw f) (off : Rejects R t (finalSignal C W))
    (enough : radius*(total b radius R C.gates W+1)≤t) :
    (single (finalSignal C W)).card≤b*(total b radius R C.gates W+1) := by
  let after := scan zero one plus times C.gates W
  let c := total b radius R C.gates W
  have done : State b radius R after c := by simpa [after,c] using propagate b radius R C.gates W 0 (start b radius pos R W raw)
  exact cut_row_radius b t radius R (finalSignal C W) off (palette after) c done.2
    (read_available after C.output) done.1 enough

#print axioms physical

end WireFrontier
