import AndTranscript
import Mathlib.Tactic

/-! At a zero input, each single-bit change that switches a monotone circuit
on needs access to a leaf in its false-output trace. At AND gates we can follow
one false operand, so only binary OR gates can branch in this trace. -/

namespace OrSensitivity

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.Helpers AndTranscript

def charge (g : Gate) : ℕ := match g.op with
  | .or => if g.inputs.length = 2 then 1 else 0
  | _ => 0

def orCount : List Gate → ℕ
  | [] => 0
  | g :: gs => charge g + orCount gs

theorem counts_disjoint (gs : List Gate) : orCount gs + count gs ≤ gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨op,ins⟩ := g
    cases op <;> cases ins with
    | nil => simp [orCount,charge,count,tap]; omega
    | cons i tail =>
      cases tail with
      | nil => simp [orCount,charge,count,tap]; omega
      | cons j tail => cases tail <;> simp [orCount,charge,count,tap] <;> omega

private theorem all_on (ins : List ℕ) (x : List Bool) :
    GateOp.and.eval (ins.map fun i => x.getD i false) = true ↔ ∀ i ∈ ins, x.getD i false = true := by
  simp [GateOp.eval, List.all_eq_true]

private theorem any_on (ins : List ℕ) (x : List Bool) :
    GateOp.or.eval (ins.map fun i => x.getD i false) = true ↔ ∃ i ∈ ins, x.getD i false = true := by
  simp [GateOp.eval, List.any_eq_true]

/-- Once the zero-input values are fixed, at most one reader is needed at an
AND and at most two are needed at an OR for every positive perturbation. -/
theorem route (g : Gate) (mono : g.op = .and ∨ g.op = .or) (fan : g.inputs.length ≤ 2)
    (y : List Bool) : ∃ S : Finset ℕ, S.card ≤ charge g + 1 ∧
    ∀ x : List Bool, value g y = false → value g x = true →
      ∃ j ∈ S, y.getD j false = false ∧ x.getD j false = true := by
  classical
  obtain ⟨op,ins⟩ := g
  rcases mono with rfl | rfl
  · by_cases all : GateOp.and.eval (ins.map fun i => y.getD i false) = true
    · refine ⟨∅,by simp,?_⟩
      intro x off
      change GateOp.and.eval _ = false at off
      rw [all] at off
      contradiction
    · have h : ¬ ∀ i ∈ ins, y.getD i false = true := fun h => all ((all_on ins y).mpr h)
      push Not at h
      obtain ⟨i,hi,off⟩ := h
      refine ⟨{i},by simp,?_⟩
      intro x _ on
      exact ⟨i,by simp,by simpa using off, (all_on ins x).mp on i hi⟩
  · refine ⟨ins.toFinset,?_,?_⟩
    · have bound := List.toFinset_card_le ins
      change ins.length ≤ 2 at fan
      by_cases h : ins.length = 2 <;> simp [charge,h] <;> omega
    · intro x off on
      obtain ⟨i,hi,one⟩ := (any_on ins x).mp on
      refine ⟨i,List.mem_toFinset.mpr hi,?_,one⟩
      cases hy : y.getD i false with
      | false => rfl
      | true =>
        have yes := (any_on ins y).mpr ⟨i,hi,hy⟩
        change GateOp.or.eval _ = false at off
        rw [yes] at off
        contradiction

variable {m : ℕ}

def changes (y : List Bool) (X : Fin m → List Bool) (j : ℕ) : Finset (Fin m) :=
  Finset.univ.filter fun i => y.getD j false = false ∧ (X i).getD j false = true

def Bound (t : ℕ) (y : List Bool) (X : Fin m → List Bool) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion (changes y X)).card ≤ t + W.card

theorem bound_step (g : Gate) (mono : g.op = .and ∨ g.op = .or) (fan : g.inputs.length ≤ 2)
    (y : List Bool) (X : Fin m → List Bool) (len : ∀ i, (X i).length = y.length)
    (t : ℕ) (old : Bound t y X) : Bound (t + charge g) (emit g y) (fun i => emit g (X i)) := by
  classical
  obtain ⟨S,small,routes⟩ := route g mono fan y
  intro W
  let new := changes (emit g y) (fun i => emit g (X i))
  have earlier (j : ℕ) (hj : j ≠ y.length) : new j = changes y X j := by
    ext i
    have neq : j ≠ (X i).length := by rw [len]; exact hj
    simp only [new,changes,Finset.mem_filter,emit,getD_snoc_ne _ _ _ _ hj,getD_snoc_ne _ _ _ _ neq]
  by_cases used : y.length ∈ W
  · have sub : W.biUnion new ⊆ (W.erase y.length ∪ S).biUnion (changes y X) := by
      intro i hi
      obtain ⟨j,hj,hit⟩ := Finset.mem_biUnion.mp hi
      by_cases atNew : j = y.length
      · subst j
        obtain ⟨off,on⟩ := (Finset.mem_filter.mp hit).2
        unfold emit at off on
        rw [getD_snoc_eq] at off
        rw [← len i, getD_snoc_eq] at on
        obtain ⟨k,hk,ky,kx⟩ := routes (X i) off on
        exact Finset.mem_biUnion.mpr ⟨k,Finset.mem_union_right _ hk,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _,ky,kx⟩⟩
      · rw [earlier j atNew] at hit
        exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨atNew,hj⟩),hit⟩
    have pos := Finset.card_pos.mpr ⟨_,used⟩
    have unionBound := Finset.card_union_le (W.erase y.length) S
    rw [Finset.card_erase_of_mem used] at unionBound
    have h := old (W.erase y.length ∪ S)
    have h' := Finset.card_le_card sub
    change (W.biUnion new).card ≤ _
    omega
  · have e : W.biUnion new = W.biUnion (changes y X) :=
      Finset.biUnion_congr rfl fun j hj => earlier j (fun eq => used (eq ▸ hj))
    change (W.biUnion new).card ≤ _
    rw [e]
    have := old W
    omega

theorem bound_wires (gs : List Gate) (mono : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (fan : ∀ g ∈ gs, g.inputs.length ≤ 2) (y : List Bool) (X : Fin m → List Bool)
    (len : ∀ i, (X i).length = y.length) (t : ℕ) (start : Bound t y X) :
    Bound (t+orCount gs) (wiresFrom gs y) (fun i => wiresFrom gs (X i)) := by
  induction gs generalizing y X t with
  | nil => simpa [orCount,wiresFrom] using start
  | cons g gs ih =>
    have h := ih (fun k hk => mono k (by simp [hk])) (fun k hk => fan k (by simp [hk]))
      (emit g y) (fun i => emit g (X i)) (fun i => by simp [emit,len]) (t+charge g)
      (bound_step g (mono g (by simp)) (fan g (by simp)) y X len t start)
    change Bound (t+(charge g+orCount gs)) (wiresFrom gs (emit g y)) (fun i => wiresFrom gs (emit g (X i)))
    rwa [← Nat.add_assoc]

theorem positive_sensitivity (C : Circuit) (mono : IsMonotoneCircuit C)
    (fan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (x : Fin m → Bool) (T : Finset (Fin m))
    (off : C.eval (List.ofFn x) = false)
    (on : ∀ i ∈ T, C.eval (List.ofFn (Function.update x i true)) = true) :
    T.card ≤ orCount C.gates + 1 := by
  classical
  let y := List.ofFn x
  let X (i : Fin m) := List.ofFn (Function.update x i true)
  have start : Bound 0 y X := by
    intro W
    apply le_trans Finset.card_biUnion_le
    rw [zero_add,Finset.card_eq_sum_ones]
    apply Finset.sum_le_sum
    intro j _
    apply Finset.card_le_one.mpr
    have val (i : Fin m) (hit : i ∈ changes y X j) : i.val = j := by
      obtain ⟨h0,h1⟩ := (Finset.mem_filter.mp hit).2
      by_cases valid : j < m
      · by_contra ne
        have diff : (⟨j,valid⟩ : Fin m) ≠ i := fun eq => ne (congrArg Fin.val eq).symm
        simp [X,List.getD_eq_getElem?_getD,valid,Function.update_of_ne diff] at h1
        simp [y,List.getD_eq_getElem?_getD,valid] at h0
        rw [h1] at h0
        contradiction
      · rw [List.getD_eq_default _ _ (by simp [X]; omega)] at h1
        contradiction
    intro a ha b hb
    exact Fin.ext ((val a ha).trans (val b hb).symm)
  have all := bound_wires C.gates mono fan y X (by simp [X,y]) 0 start {C.output}
  simp only [Finset.singleton_biUnion,zero_add,Finset.card_singleton] at all
  apply le_trans (Finset.card_le_card ?_) all
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,off,on i hi⟩

#print axioms positive_sensitivity

end OrSensitivity
