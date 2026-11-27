import PEqualNP.MetaComplexity.Helpers.Support
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi

/-! One bit for each distinct binary AND gate suffices to distinguish every
pair of rejected inputs whose coordinatewise union contains a positive test.
Inputs can be an arbitrary encoding of a circuit boundary. The same gate is
recorded once even when several later gates read it. -/

namespace AndTranscript

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.Helpers

def tap (g : Gate) : Option ℕ :=
  match g.op, g.inputs with
  | .and, [i, _] => some i
  | _, _ => none

def count : List Gate → ℕ
  | [] => 0
  | g :: gs => match tap g with
    | some _ => count gs + 1
    | none => count gs

def value (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def emit (g : Gate) (w : List Bool) : List Bool := w ++ [value g w]

/-- Record the first child's value at binary ANDs during the ordinary gate fold. -/
def sig : List Gate → List Bool → List Bool
  | [], _ => []
  | g :: gs, w =>
    match tap g with
    | some i => w.getD i false :: sig gs (emit g w)
    | none => sig gs (emit g w)

theorem sig_length (gs : List Gate) (x : List Bool) : (sig gs x).length = count gs := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih => cases h : tap g <;> simp [sig, count, h, ih]

/-- The positive assignment is coordinatewise below the union of the other two. -/
def Covered (x y z : List Bool) : Prop :=
  x.length = y.length ∧ y.length = z.length ∧
    ∀ i, x.getD i false = true → y.getD i false = true ∨ z.getD i false = true

private theorem or_on (ins : List ℕ) (w : List Bool) :
    GateOp.or.eval (ins.map fun i => w.getD i false) = true ↔ ∃ i ∈ ins, w.getD i false = true := by
  simp [GateOp.eval, List.any_eq_true]

private theorem gate_covers (g : Gate) (mono : g.op = .and ∨ g.op = .or)
    (fan : g.inputs.length ≤ 2) (x y z : List Bool) (cov : Covered x y z)
    (agree : ∀ i, tap g = some i → y.getD i false = z.getD i false) :
    value g x = true → value g y = true ∨ value g z = true := by
  obtain ⟨op, ins⟩ := g
  change op = .and ∨ op = .or at mono
  rcases mono with rfl | rfl
  · cases ins with
    | nil => simp [value, GateOp.eval]
    | cons i tail =>
      cases tail with
      | nil => simpa [value, GateOp.eval] using cov.2.2 i
      | cons j tail =>
        cases tail with
        | cons t rest => simp at fan
        | nil =>
          have same := agree i rfl
          simp only [value, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
            List.all_nil, Bool.and_true, Bool.and_eq_true, id]
          rintro ⟨xi,xj⟩
          have left := cov.2.2 i xi
          have yi : y.getD i false = true := left.elim id fun zi => same.trans zi
          have zi : z.getD i false = true := same.symm.trans yi
          rcases cov.2.2 j xj with yj | zj
          · exact Or.inl ⟨yi,yj⟩
          · exact Or.inr ⟨zi,zj⟩
  · simp only [value, or_on]
    rintro ⟨i,hi,on⟩
    rcases cov.2.2 i on with yi | zi
    · exact Or.inl ⟨i,hi,yi⟩
    · exact Or.inr ⟨i,hi,zi⟩

private theorem step_covers (g : Gate) (mono : g.op = .and ∨ g.op = .or)
    (fan : g.inputs.length ≤ 2) (x y z : List Bool) (cov : Covered x y z)
    (agree : ∀ i, tap g = some i → y.getD i false = z.getD i false) :
    Covered (emit g x) (emit g y) (emit g z) := by
  obtain ⟨hxy,hyz,reads⟩ := cov
  refine ⟨by simp [emit,hxy], by simp [emit,hyz], ?_⟩
  intro i
  unfold emit
  by_cases h : i = x.length
  · subst i
    rw [getD_snoc_eq,hxy,getD_snoc_eq,hyz,getD_snoc_eq]
    exact gate_covers g mono fan x y z ⟨hxy,hyz,reads⟩ agree
  · rw [getD_snoc_ne _ _ _ _ h, getD_snoc_ne _ _ _ _ (by omega),
        getD_snoc_ne _ _ _ _ (by omega)]
    exact reads i

theorem wires_covered (gs : List Gate) (x y z : List Bool) (cov : Covered x y z)
    (mono : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) (fan : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (same : sig gs y = sig gs z) :
    Covered (wiresFrom gs x) (wiresFrom gs y) (wiresFrom gs z) := by
  induction gs generalizing x y z with
  | nil => exact cov
  | cons g gs ih =>
    have agree : ∀ i, tap g = some i → y.getD i false = z.getD i false := by
      intro i read
      simp only [sig,read,List.cons.injEq] at same
      exact same.1
    have tail : sig gs (emit g y) = sig gs (emit g z) := by
      cases read : tap g with
      | none => simpa only [sig,read] using same
      | some i =>
        simp only [sig,read,List.cons.injEq] at same
        exact same.2
    exact ih _ _ _ (step_covers g (mono g (by simp)) (fan g (by simp)) x y z cov agree)
      (fun t ht => mono t (by simp [ht])) (fun t ht => fan t (by simp [ht])) tail

/-- A pairwise incompatible family of rejected boundary inputs requires at
least log base two of its size in binary AND gates in the downstream circuit. -/
theorem incompatible_count {ι : Type*} (F : Finset ι) (negative : ι → List Bool) (C : Circuit)
    (mono : IsMonotoneCircuit C) (fan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (off : ∀ j ∈ F, C.eval (negative j) = false)
    (pair : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → ∃ x, C.eval x = true ∧ Covered x (negative i) (negative j)) :
    F.card ≤ 2 ^ count C.gates := by
  classical
  let code (j : {i // i ∈ F}) (k : Fin (count C.gates)) : Bool :=
    (sig C.gates (negative j.val)).getD k false
  have inject : Function.Injective code := by
    intro i j eq
    by_contra ne
    have diff : i.val ≠ j.val := fun e => ne (Subtype.ext e)
    obtain ⟨x,on,cov⟩ := pair i.val i.property j.val j.property diff
    have same : sig C.gates (negative i.val) = sig C.gates (negative j.val) := by
      apply List.ext_getElem (by simp [sig_length])
      intro k hi hj
      have hk : k < count C.gates := by simpa [sig_length] using hi
      have eqbit := congrFun eq ⟨k,hk⟩
      simpa [code,List.getD_eq_getElem?_getD,hi,hj] using eqbit
    have values := (wires_covered C.gates _ _ _ cov mono fan same).2.2 C.output on
    change C.eval (negative i.val) = true ∨ C.eval (negative j.val) = true at values
    rw [off i.val i.property,off j.val j.property] at values
    simp at values
  simpa using Fintype.card_le_of_injective code inject

#print axioms incompatible_count

end AndTranscript
