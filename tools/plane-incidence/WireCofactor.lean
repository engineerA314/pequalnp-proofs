import AnchoredBoundary

/-! A sound constant-and-support checker for every wire of a binary circuit.
After a restriction a live wire can be point-only or line-only. Unsupported
operators conservatively receive the mixed label. -/

namespace WireCofactor

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.Helpers AndTranscript

inductive Kind | zero | one | points | lines | mixed deriving DecidableEq, Repr

variable {α β : Type*}

def Sound (k : Kind) (f : α → β → Bool) : Prop := match k with
  | .zero => ∀ x y, f x y = false
  | .one => ∀ x y, f x y = true
  | .points => ∀ x y z, f x y = f x z
  | .lines => ∀ x x' y, f x y = f x' y
  | .mixed => True

def andTag : Kind → Kind → Kind
  | .zero,_ | _,.zero => .zero
  | .one,k | k,.one => k
  | .points,.points => .points
  | .lines,.lines => .lines
  | _,_ => .mixed

def orTag : Kind → Kind → Kind
  | .one,_ | _,.one => .one
  | .zero,k | k,.zero => k
  | .points,.points => .points
  | .lines,.lines => .lines
  | _,_ => .mixed

theorem and_sound (k l : Kind) (f h : α → β → Bool) (a : Sound k f) (b : Sound l h) :
    Sound (andTag k l) (fun x y => f x y && h x y) := by
  cases k <;> cases l <;> simp only [andTag,Sound] at * <;>
    solve | simp [a,b] | simpa [a] using b | simpa [b] using a | intro x y z; rw [a x y z,b x y z]

theorem or_sound (k l : Kind) (f h : α → β → Bool) (a : Sound k f) (b : Sound l h) :
    Sound (orTag k l) (fun x y => f x y || h x y) := by
  cases k <;> cases l <;> simp only [orTag,Sound] at * <;>
    solve | simp [a,b] | simpa [a] using b | simpa [b] using a | intro x y z; rw [a x y z,b x y z]

def tag (g : Gate) (S : List Kind) : Kind := match g.op,g.inputs with
  | .and,[] => .one
  | .or,[] => .zero
  | .and,[i] | .or,[i] => S.getD i .zero
  | .and,[i,j] => andTag (S.getD i .zero) (S.getD j .zero)
  | .or,[i,j] => orTag (S.getD i .zero) (S.getD j .zero)
  | _,_ => .mixed

def check (S : List Kind) (gs : List Gate) := gs.foldl (fun T g => T ++ [tag g T]) S

def Valid (S : List Kind) (w : α → β → List Bool) : Prop :=
  (∀ x y, (w x y).length = S.length) ∧ ∀ j, Sound (S.getD j .zero) (fun x y => (w x y).getD j false)

theorem tag_sound (g : Gate) (S : List Kind) (w : α → β → List Bool) (valid : Valid S w) :
    Sound (tag g S) (fun x y => value g (w x y)) := by
  obtain ⟨op,ins⟩ := g
  cases op with
  | not => simp [tag,Sound]
  | mod _ => trivial
  | maj => trivial
  | and =>
    cases ins with
    | nil => simp [tag,Sound,value,GateOp.eval]
    | cons i tail =>
      cases tail with
      | nil => simpa only [tag,value,GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.all_nil,
            Bool.and_true,id_eq] using valid.2 i
      | cons j tail =>
        cases tail with
        | nil => simpa only [tag,value,GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.all_nil,
            Bool.and_true,id_eq] using and_sound _ _ _ _ (valid.2 i) (valid.2 j)
        | cons _ _ => trivial
  | or =>
    cases ins with
    | nil => simp [tag,Sound,value,GateOp.eval]
    | cons i tail =>
      cases tail with
      | nil => simpa only [tag,value,GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,
            Bool.or_false,id_eq] using valid.2 i
      | cons j tail =>
        cases tail with
        | nil => simpa only [tag,value,GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,
            Bool.or_false,id_eq] using or_sound _ _ _ _ (valid.2 i) (valid.2 j)
        | cons _ _ => trivial

theorem check_sound (gs : List Gate) (S : List Kind) (w : α → β → List Bool) (valid : Valid S w) :
    Valid (check S gs) (fun x y => wiresFrom gs (w x y)) := by
  induction gs generalizing S w with
  | nil => exact valid
  | cons g gs ih =>
    apply ih (S ++ [tag g S]) (fun x y => emit g (w x y))
    refine ⟨fun x y => by simp [emit,valid.1 x y],?_⟩
    intro j
    by_cases last : j = S.length
    · subst j
      rw [getD_snoc_eq]
      have eq : (fun x y => (emit g (w x y)).getD S.length false) = fun x y => value g (w x y) := by
        funext x y
        rw [← valid.1 x y]
        exact getD_snoc_eq _ _ _
      rw [eq]
      exact tag_sound g S w valid
    · rw [getD_snoc_ne _ _ _ _ last]
      have eq : (fun x y => (emit g (w x y)).getD j false) = fun x y => (w x y).getD j false := by
        funext x y
        exact getD_snoc_ne _ _ _ _ (by rw [valid.1]; exact last)
      rw [eq]
      exact valid.2 j

/-- A successful run certifies the hypothesis on all positive and negative
assignments with the anchor, for any chosen output indices, including every
wire at once. Monotonicity of the unrestricted circuit is a separate premise
of the boundary theorem. -/
theorem certifies_split {P L d : ℕ} (R : Finset (Fin L)) (B : AnchoredBoundary.Features P L d)
    (gs : List Gate) (S : List Kind) (w : Finset (Fin P) → {Y : Finset (Fin L) // R ⊆ Y} → List Bool)
    (valid : Valid S w) (index : Fin d → ℕ)
    (models : ∀ i X Y (h : R ⊆ Y), B X Y i = (wiresFrom gs (w X ⟨Y,h⟩)).getD (index i) false)
    (clean : ∀ i, (check S gs).getD (index i) .zero ≠ .mixed) : AnchoredBoundary.Splits B R := by
  intro i
  have h := (check_sound gs S w valid).2 (index i)
  cases ht : (check S gs).getD (index i) .zero with
  | mixed => exact False.elim (clean i ht)
  | zero =>
    rw [ht] at h
    exact Or.inl fun X Y Z ry rz => (models i X Y ry).trans ((h X ⟨Y,ry⟩).trans
      ((h X ⟨Z,rz⟩).symm.trans (models i X Z rz).symm))
  | one =>
    rw [ht] at h
    exact Or.inl fun X Y Z ry rz => (models i X Y ry).trans ((h X ⟨Y,ry⟩).trans
      ((h X ⟨Z,rz⟩).symm.trans (models i X Z rz).symm))
  | points =>
    rw [ht] at h
    exact Or.inl fun X Y Z ry rz => (models i X Y ry).trans ((h X ⟨Y,ry⟩ ⟨Z,rz⟩).trans (models i X Z rz).symm)
  | lines =>
    rw [ht] at h
    exact Or.inr fun X X' Y ry => (models i X Y ry).trans ((h X X' ⟨Y,ry⟩).trans (models i X' Y ry).symm)

#print axioms check_sound
#print axioms certifies_split

end WireCofactor
