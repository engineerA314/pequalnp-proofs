import PlaneLineOnce

/-! Detect a concrete obstruction to line-linear propagation: both operands
of the same binary AND rise when the selected line is switched on. -/

namespace LineForks

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.Helpers
open PartialSums CleanWitness ReversePath
variable {P : Type}

def rises (W : List (Signal P)) (x : List Bool) (X : Finset P) (i : ℕ) :=
  !(W.getD i zero X) && x.getD i false

def fork (g : Gate) (W : List (Signal P)) (x : List Bool) (X : Finset P) := match g.op,g.inputs with
  | .and,[i,j] => rises W x X i && rises W x X j
  | _,_ => false

def anyFork : List Gate → List (Signal P) → List Bool → Finset P → Bool
  | [],_,_,_ => false
  | g::gs,W,x,X => fork g W x X || anyFork gs (W++[baseGate g W]) (x++[actualGate g x]) X

theorem split_gate (g : Gate) (W : List (Signal P)) (D x : List Bool) (X : Finset P)
    (parts : ∀ j, x.getD j false=true → W.getD j zero X=true ∨ D.getD j false=true)
    (noFork : fork g W x X=false) :
    actualGate g x=true → baseGate g W X=true ∨ marker (arcs g W) D X=true := by
  obtain ⟨op,ins⟩ := g
  cases op <;> cases ins with
  | nil => simp [actualGate,gate,baseGate,one,zero]
  | cons i tail =>
    cases tail with
    | nil =>
      simp only [actualGate,gate,baseGate,arcs,marker,List.any_cons,List.any_nil,
        one,zero,Bool.and_true,Bool.or_false]
      all_goals first | exact parts i | simp
    | cons j tail =>
      cases tail with
      | cons _ _ => simp [actualGate,gate]
      | nil =>
        have hi := parts i
        have hj := parts j
        cases ai : W.getD i zero X <;> cases aj : W.getD j zero X <;>
          cases xi : x.getD i false <;> cases xj : x.getD j false <;>
          simp_all [fork,rises,actualGate,gate,baseGate,arcs,marker,plus,times,one,zero,List.getD_eq_getElem?_getD]


theorem all_split (gs : List Gate) (W : List (Signal P)) (D x : List Bool) (X : Finset P)
    (len : W.length=x.length) (ld : D.length=x.length)
    (parts : ∀ j, x.getD j false=true → W.getD j zero X=true ∨ D.getD j false=true)
    (noFork : anyFork gs W x X=false) : ∀ j,
    (scan false true (· || ·) (· && ·) gs x).getD j false=true →
    (scan zero one plus times gs W).getD j zero X=true ∨ (marks gs W D X).getD j false=true := by
  induction gs generalizing W D x with
  | nil => exact parts
  | cons g gs ih =>
    obtain ⟨no,tail⟩ := Bool.or_eq_false_iff.mp noFork
    apply ih _ _ _ (by simp [len]) (by simp [ld]) _ tail
    intro j
    by_cases last : j=x.length
    · subst j
      rw [getD_snoc_eq,← len,getD_snoc_eq,len,← ld,getD_snoc_eq]
      exact split_gate g W D x X parts no
    · rw [getD_snoc_ne _ _ _ _ last,getD_snoc_ne _ _ _ _ (by omega),getD_snoc_ne _ _ _ _ (by omega)]
      exact parts j

theorem actual_scan (gs : List Gate) (x : List Bool) (ops : ∀ g ∈ gs, g.op=.and ∨ g.op=.or)
    (fan : ∀ g ∈ gs, g.inputs.length≤2) :
    scan false true (· || ·) (· && ·) gs x=wiresFrom gs x := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    change scan _ _ _ _ gs (x++[actualGate g x])=wiresFrom gs (x++[AndTranscript.value g x])
    rw [project_gate g x (ops g (by simp)) (fan g (by simp))]
    exact ih _ (fun g hg => ops g (by simp [hg])) (fun g hg => fan g (by simp [hg]))

theorem base_output (C : Circuit) (W : List (Signal P)) (X : Finset P) (ops : IsMonotoneCircuit C)
    (fan : ∀ g ∈ C.gates, g.inputs.length≤2) :
    (scan zero one plus times C.gates W).getD C.output zero X = C.eval (W.map fun f => f X) := by
  let f (h : Signal P) := h X
  change f ((scan _ _ _ _ _ _).getD C.output zero)=_
  rw [← getD_map f]
  rw [scan_map f zero one plus times (· || ·) (· && ·) (fun _ _ => rfl) (fun _ _ => rfl)]
  change (scan false true _ _ C.gates _).getD C.output false=_
  rw [actual_scan C.gates _ ops fan]
  rfl

/-- If the output first becomes true when input j is enabled, either its
single-mark reverse flag is on or some AND has both operands rise. -/
theorem fork_or_flag (C : Circuit) (W : List (Signal P)) (x : List Bool) (X : Finset P) (j : ℕ)
    (ops : IsMonotoneCircuit C) (fan : ∀ g ∈ C.gates, g.inputs.length≤2) (len : W.length=x.length)
    (parts : ∀ i, x.getD i false=true → W.getD i zero X=true ∨ i=j)
    (off : C.eval (W.map fun f => f X)=false) (on : C.eval x=true) :
    anyFork C.gates W x X=true ∨ pull C.gates W C.output j X=true := by
  cases h : anyFork C.gates W x X with
  | true => exact Or.inl rfl
  | false =>
    right
    let D := List.ofFn (fun i : Fin x.length => decide (i.val=j))
    have ld : D.length=x.length := by simp [D]
    have marked (i : ℕ) : x.getD i false=true → W.getD i zero X=true ∨ D.getD i false=true := by
      intro hi
      rcases parts i hi with base | eq
      · exact Or.inl base
      · have atInput : i < x.length := by
          by_contra no; rw [List.getD_eq_default _ _ (by omega)] at hi; contradiction
        subst j
        exact Or.inr (by simp [D,List.getD_eq_getElem?_getD,atInput])
    have yes : (scan false true (· || ·) (· && ·) C.gates x).getD C.output false=true := by
      rw [actual_scan C.gates x ops fan]; exact on
    have next := all_split C.gates W D x X len ld marked h C.output yes
    rw [base_output C W X ops fan,off] at next
    have good := next.resolve_left (by simp)
    obtain ⟨i,hi,di,flag⟩ := (dual C.gates W D (len.trans ld.symm) X C.output).mpr good
    have atInput : i < x.length := by simpa [D] using hi
    have eq : i=j := by simpa [D,List.getD_eq_getElem?_getD,atInput] using di
    exact eq ▸ flag

#print axioms fork_or_flag

end LineForks
