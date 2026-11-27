import PartialSums

/-! Transpose the single-mark reachability relation of a binary gate DAG.
The gain on an AND edge is the sibling's value with all line inputs off.
Both positions of a repeated operand stay in the list. -/

namespace ReversePath

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.Helpers CleanWitness PartialSums
variable {P : Type}

abbrev Adjoints (P : Type) := ℕ → Signal P
abbrev Arcs (P : Type) := List (ℕ × Signal P)

def arcs (g : Gate) (W : List (Signal P)) : Arcs P :=
  match g.op,g.inputs with
  | .and,[i] | .or,[i] => [(i,one)]
  | .or,[i,j] => [(i,one),(j,one)]
  | .and,[i,j] => [(i,W.getD j zero),(j,W.getD i zero)]
  | _,_ => []

def scatter : Arcs P → Signal P → Adjoints P → Adjoints P
  | [],_,B => B
  | (i,a)::rest,d,B => fun j =>
    if j=i then plus (scatter rest d B j) (times d a) else scatter rest d B j

def seed (out : ℕ) : Adjoints P := fun j => if j=out then one else zero
def baseGate (g : Gate) (W : List (Signal P)) : Signal P := gate zero one plus times g W

def pull : List Gate → List (Signal P) → ℕ → Adjoints P
  | [],_,out => seed out
  | g::gs,W,out =>
    let B := pull gs (W++[baseGate g W]) out
    scatter (arcs g W) (B W.length) B

def marker (A : Arcs P) (D : List Bool) (X : Finset P) :=
  A.any fun t => D.getD t.1 false && t.2 X

def marks : List Gate → List (Signal P) → List Bool → Finset P → List Bool
  | [],_,D,_ => D
  | g::gs,W,D,X => marks gs (W++[baseGate g W]) (D++[marker (arcs g W) D X]) X

theorem marker_iff (A : Arcs P) (D : List Bool) (X : Finset P) :
    marker A D X=true ↔ ∃ t ∈ A, D.getD t.1 false=true ∧ t.2 X=true := by
  simp [marker,List.any_eq_true]

theorem scatter_iff (A : Arcs P) (d : Signal P) (B : Adjoints P) (j : ℕ) (X : Finset P) :
    scatter A d B j X=true ↔ B j X=true ∨ ∃ a : Signal P, (j,a) ∈ A ∧ d X=true ∧ a X=true := by
  induction A with
  | nil => simp [scatter]
  | cons t A ih =>
    obtain ⟨i,a⟩ := t
    by_cases eq : j=i
    · subst i
      simp only [scatter,ite_true,plus,times,Bool.or_eq_true,Bool.and_eq_true,ih,List.mem_cons,Prod.mk.injEq,true_and]
      aesop
    · simp [scatter,eq,ih]

def inner (D : List Bool) (B : Adjoints P) (X : Finset P) : Prop :=
  ∃ j, j < D.length ∧ D.getD j false=true ∧ B j X=true

theorem mark_step (A : Arcs P) (D : List Bool) (B : Adjoints P) (X : Finset P) :
    inner D (scatter A (B D.length) B) X ↔ inner (D++[marker A D X]) B X := by
  constructor
  · rintro ⟨j,hj,dj,bj⟩
    rcases (scatter_iff A (B D.length) B j X).mp bj with before | ⟨a,inA,bd,ax⟩
    · exact ⟨j,by simp; omega,by rwa [getD_snoc_ne _ _ _ _ (by omega)],before⟩
    · have yes := (marker_iff A D X).mpr ⟨(j,a),inA,dj,ax⟩
      exact ⟨D.length,by simp,by simpa only [getD_snoc_eq] using yes,bd⟩
  · rintro ⟨j,hj,dj,bj⟩
    by_cases last : j=D.length
    · subst j
      rw [getD_snoc_eq] at dj
      obtain ⟨⟨i,a⟩,inA,di,ax⟩ := (marker_iff A D X).mp dj
      have hi : i < D.length := by
        by_contra no
        rw [List.getD_eq_default _ _ (by omega)] at di
        contradiction
      exact ⟨i,hi,di,(scatter_iff A (B D.length) B i X).mpr (Or.inr ⟨a,inA,bj,ax⟩)⟩
    · simp only [List.length_append,List.length_singleton] at hj
      exact ⟨j,by omega,by rwa [getD_snoc_ne _ _ _ _ last] at dj,
        (scatter_iff A (B D.length) B j X).mpr (Or.inl bj)⟩

theorem dual (gs : List Gate) (W : List (Signal P)) (D : List Bool) (len : W.length=D.length)
    (X : Finset P) (out : ℕ) : inner D (pull gs W out) X ↔ (marks gs W D X).getD out false=true := by
  induction gs generalizing W D with
  | nil =>
    constructor
    · rintro ⟨j,_,dj,bj⟩
      by_cases e : j=out
      · exact e ▸ dj
      · simp [pull,seed,e,zero] at bj
    · intro hit
      have h : out < D.length := by
        by_contra no
        change D.getD out false=true at hit
        rw [List.getD_eq_default _ _ (by omega : D.length≤out)] at hit
        contradiction
      exact ⟨out,h,hit,by simp [pull,seed,one]⟩
  | cons g gs ih =>
    simp only [pull,marks]
    let B := pull gs (W++[baseGate g W]) out
    change inner D (scatter (arcs g W) (B W.length) B) X ↔ _
    rw [len,mark_step]
    exact ih _ _ (by simp [len])

def actualGate (g : Gate) (x : List Bool) := gate false true (· || ·) (· && ·) g x

theorem project_gate (g : Gate) (x : List Bool) (mono : g.op=.and ∨ g.op=.or) (fan : g.inputs.length≤2) :
    actualGate g x = AndTranscript.value g x := by
  obtain ⟨op,ins⟩ := g
  rcases mono with rfl | rfl <;> cases ins with
  | nil => simp [actualGate,gate,AndTranscript.value,GateOp.eval]
  | cons i tail =>
    cases tail with
    | nil => simp [actualGate,gate,AndTranscript.value,GateOp.eval]
    | cons j tail => cases tail <;> simp_all [actualGate,gate,AndTranscript.value,GateOp.eval]

theorem base_mark_on (g : Gate) (W : List (Signal P)) (D x : List Bool) (X : Finset P)
    (base : ∀ j, W.getD j zero X=true → x.getD j false=true)
    (marked : ∀ j, D.getD j false=true → x.getD j false=true) :
    (baseGate g W X=true → actualGate g x=true) ∧
    (marker (arcs g W) D X=true → actualGate g x=true) := by
  obtain ⟨op,ins⟩ := g
  cases op <;> cases ins with
  | nil => simp [arcs,marker,baseGate,actualGate,gate,one,zero]
  | cons i tail =>
    cases tail with
    | nil =>
      simp [arcs,marker,baseGate,actualGate,gate,one,zero]
      all_goals exact ⟨base i,marked i⟩
    | cons j tail =>
      cases tail <;>
        simp only [arcs,marker,baseGate,actualGate,gate,one,zero,plus,times,
          List.any_cons,List.any_nil,Bool.or_false,Bool.or_eq_true,Bool.and_eq_true,Bool.and_true] <;>
        aesop

theorem marked_sound (gs : List Gate) (W : List (Signal P)) (D x : List Bool) (X : Finset P)
    (ops : ∀ g ∈ gs, g.op=.and ∨ g.op=.or) (fan : ∀ g ∈ gs, g.inputs.length≤2)
    (len : W.length=x.length) (ld : D.length=x.length)
    (base : ∀ j, W.getD j zero X=true → x.getD j false=true)
    (marked : ∀ j, D.getD j false=true → x.getD j false=true) :
    ∀ j, (marks gs W D X).getD j false=true → (wiresFrom gs x).getD j false=true := by
  induction gs generalizing W D x with
  | nil => exact marked
  | cons g gs ih =>
    have eq := project_gate g x (ops g (by simp)) (fan g (by simp))
    have h := base_mark_on g W D x X base marked
    rw [eq] at h
    apply ih _ _ _ (fun g hg => ops g (by simp [hg])) (fun g hg => fan g (by simp [hg]))
      (by simp [len]) (by simp [ld])
    · intro j
      by_cases e : j=W.length
      · subst j
        rw [getD_snoc_eq,len,getD_snoc_eq]
        exact h.1
      · rw [getD_snoc_ne _ _ _ _ e,getD_snoc_ne _ _ _ _ (by omega)]
        exact base j
    · intro j
      by_cases e : j=D.length
      · subst j
        rw [getD_snoc_eq,ld,getD_snoc_eq]
        exact h.2
      · rw [getD_snoc_ne _ _ _ _ e,getD_snoc_ne _ _ _ _ (by omega)]
        exact marked j

#print axioms dual
#print axioms marked_sound

end ReversePath
