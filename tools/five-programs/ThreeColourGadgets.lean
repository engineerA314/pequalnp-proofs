import Mathlib

/-! The graph part of the 3-SAT to adjacency-matrix 3-colouring reduction.
The two Boolean triangles in a clause implement not-all-equal. -/

namespace ThreeColourGadgets

abbrev Form (n m : ℕ) := Fin m → Fin 3 → Fin n × Bool
abbrev Variables (n m : ℕ) := Fin n ⊕ Fin m
abbrev Vertex (n m : ℕ) := Fin 3 ⊕ ((Variables n m × Bool) ⊕ (Fin m × Bool × Fin 3))
variable {n m : ℕ}

def pal (j : Fin 3) : Vertex n m := .inl j
def lit (x : Variables n m) (b : Bool) : Vertex n m := .inr (.inl (x,b))
def aux (i : Fin m) (t : Bool) (j : Fin 3) : Vertex n m := .inr (.inr (i,t,j))

def three {α : Type} (a b c : α) : Fin 3 → α := ![a,b,c]
def bit (b : Bool) : Fin 3 := if b then 1 else 0
abbrev nae (v : Fin 3 → Bool) := v 0 ≠ v 1 ∨ v 1 ≠ v 2

def ev (A : Fin n → Bool) (x : Fin n × Bool) := A x.1 == x.2
def Sat (F : Form n m) := ∃ A : Fin n → Bool, ∀ i, ev A (F i 0) || ev A (F i 1) || ev A (F i 2)

def feeds (F : Form n m) (i : Fin m) (t : Bool) : Fin 3 → Vertex n m :=
  let orig := fun j => lit (.inl (F i j).1) (F i j).2
  if t then three (lit (.inr i) false) (orig 2) (pal 0)
  else three (orig 0) (orig 1) (lit (.inr i) true)

inductive Edge (F : Form n m) : Vertex n m → Vertex n m → Prop
  | palette (a b : Fin 3) (diff : a ≠ b) : Edge F (pal a) (pal b)
  | boolean (x : Variables n m) (b : Bool) : Edge F (lit x b) (pal 2)
  | opposite (x : Variables n m) : Edge F (lit x true) (lit x false)
  | triangle (i : Fin m) (t : Bool) (a b : Fin 3) (diff : a ≠ b) : Edge F (aux i t a) (aux i t b)
  | wire (i : Fin m) (t : Bool) (a : Fin 3) : Edge F (aux i t a) (feeds F i t a)

def Proper (F : Form n m) (c : Vertex n m → Fin 3) := ∀ u v, Edge F u v → c u ≠ c v

-- The finite checks concern one triangle, independent of formula size.
theorem triangle_table : ∀ u : Fin 3 → Bool,
    (∃ c : Fin 3 → Fin 3, (∀ i j, i ≠ j → c i ≠ c j) ∧ ∀ j, c j ≠ bit (u j)) ↔ nae u := by decide

theorem split_table : ∀ a b c : Bool,
    ((∃ z : Bool, nae (three a b z) ∧ nae (three (!z) c false)) ↔ a || b || c) := by decide

theorem choose_split : ∀ a b c : Bool, (a || b || c)=true →
    nae (three a b (!(a||b))) ∧ nae (three (a||b) c false) := by decide

theorem literal_table : ∀ a d : Fin 3, a≠2 → d≠2 → a≠d → ∀ s : Bool,
    (if s then a else d)=bit (decide (a=1) == s) := by decide

def feedValues (F : Form n m) (A : Variables n m → Bool) (i : Fin m) (t : Bool) : Fin 3 → Bool :=
  let orig := fun j => A (.inl (F i j).1) == (F i j).2
  if t then three (!(A (.inr i))) (orig 2) false
  else three (orig 0) (orig 1) (A (.inr i))

theorem read_feeds (F : Form n m) (A : Variables n m → Bool) (col : Vertex n m → Fin 3)
    (hp : ∀ j, col (pal j)=j) (hl : ∀ x b, col (lit x b)=bit (A x == b))
    (i : Fin m) (t : Bool) (j : Fin 3) : col (feeds F i t j)=bit (feedValues F A i t j) := by
  cases t <;> fin_cases j <;> simp [feeds,feedValues,three,hp,hl,bit]

theorem normalize (F : Form n m) (c : Vertex n m → Fin 3) (ok : Proper F c) :
    ∃ d : Vertex n m → Fin 3, Proper F d ∧ ∀ j, d (pal j)=j := by
  have inj : Function.Injective (fun j : Fin 3 => c (pal j)) := by
    intro i j e
    by_contra ne
    exact ok _ _ (.palette i j ne) e
  let perm := Equiv.ofBijective (fun j : Fin 3 => c (pal j)) inj.bijective_of_finite
  exact ⟨perm.symm ∘ c,fun u v e h => ok u v e (perm.symm.injective h),fun j => perm.symm_apply_apply j⟩

theorem decode (F : Form n m) (col : Vertex n m → Fin 3) (ok : Proper F col) : Sat F := by
  obtain ⟨d,good,hp⟩ := normalize F col ok
  let A := fun x : Variables n m => decide (d (lit x true)=1)
  have hl (x : Variables n m) (b : Bool) : d (lit x b)=bit (A x == b) := by
    have h1 := good _ _ (.boolean x true)
    have h0 := good _ _ (.boolean x false)
    rw [hp] at h1 h0
    have eq := literal_table _ _ h1 h0 (good _ _ (.opposite x)) b
    cases b <;> exact eq
  have allNae (i : Fin m) (t : Bool) : nae (feedValues F A i t) := by
    apply (triangle_table _).mp
    refine ⟨fun j => d (aux i t j),fun j k ne => good _ _ (.triangle i t j k ne),fun j => ?_⟩
    rw [← read_feeds F A d hp hl]
    exact good _ _ (.wire i t j)
  refine ⟨fun x => A (.inl x),fun i => (split_table _ _ _).mp ⟨A (.inr i),?_,?_⟩⟩
  · exact allNae i false
  · exact allNae i true

theorem encode (F : Form n m) (sat : Sat F) : ∃ c : Vertex n m → Fin 3, Proper F c := by
  classical
  obtain ⟨B,sat⟩ := sat
  let A : Variables n m → Bool := Sum.elim B (fun i => !(ev B (F i 0)||ev B (F i 1)))
  have allNae (i : Fin m) (t : Bool) : nae (feedValues F A i t) := by
    have h := choose_split _ _ _ (sat i)
    cases t
    · exact h.1
    · simpa [feedValues,A,ev] using h.2
  choose tri distinct avoid using fun i t => (triangle_table _).mpr (allNae i t)
  let col : Vertex n m → Fin 3 := Sum.elim id (Sum.elim (fun v => bit (A v.1 == v.2)) (fun v => tri v.1 v.2.1 v.2.2))
  have hp (j : Fin 3) : col (pal j)=j := rfl
  have hl (x : Variables n m) (b : Bool) : col (lit x b)=bit (A x == b) := rfl
  refine ⟨col,fun u v e => ?_⟩
  cases e with
  | palette a b ne => exact ne
  | boolean x b => rw [hl,hp]; cases A x <;> cases b <;> decide
  | opposite x => rw [hl,hl]; cases A x <;> decide
  | triangle i t a b ne => exact distinct i t a b ne
  | wire i t a => rw [read_feeds F A col hp hl]; exact avoid i t a

theorem graph_iff (F : Form n m) : Sat F ↔ ∃ c : Vertex n m → Fin 3, Proper F c :=
  ⟨encode F,fun ⟨c,h⟩ => decode F c h⟩

theorem vertex_count (n m : ℕ) : Fintype.card (Vertex n m)=3+2*n+8*m := by
  simp [Vertex,Variables]
  omega

#print axioms graph_iff

end ThreeColourGadgets
