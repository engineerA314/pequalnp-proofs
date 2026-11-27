import GraphStreamForm
import ThreeColourMatrix

namespace GraphStreamRoles

open WordMachine GraphStreamForm ThreeColourGadgets

inductive Shape
  | pal (c : Fin 3)
  | var (extra sign : Bool)
  | tri (layer : Bool) (port : Fin 3)
  deriving DecidableEq

def roles : Fin 13 → Shape := ![.pal 0,.pal 1,.pal 2,.var false false,.var false true,
  .var true false,.var true true,.tri false 0,.tri false 1,.tri false 2,.tri true 0,.tri true 1,.tri true 2]

theorem all_roles : Function.Surjective roles := by
  intro s
  cases s with
  | pal c => fin_cases c <;> first | exact ⟨0,rfl⟩ | exact ⟨1,rfl⟩ | exact ⟨2,rfl⟩
  | var a b => cases a <;> cases b <;> first | exact ⟨3,rfl⟩ | exact ⟨4,rfl⟩ | exact ⟨5,rfl⟩ | exact ⟨6,rfl⟩
  | tri a c => cases a <;> fin_cases c <;> first | exact ⟨7,rfl⟩ | exact ⟨8,rfl⟩ | exact ⟨9,rfl⟩ | exact ⟨10,rfl⟩ | exact ⟨11,rfl⟩ | exact ⟨12,rfl⟩

def vertex {n : ℕ} (r : Shape) (i : Fin n) : Vertex n n :=
  match r with
  | .pal c => pal c
  | .var a b => lit (if a then .inr i else .inl i) b
  | .tri t p => aux i t p

theorem projects (n : ℕ) (w : Vertex (n+1) (n+1)) : ∃ r i, vertex r i=w := by
  rcases w with c | (⟨i,b⟩ | ⟨i,t,p⟩)
  · exact ⟨.pal c,0,rfl⟩
  · cases i with
    | inl i => exact ⟨.var false b,i,rfl⟩
    | inr i => exact ⟨.var true b,i,rfl⟩
  · exact ⟨.tri t p,i,rfl⟩

def norm (r : Shape) (i : ℕ) := match r with | .pal _ => 0 | _ => i
def same (r : Shape) (i : ℕ) (s : Shape) (j : ℕ) :=
  decide (r=s) && decide (norm r i=norm s j)

theorem same_iff {n : ℕ} (r : Shape) (i : Fin n) (s : Shape) (j : Fin n) :
    same r i.val s j.val=decide (vertex r i=vertex s j) := by
  cases r <;> cases s <;> simp [same,norm,vertex,ThreeColourGadgets.pal,lit,aux,Fin.ext_iff] <;>
    try (split <;> split <;> simp_all [Fin.ext_iff])
  all_goals ac_rfl

inductive Ref | orig (p : Fin 3) | fixed (s : Shape)

def feedRef (t : Bool) (p : Fin 3) : Ref :=
  if t then three (.fixed (.var true false)) (.orig 2) (.fixed (.pal 0)) p
  else three (.orig 0) (.orig 1) (.fixed (.var true true)) p

def target (w : W) (i : ℕ) : Ref → Shape × ℕ
  | .orig p => (.var false (pos w i p).2,(pos w i p).1.val)
  | .fixed s => (s,i)

def hit (w : W) (i : ℕ) (f : Ref) (s : Shape) (j : ℕ) :=
  same s j (target w i f).1 (target w i f).2

theorem feed_hit (w : W) (i j : Fin (B w)) (t : Bool) (p : Fin 3) (s : Shape) :
    hit w i.val (feedRef t p) s j.val=decide (vertex s j=feeds (streamed w) i t p) := by
  cases t <;> fin_cases p
  all_goals first
    | exact same_iff s j (.var false (pos w i.val 0).2) (pos w i.val 0).1
    | exact same_iff s j (.var false (pos w i.val 1).2) (pos w i.val 1).1
    | exact same_iff s j (.var false (pos w i.val 2).2) (pos w i.val 2).1
    | exact same_iff s j (.var true true) i
    | exact same_iff s j (.var true false) i
    | exact same_iff s j (.pal 0) i

def direction (w : W) (r : Shape) (i : ℕ) (s : Shape) (j : ℕ) : Bool :=
  match r with
  | .pal a => match s with | .pal b => decide (a≠b) | _ => false
  | .var a b => same s j (.pal 2) i || (b && same s j (.var a false) i)
  | .tri t p => hit w i (feedRef t p) s j || match s with
    | .tri u q => decide (i=j) && decide (t=u ∧ p≠q)
    | _ => false

theorem direction_arc (w : W) (r : Shape) (i : Fin (B w)) (s : Shape) (j : Fin (B w)) :
    direction w r i.val s j.val=ThreeColourMatrix.arc (streamed w) (vertex r i) (vertex s j) := by
  cases r with
  | pal a => cases s <;> rfl
  | var a b => simp only [direction,same_iff]; rfl
  | tri t p =>
    simp only [direction,feed_hit]
    cases s <;> simp [vertex,aux,ThreeColourMatrix.arc,ThreeColourGadgets.pal,lit,Fin.ext_iff]

#print axioms direction_arc

end GraphStreamRoles
