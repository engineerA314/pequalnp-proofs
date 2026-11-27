import Mathlib

namespace ResidualAntichain

open Finset

abbrev C (V : Type) := Finset (V × Bool)
abbrev F (V : Type) := Finset (C V)
variable {V : Type} [Fintype V] [DecidableEq V]

def hit (x : V → Bool) (c : C V) := ∃ l∈c,x l.1=l.2
def sat (x : V → Bool) (f : F V) := ∀ c∈f,hit x c
def taut (c : C V) := ∃ v : V,(v,false)∈c ∧ (v,true)∈c
instance (c : C V) : Decidable (taut c) := by unfold taut; infer_instance

def clean (f : F V) := f.filter (fun c => ¬taut c)
def normal (f : F V) := (clean f).filter (fun c => ∀ d∈clean f,¬d⊂c)

theorem taut_hit (x : V → Bool) {c : C V} (h : taut c) : hit x c := by
  obtain ⟨v,neg,pos⟩ := h
  cases e : x v with
  | false => exact ⟨_,neg,e⟩
  | true => exact ⟨_,pos,e⟩

theorem hit_mono (x : V → Bool) {c d : C V} (inc : c⊆d) (h : hit x c) : hit x d := by
  obtain ⟨l,hl,yes⟩ := h
  exact ⟨l,inc hl,yes⟩

theorem normalized (x : V → Bool) (f : F V) : sat x (normal f) ↔ sat x f := by
  classical
  constructor
  · intro all c hc
    by_cases top : taut c
    · exact taut_hit x top
    let A := (clean f).filter fun d => d⊆c
    have mem : c∈A := by simp [A,clean,hc,top]
    obtain ⟨d,hd,minimal⟩ := Finset.exists_min_image A Finset.card ⟨c,mem⟩
    obtain ⟨good,sub⟩ := Finset.mem_filter.mp hd
    apply hit_mono x sub
    apply all d
    refine Finset.mem_filter.mpr ⟨good,?_⟩
    intro e he proper
    have eIn : e∈A := Finset.mem_filter.mpr ⟨he,proper.subset.trans sub⟩
    exact (Nat.not_lt_of_ge (minimal _ eIn)) (Finset.card_lt_card proper)
  · intro all c hc
    exact all c (Finset.mem_filter.mp (Finset.mem_filter.mp hc).1).1

def tail {n : ℕ} (c : C (Fin (n+1))) : C (Fin n) := univ.filter fun l => (l.1.succ,l.2)∈c

def branch {n : ℕ} (f : F (Fin (n+1))) (b : Bool) : F (Fin n) :=
  normal ((f.filter (fun c => (0,b)∉c)).image tail)

theorem literal_split {n : ℕ} (c : C (Fin (n+1))) (b : Bool) (x : Fin n → Bool) :
    hit (Fin.cons b x) c ↔ (0,b)∈c ∨ hit x (tail c) := by
  constructor
  · rintro ⟨⟨i,s⟩,mem,yes⟩
    induction i using Fin.cases with
    | zero =>
      change b=s at yes
      exact Or.inl (yes.symm ▸ mem)
    | succ i =>
      exact Or.inr ⟨(i,s),Finset.mem_filter.mpr ⟨Finset.mem_univ _,mem⟩,by simpa using yes⟩
  · rintro (mem|⟨⟨i,s⟩,mem,yes⟩)
    · exact ⟨(0,b),mem,rfl⟩
    · exact ⟨(i.succ,s),(Finset.mem_filter.mp mem).2,by simpa using yes⟩

theorem branch_sat {n : ℕ} (f : F (Fin (n+1))) (b : Bool) (x : Fin n → Bool) :
    sat x (branch f b) ↔ sat (Fin.cons b x) f := by
  rw [branch,normalized]
  constructor
  · intro all c hc
    apply (literal_split c b x).mpr
    by_cases h : (0,b)∈c
    · exact Or.inl h
    · exact Or.inr (all _ (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hc,h⟩)))
  · intro all tailClause ht
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨inc,no⟩ := Finset.mem_filter.mp hc
    exact ((literal_split c b x).mp (all c inc)).resolve_left no

#print axioms normalized
#print axioms branch_sat

end ResidualAntichain
