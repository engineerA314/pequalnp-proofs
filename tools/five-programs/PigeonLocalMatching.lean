import PEqualNP.ProofComplexity.Helpers.Resolution
import Mathlib

namespace PigeonLocalMatching

open Finset PEqualNP.ProofComplexity

variable {P H : Type} [DecidableEq P] [DecidableEq H]

abbrev Line (P H : Type) := Clause (P × H)
def support (C : Line P H) := C.image fun l => l.1.1
def assign (f : P → H) (x : P × H) : Bool := decide (f x.1=x.2)
def good (E : P → Finset H) (S : Finset P) (f : P → H) :=
  Set.InjOn f (↑S : Set P) ∧ ∀ p∈S,f p∈E p
def valid (E : P → Finset H) (C : Line P H) :=
  ∀ f,good E (support C) f → ClauseSat (assign f) C

theorem belongs {l : Literal (P × H)} {C : Line P H} (h : l∈C) : l.1.1∈support C :=
  Finset.mem_image_of_mem _ h

theorem good_mono {E : P → Finset H} {S T : Finset P} {f : P → H}
    (h : good E T f) (st : S⊆T) : good E S f :=
  ⟨h.1.mono (by exact_mod_cast st),fun p hp => h.2 p (st hp)⟩

def row (E : P → Finset H) (p : P) : Line P H := (E p).image fun h => ((p,h),true)
def clash (p q : P) (h : H) : Line P H := {((p,h),false),((q,h),false)}

def axioms (E : P → Finset H) : Set (Line P H) :=
  {C | (∃ p,C=row E p) ∨ ∃ p q h,p≠q ∧ C=clash p q h}

theorem row_valid (E : P → Finset H) (p : P) (live : (E p).Nonempty) : valid E (row E p) := by
  intro f hf
  obtain ⟨j,hj⟩ := live
  have hp : p∈support (row E p) := belongs (Finset.mem_image_of_mem (fun h => ((p,h),true)) hj)
  refine ⟨((p,f p),true),Finset.mem_image_of_mem _ (hf.2 p hp),?_⟩
  simp [assign]

theorem clash_valid (E : P → Finset H) (p q : P) (j : H) (ne : p≠q) : valid E (clash p q j) := by
  intro f hf
  have hp : ((p,j),false)∈clash p q j := by simp [clash]
  have hq : ((q,j),false)∈clash p q j := by simp [clash]
  by_cases eq : f p=j
  · have neq : f q≠j := fun b => ne (hf.1 (belongs hp) (belongs hq) (eq.trans b.symm))
    exact ⟨_,hq,by simp [assign,neq]⟩
  · exact ⟨_,hp,by simp [assign,eq]⟩

theorem ax_valid (E : P → Finset H) (live : ∀ p,(E p).Nonempty) {C : Line P H} (h : C∈axioms E) :
    valid E C := by
  rcases h with ⟨p,rfl⟩|⟨p,q,j,ne,rfl⟩
  · exact row_valid E p (live p)
  · exact clash_valid E p q j ne

theorem extend {E : P → Finset H} {S : Finset P} {p : P} {j : H} {f : P → H}
    (h : good E S f) (fresh : p∉S) (edge : j∈E p) (free : j∉S.image f) :
    good E (insert p S) (Function.update f p j) := by
  have diff (q : P) (hq : q∈S) : q≠p := fun eq => fresh (eq ▸ hq)
  have unused (q : P) (hq : q∈S) : f q≠j := fun eq => free (eq ▸ Finset.mem_image_of_mem f hq)
  constructor
  · intro x hx y hy eq
    change x∈insert p S at hx
    change y∈insert p S at hy
    rcases mem_insert.mp hx with rfl|hxS <;> rcases mem_insert.mp hy with rfl|hyS
    · rfl
    · simp [Function.update_of_ne (diff _ hyS),Ne.symm (unused _ hyS)] at eq
    · simp [Function.update_of_ne (diff _ hxS),unused _ hxS] at eq
    · apply h.1 hxS hyS
      simpa [Function.update_of_ne (diff _ hxS),Function.update_of_ne (diff _ hyS)] using eq
  · intro x hx
    rcases mem_insert.mp hx with rfl|hx
    · simpa using edge
    · simpa [Function.update_of_ne (diff _ hx)] using h.2 x hx

theorem sat_ext {C : Line P H} {f g : P → H}
    (eq : ∀ i∈support C,g i=f i) (h : ClauseSat (assign g) C) : ClauseSat (assign f) C := by
  obtain ⟨l,hl,yes⟩ := h
  refine ⟨l,hl,?_⟩
  simpa [assign,eq l.1.1 (belongs hl)] using yes

#print axioms extend

end PigeonLocalMatching
