import ResidualAntichain
import Mathlib

namespace ResidualInducedMatching

open Finset

variable {V : Type} [DecidableEq V] {k : ℕ}

def independent (G : SimpleGraph V) (S : Finset V) := ∀ u∈S,∀ v∈S,¬G.Adj u v

structure CutMatching (G : SimpleGraph V) (S : Finset V) (k : ℕ) where
  left : Fin k → V
  right : Fin k → V
  before : ∀ i,left i∈S
  afterCut : ∀ i,right i∉S
  edge : ∀ i,G.Adj (left i) (right i)
  noLeft : ∀ i j,¬G.Adj (left i) (left j)
  onlyPair : ∀ i j,G.Adj (left i) (right j) → i=j

def tests (G : SimpleGraph V) {S : Finset V} (M : CutMatching G S k) (A : Finset (Fin k)) (j : Fin k) :=
  independent G (insert (M.right j) (A.image M.left))

theorem separates (G : SimpleGraph V) {S : Finset V} (M : CutMatching G S k) (A : Finset (Fin k)) (j : Fin k) :
    tests G M A j ↔ j∉A := by
  constructor
  · intro ok mem
    exact ok (M.left j) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ mem)) (M.right j) (Finset.mem_insert_self ..) (M.edge j)
  · intro out u hu v hv adj
    rcases Finset.mem_insert.mp hu with rfl|hu <;> rcases Finset.mem_insert.mp hv with rfl|hv
    · exact G.loopless.irrefl _ adj
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
      exact out (M.onlyPair i j adj.symm ▸ hi)
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hu
      exact out (M.onlyPair i j adj ▸ hi)
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨h,_,rfl⟩ := Finset.mem_image.mp hv
      exact M.noLeft i h adj

theorem states (G : SimpleGraph V) {S : Finset V} (M : CutMatching G S k) {Q : Type} [Fintype Q]
    (store : Finset (Fin k) → Q) (read : Q → Fin k → Prop)
    (accurate : ∀ A j,read (store A) j ↔ tests G M A j) : 2^k ≤ Fintype.card Q := by
  classical
  have inj : Function.Injective store := by
    intro A B eq
    ext j
    have h := ((accurate A j).trans (separates G M A j)).symm
    rw [eq] at h
    have same := (h.trans (accurate B j)).trans (separates G M B j)
    tauto
  simpa using Fintype.card_le_of_injective store inj

def edgeCNF [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : ResidualAntichain.F V :=
  ((univ : Finset (V × V)).filter (fun p => G.Adj p.1 p.2)).image fun p => {(p.1,true),(p.2,true)}

theorem zero_set [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) :
    ResidualAntichain.sat (fun v => decide (v∉A)) (edgeCNF G) ↔ independent G A := by
  classical
  constructor
  · intro ok u hu v hv edge
    have h := ok _ (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨mem_univ (u,v),edge⟩))
    simpa [ResidualAntichain.hit,hu,hv] using h
  · intro good c hc
    obtain ⟨⟨u,v⟩,h,rfl⟩ := Finset.mem_image.mp hc
    have edge := (Finset.mem_filter.mp h).2
    by_cases hu : u∈A
    · have hv : v∉A := fun hv => good u hu v hv edge
      simp [ResidualAntichain.hit,hv]
    · simp [ResidualAntichain.hit,hu]

#print axioms states
#print axioms zero_set

end ResidualInducedMatching
