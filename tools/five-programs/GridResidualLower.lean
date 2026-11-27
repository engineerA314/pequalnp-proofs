import GridOrderCut

namespace GridResidualLower

open Finset GridOrderCut ResidualInducedMatching GridStripMatching

variable {V : Type} [Fintype V] [DecidableEq V]

def correct (G : SimpleGraph V) (S : Finset V) {Q : Type} (encode : Finset V → Q) (read : Q → Finset V → Prop) :=
  ∀ A,A⊆S → ∀ B,Disjoint B S → (read (encode A) B ↔ independent G (A∪B))

theorem on_cut (G : SimpleGraph V) (S : Finset V) {k : ℕ} (M : CutMatching G S k) (Q : Type)
    [Fintype Q] (encode : Finset V → Q) (read : Q → Finset V → Prop) (h : correct G S encode read) :
    2^k≤Fintype.card Q := by
  classical
  apply states G M (fun A => encode (A.image M.left)) (fun q j => read q {M.right j})
  intro A j
  have left : A.image M.left⊆S := by
    intro p hp
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
    exact M.before i
  have right : Disjoint ({M.right j} : Finset V) S := by simpa using M.afterCut j
  simpa [tests,Finset.union_comm] using h _ left _ right

theorem all_orders (k : ℕ) (time : Fin (2*k+2) × Fin (2*k+2) → ℕ) (unique : Function.Injective time) :
    ∃ t,∀ (Q : Type) [Fintype Q] (encode : Finset (Fin (2*k+2) × Fin (2*k+2)) → Q)
      (read : Q → Finset (Fin (2*k+2) × Fin (2*k+2)) → Prop),
      correct (grid _) (beforeTime _ time t) encode read → 2^(k+1)≤Fintype.card Q := by
  obtain ⟨t,⟨M⟩⟩ := any_order k time unique
  exact ⟨t,fun Q _ enc read valid => on_cut _ _ M Q enc read valid⟩

#print axioms all_orders

end GridResidualLower
