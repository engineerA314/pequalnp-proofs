import ProofDagBudget
import PEqualNP.ProofComplexity.Helpers.Resolution

namespace ResolutionChain

open PEqualNP.ProofComplexity PEqualNP.ProofComplexity.Helpers ProofDagBudget

def pos (i : ℕ) : Clause ℕ := {(i,true)}
def neg (i : ℕ) : Clause ℕ := {(i,false)}
def link (i : ℕ) : Clause ℕ := {(i,false),(i+1,true)}
def input (n : ℕ) := insert (pos 0) (insert (neg n) ((Finset.range n).image link))

theorem link_inj : Function.Injective link := by
  intro i j h
  have mark : (i,false)∈link j := h ▸ (show (i,false)∈link i by simp [link])
  simpa [link] using mark

theorem no_pos (i : ℕ) : link i≠pos 0 := by
  intro h
  have mark : (i,false)∈pos 0 := h ▸ (show (i,false)∈link i by simp [link])
  simp [pos] at mark

theorem no_neg (i n : ℕ) : link i≠neg n := by
  intro h
  have mark : (i+1,true)∈neg n := h ▸ (show (i+1,true)∈link i by simp [link])
  simp [neg] at mark

theorem card_input (n : ℕ) : (input n).card=n+2 := by
  have p : pos 0∉insert (neg n) ((Finset.range n).image link) := by
    intro h
    rcases Finset.mem_insert.mp h with same|later
    · have different : pos 0≠neg n := by simp [pos,neg]
      exact different same
    · obtain ⟨i,_,eq⟩ := Finset.mem_image.mp later
      exact no_pos i eq
  have m : neg n∉(Finset.range n).image link := by simp [no_neg]
  rw [input,Finset.card_insert_of_notMem p,Finset.card_insert_of_notMem m,
    Finset.card_image_of_injective _ link_inj, Finset.card_range]

def holds (C : Clause ℕ) (x : ℕ → Bool) := ClauseSat x C

theorem val_pos (x : ℕ → Bool) (i : ℕ) : holds (pos i) x ↔ x i=true := by simp [holds,ClauseSat,pos]
theorem val_neg (x : ℕ → Bool) (i : ℕ) : holds (neg i) x ↔ x i=false := by simp [holds,ClauseSat,neg]
theorem val_link (x : ℕ → Bool) (i : ℕ) : holds (link i) x ↔ x i=false ∨ x (i+1)=true := by
  simp [holds,ClauseSat,link]

theorem critical (n : ℕ) : Critical holds (input n) := by
  intro C hc
  simp only [input,Finset.mem_insert,Finset.mem_image,Finset.mem_range] at hc
  rcases hc with rfl|rfl|⟨k,hk,rfl⟩
  · refine ⟨fun _ => false,?_⟩
    intro B hb ne
    simp only [input,Finset.mem_insert,Finset.mem_image,Finset.mem_range] at hb
    rcases hb with rfl|rfl|⟨i,_,rfl⟩
    · contradiction
    · exact (val_neg _ _).mpr rfl
    · exact (val_link _ _).mpr (Or.inl rfl)
  · refine ⟨fun _ => true,?_⟩
    intro B hb ne
    simp only [input,Finset.mem_insert,Finset.mem_image,Finset.mem_range] at hb
    rcases hb with rfl|rfl|⟨i,_,rfl⟩
    · exact (val_pos _ _).mpr rfl
    · contradiction
    · exact (val_link _ _).mpr (Or.inr rfl)
  · refine ⟨fun j => decide (j≤k),?_⟩
    intro B hb ne
    simp only [input,Finset.mem_insert,Finset.mem_image,Finset.mem_range] at hb
    rcases hb with rfl|rfl|⟨i,_,rfl⟩
    · apply (val_pos _ _).mpr; simp
    · apply (val_neg _ _).mpr; simp [not_le_of_gt hk]
    · apply (val_link _ _).mpr
      have neq : i≠k := fun e => ne (e ▸ rfl)
      simp only [decide_eq_false_iff_not,decide_eq_true_eq]
      omega

theorem steps (n : ℕ) (W : List (Clause ℕ)) (h : IsDerivation (↑(input n) : Set (Clause ℕ)) W) :
    Derives holds (input n) W := by
  induction h with
  | nil => exact .nil
  | ax _ src ih => exact .step ih _ (Or.inl src)
  | @res π C D R _ hc hd rule ih =>
    refine .step ih R (Or.inr ⟨{C,D},Finset.card_le_two,?_,?_⟩)
    · intro f hf
      rcases Finset.mem_insert.mp hf with rfl|e
      · exact hc
      · exact Finset.mem_singleton.mp e ▸ hd
    · intro x hx t ht
      rw [Finset.mem_singleton.mp ht]
      exact resolvent_sound x rule (hx _ (by simp)) (hx _ (by simp))

def propagation : ℕ → List (Clause ℕ)
  | 0 => [pos 0]
  | k+1 => pos (k+1)::link k::propagation k

theorem last (k : ℕ) : pos k∈propagation k := by cases k <;> simp [propagation]

theorem build (n k : ℕ) (le : k≤n) : IsDerivation (↑(input n) : Set (Clause ℕ)) (propagation k) := by
  induction k with
  | zero => exact .ax .nil (by simp [input])
  | succ k ih =>
    have hLink : link k∈input n := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by omega))))
    refine .res (.ax (ih (by omega)) hLink) (List.mem_cons_of_mem _ (last k)) List.mem_cons_self ?_
    exact ⟨k,by simp [pos],by simp [link],by simp [pos,link]⟩

def proof (n : ℕ) : List (Clause ℕ) := ∅::neg n::propagation n

theorem valid (n : ℕ) : IsRefutation (↑(input n) : Set (Clause ℕ)) (proof n) := by
  refine ⟨.res (.ax (build n n le_rfl) (by simp [input])) (List.mem_cons_of_mem _ (last n)) List.mem_cons_self ?_,by simp [proof]⟩
  exact ⟨n,by simp [pos],by simp [neg],by simp [pos,neg]⟩

theorem size (n : ℕ) : (proof n).length=2*n+3 := by
  have len (k : ℕ) : (propagation k).length=2*k+1 := by
    induction k with
    | zero => rfl
    | succ k ih => simp [propagation,ih]; omega
  simp [proof,len]

theorem sharp (n : ℕ) : IsRefutation (↑(input n) : Set (Clause ℕ)) (proof n) ∧ (proof n).length=2*n+3 ∧
    ∀ W, IsRefutation (↑(input n) : Set (Clause ℕ)) W → 2*n+3≤W.length := by
  refine ⟨valid n,size n,?_⟩
  intro W h
  have bad : ∀ x, ¬holds (∅ : Clause ℕ) x := by simp [holds,ClauseSat]
  have b := length_bound _ _ _ (steps n W h.1) ∅ h.2 bad (critical n)
  rw [card_input n] at b
  omega

#print axioms sharp

end ResolutionChain
