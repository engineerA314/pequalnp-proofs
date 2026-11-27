import SparseNegatives
import AndTranscript

/-! Binary AND lower bounds for a downstream correction with primary inputs
and a fixed boundary value. A prefix whose single output is one on all
counted negative inputs is a special case. -/

namespace RepairAnds

open PEqualNP.CircuitLowerBounds SparseNegatives AndTranscript

def bits {n : ℕ} (S : Finset (Fin n)) : List Bool := List.ofFn fun i => decide (i ∈ S)

def inputs {P L : ℕ} (X : Finset (Fin P)) (Y : Finset (Fin L)) (tail : List Bool) :=
  bits X ++ bits Y ++ tail

theorem bits_covered {n : ℕ} (S A B : Finset (Fin n)) (sub : S ⊆ A ∪ B) :
    Covered (bits S) (bits A) (bits B) := by
  refine ⟨by simp [bits],by simp [bits],?_⟩
  intro i on
  by_cases h : i < n
  · simp [bits,List.getD_eq_getElem?_getD,h] at on ⊢
    exact Finset.mem_union.mp (sub on)
  · rw [List.getD_eq_default _ _ (by simp [bits]; omega)] at on
    contradiction

theorem covered_append {a b c a' b' c' : List Bool} (h : Covered a b c) (h' : Covered a' b' c') :
    Covered (a++a') (b++b') (c++c') := by
  obtain ⟨h1,h2,cover⟩ := h
  obtain ⟨h3,h4,tail⟩ := h'
  refine ⟨by simp [h1,h3],by simp [h2,h4],?_⟩
  intro i
  by_cases hi : i < a.length
  · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (by omega),
        List.getD_append _ _ _ _ (by omega)]
    exact cover i
  · rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by omega), ← h2, ← h1]
    exact tail _

variable {P L : ℕ}

/-- The separating argument applies to any family of sparse canonical negatives and
a common auxiliary input. The empty list gives the full circuit on the primary inputs. -/
theorem fixed_boundary (I : Lines P L) (q : ℕ) (size : ∀ w, q < (I w).card)
    (linear : ∀ w v, w ≠ v → (I w ∩ I v).card ≤ 1)
    (C : Circuit) (mono : IsMonotoneCircuit C) (fan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (tail : List Bool) (positive : ∀ w p, p ∈ I w → C.eval (inputs {p} {w} tail) = true)
    (F : Finset (Finset (Fin L))) (short : ∀ Y ∈ F, Y.card ≤ q)
    (negative : ∀ Y ∈ F, C.eval (inputs (outside I Y) Y tail) = false) :
    F.card ≤ 2 ^ count C.gates := by
  apply incompatible_count F (fun Y => inputs (outside I Y) Y tail) C mono fan negative
  intro Y hy Z hz ne
  obtain ⟨p,w,pw,point,line⟩ := crossing_pair I q size linear Y Z (short Y hy) (short Z hz) ne
  refine ⟨inputs {p} {w} tail, positive w p pw, ?_⟩
  apply covered_append
  · apply covered_append
    · exact bits_covered _ _ _ (Finset.singleton_subset_iff.mpr (Finset.mem_union.mpr point))
    · exact bits_covered _ _ _ (Finset.singleton_subset_iff.mpr (Finset.mem_union.mpr line))
  · exact ⟨rfl,rfl,fun _ on => Or.inl on⟩

/-- A general AND/OR suffix receiving the primary inputs and one true prefix
bit needs enough distinct binary ANDs to distinguish the leaking line sets. -/
theorem one_bit_repair (I : Lines P L) (q : ℕ) (size : ∀ w, q < (I w).card)
    (linear : ∀ w v, w ≠ v → (I w ∩ I v).card ≤ 1)
    (A : Finset (Fin P) → Finset (Fin L) → Prop) (C : Circuit) (mono : IsMonotoneCircuit C)
    (fan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (positive : ∀ w p, p ∈ I w → C.eval (inputs {p} {w} [true]) = true)
    (negative : ∀ Y ∈ leaks I q A, C.eval (inputs (outside I Y) Y [true]) = false) :
    (leaks I q A).card ≤ 2 ^ count C.gates :=
  fixed_boundary I q size linear C mono fan [true] positive _
    (fun Y h => ((mem_leaks I q A Y).mp h).1) negative

/-- With all sparse independent tests at the output, the entire circuit must
have enough binary AND gates for all sparse line sets. -/
theorem whole_circuit (I : Lines P L) (q : ℕ) (size : ∀ w, q < (I w).card)
    (linear : ∀ w v, w ≠ v → (I w ∩ I v).card ≤ 1)
    (C : Circuit) (mono : IsMonotoneCircuit C) (fan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (positive : ∀ w p, p ∈ I w → C.eval (bits {p} ++ bits {w}) = true)
    (negative : ∀ Y, Y.card ≤ q → C.eval (bits (outside I Y) ++ bits Y) = false) :
    ∑ j ∈ Finset.range (q+1), L.choose j ≤ 2 ^ count C.gates := by
  classical
  let F := (Finset.univ : Finset (Fin L)).powerset.filter fun Y => Y.card ≤ q
  have few (Y : Finset (Fin L)) : Y ∈ F ↔ Y.card ≤ q := by simp [F]
  have h := fixed_boundary I q size linear C mono fan [] (by simpa [inputs] using positive) F
    (fun Y hy => (few Y).mp hy) (by
      intro Y hy
      simpa [inputs] using negative Y ((few Y).mp hy))
  have hf := count_small_subsets (Finset.univ : Finset (Fin L)) q
  change F.card = _ at hf
  simpa [hf] using h

#print axioms one_bit_repair
#print axioms whole_circuit

end RepairAnds
