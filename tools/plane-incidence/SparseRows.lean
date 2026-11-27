import SparseFrontier

/-! Combine the row-specific frontiers with actual sparse outside tests.
Each easy boundary signal is activated by at most one outside input. -/

namespace SparseRows

open PartialSums SparseFrontier

variable {P L : Type} [Fintype P] [DecidableEq P]

def Rejects (R : Finset P) (t : ℕ) (f : Signal P) :=
  ∀ Y : Finset P, Disjoint Y R → Y.card≤t → f Y=false

theorem witnesses (radius : ℕ) (R : Finset P) (G : Finset (Signal P)) (easy : ∀ f∈G, ¬SmallOff R f radius)
    (mon : ∀ f∈G, Mono f) : ∃ Y : Finset P, Disjoint Y R ∧ Y.card≤radius*G.card ∧ ∀ f∈G, f Y=true := by
  classical
  have chooseY (f : Signal P) : ∃ Y : Finset P,
      Disjoint Y R ∧ Y.card≤radius ∧ (f∈G → f Y=true) := by
    by_cases h : f∈G
    · have existsOn := easy f h
      unfold SmallOff at existsOn
      push Not at existsOn
      obtain ⟨Y,apart,few,on⟩ := existsOn
      exact ⟨Y,apart,few,fun _ => by simpa using on⟩
    · exact ⟨∅,by simp,by simp,fun m => False.elim (h m)⟩
  choose pick apart few fires using chooseY
  let Y := G.biUnion pick
  refine ⟨Y,?_,?_,?_⟩
  · apply Finset.disjoint_left.mpr
    intro p hp inside
    obtain ⟨f,_,m⟩ := Finset.mem_biUnion.mp hp
    exact Finset.disjoint_left.mp (apart f) m inside
  · apply Finset.card_biUnion_le.trans
    simpa [Nat.mul_comm] using Finset.sum_le_sum (s := G) (fun f _ => few f)
  · intro f hf
    exact mon f hf (pick f) Y (fun _ m => Finset.mem_biUnion.mpr ⟨f,hf,m⟩) (fires f hf)

theorem boundary (b t radius : ℕ) (R : Finset P) (f : Signal P) (off : Rejects R t f)
    (F : Finset (Signal P)) (terminal : ∀ h ∈ F, ¬Private b R h radius) (mon : ∀ h ∈ F, Mono h)
    (cover : Covers F {f}) : radius*F.card≤t → (single f).card≤b*F.card := by
  classical
  intro enough
  let A := F.filter fun h => SmallOff R h radius
  let G := F.filter fun h => ¬SmallOff R h radius
  have ca : A.card≤F.card := Finset.card_filter_le _ _
  have cg : G.card≤F.card := Finset.card_filter_le _ _
  have small (h : Signal P) (hh : h∈A) : (single h).card≤b := by
    obtain ⟨hf,hard⟩ := Finset.mem_filter.mp hh
    exact Nat.le_of_not_gt fun big => terminal h hf ⟨hard,big⟩
  obtain ⟨Y,apart,few,fire⟩ := witnesses radius R G (fun h hh => (Finset.mem_filter.mp hh).2)
    (fun h hh => mon h (Finset.mem_filter.mp hh).1)
  have falseAt := off Y apart (few.trans ((Nat.mul_le_mul_left radius cg).trans enough))
  have sub : single f ⊆ A.biUnion single := by
    intro p hp
    by_contra missing
    have lift : Rel F {p} Y := by
      intro h hf yes
      by_cases hard : SmallOff R h radius
      · have ha : h ∈ A := Finset.mem_filter.mpr ⟨hf,hard⟩
        have hit : p ∈ single h := Finset.mem_filter.mpr ⟨Finset.mem_univ _,yes⟩
        exact False.elim (missing (Finset.mem_biUnion.mpr ⟨h,ha,hit⟩))
      · exact fire h (Finset.mem_filter.mpr ⟨hf,hard⟩)
    have contradictionAt := cover {p} Y lift f (by simp) (Finset.mem_filter.mp hp).2
    rw [falseAt] at contradictionAt
    contradiction
  calc
    _ ≤ (A.biUnion single).card := Finset.card_le_card sub
    _ ≤ ∑ h∈A, (single h).card := Finset.card_biUnion_le
    _ ≤ ∑ _h∈A, b := Finset.sum_le_sum small
    _ ≤ b*F.card := by simpa [Nat.mul_comm] using Nat.mul_le_mul_left b ca

theorem cut_row_radius (b t radius : ℕ) (R : Finset P) (f : Signal P) (off : Rejects R t f)
    (W : List (Signal P)) (c : ℕ) (mon : ∀ h∈W, Mono h) (hf : f∈W) (front : Frontier b R W c radius)
    (few : radius*(c+1)≤t) : (single f).card≤b*(c+1) := by
  classical
  obtain ⟨F,af,terminal,cost,cover⟩ := front {f} (by intro h mem; exact (Finset.mem_singleton.mp mem) ▸ hf)
  have cap : F.card≤c+1 := by simpa using cost
  exact (boundary b t radius R f off F terminal (fun h m => mon h (af h m)) cover
    ((Nat.mul_le_mul_left radius cap).trans few)).trans (Nat.mul_le_mul_left b cap)

theorem charge [Fintype L] (b t : ℕ) (pos : 1≤b) (I : L → Finset P)
    (linear : ∀ l m, l≠m → (I l ∩ I m).card≤b) (W : List (Signal P)) (k : ℕ) (net : Net W k)
    (out : L → Signal P) (outputs : ∀ l, out l∈W) (off : ∀ l, Rejects (I l) t (out l)) :
    ∃ c : L → ℕ, (∑ l, c l)≤k ∧ ∀ l, c l<t → (single (out l)).card≤b*(c l+1) := by
  obtain ⟨c,spent,front⟩ := ledger b pos I linear W k net
  obtain ⟨a,built⟩ := asBuilt W k net
  exact ⟨c,spent,fun l h => cut_row_radius b t 1 (I l) (out l) (off l) W (c l) (mono W a built) (outputs l) (front l) (by omega)⟩

/-- Full rows of width q+1 with pairwise intersections ≤1. Exactness on
outside sets of size t alone forces t gates per output whenever t≤q. -/
theorem uniform [Fintype L] (t : ℕ) (I : L → Finset P)
    (linear : ∀ l m, l≠m → (I l ∩ I m).card≤1) (W : List (Signal P)) (k : ℕ) (net : Net W k)
    (out : L → Signal P) (outputs : ∀ l, out l∈W) (off : ∀ l, Rejects (I l) t (out l))
    (many : ∀ l, t<(single (out l)).card) : Fintype.card L*t≤k := by
  obtain ⟨c,spent,row⟩ := charge 1 t (by decide) I linear W k net out outputs off
  have each (l : L) : t≤c l := by
    by_contra! few
    have b := row l few
    have m := many l
    omega
  have lt := Finset.sum_le_sum (s := Finset.univ) (fun l _ => each l)
  exact (by simpa [Finset.sum_const,smul_eq_mul] using lt : Fintype.card L*t≤∑ l,c l).trans spent

/-- With at most t+1 singleton hits per row this counts all recognized
singleton pairs, including when an output accepts only part of its row. -/
theorem partial_count [Fintype L] (t : ℕ) (I : L → Finset P)
    (linear : ∀ l m, l≠m → (I l ∩ I m).card≤1) (W : List (Signal P)) (k : ℕ) (net : Net W k)
    (out : L → Signal P) (outputs : ∀ l, out l∈W) (off : ∀ l, Rejects (I l) t (out l))
    (cap : ∀ l, (single (out l)).card≤t+1) : (∑ l,(single (out l)).card)≤k+Fintype.card L := by
  obtain ⟨c,spent,row⟩ := charge 1 t (by decide) I linear W k net out outputs off
  have each (l : L) : (single (out l)).card≤c l+1 := by
    by_cases few : c l<t
    · simpa using row l few
    · have top := cap l; omega
  calc
    _ ≤ ∑ l, (c l+1) := Finset.sum_le_sum (fun l _ => each l)
    _ ≤ _ := by simpa [Finset.sum_add_distrib] using Nat.add_le_add_right spent (Fintype.card L)

#print axioms uniform
#print axioms partial_count

end SparseRows
