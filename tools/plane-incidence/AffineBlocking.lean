import Mathlib.FieldTheory.ChevalleyWarning
import Mathlib.Tactic

/-! Finite affine blocking sets. The lower bound is the Jamison and
Brouwer--Schrijver theorem. A product of linear factors represents the delta
function at the zero normal. Mathlib's finite-field sum lemma supplies its
degree lower bound. -/

namespace AffineBlocking

open MvPolynomial

variable {K ι : Type*} [Field K] [Fintype ι]

def dot (v b : ι → K) := ∑ i, b i*v i

def Blocks (B : Finset (ι → K)) : Prop := ∀ v : ι → K, v ≠ 0 → ∀ c : K, ∃ b ∈ B, dot v b = c

noncomputable def factor (a b : ι → K) : MvPolynomial ι K := 1 - ∑ i, C (b i-a i)*X i

theorem degree_factor (a b : ι → K) : (factor a b).totalDegree ≤ 1 := by
  apply (totalDegree_sub _ _).trans
  apply max_le (by simp)
  apply totalDegree_finsetSum_le
  intro i _
  exact (totalDegree_mul _ _).trans (by rw [totalDegree_C,totalDegree_X])

theorem eval_factor (a b v : ι → K) : eval v (factor a b) = 1 - (dot v b-dot v a) := by
  simp [factor,dot,sub_mul,Finset.sum_sub_distrib]

variable [Fintype K] [DecidableEq ι]

/-- A set meeting every affine hyperplane of a positive-dimensional finite
vector space has at least dim*(field order-1)+1 points. -/
theorem lower [Nonempty ι] (B : Finset (ι → K)) (blocks : Blocks B) :
    Fintype.card ι * (Fintype.card K-1) + 1 ≤ B.card := by
  classical
  have ne : (fun _ : ι => (1 : K)) ≠ 0 := by
    intro eq
    have h := congrFun eq (Classical.arbitrary ι)
    exact one_ne_zero h
  obtain ⟨a,ha,_⟩ := blocks _ ne 0
  let F : MvPolynomial ι K := ∏ b ∈ B.erase a, factor a b
  have deg : F.totalDegree ≤ (B.erase a).card := calc
    _ ≤ ∑ b ∈ B.erase a, (factor a b).totalDegree := totalDegree_finsetProd _ _
    _ ≤ ∑ _b ∈ B.erase a, 1 := Finset.sum_le_sum fun b _ => degree_factor a b
    _ = _ := by simp
  have atZero : eval (0 : ι → K) F = 1 := by
    simp only [F,map_prod,eval_factor]
    simp [dot]
  have elsewhere (v : ι → K) (nz : v ≠ 0) : eval v F = 0 := by
    obtain ⟨b,hb,val⟩ := blocks v nz (dot v a + 1)
    have ba : b ≠ a := by rintro rfl; exact one_ne_zero (by linear_combination -val)
    simp only [F,map_prod]
    apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨ba,hb⟩)
    rw [eval_factor,val]
    ring
  have sum1 : (∑ v : ι → K, eval v F) = 1 := by
    rw [Finset.sum_eq_single (0 : ι → K)]
    · exact atZero
    · exact fun v _ h => elsewhere v h
    · simp
  by_contra! small
  have pos := Finset.card_pos.mpr ⟨a,ha⟩
  rw [Finset.card_erase_of_mem ha] at deg
  have degree_lt : F.totalDegree < (Fintype.card K-1) * Fintype.card ι := by
    rw [Nat.mul_comm]
    omega
  exact one_ne_zero (sum1.symm.trans (F.sum_eval_eq_zero degree_lt))

/- The upper witness is the origin together with each coordinate axis minus
its origin. Distinct axes meet only at zero. -/

noncomputable def axes : Finset (ι → K) := by
  classical
  exact insert 0 (Finset.univ.biUnion fun i : ι => (Finset.univ.erase (0 : K)).image (Pi.single i))

theorem axes_size : (axes (ι := ι) (K := K)).card = Fintype.card ι * (Fintype.card K-1)+1 := by
  classical
  let rays (i : ι) := (Finset.univ.erase (0 : K)).image (fun x : K => Pi.single (M := fun _ : ι => K) i x)
  have atIndex (i : ι) (x : K) : Pi.single (M := fun _ : ι => K) i x i = x := by simp
  have nzray (i : ι) (b : ι → K) (hb : b ∈ rays i) : b i ≠ 0 := by
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hb
    simpa [atIndex] using (Finset.mem_erase.mp hx).1
  have size (i : ι) : (rays i).card = Fintype.card K-1 := by
    dsimp only [rays]
    rw [Finset.card_image_of_injective _ (fun x y eq => by simpa only [atIndex] using congrFun eq i),
        Finset.card_erase_of_mem (Finset.mem_univ _),Finset.card_univ]
  have dj : ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint rays := by
    intro i _ j _ ne
    rw [Function.onFun,Finset.disjoint_left]
    intro b bi bj
    have nonzero := nzray i b bi
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp bj
    exact nonzero (by simp [ne])
  have nozero : 0 ∉ Finset.univ.biUnion rays := by
    intro h
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp h
    exact nzray i 0 hi rfl
  change (insert 0 (Finset.univ.biUnion rays)).card = _
  rw [Finset.card_insert_of_notMem nozero,Finset.card_biUnion dj]
  simp [size]

theorem axes_blocks : Blocks (axes (ι := ι) (K := K)) := by
  classical
  intro v nz c
  by_cases cz : c=0
  · exact ⟨0,Finset.mem_insert_self _ _,by simp [dot,cz]⟩
  · have someNonzero : ∃ i, v i ≠ 0 := by
      by_contra! all
      exact nz (funext all)
    obtain ⟨i,vi⟩ := someNonzero
    let b := c/v i
    have bn : b ≠ 0 := div_ne_zero cz vi
    refine ⟨Pi.single i b,Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr
      ⟨i,Finset.mem_univ _,Finset.mem_image.mpr ⟨b,Finset.mem_erase.mpr ⟨bn,Finset.mem_univ _⟩,rfl⟩⟩),?_⟩
    unfold dot
    rw [Finset.sum_eq_single i]
    · simp [b,vi]
    · intro j _ ji
      rw [Pi.single_eq_of_ne ji,zero_mul]
    · simp

#print axioms lower
#print axioms axes_size
#print axioms axes_blocks

end AffineBlocking
