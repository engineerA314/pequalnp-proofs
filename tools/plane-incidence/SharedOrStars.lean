import PEqualNP.MetaComplexity.Helpers.Support
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! Shared OR preparations for stars in a C4-free graph. A preparation gate
whose support has at least two members can fit in at most one neighborhood.
Singleton or empty supports can be accounted for by the number of roots. -/

namespace SharedOrStars

open PEqualNP.MetaComplexity.Helpers

variable {V : Type} [DecidableEq V]

abbrev OrGate := ℕ × ℕ

def joined (S : List (Finset V)) (g : OrGate) := S.getD g.1 ∅ ∪ S.getD g.2 ∅

def run : List OrGate → List (Finset V) → List (Finset V)
  | [],S => S
  | g :: gs,S => run gs (S ++ [joined S g])

def fee (A U : Finset V) : ℕ := if U ⊆ A ∧ 2 ≤ U.card then 1 else 0

def charged (A : Finset V) : List OrGate → List (Finset V) → ℕ
  | [],_ => 0
  | g :: gs,S => fee A (joined S g) + charged A gs (S ++ [joined S g])

def joint (S : List (Finset V)) (W : Finset ℕ) := W.biUnion fun j => S.getD j ∅

def Budget (A : Finset V) (t : ℕ) (S : List (Finset V)) : Prop :=
  ∀ W : Finset ℕ, (∀ j ∈ W, S.getD j ∅ ⊆ A) → (joint S W).card ≤ t+W.card

theorem initial (A : Finset V) (S : List (Finset V)) (atomic : ∀ j, (S.getD j ∅).card ≤ 1) :
    Budget A 0 S := by
  intro W _
  apply le_trans Finset.card_biUnion_le
  rw [zero_add,Finset.card_eq_sum_ones]
  exact Finset.sum_le_sum fun j _ => atomic j

theorem step (A : Finset V) (t : ℕ) (S : List (Finset V)) (g : OrGate) (old : Budget A t S) :
    Budget A (t+fee A (joined S g)) (S ++ [joined S g]) := by
  classical
  let U := joined S g
  intro W good
  by_cases used : S.length ∈ W
  · let W' := W.erase S.length
    have early (j : ℕ) (hj : j ∈ W') : j ≠ S.length := (Finset.mem_erase.mp hj).1
    have good' (j : ℕ) (hj : j ∈ W') : S.getD j ∅ ⊆ A := by
      have h := good j (Finset.mem_of_mem_erase hj)
      rwa [getD_snoc_ne _ _ _ _ (early _ hj)] at h
    have contained : U ⊆ A := by simpa only [getD_snoc_eq,U] using good S.length used
    have stepSet : joint (S ++ [U]) W ⊆ joint S W' ∪ U := by
      intro x hx
      obtain ⟨j,hj,mem⟩ := Finset.mem_biUnion.mp hx
      by_cases eq : j = S.length
      · subst j; exact Finset.mem_union_right _ (by simpa only [getD_snoc_eq] using mem)
      · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
          ⟨j,Finset.mem_erase.mpr ⟨eq,hj⟩,by rwa [getD_snoc_ne _ _ _ _ eq] at mem⟩)
    have cardW : W'.card = W.card-1 := Finset.card_erase_of_mem used
    have pos := Finset.card_pos.mpr ⟨_,used⟩
    by_cases big : 2 ≤ U.card
    · let parents : Finset ℕ := {g.1,g.2}
      have sub : joint S W' ∪ U ⊆ joint S (W' ∪ parents) := by
        intro x hx
        rcases Finset.mem_union.mp hx with orig | added
        · obtain ⟨j,hj,mem⟩ := Finset.mem_biUnion.mp orig
          exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_union_left _ hj,mem⟩
        · rcases Finset.mem_union.mp added with l | r
          · exact Finset.mem_biUnion.mpr ⟨g.1,Finset.mem_union_right _ (by simp [parents]),l⟩
          · exact Finset.mem_biUnion.mpr ⟨g.2,Finset.mem_union_right _ (by simp [parents]),r⟩
      have newGood : ∀ j ∈ W' ∪ parents, S.getD j ∅ ⊆ A := by
        intro j hj
        rcases Finset.mem_union.mp hj with before | parent
        · exact good' j before
        · simp only [parents,Finset.mem_insert,Finset.mem_singleton] at parent
          rcases parent with rfl | rfl
          · exact Finset.Subset.trans Finset.subset_union_left contained
          · exact Finset.Subset.trans Finset.subset_union_right contained
      have cp : parents.card ≤ 2 := by exact Finset.card_le_two
      have c := (Finset.card_le_card (Finset.Subset.trans stepSet sub)).trans (old _ newGood)
      have cu := Finset.card_union_le W' parents
      change (joint (S ++ [U]) W).card ≤ t + fee A U + W.card
      have hf : fee A U = 1 := by simp [fee,contained,big]
      rw [hf]
      omega
    · have c := (Finset.card_le_card stepSet).trans (Finset.card_union_le _ _)
      have older := old W' good'
      change (joint (S ++ [U]) W).card ≤ t + fee A U + W.card
      omega
  · have eq : joint (S ++ [joined S g]) W = joint S W :=
      Finset.biUnion_congr rfl fun j hj => getD_snoc_ne _ _ _ _ (fun e => used (e ▸ hj))
    have good' : ∀ j ∈ W, S.getD j ∅ ⊆ A := by
      intro j hj
      have h := good j hj
      rwa [getD_snoc_ne _ _ _ _ (fun e => used (e ▸ hj))] at h
    rw [eq]
    have := old W good'
    omega

theorem prep_bound (A : Finset V) (gs : List OrGate) (S : List (Finset V)) (t : ℕ) (start : Budget A t S) :
    Budget A (t+charged A gs S) (run gs S) := by
  induction gs generalizing S t with
  | nil => simpa [run,charged] using start
  | cons g gs ih =>
    simpa only [run,charged,← Nat.add_assoc] using ih _ _ (step A t S g start)

theorem fee_once {κ : Type*} [Fintype κ] (neighbors : κ → Finset V)
    (linear : ∀ c d, c ≠ d → (neighbors c ∩ neighbors d).card ≤ 1) (U : Finset V) :
    ∑ c, fee (neighbors c) U ≤ 1 := by
  classical
  let owners := Finset.univ.filter fun c => U ⊆ neighbors c ∧ 2 ≤ U.card
  have small : owners.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro c hc d hd
    by_contra ne
    obtain ⟨subc,big⟩ := (Finset.mem_filter.mp hc).2
    have subd := (Finset.mem_filter.mp hd).2.1
    have sub : U ⊆ neighbors c ∩ neighbors d := fun x hx => Finset.mem_inter.mpr ⟨subc hx,subd hx⟩
    have := (Finset.card_le_card sub).trans (linear c d ne)
    omega
  simpa [fee,owners,Finset.sum_boole] using small

theorem charges_disjoint {κ : Type*} [Fintype κ] (neighbors : κ → Finset V)
    (linear : ∀ c d, c ≠ d → (neighbors c ∩ neighbors d).card ≤ 1)
    (gs : List OrGate) (S : List (Finset V)) : (∑ c, charged (neighbors c) gs S) ≤ gs.length := by
  induction gs generalizing S with
  | nil => simp [charged]
  | cons g gs ih =>
    simp only [charged,Finset.sum_add_distrib,List.length_cons]
    have f := fee_once neighbors linear (joined S g)
    have h := ih (S ++ [joined S g])
    omega

/-- Any cover of the edge set by star arms produced in a shared OR network
pays at least one preparation OR or one product term for every edge. -/
theorem cover_cost {κ : Type*} [Fintype V] [DecidableEq κ]
    (neighbors : V → Finset V) (linear : ∀ c d, c ≠ d → (neighbors c ∩ neighbors d).card ≤ 1)
    (E : Finset (Finset V)) (gs : List OrGate) (S : List (Finset V))
    (atomic : ∀ j, (S.getD j ∅).card ≤ 1) (T : Finset κ) (center : κ → V) (arm : κ → ℕ)
    (inside : ∀ i ∈ T, (run gs S).getD (arm i) ∅ ⊆ neighbors (center i))
    (cover : ∀ e ∈ E, ∃ i ∈ T, ∃ v ∈ (run gs S).getD (arm i) ∅, e = {center i,v}) :
    E.card ≤ gs.length+T.card := by
  classical
  let terms (c : V) := T.filter fun i => center i = c
  let roots (c : V) := (terms c).image arm
  let pts (c : V) := joint (run gs S) (roots c)
  let stars (c : V) := (pts c).image fun v => ({c,v} : Finset V)
  have budgets (c : V) : (pts c).card ≤ charged (neighbors c) gs S + (terms c).card := by
    have b := prep_bound (neighbors c) gs S 0 (initial _ S atomic) (roots c) (by
      intro j hj
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
      obtain ⟨ht,eq⟩ := Finset.mem_filter.mp hi
      exact eq ▸ inside i ht)
    have r : (roots c).card ≤ (terms c).card := Finset.card_image_le
    change (joint (run gs S) (roots c)).card ≤ _
    omega
  have sub : E ⊆ Finset.univ.biUnion stars := by
    intro e he
    obtain ⟨i,hi,v,hv,rfl⟩ := cover e he
    refine Finset.mem_biUnion.mpr ⟨center i,Finset.mem_univ _,Finset.mem_image_of_mem _ ?_⟩
    exact Finset.mem_biUnion.mpr ⟨arm i,Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hi,rfl⟩),hv⟩
  have totalTerms : ∑ c, (terms c).card = T.card :=
    (Finset.card_eq_sum_card_fiberwise (f := center) (s := T) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)).symm
  calc
    E.card ≤ (Finset.univ.biUnion stars).card := Finset.card_le_card sub
    _ ≤ ∑ c, (stars c).card := Finset.card_biUnion_le
    _ ≤ ∑ c, (charged (neighbors c) gs S + (terms c).card) :=
        Finset.sum_le_sum fun c _ => Finset.card_image_le.trans (budgets c)
    _ = (∑ c, charged (neighbors c) gs S) + T.card := by rw [Finset.sum_add_distrib,totalTerms]
    _ ≤ _ := Nat.add_le_add_right (charges_disjoint neighbors linear gs S) _

#print axioms cover_cost

end SharedOrStars
