import AffineBlocking
import ProjectionTests
import Mathlib.Logic.Equiv.Fin.Basic

/-! Minimum number of ordinary active lines that forces every projected
incidence bucket on at every affine abscissa. The full-direction case is an
affine blocking problem already visible in the column x=0. -/

namespace ProjectionAnchors

open ProjectionTests

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

abbrev Point (K : Type*) := K × K
abbrev Line (K : Type*) := Point K × Point K

def Surjects (D : Finset (Option K)) (B : Finset (Point K)) : Prop :=
  ∀ d ∈ D, ∀ c : K, ∃ b ∈ B, project d b = c

def Saturates (u v : K) (D : Finset (Option K)) (R : Finset (Line K)) : Prop :=
  ∀ (x : Point K) d, d ∈ D → ∀ c : K, ∃ l ∈ R, project d (ordinate u v x l.1 l.2) = c

def horizontal (b : Point K) : Line K := ((0,0),b)

omit [Fintype K] in
theorem horizontal_saturates (u v : K) (D : Finset (Option K)) (B : Finset (Point K))
    (h : Surjects D B) : Saturates u v D (B.image horizontal) := by
  intro x d hd c
  obtain ⟨b,hb,e⟩ := h d hd c
  refine ⟨horizontal b,Finset.mem_image_of_mem _ hb,?_⟩
  simpa [horizontal,ordinate] using e

omit [Fintype K] in
theorem intercepts_surject (u v : K) (D : Finset (Option K)) (R : Finset (Line K))
    (h : Saturates u v D R) : Surjects D (R.image Prod.snd) := by
  intro d hd c
  obtain ⟨l,hl,e⟩ := h (0,0) d hd c
  exact ⟨l.2,Finset.mem_image_of_mem _ hl,by simpa [ordinate,theta] using e⟩

theorem field_lower (D : Finset (Option K)) (B : Finset (Point K)) (has : D.Nonempty)
    (surj : Surjects D B) : Fintype.card K ≤ B.card := by
  obtain ⟨d,hd⟩ := has
  have eq : B.image (project d) = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro c
    exact Finset.mem_image.mpr (surj d hd c)
  have h := Finset.card_image_le (s := B) (f := project d)
  simpa [eq] using h

def scale (a : K) (b : Point K) : Point K := (a*b.1,a*b.2)

omit [Fintype K] [DecidableEq K] in
theorem project_scale (d : Option K) (a : K) (b : Point K) : project d (scale a b) = a*project d b := by
  cases d <;> simp [project,scale]
  ring

theorem proper_optimum (u v : K) (D : Finset (Option K)) (has : D.Nonempty) (missing : ∃ d, d ∉ D) :
    (∃ R, Saturates u v D R ∧ R.card = Fintype.card K) ∧
    (∀ R, Saturates u v D R → Fintype.card K ≤ R.card) := by
  obtain ⟨m,hm⟩ := missing
  let ray := kernelPoint m
  let B := Finset.univ.image fun a : K => scale a ray
  have nz : ray ≠ (0,0) := by cases m <;> simp [ray,kernelPoint]
  have m0 : project m ray = project m (0,0) := by cases m <;> simp [ray,kernelPoint,project]
  have surj : Surjects D B := by
    intro d hd c
    have den : project d ray ≠ 0 := by
      intro h
      have dz : project d ray = project d (0,0) := by cases d <;> simpa [project] using h
      exact hm (unique_direction nz d m dz m0 ▸ hd)
    refine ⟨scale (c/project d ray) ray,Finset.mem_image_of_mem _ (Finset.mem_univ _),?_⟩
    rw [project_scale,div_mul_cancel₀ _ den]
  have lower (R : Finset (Line K)) (h : Saturates u v D R) :=
    (field_lower D (R.image Prod.snd) has (intercepts_surject u v D R h)).trans Finset.card_image_le
  have good := horizontal_saturates u v D B surj
  have small : (B.image horizontal).card ≤ Fintype.card K :=
    Finset.card_image_le.trans (Finset.card_image_le.trans (le_of_eq Finset.card_univ))
  exact ⟨⟨_,good,Nat.le_antisymm small (lower _ good)⟩,lower⟩

def vec (b : Point K) : Fin 2 → K := ![b.1,b.2]

theorem all_iff_blocks (B : Finset (Point K)) :
    Surjects Finset.univ B ↔ AffineBlocking.Blocks (B.image vec) := by
  constructor
  · intro surj w nz c
    have someCoeff : w 0 ≠ 0 ∨ w 1 ≠ 0 := by
      by_contra! empty
      apply nz
      funext i
      fin_cases i <;> simp [empty.1,empty.2]
    by_cases first : w 0 = 0
    · have nonzero := someCoeff.resolve_left (not_not.mpr first)
      obtain ⟨b,hb,eq⟩ := surj none (Finset.mem_univ _) (c/w 1)
      refine ⟨vec b,Finset.mem_image_of_mem _ hb,?_⟩
      change b.2 = c / w 1 at eq
      simp [AffineBlocking.dot,Fin.sum_univ_two,vec,first,eq,nonzero]
    · obtain ⟨b,hb,eq⟩ := surj (some (w 1/w 0)) (Finset.mem_univ _) (c/w 0)
      refine ⟨vec b,Finset.mem_image_of_mem _ hb,?_⟩
      change b.1 + (w 1/w 0)*b.2 = c / w 0 at eq
      simp only [AffineBlocking.dot,Fin.sum_univ_two,vec,Matrix.cons_val_zero,Matrix.cons_val_one]
      field_simp [first] at eq
      linear_combination eq
  · intro block d _ c
    cases d with
    | none =>
      let w : Fin 2 → K := ![0,1]
      have nz : w ≠ 0 := by intro e; exact one_ne_zero (congrFun e 1)
      obtain ⟨v,hv,eq⟩ := block w nz c
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hv
      exact ⟨b,hb,by simpa [AffineBlocking.dot,Fin.sum_univ_two,w,vec,project] using eq⟩
    | some a =>
      let w : Fin 2 → K := ![1,a]
      have nz : w ≠ 0 := by intro e; exact one_ne_zero (congrFun e 0)
      obtain ⟨v,hv,eq⟩ := block w nz c
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hv
      exact ⟨b,hb,by simpa [AffineBlocking.dot,Fin.sum_univ_two,w,vec,project,mul_comm] using eq⟩

theorem full_optimum (u v : K) :
    (∃ R, Saturates u v Finset.univ R ∧ R.card = 2*(Fintype.card K-1)+1) ∧
    (∀ R, Saturates u v Finset.univ R → 2*(Fintype.card K-1)+1 ≤ R.card) := by
  have lower (R : Finset (Line K)) (h : Saturates u v Finset.univ R) : 2*(Fintype.card K-1)+1 ≤ R.card := by
    have b := (all_iff_blocks _).mp (intercepts_surject u v _ R h)
    have l := AffineBlocking.lower _ b
    simp only [Fintype.card_fin] at l
    exact l.trans (Finset.card_image_le.trans Finset.card_image_le)
  let A := AffineBlocking.axes (K := K) (ι := Fin 2)
  let B := A.image fun x => (x 0,x 1)
  have inverse (x : Fin 2 → K) : vec (x 0,x 1) = x := by
    funext i
    fin_cases i <;> rfl
  have eq : B.image vec = A := by
    ext x
    simp [B,Finset.image_image,Function.comp_def,inverse]
  have surj : Surjects Finset.univ B := (all_iff_blocks B).mpr (eq ▸ AffineBlocking.axes_blocks)
  have h := horizontal_saturates u v _ B surj
  have cap : (B.image horizontal).card ≤ 2*(Fintype.card K-1)+1 := calc
    _ ≤ B.card := Finset.card_image_le
    _ ≤ A.card := Finset.card_image_le
    _ = _ := by simp [A,AffineBlocking.axes_size]
  exact ⟨⟨_,h,Nat.le_antisymm cap (lower _ h)⟩,lower⟩

#print axioms proper_optimum
#print axioms full_optimum

end ProjectionAnchors
