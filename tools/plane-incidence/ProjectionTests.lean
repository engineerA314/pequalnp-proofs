import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! Sparse incidence membership from projected ordinates. The separation lemma
works for every family of tests in which two different words agree in at most
one position. The affine construction uses the projective directions of K². -/

namespace ProjectionTests

section Separation

variable {α δ β : Type*} [DecidableEq α] [DecidableEq δ]

def Passes (proj : δ → α → β) (directions : Finset δ) (ordinates : Finset α) (z : α) : Prop :=
  ∀ d ∈ directions, ∃ w ∈ ordinates, proj d z = proj d w

theorem separates (proj : δ → α → β)
    (unique : ∀ {z w : α}, z ≠ w → ∀ d e, proj d z = proj d w → proj e z = proj e w → d = e)
    (D : Finset δ) (W : Finset α) (z : α) (few : W.card < D.card) :
    Passes proj D W z ↔ z ∈ W := by
  classical
  constructor
  · intro pass
    by_contra missing
    let bad (w : α) := D.filter fun d => proj d z = proj d w
    have one : ∀ w ∈ W, (bad w).card ≤ 1 := by
      intro w hw
      apply Finset.card_le_one.mpr
      intro d hd e he
      have diff : z ≠ w := by rintro rfl; exact missing hw
      exact unique diff d e (Finset.mem_filter.mp hd).2
        (Finset.mem_filter.mp he).2
    have sub : D ⊆ W.biUnion bad := by
      intro d hd
      obtain ⟨w,hw,agree⟩ := pass d hd
      exact Finset.mem_biUnion.mpr ⟨w,hw,Finset.mem_filter.mpr ⟨hd,agree⟩⟩
    have bound : D.card ≤ W.card := calc
      _ ≤ (W.biUnion bad).card := Finset.card_le_card sub
      _ ≤ ∑ w ∈ W, (bad w).card := Finset.card_biUnion_le
      _ ≤ ∑ _w ∈ W, 1 := Finset.sum_le_sum one
      _ = _ := by simp
    omega
  · exact fun hz _ _ => ⟨z,hz,rfl⟩

end Separation

variable {K : Type*} [Field K]

def project : Option K → K × K → K
  | none, z => z.2
  | some a, z => z.1 + a*z.2

theorem unique_direction {z w : K × K} (ne : z ≠ w) (d e : Option K)
    (hd : project d z = project d w) (he : project e z = project e w) : d = e := by
  have same_two (a : K) (h0 : z.2 = w.2) (ha : z.1 + a*z.2 = w.1 + a*w.2) : False := by
    rw [h0] at ha
    exact ne (Prod.ext (add_right_cancel ha) h0)
  cases d with
  | none =>
    cases e with
    | none => rfl
    | some b => exact False.elim (same_two b hd he)
  | some a =>
    cases e with
    | none => exact False.elim (same_two a he hd)
    | some b =>
      change z.1 + a*z.2 = w.1 + a*w.2 at hd
      change z.1 + b*z.2 = w.1 + b*w.2 at he
      have nz : z.2 ≠ w.2 := fun eq => same_two a eq hd
      have prod : (a-b)*(z.2-w.2) = 0 := by linear_combination hd - he
      exact congrArg some (sub_eq_zero.mp ((mul_eq_zero.mp prod).resolve_right (sub_ne_zero.mpr nz)))

def kernelPoint : Option K → K × K
  | none => (1,0)
  | some a => (-a,1)

theorem kernel_injective : Function.Injective (kernelPoint (K := K)) := by
  intro d e eq
  cases d <;> cases e <;> simp_all [kernelPoint]

/-- Exactly one nonzero witness per selected direction suffices to spoof a
target ordinate. Distinct directions contribute distinct horizontal lines. -/
theorem sharp [DecidableEq K] (D : Finset (Option K)) :
    ∃ W : Finset (K × K), W.card = D.card ∧ (0,0) ∉ W ∧ Passes project D W (0,0) := by
  refine ⟨D.image kernelPoint, Finset.card_image_of_injective _ kernel_injective, ?_, ?_⟩
  · intro mem
    obtain ⟨d,_,e⟩ := Finset.mem_image.mp mem
    cases d <;> simp_all [kernelPoint]
  · intro d hd
    refine ⟨kernelPoint d,Finset.mem_image_of_mem _ hd,?_⟩
    cases d <;> simp [project,kernelPoint]

/- The coordinate ring has θ² = u + vθ. These identities hold for all u,v.
Choosing an irreducible quadratic gives the affine part of PG(2, |K|²). -/

def theta (u v : K) (x : K × K) : K × K := (u*x.2,x.1+v*x.2)

def ordinate (u v : K) (x a b : K × K) : K × K :=
  (a.1*x.1 + a.2*(theta u v x).1 + b.1, a.1*x.2 + a.2*(theta u v x).2 + b.2)

theorem project_ordinate (u v : K) (d : Option K) (x a b : K × K) :
    project d (ordinate u v x a b) = project d x * a.1 + project d (theta u v x) * a.2 + project d b := by
  cases d <;> simp [ordinate,project] <;> ring

def firstLayer (Y : (K × K) → (K × K) → Prop) (d : Option K) (a0 a1 h : K) : Prop :=
  ∃ b, Y (a0,a1) b ∧ project d b = h

def secondLayer (Y : (K × K) → (K × K) → Prop) (d : Option K) (a0 c1 h : K) : Prop :=
  ∃ a1, firstLayer Y d a0 a1 (h-c1*a1)

def thirdLayer (Y : (K × K) → (K × K) → Prop) (d : Option K) (c0 c1 h : K) : Prop :=
  ∃ a0, secondLayer Y d a0 c1 (h-c0*a0)

theorem three_layers (u v : K) (d : Option K) (x z : K × K) (Y : (K × K) → (K × K) → Prop) :
    thirdLayer Y d (project d x) (project d (theta u v x)) (project d z) ↔
      ∃ a b, Y a b ∧ project d z = project d (ordinate u v x a b) := by
  constructor
  · rintro ⟨a0,a1,b,active,same⟩
    refine ⟨(a0,a1),b,active,?_⟩
    rw [project_ordinate]
    dsimp only
    linear_combination -same
  · rintro ⟨⟨a0,a1⟩,b,active,same⟩
    refine ⟨a0,a1,b,active,?_⟩
    rw [project_ordinate] at same
    dsimp only at same
    linear_combination -same

/-- The actual three-layer predicates fed to the AND for a point are exact
when fewer ordinary lines are active than there are selected directions. -/
theorem sparse_membership [DecidableEq K] (u v : K) (D : Finset (Option K))
    (Y : Finset ((K × K) × (K × K))) (x z : K × K) (few : Y.card < D.card) :
    (∀ d ∈ D, thirdLayer (fun a b => (a,b) ∈ Y) d (project d x) (project d (theta u v x)) (project d z)) ↔
    ∃ l ∈ Y, z = ordinate u v x l.1 l.2 := by
  let W := Y.image fun l => ordinate u v x l.1 l.2
  have bound : W.card < D.card := lt_of_le_of_lt Finset.card_image_le few
  have sep := separates project unique_direction D W z bound
  have iff : (∀ d ∈ D, thirdLayer (fun a b => (a,b) ∈ Y) d (project d x)
      (project d (theta u v x)) (project d z)) ↔ Passes project D W z := by
    constructor
    · intro h d hd
      obtain ⟨a,b,active,e⟩ := (three_layers u v d x z _).mp (h d hd)
      exact ⟨_,Finset.mem_image_of_mem _ active,e⟩
    · intro h d hd
      obtain ⟨w,hw,e⟩ := h d hd
      obtain ⟨l,active,rfl⟩ := Finset.mem_image.mp hw
      exact (three_layers u v d x z _).mpr ⟨l.1,l.2,active,e⟩
  rw [iff,sep]
  constructor
  · intro hz
    obtain ⟨l,hl,eq⟩ := Finset.mem_image.mp hz
    exact ⟨l,hl,eq.symm⟩
  · rintro ⟨l,hl,rfl⟩
    exact Finset.mem_image_of_mem _ hl

#print axioms sparse_membership
#print axioms sharp

end ProjectionTests
