import SingleLevelStars
import Mathlib.Data.Fintype.Prod

/-! Exact edge count and minimum cover of the affine restriction obtained by
fixing horizontal anchors and retaining nonhorizontal ordinary lines. -/

namespace AffineStarBound

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

abbrev Point (B : Finset K) := K × {z : K // z ∉ B}
abbrev Slope (K : Type) [Zero K] := {a : K // a ≠ 0}
abbrev Line (K : Type) [Zero K] := Slope K × K
abbrev Vertex (B : Finset K) := Point B ⊕ Line K

def lineAt {B : Finset K} (p : Point B) (a : Slope K) : Line K := (a,p.2.val-a.val*p.1)
def Incident {B : Finset K} (p : Point B) (l : Line K) := p.2.val=l.1.val*p.1+l.2
def edge {B : Finset K} (p : Point B) (l : Line K) : Finset (Vertex B) := {.inl p,.inr l}
def edges (B : Finset K) := Finset.univ.image fun t : Point B × Slope K => edge t.1 (lineAt t.1 t.2)

omit [Fintype K] in
theorem edge_inj {B : Finset K} {p u : Point B} {l m : Line K} (h : edge p l = edge u m) : p=u ∧ l=m := by
  have hp : Sum.inl p ∈ edge u m := h ▸ (by simp [edge])
  have hl : Sum.inr l ∈ edge u m := h ▸ (by simp [edge])
  exact ⟨by simpa [edge] using hp,by simpa [edge] using hl⟩

theorem count (B : Finset K) : (edges B).card=Fintype.card (Point B)*Fintype.card (Slope K) := by
  rw [edges,Finset.card_image_of_injective _ ?_,Finset.card_univ,Fintype.card_prod]
  intro a b h
  obtain ⟨hp,hl⟩ := edge_inj h
  exact Prod.ext hp (congrArg Prod.fst hl)

def Adj {B : Finset K} : Vertex B → Vertex B → Prop
  | .inl p,.inr l | .inr l,.inl p => Incident p l
  | _,_ => False

theorem cross {B : Finset K} (p : Point B) (l : Line K) : edge p l ∈ edges B ↔ Incident p l := by
  constructor
  · intro h
    obtain ⟨⟨u,a⟩,_,eq⟩ := Finset.mem_image.mp h
    obtain ⟨hp,hl⟩ := edge_inj eq
    subst p; subst l
    simp [Incident,lineAt]
  · intro h
    refine Finset.mem_image.mpr ⟨(p,l.1),Finset.mem_univ _,?_⟩
    have hl : lineAt p l.1 = l := by
      refine Prod.ext ?_ ?_
      · rfl
      change p.2.val-l.1.val*p.1=l.2
      rw [h]
      ring
    rw [hl]

theorem adjacency {B : Finset K} (u v : Vertex B) : {u,v} ∈ edges B ↔ Adj u v := by
  cases u with
  | inl p =>
    cases v with
    | inr l => exact cross p l
    | inl p' =>
      refine ⟨fun h => ?_,False.elim⟩
      obtain ⟨⟨t,a⟩,_,e⟩ := Finset.mem_image.mp h
      have bad : Sum.inr (lineAt t a) ∈ ({Sum.inl p,Sum.inl p'} : Finset (Vertex B)) := e ▸ (by simp [edge])
      simp at bad
  | inr l =>
    cases v with
    | inl p => rw [Finset.pair_comm]; exact cross p l
    | inr l' =>
      refine ⟨fun h => ?_,False.elim⟩
      obtain ⟨⟨t,a⟩,_,e⟩ := Finset.mem_image.mp h
      have bad : Sum.inl t ∈ ({Sum.inr l,Sum.inr l'} : Finset (Vertex B)) := e ▸ (by simp [edge])
      simp at bad

omit [Fintype K] [DecidableEq K] in
theorem no_rectangle {B : Finset K} (p u : Point B) (l m : Line K)
    (pl : Incident p l) (pm : Incident p m) (ul : Incident u l) (um : Incident u m) :
    p=u ∨ l=m := by
  unfold Incident at pl pm ul um
  have product : (l.1.val-m.1.val)*(p.1-u.1)=0 := by linear_combination -pl+pm+ul-um
  rcases mul_eq_zero.mp product with sameSlope | sameX
  · have a := sub_eq_zero.mp sameSlope
    right
    exact Prod.ext (Subtype.ext a) (by rw [a] at pl; linear_combination pm-pl)
  · have x := sub_eq_zero.mp sameX
    left
    exact Prod.ext x (Subtype.ext (by rw [x] at pl; linear_combination pl-ul))

theorem linear (B : Finset K) (c d : Vertex B) (ne : c≠d) :
    (SingleLevelStars.neighbors (edges B) c ∩ SingleLevelStars.neighbors (edges B) d).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro u hu v hv
  simp only [Finset.mem_inter,SingleLevelStars.mem_neighbors,adjacency] at hu hv
  obtain ⟨cu,du⟩ := hu
  obtain ⟨cv,dv⟩ := hv
  cases c <;> cases d <;> cases u <;> cases v <;> simp_all only [Adj,Sum.inl.injEq,Sum.inr.injEq]
  · rename_i p u l m
    exact (no_rectangle p u l m cu cv du dv).resolve_left (fun e => ne (congrArg Sum.inl e))
  · rename_i l m p u
    exact (no_rectangle p u l m cu du cv dv).resolve_right (fun e => ne (congrArg Sum.inr e))

def matchingLine {B : Finset K} (b : K) (hb : b ∈ B) (p : Point B) : Line K :=
  lineAt p ⟨p.2.val-b,sub_ne_zero.mpr (fun e => p.2.property (e ▸ hb))⟩

omit [Fintype K] [DecidableEq K] in
theorem matching_injective {B : Finset K} (b : K) (hb : b ∈ B) : Function.Injective (matchingLine b hb) := by
  intro p u e
  have slopes := congrArg (fun l : Line K => l.1.val) e
  have intercepts := congrArg (fun l : Line K => l.2) e
  change p.2.val-b=u.2.val-b at slopes
  change p.2.val-(p.2.val-b)*p.1=u.2.val-(u.2.val-b)*u.1 at intercepts
  have z : p.2.val = u.2.val := by linear_combination slopes
  rw [z] at intercepts
  have nz : u.2.val-b ≠ 0 := sub_ne_zero.mpr fun eq => u.2.property (eq ▸ hb)
  exact Prod.ext (mul_left_cancel₀ nz (sub_right_inj.mp intercepts)) (Subtype.ext z)

theorem cover_lower {B : Finset K} (b : K) (hb : b ∈ B) (Z : Finset (Vertex B))
    (cover : SingleLevelStars.Covers (edges B) Z) : Fintype.card (Point B) ≤ Z.card := by
  classical
  let f (p : Point B) : Vertex B := if Sum.inl p ∈ Z then .inl p else .inr (matchingLine b hb p)
  have inside (p : Point B) : f p ∈ Z := by
    by_cases hp : Sum.inl p ∈ Z
    · simp [f,hp]
    · have incident : edge p (matchingLine b hb p) ∈ edges B := by
        apply (cross p _).mpr
        simp [Incident,matchingLine,lineAt]
      obtain ⟨w,hw,one⟩ := cover _ incident
      simp only [edge,Finset.mem_insert,Finset.mem_singleton] at one
      rcases one with rfl | rfl
      · contradiction
      · simpa [f,hp] using hw
  have inj : Function.Injective f := by
    intro p u e
    by_cases hp : Sum.inl p ∈ Z <;> by_cases hu : Sum.inl u ∈ Z <;> simp_all [f,matching_injective b hb |>.eq_iff]
  have bound := Finset.card_le_card_of_injOn f (s := Finset.univ) (t := Z)
    (fun p _ => inside p) inj.injOn
  simpa using bound

omit [Field K] in
theorem point_count (B : Finset K) : Fintype.card (Point B)=Fintype.card K*(Fintype.card K-B.card) := by
  rw [Fintype.card_prod,Fintype.card_subtype_compl]
  simp

theorem slope_count : Fintype.card (Slope K)=Fintype.card K-1 := by
  rw [Fintype.card_subtype_compl]
  simp

theorem restricted_lower (B : Finset K) (anchor : B.Nonempty)
    (prep : List SharedOrStars.OrGate) (raw : List (Finset (Vertex B)))
    (atomic : ∀ j, (raw.getD j ∅).card ≤ 1) {r : ℕ} (left right : Fin r → ℕ)
    (correct : ∀ u v : Vertex B, (∃ i : Fin r,
      SingleLevelStars.Fires ((SharedOrStars.run prep raw).getD (left i) ∅) {u,v} ∧
      SingleLevelStars.Fires ((SharedOrStars.run prep raw).getD (right i) ∅) {u,v}) ↔ {u,v} ∈ edges B) :
    (Fintype.card K)^2*(Fintype.card K-B.card) ≤ prep.length+2*r := by
  obtain ⟨b,hb⟩ := anchor
  have simple (e : Finset (Vertex B)) (he : e ∈ edges B) : e.card=2 := by
    obtain ⟨⟨p,a⟩,_,rfl⟩ := Finset.mem_image.mp he
    simp [edge]
  have lower := SingleLevelStars.lower _ simple (linear B) prep raw atomic left right correct _
    (cover_lower b hb)
  rw [count,slope_count,point_count] at lower
  have pos : 0 < Fintype.card K := Fintype.card_pos
  have inc : (Fintype.card K-1).succ=Fintype.card K := by omega
  rw [← Nat.mul_succ,inc] at lower
  nlinarith

#print axioms restricted_lower

end AffineStarBound
