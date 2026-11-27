import ProjectionTests
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Prod

/-! Row sizes and intersections of all projected ordinate queries, including
rows at different abscissas. The geometry requires a field for slopes and
balanced separating projection fibers on the ordinates. -/

namespace ProjectionRows

variable {E K H : Type} [Field E] [Fintype E] [DecidableEq E] [Fintype K] [DecidableEq K]

abbrev Query (H E K : Type) := H × E × K
def fiber (h : H → E → K) (d : H) (j : K) := Finset.univ.filter fun z => h d z=j
def row (h : H → E → K) (Q : Query H E K) := Finset.univ.filter fun l : E × E => h Q.1 (l.1*Q.2.1+l.2)=Q.2.2

@[simp] theorem mem_row (h : H → E → K) (d : H) (x : E) (j : K) (l : E × E) :
    l ∈ row h (d,x,j) ↔ h d (l.1*x+l.2)=j := by simp [row]

theorem row_card (h : H → E → K) (d : H) (x : E) (j : K) :
    (row h (d,x,j)).card=Fintype.card E*(fiber h d j).card := by
  classical
  let toOrd (l : E × E) := (l.1,l.1*x+l.2)
  let fromOrd (z : E × E) := (z.1,z.2-z.1*x)
  let T := (Finset.univ : Finset E) ×ˢ (fiber h d j)
  have eq : (row h (d,x,j)).card=T.card := by
    apply Finset.card_nbij' toOrd fromOrd
    · intro l hl
      simpa [T,toOrd,fiber] using (mem_row ..).mp hl
    · intro z hz
      have yes : h d z.2=j := by simpa [T,fiber] using hz
      simpa [fromOrd,add_sub_cancel] using yes
    · intro l _; apply Prod.ext <;> simp [toOrd,fromOrd]
    · intro z _; apply Prod.ext <;> simp [toOrd,fromOrd]
  simpa [T] using eq

private theorem two_values {a b c d x y : E} (different : x≠y)
    (left : a*x+b=c*x+d) (right : a*y+b=c*y+d) : a=c ∧ b=d := by
  have zero : (a-c)*(x-y)=0 := by linear_combination left - right
  have same := sub_eq_zero.mp ((mul_eq_zero.mp zero).resolve_right (sub_ne_zero.mpr different))
  subst c
  exact ⟨rfl,add_left_cancel left⟩

theorem row_overlap (h : H → E → K) (s : ℕ) (balanced : ∀ d j, (fiber h d j).card=s)
    (order : Fintype.card E=s*s)
    (separate : ∀ d e, d≠e → ∀ z z', h d z=h d z' → h e z=h e z' → z=z')
    (Q Q' : Query H E K) (ne : Q≠Q') : (row h Q ∩ row h Q').card≤s*s := by
  classical
  rcases Q with ⟨d,x,j⟩
  rcases Q' with ⟨e,y,k⟩
  let A := row h (d,x,j) ∩ row h (e,y,k)
  have hits (l : E × E) (hl : l∈A) : h d (l.1*x+l.2)=j ∧ h e (l.1*y+l.2)=k := by simpa [A] using hl
  change A.card≤_
  by_cases xy : x=y
  · subst y
    have inj : (A : Set (E × E)).InjOn Prod.fst := by
      intro l hl m hm slope
      obtain ⟨ld,le⟩ := hits l hl
      obtain ⟨md,me⟩ := hits m hm
      by_cases de : d=e
      · subst e
        exact False.elim (ne (by rw [←ld,←le]))
      · have ordinate := separate d e de _ _ (ld.trans md.symm) (le.trans me.symm)
        rw [slope] at ordinate
        exact Prod.ext slope (add_left_cancel ordinate)
    have c := Finset.card_le_card_of_injOn (s := A) (t := Finset.univ) Prod.fst (fun _ _ => Finset.mem_univ _) inj
    simpa [order] using c
  · let f (l : E × E) := (l.1*x+l.2,l.1*y+l.2)
    have toProd : Set.MapsTo f A ((fiber h d j ×ˢ fiber h e k : Finset (E × E)) : Set (E × E)) := by
      intro l hl
      simpa [f,fiber] using hits l hl
    have inj : (A : Set (E × E)).InjOn f := by
      intro l _ m _ eq
      have sides := two_values xy (congrArg Prod.fst eq) (congrArg Prod.snd eq)
      exact Prod.ext sides.1 sides.2
    simpa [balanced] using Finset.card_le_card_of_injOn f toProd inj

section Square
variable [Field K]
def projected (coords : E ≃ K × K) (D : Finset (Option K)) (d : ↥D) (z : E) :=
  ProjectionTests.project d.val (coords z)

theorem square_order (coords : E ≃ K × K) : Fintype.card E=Fintype.card K*Fintype.card K := by
  simpa using Fintype.card_congr coords

theorem square_balanced (coords : E ≃ K × K) (D : Finset (Option K)) (d : ↥D) (j : K) :
    (fiber (projected coords D) d j).card=Fintype.card K := by
  classical
  rcases d with ⟨d,hd⟩
  cases d with
  | none =>
    rw [← Finset.card_univ (α := K)]
    apply Finset.card_nbij' (fun a => (coords a).1) (fun v => coords.symm (v,j))
    · simp
    · intro v _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp [projected,ProjectionTests.project]⟩
    · intro a ha
      apply coords.injective
      have val : (coords a).2=j := (Finset.mem_filter.mp ha).2
      simp [← val]
    · intro v _; simp
  | some c =>
    rw [← Finset.card_univ (α := K)]
    apply Finset.card_nbij' (fun a => (coords a).2) (fun v => coords.symm (j-c*v,v))
    · simp
    · intro v _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp [projected,ProjectionTests.project]⟩
    · intro a ha
      apply coords.injective
      have val : (coords a).1+c*(coords a).2=j := (Finset.mem_filter.mp ha).2
      simp [←val]
    · intro v _; simp

theorem square_separate (coords : E ≃ K × K) (D : Finset (Option K)) (d e : ↥D) (ne : d≠e)
    (z z' : E) (ld : projected coords D d z=projected coords D d z')
    (le : projected coords D e z=projected coords D e z') : z=z' := by
  by_contra diff
  have diff' : coords z ≠ coords z' := fun he => diff (coords.injective he)
  exact ne (Subtype.ext (ProjectionTests.unique_direction diff' d.val e.val ld le))

end Square

#print axioms row_overlap
#print axioms square_balanced

end ProjectionRows
