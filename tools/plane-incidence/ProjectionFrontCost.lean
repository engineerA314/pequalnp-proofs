import OverlapSums
import ProjectionRows

/-! Total cost of producing the shared projected outputs, even when their
entire implementation is replaced by an arbitrary monotone network. -/

namespace ProjectionFrontCost

open PartialSums ProjectionRows

theorem uniform {P L : Type} [Fintype P] [DecidableEq P] [Fintype L] (b s : ℕ) (pos : 0<b)
    (I : L → Finset P) (linear : ∀ l m, l≠m → (I l ∩ I m).card≤b) (size : ∀ l, b*s≤(I l).card)
    (W : List (Signal P)) (k : ℕ) (net : Built W k) (out : L → Signal P)
    (outputs : ∀ l, out l ∈ W) (accept : ∀ l p, p∈I l → out l {p}=true)
    (reject : ∀ l, out l (outside I l)=false) : Fintype.card L*(s-1)≤k := by
  have each (l : L) : b*s≤(single (out l)).card := by
    apply (size l).trans (Finset.card_le_card ?_)
    exact fun p hp => Finset.mem_filter.mpr ⟨Finset.mem_univ _,accept l p hp⟩
  have sum := Finset.sum_le_sum (s := Finset.univ) (fun l _ => each l)
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul] at sum
  have bound := sum.trans (OverlapSums.total b pos I linear W k net out outputs reject)
  have normalized : b*(Fintype.card L*s)≤b*(k+Fintype.card L) := by
    simpa only [Nat.mul_left_comm,Nat.mul_assoc,Nat.mul_comm] using bound
  have c := Nat.le_of_mul_le_mul_left normalized pos
  rw [Nat.mul_sub,Nat.mul_one]
  omega

variable {E K H : Type} [Field E] [Fintype E] [DecidableEq E] [Fintype K] [DecidableEq K]

def firstRow (h : H → E → K) (Q : Query H E K) :=
  ({Q.2.1} : Finset E) ×ˢ fiber h Q.1 Q.2.2

theorem first_overlap (h : H → E → K)
    (separate : ∀ d e, d≠e → ∀ z z', h d z=h d z' → h e z=h e z' → z=z')
    (Q Q' : Query H E K) (ne : Q≠Q') : (firstRow h Q ∩ firstRow h Q').card≤1 := by
  classical
  rcases Q with ⟨d,a,j⟩
  rcases Q' with ⟨e,a',j'⟩
  apply Finset.card_le_one.mpr
  intro l hl m hm
  simp only [firstRow,Finset.mem_inter,Finset.mem_product,Finset.mem_singleton,
    fiber,Finset.mem_filter,Finset.mem_univ,true_and] at hl hm
  have aa : a=a' := hl.1.1.symm.trans hl.2.1
  by_cases de : d=e
  · subst e
    have jj := hl.1.2.symm.trans hl.2.2
    exact False.elim (ne (by rw [aa,jj]))
  · exact Prod.ext (hl.1.1.trans hm.1.1.symm)
      (separate d e de _ _ (hl.1.2.trans hm.1.2.symm) (hl.2.2.trans hm.2.2.symm))

section Square
variable [Field K]

def targets (s d : ℕ) := d*(s*s)*s

theorem square_final (coords : E ≃ K × K) (D : Finset (Option K)) (W : List (Signal (E × E)))
    (k : ℕ) (net : Built W k) (out : Query ↥D E K → Signal (E × E))
    (outputs : ∀ Q, out Q ∈ W)
    (accept : ∀ Q l, l∈row (projected coords D) Q → out Q {l}=true)
    (reject : ∀ Q, out Q (outside (row (projected coords D)) Q)=false) :
    targets (Fintype.card K) D.card*(Fintype.card K-1)≤k := by
  let s := Fintype.card K
  let h := projected coords D
  have order : Fintype.card E=s*s := square_order coords
  have balanced : ∀ d j, (fiber h d j).card=s := square_balanced coords D
  have pos : 0<s := Fintype.card_pos
  have size (Q : Query ↥D E K) : (s*s)*s≤(row h Q).card := by
    obtain ⟨d,x,j⟩ := Q
    rw [row_card,balanced,order]
  have bound := uniform (s*s) s (by positivity) (row h)
    (row_overlap h s balanced order (square_separate coords D)) size W k net out outputs accept reject
  simpa [targets,Query,s,Fintype.card_prod,order,Nat.mul_assoc] using bound

theorem square_first (coords : E ≃ K × K) (D : Finset (Option K)) (W : List (Signal (E × E)))
    (k : ℕ) (net : Built W k) (out : Query ↥D E K → Signal (E × E))
    (outputs : ∀ Q, out Q ∈ W)
    (accept : ∀ Q l, l∈firstRow (projected coords D) Q → out Q {l}=true)
    (reject : ∀ Q, out Q (outside (firstRow (projected coords D)) Q)=false) :
    targets (Fintype.card K) D.card*(Fintype.card K-1)≤k := by
  let s := Fintype.card K
  let h := projected coords D
  have order : Fintype.card E=s*s := square_order coords
  have balanced : ∀ d j, (fiber h d j).card=s := square_balanced coords D
  have size (Q : Query ↥D E K) : 1*s≤(firstRow h Q).card := by
    simp [firstRow,balanced]
  have bound := uniform 1 s (by decide) (firstRow h) (first_overlap h (square_separate coords D))
    size W k net out outputs accept reject
  simpa [targets,Query,s,Fintype.card_prod,order,Nat.mul_assoc] using bound

end Square

#print axioms square_final
#print axioms square_first

end ProjectionFrontCost
