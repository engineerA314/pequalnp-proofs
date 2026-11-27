import SparseRows
import PlaneAnchorBudget
import ProjectionFrontCost

/-! Projective pencils give an exact Nq multi-output lower bound under
q-sparse soundness. The same sparse cut also applies to projection rows. -/

namespace SparsePlanes

open PartialSums SparseFrontier SparseRows PlaneAnchorBudget ProjectionRows

def pencil {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (p : Fin N) :=
  Finset.univ.filter fun w => I p w

theorem pencil_overlap {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (unique : ∀ p r, p≠r → ∃! w, I p w ∧ I r w) (p r : Fin N) (ne : p≠r) :
    (pencil I p ∩ pencil I r).card≤1 := by
  obtain ⟨_,_,only⟩ := unique p r ne
  apply Finset.card_le_one.mpr
  intro u hu v hv
  simp only [pencil,Finset.mem_inter,Finset.mem_filter,Finset.mem_univ,true_and] at hu hv
  exact (only u hu).trans (only v hv).symm

theorem pencil_size {N q : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (hq : 0<q)
    (size : N=q^2+q+1) (lengths : ∀ w, (lineSet I w).card=q+1)
    (unique : ∀ p r, p≠r → ∃! w, I p w ∧ I r w) (p : Fin N) : (pencil I p).card=q+1 := by
  classical
  let T := pencil I p
  let B (w : Fin N) := (lineSet I w).erase p
  have cover : T.biUnion B=Finset.univ.erase p := by
    ext r
    simp only [Finset.mem_biUnion,Finset.mem_erase,Finset.mem_univ,and_true]
    constructor
    · rintro ⟨_,_,h⟩
      exact (Finset.mem_erase.mp h).1
    · intro rp
      obtain ⟨w,⟨pw,rw⟩,_⟩ := unique p r rp.symm
      exact ⟨w,by simpa [T,pencil] using pw,Finset.mem_erase.mpr ⟨rp,by simpa [lineSet] using rw⟩⟩
  have disjoint : (T : Set (Fin N)).PairwiseDisjoint B := by
    intro w hw v hv ne
    apply Finset.disjoint_left.mpr
    intro r hrw hrv
    obtain ⟨rp,rw⟩ := Finset.mem_erase.mp hrw
    have rv := (Finset.mem_erase.mp hrv).2
    obtain ⟨_,_,only⟩ := unique p r rp.symm
    exact ne ((only w ⟨(Finset.mem_filter.mp hw).2,(Finset.mem_filter.mp rw).2⟩).trans
      (only v ⟨(Finset.mem_filter.mp hv).2,(Finset.mem_filter.mp rv).2⟩).symm)
  have sizes (w : Fin N) (hw : w∈T) : (B w).card=q := by
    have inside : p∈lineSet I w := by simpa [lineSet,pencil,T] using hw
    simp [B,Finset.card_erase_of_mem inside,lengths]
  have count := congrArg Finset.card cover
  rw [Finset.card_biUnion disjoint,Finset.sum_congr rfl (fun w hw => sizes w hw),
    Finset.card_erase_of_mem (Finset.mem_univ p)] at count
  simp only [Finset.sum_const,smul_eq_mul,Finset.card_univ,Fintype.card_fin] at count
  have exactCount : T.card*q=(q+1)*q := by
    rw [count,size,Nat.add_sub_cancel]
    ring
  exact Nat.eq_of_mul_eq_mul_right hq exactCount

theorem point_outputs {N q t : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 0<q) (size : N=q^2+q+1) (lengths : ∀ w, (lineSet I w).card=q+1)
    (unique : ∀ p r, p≠r → ∃! w, I p w ∧ I r w) (tq : t≤q)
    (W : List (Signal (Fin N))) (k : ℕ) (net : Net W k) (out : Fin N → Signal (Fin N))
    (outputs : ∀ p, out p∈W) (yes : ∀ p w, I p w → out p {w}=true)
    (no : ∀ p, Rejects (pencil I p) t (out p)) : N*t≤k := by
  have many (p : Fin N) : t<(single (out p)).card := by
    have sub : pencil I p ⊆ single (out p) := fun w hw => Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,yes p w (Finset.mem_filter.mp hw).2⟩
    have b := Finset.card_le_card sub
    rw [pencil_size I hq size lengths unique p] at b
    omega
  simpa using uniform t (pencil I) (pencil_overlap I unique) W k net out outputs no many

theorem projected_sparse {E K : Type} [Field E] [Fintype E] [DecidableEq E]
    [Field K] [Fintype K] [DecidableEq K] (coords : E ≃ K × K) (D : Finset (Option K))
    (t : ℕ) (room : Fintype.card K-1≤t)
    (W : List (Signal (E × E))) (k : ℕ) (net : Net W k) (out : Query ↥D E K → Signal (E × E))
    (outputs : ∀ Q, out Q∈W)
    (yes : ∀ Q l, l∈row (projected coords D) Q → out Q {l}=true)
    (no : ∀ Q, Rejects (row (projected coords D) Q) t (out Q)) :
    ProjectionFrontCost.targets (Fintype.card K) D.card*(Fintype.card K-1)≤k := by
  let s := Fintype.card K
  let h := projected coords D
  have pos : 0<s := Fintype.card_pos
  have order := square_order coords
  have balanced := square_balanced coords D
  obtain ⟨c,spent,each⟩ := charge (s*s) t (Nat.mul_pos pos pos) (row h)
    (row_overlap h s balanced order (square_separate coords D)) W k net out outputs no
  have lower (Q : Query ↥D E K) : s-1≤c Q := by
    by_contra! few
    have short : c Q<t := by change s-1≤t at room; omega
    have upper := each Q short
    have sub : row h Q ⊆ single (out Q) := fun l hl => Finset.mem_filter.mpr ⟨Finset.mem_univ _,yes Q l hl⟩
    have le := (Finset.card_le_card sub).trans upper
    obtain ⟨d,x,j⟩ := Q
    rw [row_card,balanced,order] at le
    have small := Nat.le_of_mul_le_mul_left (show (s*s)*s≤(s*s)*(c (d,x,j)+1) from le) (by positivity)
    omega
  have sum := (Finset.sum_le_sum (s := Finset.univ) (fun Q _ => lower Q)).trans spent
  simpa [ProjectionFrontCost.targets,Query,s,order,Nat.mul_assoc,smul_eq_mul] using sum

#print axioms point_outputs
#print axioms projected_sparse

end SparsePlanes
