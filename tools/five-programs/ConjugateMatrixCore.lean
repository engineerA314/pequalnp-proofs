import PermanentJetOnes

namespace ConjugateMatrixCore

open Finset PermanentJetOnes ComplexConjugate

variable {p q : ℕ}

def bar (x : Mat p q) : Mat p q := fun a => conj (x a)

@[simp] theorem bar_zero : bar (0 : Mat p q)=0 := by funext a; simp [bar]
@[simp] theorem bar_add (x y : Mat p q) : bar (x+y)=bar x+bar y := by funext a; simp [bar]
@[simp] theorem bar_smul (c : ℂ) (x : Mat p q) : bar (c • x)=conj c • bar x := by
  funext a; simp [bar,Pi.smul_apply,smul_eq_mul]

def core (L : Submodule ℂ (Mat p q)) : Submodule ℂ (Mat p q) where
  carrier := {t | t∈L ∧ bar t∈L}
  zero_mem' := ⟨L.zero_mem,by rw [bar_zero]; exact L.zero_mem⟩
  add_mem' := by
    rintro x y ⟨hx,hbx⟩ ⟨hy,hby⟩
    exact ⟨L.add_mem hx hy,by rw [bar_add]; exact L.add_mem hbx hby⟩
  smul_mem' := by
    rintro c x ⟨hx,hbx⟩
    exact ⟨L.smul_mem c hx,by rw [bar_smul]; exact L.smul_mem (conj c) hbx⟩

theorem core_le (L : Submodule ℂ (Mat p q)) : core L ≤ L := fun _ h => h.1

theorem core_eq (L : Submodule ℂ (Mat p q)) (h : ∀ x∈L,bar x∈L) : core L=L :=
  le_antisymm (core_le L) (fun x hx => ⟨hx,h x hx⟩)

def centered (x : Mat p q) := (∀ i,∑ j,x (i,j)=0) ∧ (∀ j,∑ i,x (i,j)=0)

theorem centered_add {x y : Mat p q} (hx : centered x) (hy : centered y) : centered (x+y) := by
  constructor <;> intro i <;> simp [Finset.sum_add_distrib,hx.1,hx.2,hy.1,hy.2]

theorem centered_bar {x : Mat p q} (hx : centered x) : centered (bar x) := by
  constructor <;> intro i <;> simp [bar,← map_sum,hx.1,hx.2]

theorem squares_zero {x : Mat p q} (h : disjointSum x=0) (center : centered x) :
    ∑ i,∑ j,x (i,j)^2=0 := by
  unfold disjointSum at h
  rw [PEqualNP.Gct.Helpers.RealLevel.ident] at h
  simpa [center.1,center.2] using h

def dot (x y : Mat p q) := ∑ i,∑ j,x (i,j)*y (i,j)

theorem orthogonal (L : Submodule ℂ (Mat p q)) (hL : ∀ t∈L,disjointSum t=0)
    {x y : Mat p q} (hx : x∈L) (hy : y∈L) (cx : centered x) (cy : centered y) : dot x y=0 := by
  have sx := squares_zero (hL _ hx) cx
  have sy := squares_zero (hL _ hy) cy
  have s := squares_zero (hL _ (L.add_mem hx hy)) (centered_add cx cy)
  simp only [Pi.add_apply,add_sq,Finset.sum_add_distrib,mul_assoc,← Finset.mul_sum,sx,sy,zero_add,add_zero] at s
  unfold dot
  exact (mul_eq_zero.mp s).resolve_left (by norm_num)

theorem centered_in_core {L : Submodule ℂ (Mat p q)} (hL : ∀ t∈L,disjointSum t=0)
    {t : Mat p q} (ht : t∈core L) (cx : centered t) : t=0 := by
  have h := orthogonal L hL ht.1 ht.2 cx (centered_bar cx)
  unfold dot bar at h
  simp_rw [Complex.mul_conj,← Complex.ofReal_sum] at h
  have h0 : ∑ i,∑ j,Complex.normSq (t (i,j))=0 := by exact_mod_cast h
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _)] at h0
  funext ⟨i,j⟩
  have row := h0 i (Finset.mem_univ _)
  have entry := (Finset.sum_eq_zero_iff_of_nonneg (fun (l : Fin q) _ => Complex.normSq_nonneg (t (i,l)))).mp row j (Finset.mem_univ _)
  exact Complex.normSq_eq_zero.mp entry

#print axioms orthogonal
#print axioms centered_in_core

end ConjugateMatrixCore
