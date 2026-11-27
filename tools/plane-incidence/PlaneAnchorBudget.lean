import AnchorPruning

/-! A fixed-anchor lower bound and its average over all r-line sets. Each
original binary AND contributes its singleton footprint, counted once. -/

namespace PlaneAnchorBudget

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open AnchorPruning SparseNegatives RepairAnds AnchoredBoundary AndTranscript

variable {P L : ℕ}

def raw (X : Finset (Fin P)) (Y : Finset (Fin L)) := List.ofFn (PlaneGateBound.row X Y)

def probes (P L : ℕ) : Probes L := fun u => raw (∅ : Finset (Fin P)) {u}

theorem raw_below (R : Finset (Fin L)) (X : Finset (Fin P)) (Y : Finset (Fin L)) (ry : R ⊆ Y) :
    Below (probes P L) R (raw X Y) := by
  intro u hu
  refine ⟨by simp [probes,raw],?_⟩
  intro j
  by_cases hj : j<P+L
  · have atIndex (i : Fin (P+L)) : PlaneGateBound.row (∅ : Finset (Fin P)) {u} i=true →
        PlaneGateBound.row X Y i=true := by
      refine Fin.addCases (fun p => ?_) (fun w => ?_) i
      · simp [PlaneGateBound.row]
      · simp only [PlaneGateBound.row,Fin.append_right,decide_eq_true_eq,Finset.mem_singleton]
        rintro rfl; exact ry hu
    simpa [probes,raw,List.getD_eq_getElem?_getD,hj] using atIndex ⟨j,hj⟩
  · simp [probes,raw,List.getD_eq_getElem?_getD,hj]

def level (L t r : ℕ) := Nat.clog 2 (∑ j ∈ Finset.range (t-r+1), (L-r).choose j)

theorem anchored (I : Lines P L) (t : ℕ) (long : ∀ w, t < (I w).card)
    (linear : ∀ w v, w≠v → (I w ∩ I v).card≤1) (C : Circuit) (mc : Monotone2 C)
    (positive : ∀ p w, p∈I w → circuitFun (P+L) C (PlaneGateBound.row {p} {w})=true)
    (negative : ∀ Y, Y.card≤t → C.eval (raw (outside I Y) Y)=false)
    (R : Finset (Fin L)) (room : R.card≤t) :
    level L t R.card ≤ surviving (profiles true C.gates (probes P L)) R := by
  classical
  let F := extensions R t
  let D : Circuit := ⟨reduce C.gates (probes P L) R,C.output⟩
  have legal : ∀ g ∈ D.gates, Legal g := reduce_legal _ _ _ mc
  have mono : IsMonotoneCircuit C := fun g hg => (mc g hg).1
  have eq (X : Finset (Fin P)) (Y : Finset (Fin L)) (above : R ⊆ Y) :
      D.eval (raw X Y)=C.eval (raw X Y) :=
    congrArg (fun w : List Bool => w.getD C.output false)
      (wires_eq _ (probes P L) R _ (raw_below R X Y above) mono)
  have memF (Y : Finset (Fin L)) : Y ∈ F ↔ R ⊆ Y ∧ Y.card≤t := by simp [F,extensions]
  have bound : F.card≤2^count D.gates := by
    apply incompatible_count F (fun Y => raw (outside I Y) Y) D
      (fun g hg => (legal g hg).1) (fun g hg => (legal g hg).2)
    · intro Y hy
      rw [eq _ _ ((memF Y).mp hy).1]; exact negative Y ((memF Y).mp hy).2
    · intro Y hy Z hz ne
      obtain ⟨ry,sy⟩ := (memF Y).mp hy
      obtain ⟨rz,sz⟩ := (memF Z).mp hz
      obtain ⟨p,w,edge,point,line⟩ := crossing_pair I t long linear Y Z sy sz ne
      refine ⟨raw {p} (insert w R),?_,?_⟩
      · rw [eq _ _ (Finset.subset_insert _ _)]
        exact PlaneGateBound.accepts_pair C mono p w (positive p w edge) _
          (by simp [PlaneGateBound.row]) (by simp [PlaneGateBound.row])
      · have points := bits_covered {p} (outside I Y) (outside I Z) (Finset.singleton_subset_iff.mpr (Finset.mem_union.mpr point))
        have lines := bits_covered (insert w R) Y Z (Finset.insert_subset (Finset.mem_union.mpr line)
          (Finset.Subset.trans ry Finset.subset_union_left))
        simpa [raw,PlaneGateBound.row,bits] using covered_append points lines
  have card : F.card=_ := count_extensions R t room
  rw [card] at bound
  rw [← (budgets C.gates (probes P L) R).1]
  exact Nat.clog_le_of_le_pow bound

def weight (r : ℕ) (A : List (Finset (Fin L))) :=
  (A.map fun D => (L-D.card).choose r).sum

theorem avoiding (D : Finset (Fin L)) (r : ℕ) :
    (((Finset.univ : Finset (Fin L)).powersetCard r).filter fun R => Disjoint R D).card=(L-D.card).choose r := by
  classical
  let V := (Finset.univ : Finset (Fin L))
  have e : (V.powersetCard r).filter (fun R => Disjoint R D)=(V \ D).powersetCard r := by
    ext R
    simp only [Finset.mem_filter,Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨sub,cr⟩,apart⟩
      exact ⟨fun u hu => Finset.mem_sdiff.mpr ⟨sub hu,Finset.disjoint_left.mp apart hu⟩,cr⟩
    · rintro ⟨sub,cr⟩
      exact ⟨⟨fun u hu => (Finset.mem_sdiff.mp (sub hu)).1,cr⟩,
        Finset.disjoint_left.mpr fun u hu => (Finset.mem_sdiff.mp (sub hu)).2⟩
  rw [e,Finset.card_powersetCard,Finset.card_sdiff_of_subset (Finset.subset_univ D)]
  simp

theorem double_count (r : ℕ) (A : List (Finset (Fin L))) :
    (∑ R ∈ (Finset.univ : Finset (Fin L)).powersetCard r, surviving A R)=weight r A := by
  classical
  induction A with
  | nil => simp [surviving,weight]
  | cons D A ih =>
    have step (R : Finset (Fin L)) : surviving (D::A) R=(if Disjoint R D then 1 else 0)+surviving A R := by
      by_cases h : Disjoint R D <;> simp [surviving,h,Nat.add_comm]
    rw [Finset.sum_congr rfl (fun R _ => step R),Finset.sum_add_distrib,ih]
    have h := avoiding D r
    rw [Finset.card_eq_sum_ones,Finset.sum_filter] at h
    simpa [weight] using congrArg (· + weight r A) h

theorem averaged (I : Lines P L) (t r : ℕ) (rt : r ≤ t) (long : ∀ w, t < (I w).card)
    (linear : ∀ w v, w≠v → (I w ∩ I v).card≤1) (C : Circuit) (mc : Monotone2 C)
    (positive : ∀ p w, p∈I w → circuitFun (P+L) C (PlaneGateBound.row {p} {w})=true)
    (negative : ∀ Y, Y.card≤t → C.eval (raw (outside I Y) Y)=false) :
    L.choose r * level L t r ≤ weight r (profiles true C.gates (probes P L)) := by
  let family := (Finset.univ : Finset (Fin L)).powersetCard r
  have each (R : Finset (Fin L)) (h : R∈family) : level L t r≤surviving (profiles true C.gates (probes P L)) R := by
    have card := (Finset.mem_powersetCard.mp h).2
    simpa [card] using anchored I t long linear C mc positive negative R (by omega)
  have total := Finset.sum_le_sum (s := family) each
  simpa [family,double_count,Finset.sum_const,smul_eq_mul] using total

def lineSet {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] : Lines N N :=
  fun w => Finset.univ.filter fun p => I p w

theorem set_linear {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (unique : ∀ p r, p≠r → ∃! w, I p w ∧ I r w) (v w : Fin N) (ne : v≠w) :
    (lineSet I v ∩ lineSet I w).card≤1 := by
  apply Finset.card_le_one.mpr
  intro p hp r hr
  by_contra diff
  obtain ⟨k,_,only⟩ := unique p r diff
  simp only [lineSet,Finset.mem_inter,Finset.mem_filter,Finset.mem_univ,true_and] at hp hr
  exact ne ((only v ⟨hp.1,hr.1⟩).trans (only w ⟨hp.2,hr.2⟩).symm)

theorem negative_row {N t : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (neg : ∀ z : Fin (N+N) → Bool, (Finset.univ.filter fun w => z (Fin.natAdd N w)=true).card≤t →
      (¬∃ p w, I p w ∧ z (Fin.castAdd N p)=true ∧ z (Fin.natAdd N w)=true) → circuitFun (N+N) C z=false)
    (Y : Finset (Fin N)) (few : Y.card≤t) : C.eval (raw (outside (lineSet I) Y) Y)=false := by
  apply neg
  · simpa only [PlaneGateBound.row,Fin.append_right,decide_eq_true_eq,Finset.filter_mem_eq_inter,Finset.univ_inter] using few
  · rintro ⟨p,w,pw,px,wy⟩
    have hull : p ∈ outside (lineSet I) Y := by simpa [PlaneGateBound.row] using px
    have chosen : w ∈ Y := by simpa only [PlaneGateBound.row,Fin.append_right,decide_eq_true_eq] using wy
    exact (Finset.mem_sdiff.mp hull).2 (Finset.mem_biUnion.mpr ⟨w,chosen,by simpa [lineSet] using pw⟩)

theorem plane {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit) (r : ℕ) (rq : r≤q)
    (lengths : ∀ w, (lineSet I w).card=q+1) (unique : ∀ p r, p≠r → ∃! w, I p w ∧ I r w) (mc : Monotone2 C)
    (positive : ∀ p w, I p w → circuitFun (N+N) C (fun k => decide (k=Fin.castAdd N p ∨ k=Fin.natAdd N w))=true)
    (negative : ∀ z : Fin (N+N) → Bool, (Finset.univ.filter fun w => z (Fin.natAdd N w)=true).card≤q →
      (¬∃ p w, I p w ∧ z (Fin.castAdd N p)=true ∧ z (Fin.natAdd N w)=true) → circuitFun (N+N) C z=false) :
    N.choose r * level N q r ≤ weight r (profiles true C.gates (probes N N)) := by
  apply averaged (lineSet I) q r rq (fun w => by rw [lengths]; omega) (set_linear I unique) C mc
  · intro p w pw
    rw [PlaneGateBound.singleton_row]
    exact positive p w (by simpa [lineSet] using pw)
  · exact negative_row I C negative

#print axioms plane

#print axioms anchored
#print axioms averaged

end PlaneAnchorBudget
