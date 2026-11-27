import IntegerPigeonAxioms

namespace IntegerPigeonProof

open ProofDagBudget PEqualNP.ProofComplexity PEqualNP.Search PEqualNP.Search.Helpers IntegerPigeonAxioms
open ParityProofBudget (VBit)
variable {V : Type} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem unordered (L : QLine V) (x : V → Bool) : Holds L.toFinset x ↔ QLine.Holds x L := by
  simp [Holds,QLine.Holds]

omit [DecidableEq V] in
theorem resolution (x : V → Bool) (e e' : QEq V) (C D : QLine V) (a b : ℤ)
    (left : QLine.Holds x (e::C)) (right : QLine.Holds x (e'::D)) :
    QLine.Holds x (((a • e.1+b • e'.1,a*e.2+b*e'.2) : QEq V)::(C++D)) := by
  obtain ⟨f,hf,on⟩ := left
  obtain ⟨g,hg,other⟩ := right
  rcases List.mem_cons.mp hf with rfl|old
  · rcases List.mem_cons.mp hg with rfl|old
    · exact ⟨_,List.mem_cons_self,combo_holds x _ _ _ _ on other⟩
    · exact ⟨g,List.mem_cons_of_mem _ (List.mem_append_right _ old),other⟩
  · exact ⟨f,List.mem_cons_of_mem _ (List.mem_append_left _ old),on⟩

theorem run (F : Finset (Clause V)) (π : List (QLine V)) (run : IsResLinQSynDerivation (↑F) π) :
    Derives Holds (F.image encode) (π.map List.toFinset) := by
  classical
  induction run with
  | nil => exact .nil
  | @ax π L C _ source same ih =>
    refine .step ih _ (Or.inl (Finset.mem_image.mpr ⟨C,source,?_⟩))
    ext e
    simp only [encode,Finset.mem_image,List.mem_toFinset]
    exact (exists_congr fun f => and_congr_right fun _ => eq_comm).trans (same e).symm
  | bool v _ ih =>
    refine .step ih _ (Or.inr ⟨∅,by simp,by simp,?_⟩)
    intro x _ T ht
    rw [Finset.mem_singleton.mp ht]
    apply (unordered _ x).mpr
    exact ⟨litQEq (v,x v),by cases x v <;> simp,litQEq_holds x (v,x v) rfl⟩
  | @res π e f C D a b _ hc hd ih =>
    refine .step ih _ (Or.inr ⟨{(e::C).toFinset,(f::D).toFinset},Finset.card_le_two,?_,?_⟩)
    · intro t ht
      rcases Finset.mem_insert.mp ht with rfl|eq
      · exact List.mem_map_of_mem hc
      · exact Finset.mem_singleton.mp eq ▸ List.mem_map_of_mem hd
    · intro x hx T ht
      rw [Finset.mem_singleton.mp ht]
      apply (unordered _ _).mpr
      exact resolution x e f C D a b ((unordered _ _).mp (hx _ (by simp)))
        ((unordered _ _).mp (hx _ (by simp)))
  | @weaken π C D _ hc enlarge ih =>
    refine .step ih _ (Or.inr ⟨{C.toFinset},by simp,?_,?_⟩)
    · intro t ht
      exact Finset.mem_singleton.mp ht ▸ List.mem_map_of_mem hc
    · intro x hx T ht
      rw [Finset.mem_singleton.mp ht]
      obtain ⟨e,he,on⟩ := (unordered C x).mp (hx C.toFinset (Finset.mem_singleton_self _))
      exact (unordered _ _).mpr ⟨e,enlarge _ he,on⟩
  | @simp π C _ hc ih =>
    refine .step ih _ (Or.inr ⟨{C.toFinset},by simp,?_,?_⟩)
    · intro t ht
      exact Finset.mem_singleton.mp ht ▸ List.mem_map_of_mem hc
    · intro x hx T ht
      rw [Finset.mem_singleton.mp ht]
      obtain ⟨e,he,on⟩ := (unordered C x).mp (hx C.toFinset (Finset.mem_singleton_self _))
      apply (unordered _ _).mpr
      refine ⟨e,List.mem_filter.mpr ⟨he,?_⟩,on⟩
      apply decide_eq_true
      rintro ⟨zero,off⟩
      apply off
      simpa [QEq.Holds,zero] using on.symm

omit [DecidableEq V] in
theorem size_cons (L : QLine V) (π : List (QLine V)) :
    resLinQSize (L::π)=(1+(L.map QEq.size).sum)+resLinQSize π := rfl

omit [DecidableEq V] in
theorem equation_mass (L : QLine V) (all : ∀ e∈L,2≤QEq.size e) :
    2*L.length≤(L.map QEq.size).sum := by
  induction L with
  | nil => simp
  | cons e L ih =>
    have a := all e List.mem_cons_self
    have b := ih (fun f hf => all f (List.mem_cons_of_mem _ hf))
    simp; omega

theorem source_size (l : ℕ) (L : QLine (VBit l)) (src : L.toFinset∈axioms l) :
    4*l≤(L.map QEq.size).sum := by
  classical
  obtain ⟨C,hC,eq⟩ := Finset.mem_image.mp src
  have len := List.toFinset_card_le L
  rw [← eq,encode,Finset.card_image_of_injective _ literal_inj,number_literals _ _ hC] at len
  have all (e : QEq (VBit l)) (he : e∈L) : 2≤QEq.size e := by
    have inC : e∈encode C := eq ▸ List.mem_toFinset.mpr he
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp inC
    rw [literal_size]
    omega
  have mass := equation_mass L all
  omega

theorem mass (l : ℕ) (π : List (QLine (VBit l))) :
    (1+4*l)*((π.map List.toFinset).filter (fun L => decide (L∈axioms l))).length+
    paid (axioms l) (π.map List.toFinset)≤resLinQSize π := by
  classical
  induction π with
  | nil => simp [paid,resLinQSize]
  | cons L π ih =>
    rw [size_cons]
    by_cases appeared : L.toFinset∈axioms l
    · have cost := source_size l L appeared
      simp [paid,appeared,Nat.mul_add] at ih ⊢
      omega
    · simp [paid,appeared] at ih ⊢
      omega

theorem full (l : ℕ) (hl : 0<l) (π : List (QLine (VBit l)))
    (h : IsResLinQSynRefutation (BPHP (2^l+1) l) π) :
    (4*l+2)*(2^l*(2^l+1).choose 2)≤resLinQSize π+1 := by
  classical
  have eq : (↑(raw l) : Set (Clause (VBit l)))=BPHP (2^l+1) l := Set.ext (raw_mem _)
  have legal := h.1
  rw [← eq] at legal
  have graph := run _ _ legal
  have endIn : (∅ : Finset (QEq (VBit l)))∈π.map List.toFinset :=
    List.mem_map.mpr ⟨[],h.2,rfl⟩
  have bad : ∀ x, ¬Holds (∅ : Finset (QEq (VBit l))) x := by simp [Holds]
  obtain ⟨allA,steps⟩ := essential Holds (axioms l) _ graph _ endIn bad (critical l)
  have card := (Finset.card_le_card allA).trans (List.toFinset_card_le _)
  rw [card_axioms l hl] at card steps
  have scaled := Nat.mul_le_mul_left (1+4*l) card
  have spent := mass l π
  have alg (K : ℕ) : (4*l+2)*K=(1+4*l)*K+K := by ring
  rw [alg]
  omega

#print axioms full

end IntegerPigeonProof
