import SparsePencilRoots

namespace SparsePencilDIV

open Polynomial SparsePencilChart SparsePencilRoots

abbrev realMap := Int.castRingHom ℝ

noncomputable def sumP {K : ℕ} (s : Fin K → ℤ) (g : Fin K → Polynomial ℤ) (d : ℕ) :=
  ∑ i,C (s i)*g i^d

noncomputable def factorialPoly (N : ℕ) : Polynomial ℤ :=
  ∏ j ∈ Finset.range N,(X+C ((j:ℤ)+1))

theorem vanishes {N : ℕ} {P : Polynomial ℤ} (fac : factorialPoly N∣P) (j : ℕ) (hj : j<N) :
    P.eval (-((j:ℤ)+1))=0 := by
  obtain ⟨Q,rfl⟩ := fac
  rw [eval_mul]
  suffices (factorialPoly N).eval (-((j:ℤ)+1))=0 by rw [this,zero_mul]
  unfold factorialPoly
  rw [eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_range.mpr hj)
  simp

noncomputable def samples (N : ℕ) : Finset ℝ := (Finset.range N).image (fun j : ℕ => -((j:ℝ)+1))

theorem size_samples (N : ℕ) : (samples N).card=N := by
  rw [samples,Finset.card_image_of_injective _ (by intro a b h; exact_mod_cast (show (a:ℝ)=b by linarith))]
  simp

theorem neg_samples {N : ℕ} (x : ℝ) (hx : x∈samples N) : x<0 := by
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hx
  have : (0:ℝ)≤j := by positivity
  linarith

theorem real_roots {N : ℕ} {P : Polynomial ℤ} (fac : factorialPoly N∣P)
    (x : ℝ) (hx : x∈samples N) : (P.map realMap).eval x=0 := by
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hx
  have z := vanishes fac j (Finset.mem_range.mp hj)
  have e := Polynomial.eval_map_apply (p:=P) realMap (-((j:ℤ)+1))
  rw [z,map_zero] at e
  simpa only [realMap,map_neg,map_add,map_one,map_natCast] using e

theorem sparse_div {N K : ℕ} (s : Fin K → ℤ) (g : Fin K → Polynomial ℤ) (d : ℕ) (hd : 0<d)
    (A B : Polynomial ℝ) (a b : Fin K → ℝ) (span : ∀ i,(g i).map realMap=C (a i)*A+C (b i)*B)
    (hb : B≠0) (indep : ∀ r : ℝ,A-C r*B≠0) (live : sumP s g d≠0)
    (fac : factorialPoly N∣sumP s g d) :
    N ≤ d*((A.support∪B.support).card-1) := by
  have eq : (sumP s g d).map realMap=mix (fun i => (s i:ℝ)) a b d A B := by
    simp [sumP,mix,Polynomial.map_sum,span,realMap]
  have nz : (sumP s g d).map realMap≠0 := (Polynomial.map_ne_zero_iff (Int.cast_injective (α:=ℝ))).mpr live
  have bound := pencil (fun i => (s i:ℝ)) a b d hd A B hb indep (eq ▸ nz) (samples N) neg_samples
    (fun x hx => eq ▸ real_roots fac x hx)
  rwa [size_samples] at bound

theorem linear_bound {N K T : ℕ} (s : Fin K → ℤ) (g : Fin K → Polynomial ℤ) (d : ℕ) (hd : 0<d)
    (A B : Polynomial ℝ) (a b : Fin K → ℝ) (span : ∀ i,(g i).map realMap=C (a i)*A+C (b i)*B)
    (ha : A.support.card≤T) (hs : B.support.card≤T) (hb : B≠0) (indep : ∀ r : ℝ,A-C r*B≠0)
    (live : sumP s g d≠0) (fac : factorialPoly N∣sumP s g d) : N ≤ d*(2*T-1) := by
  have card := Finset.card_union_le A.support B.support
  exact (sparse_div s g d hd A B a b span hb indep live fac).trans (Nat.mul_le_mul_left d (by omega))

#print axioms linear_bound

end SparsePencilDIV
