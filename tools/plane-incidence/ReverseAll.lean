import ReverseCost
import SparseFrontier

/-! The same reverse pass now counts both binary ANDs and ORs. Each forward
gate costs at most one, and each of its two reverse arcs costs at most two. -/

namespace ReverseAll

open PEqualNP.CircuitLowerBounds PartialSums SparseFrontier ReversePath
open ReverseCost (Keeps keeps_refl keeps_snoc keeps_trans reads arc_info)
variable {P : Type} [DecidableEq P]

theorem orStep {W : List (Signal P)} {k : ℕ} (old : Net W k) (f g : Signal P)
    (hf : f∈W) (hg : g∈W) : Net (W++[plus f g]) (k+1) := Net.gate old true f g hf hg

theorem andStep {W : List (Signal P)} {k : ℕ} (old : Net W k) (f g : Signal P)
    (hf : f∈W) (hg : g∈W) : Net (W++[times f g]) (k+1) := Net.gate old false f g hf hg

def Provided (H : List (Signal P)) (k b : ℕ) (f : Signal P) : Prop :=
  ∃ K u, Net K u ∧ Keeps H K ∧ u≤k+b ∧ f ∈ K

theorem available {H : List (Signal P)} {k : ℕ} (net : Net H k) {f : Signal P} (hf : f ∈ H) :
    Provided H k 1 f := ⟨H,k,net,keeps_refl _,by omega,hf⟩

theorem forward_gate (g : Gate) (H W : List (Signal P)) (k : ℕ) (net : Net H k)
    (zero_in : zero ∈ H) (one_in : one ∈ H) (forward : Keeps W H) : Provided H k 1 (baseGate g W) := by
  have add (f h : Signal P) (hf : f ∈ H) (hh : h ∈ H) : Provided H k 1 (plus f h) :=
    ⟨_,k+1,orStep net f h hf hh,keeps_snoc _ _,le_rfl,by simp⟩
  have prod (f h : Signal P) (hf : f ∈ H) (hh : h ∈ H) : Provided H k 1 (times f h) :=
    ⟨_,k+1,andStep net f h hf hh,keeps_snoc _ _,by omega,by simp⟩
  obtain ⟨op,ins⟩ := g
  cases op <;> cases ins with
  | nil => first | exact available net one_in | exact available net zero_in
  | cons i tail =>
    cases tail with
    | nil => first | exact available net (reads forward zero_in i) | exact available net zero_in
    | cons j tail =>
      cases tail with
      | nil => first | exact add _ _ (reads forward zero_in i) (reads forward zero_in j) | exact prod _ _ (reads forward zero_in i) (reads forward zero_in j) | exact available net zero_in
      | cons _ _ => exact available net zero_in

/-- A shared realization of all forward wire functions with at most one
actual binary gate per original gate, even when additional outputs are tapped. -/
theorem forward (gs : List Gate) (W H : List (Signal P)) (k : ℕ) (net : Net H k)
    (zero_in : zero ∈ H) (one_in : one ∈ H) (inside : Keeps W H) :
    ∃ K u, Net K u ∧ u≤k+gs.length ∧ Keeps (CleanWitness.scan zero one plus times gs W) K := by
  induction gs generalizing W H k with
  | nil => exact ⟨H,k,net,by simp,inside⟩
  | cons g gs ih =>
    obtain ⟨J,v,built,keep,spent,wire⟩ := forward_gate g H W k net zero_in one_in inside
    have fw : Keeps (W++[baseGate g W]) J := by
      intro f hf
      rcases List.mem_append.mp hf with old | new
      · exact keep _ (inside _ old)
      · exact (List.mem_singleton.mp new) ▸ wire
    obtain ⟨K,u,done,cost,last⟩ := ih _ J v built (keep _ zero_in) (keep _ one_in) fw
    exact ⟨K,u,done,by simp only [List.length_cons]; omega,last⟩

theorem scatter_build (A : Arcs P) (d : Signal P) (B : Adjoints P) (H : List (Signal P)) (k : ℕ)
    (net : Net H k) (hd : d ∈ H) (gains : ∀ t ∈ A, t.2 ∈ H) (old : ∀ i, B i ∈ H) :
    ∃ K, Net K (k+2*A.length) ∧ Keeps H K ∧ ∀ i, scatter A d B i ∈ K := by
  induction A with
  | nil => exact ⟨H,net,keeps_refl _,old⟩
  | cons t A ih =>
    obtain ⟨j,a⟩ := t
    obtain ⟨K,built,keep,has⟩ := ih (fun t ht => gains t (by simp [ht]))
    have ha : a ∈ K := keep _ (gains (j,a) (by simp))
    have first := andStep built d a (keep _ hd) ha
    have next := orStep first (scatter A d B j) (times d a) (List.mem_append_left _ (has j)) (by simp)
    refine ⟨_,by simpa [Nat.mul_add,Nat.add_assoc] using next,keeps_trans keep (keeps_trans (keeps_snoc _ _) (keeps_snoc _ _)),?_⟩
    intro i
    by_cases e : i=j
    · simp [scatter,e]
    · simp [scatter,e,has i]

theorem compile (gs : List Gate) (W H : List (Signal P)) (out k : ℕ)
    (net : Net H k) (zero_in : zero ∈ H) (one_in : one ∈ H) (forward : Keeps W H) :
    ∃ K u, Net K u ∧ Keeps H K ∧ u≤k+5*gs.length ∧ ∀ i, pull gs W out i ∈ K := by
  induction gs generalizing W H k with
  | nil =>
    exact ⟨H,k,net,keeps_refl _,by simp,fun i => by by_cases e : i=out <;> simp [pull,seed,e,one_in,zero_in]⟩
  | cons g gs ih =>
    obtain ⟨K,u,built,keep,spent,new⟩ := forward_gate g H W k net zero_in one_in forward
    have fw : Keeps (W++[baseGate g W]) K := by
      intro f hf
      rcases List.mem_append.mp hf with old | last
      · exact keep _ (forward _ old)
      · exact (List.mem_singleton.mp last) ▸ new
    obtain ⟨J,v,tail,keepK,tailCost,flags⟩ := ih _ K u built (keep _ zero_in) (keep _ one_in) fw
    have info := arc_info g W H forward zero_in one_in
    let B := pull gs (W++[baseGate g W]) out
    obtain ⟨T,full,keepJ,final⟩ := scatter_build (arcs g W) (B W.length) B J v tail
      (flags _) (fun t ht => keepK _ (keep _ (info.2 t ht))) flags
    refine ⟨T,_,full,keeps_trans (keeps_trans keep keepK) keepJ,?_,final⟩
    have two := info.1
    simp only [List.length_cons]
    omega

theorem outputs (C : Circuit) (W : List (Signal P)) (raw : ∀ f ∈ W, IsRaw f) :
    ∃ K u, Net K u ∧ u≤5*C.size ∧ ∀ i, pull C.gates W C.output i ∈ K := by
  let H := zero :: one :: W
  have initial : Net H 0 := by
    apply Net.raw
    intro f hf
    simp only [H,List.mem_cons] at hf
    rcases hf with rfl | rfl | h
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact raw f h
  obtain ⟨K,u,net,_,cost,flags⟩ := compile C.gates W H C.output 0 initial (by simp [H]) (by simp [H])
    (fun f hf => by simp [H,hf])
  exact ⟨K,u,net,by simpa [Circuit.size] using cost,flags⟩

#print axioms outputs
#print axioms forward

end ReverseAll
