import ReversePath
import RepairAnds

/-! Compile all reverse flags in a single shared point-input network.
One forward binary OR and at most two reverse accumulator ORs per original
gate suffice. All statements use the actual project gate format. -/

namespace ReverseCost

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.Helpers PartialSums ReversePath
variable {P : Type} [DecidableEq P]

def Keeps (H K : List (Signal P)) := ∀ f ∈ H, f ∈ K

omit [DecidableEq P] in
theorem keeps_refl (H : List (Signal P)) : Keeps H H := fun _ h => h
omit [DecidableEq P] in
theorem keeps_snoc (H : List (Signal P)) (f : Signal P) : Keeps H (H++[f]) :=
  fun _ h => List.mem_append_left _ h
omit [DecidableEq P] in
theorem keeps_trans {H K J : List (Signal P)} (a : Keeps H K) (b : Keeps K J) : Keeps H J :=
  fun f hf => b _ (a f hf)

omit [DecidableEq P] in
theorem reads {H W : List (Signal P)} (forward : Keeps W H) (zero_in : zero ∈ H) (i : ℕ) : W.getD i zero ∈ H := by
  by_cases hi : i < W.length
  · exact forward _ (by simp [List.getD_eq_getElem?_getD,hi])
  · simpa [List.getD_eq_getElem?_getD,hi] using zero_in

def Produced (H : List (Signal P)) (k b : ℕ) (f : Signal P) : Prop :=
  ∃ K u, Built K u ∧ Keeps H K ∧ u≤k+b ∧ f ∈ K

theorem available {H : List (Signal P)} {k : ℕ} (net : Built H k) {f : Signal P} (hf : f ∈ H) :
    Produced H k 1 f := ⟨H,k,net,keeps_refl _,by omega,hf⟩

theorem forward_gate (g : Gate) (H W : List (Signal P)) (k : ℕ) (net : Built H k)
    (zero_in : zero ∈ H) (one_in : one ∈ H) (forward : Keeps W H) : Produced H k 1 (baseGate g W) := by
  have add (f h : Signal P) (hf : f ∈ H) (hh : h ∈ H) : Produced H k 1 (plus f h) :=
    ⟨_,k+1,Built.sum net f h hf hh,keeps_snoc _ _,le_rfl,by simp⟩
  have prod (f h : Signal P) (hf : f ∈ H) (hh : h ∈ H) : Produced H k 1 (times f h) :=
    ⟨_,k,Built.prod net f h hf hh,keeps_snoc _ _,by omega,by simp⟩
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

omit [DecidableEq P] in
theorem arc_info (g : Gate) (W H : List (Signal P)) (forward : Keeps W H)
    (zero_in : zero ∈ H) (one_in : one ∈ H) :
    (arcs g W).length≤2 ∧ ∀ t ∈ arcs g W, t.2 ∈ H := by
  obtain ⟨op,ins⟩ := g
  cases op <;> cases ins with
  | nil => simp [arcs]
  | cons i tail =>
    cases tail with
    | nil => simp [arcs,one_in]
    | cons j tail =>
      cases tail <;> simp [arcs,one_in] <;> exact ⟨reads forward zero_in j,reads forward zero_in i⟩

theorem scatter_build (A : Arcs P) (d : Signal P) (B : Adjoints P) (H : List (Signal P)) (k : ℕ)
    (net : Built H k) (hd : d ∈ H) (gains : ∀ t ∈ A, t.2 ∈ H) (old : ∀ i, B i ∈ H) :
    ∃ K, Built K (k+A.length) ∧ Keeps H K ∧ ∀ i, scatter A d B i ∈ K := by
  induction A with
  | nil => exact ⟨H,net,keeps_refl _,old⟩
  | cons t A ih =>
    obtain ⟨j,a⟩ := t
    obtain ⟨K,built,keep,has⟩ := ih (fun t ht => gains t (by simp [ht]))
    have ha : a ∈ K := keep _ (gains (j,a) (by simp))
    have first := Built.prod built d a (keep _ hd) ha
    have next := Built.sum first (scatter A d B j) (times d a) (List.mem_append_left _ (has j)) (by simp)
    refine ⟨_,by simpa [Nat.add_assoc] using next,keeps_trans keep (keeps_trans (keeps_snoc _ _) (keeps_snoc _ _)),?_⟩
    intro i
    by_cases e : i=j
    · simp [scatter,e]
    · simp [scatter,e,has i]

theorem compile (gs : List Gate) (W H : List (Signal P)) (out k : ℕ)
    (net : Built H k) (zero_in : zero ∈ H) (one_in : one ∈ H) (forward : Keeps W H) :
    ∃ K u, Built K u ∧ Keeps H K ∧ u≤k+3*gs.length ∧ ∀ i, pull gs W out i ∈ K := by
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
    ∃ K u, Built K u ∧ u≤3*C.size ∧ ∀ i, pull C.gates W C.output i ∈ K := by
  let H := zero :: one :: W
  have initial : Built H 0 := by
    apply Built.raw
    intro f hf
    simp only [H,List.mem_cons] at hf
    rcases hf with rfl | rfl | h
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact raw f h
  obtain ⟨K,u,net,_,cost,flags⟩ := compile C.gates W H C.output 0 initial (by simp [H]) (by simp [H])
    (fun f hf => by simp [H,hf])
  exact ⟨K,u,net,by simpa [Circuit.size] using cost,flags⟩

omit [DecidableEq P] in
theorem flag_sound (C : Circuit) (W : List (Signal P)) (X : Finset P) (x : List Bool) (j : ℕ)
    (ops : IsMonotoneCircuit C) (fan : ∀ g ∈ C.gates, g.inputs.length≤2)
    (len : W.length=x.length) (hj : j < x.length) (yes : x.getD j false=true)
    (base : ∀ i, W.getD i zero X=true → x.getD i false=true)
    (flag : pull C.gates W C.output j X=true) : C.eval x=true := by
  let D := List.ofFn (fun k : Fin x.length => decide (k.val=j))
  have ld : D.length=x.length := by simp [D]
  have mark : D.getD j false=true := by simp [D,List.getD_eq_getElem?_getD,hj]
  have sound (i : ℕ) : D.getD i false=true → x.getD i false=true := by
    by_cases hi : i < x.length
    · intro hit
      have e : i=j := by simpa [D,List.getD_eq_getElem?_getD,hi] using hit
      exact e ▸ yes
    · simp [D,List.getD_eq_getElem?_getD,hi]
  have forward := (dual C.gates W D (len.trans ld.symm) X C.output).mp ⟨j,ld ▸ hj,mark,flag⟩
  exact marked_sound C.gates W D x X ops fan len ld base sound C.output forward

variable [Fintype P] {L : Type} [Fintype L]

/-- For each line provide its single-line negative input and its line slot.
The same original DAG yields the whole point-input operator simultaneously. -/
theorem line_once (I : L → Finset P) (linear : ∀ l m, l≠m → (I l ∩ I m).card≤1)
    (C : Circuit) (W : List (Signal P)) (raw : ∀ f ∈ W, IsRaw f)
    (slot : L → ℕ) (neg : L → List Bool) (ops : IsMonotoneCircuit C) (fan : ∀ g ∈ C.gates, g.inputs.length≤2)
    (len : ∀ l, W.length=(neg l).length) (has : ∀ l, slot l < (neg l).length)
    (lineOn : ∀ l, (neg l).getD (slot l) false=true)
    (base : ∀ l i, W.getD i zero (outside I l)=true → (neg l).getD i false=true)
    (reject : ∀ l, C.eval (neg l)=false) :
    (∑ l, (single (pull C.gates W C.output (slot l))).card)≤3*C.size+Fintype.card L := by
  obtain ⟨K,u,net,cost,flags⟩ := outputs C W raw
  have off (l : L) : pull C.gates W C.output (slot l) (outside I l)=false := by
    cases h : pull C.gates W C.output (slot l) (outside I l) with
    | false => rfl
    | true =>
      have yes := flag_sound C W _ (neg l) (slot l) ops fan (len l) (has l) (lineOn l) (base l) h
      rw [reject l] at yes
      contradiction
  exact (total I linear _ _ net _ (fun l => flags (slot l)) off).trans (Nat.add_le_add_right cost _)

#print axioms outputs
#print axioms line_once

end ReverseCost
