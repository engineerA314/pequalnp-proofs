import OverlapSums

/-! Trace sets of output wires through their row-specific gates. The
remaining boundary has at most one additional wire per traced gate. -/

namespace SparseFrontier

open PartialSums
variable {P L : Type} [Fintype P] [DecidableEq P]

def combine (disj : Bool) (f g : Signal P) := if disj then plus f g else times f g

inductive Net : List (Signal P) → ℕ → Prop where
  | raw (W : List (Signal P)) (h : ∀ f ∈ W, IsRaw f) : Net W 0
  | gate {W k} (old : Net W k) (d : Bool) (f g : Signal P) (hf : f∈W) (hg : g∈W) :
      Net (W++[combine d f g]) (k+1)

theorem asBuilt (W : List (Signal P)) (k : ℕ) (net : Net W k) : ∃ a, Built W a := by
  induction net with
  | raw W h => exact ⟨0,Built.raw W h⟩
  | gate old d f g hf hg ih =>
    obtain ⟨a,prev⟩ := ih
    cases d
    · exact ⟨a,Built.prod prev f g hf hg⟩
    · exact ⟨a+1,Built.sum prev f g hf hg⟩

/-- No set of at most one outside input suffices to activate this wire. -/
def SmallOff (R : Finset P) (f : Signal P) (radius : ℕ := 1) :=
  ∀ Y : Finset P, Disjoint Y R → Y.card≤radius → f Y=false

def Private (b : ℕ) (R : Finset P) (f : Signal P) (radius : ℕ := 1) := SmallOff R f radius ∧ b<(single f).card

noncomputable def fee (b : ℕ) (R : Finset P) (f : Signal P) (radius : ℕ := 1) : ℕ := by
  classical exact if Private b R f radius then 1 else 0

theorem off_inside (R : Finset P) (f : Signal P) (off : SmallOff R f) : single f⊆R := by
  intro p hp
  by_contra no
  have z := off {p} (by simpa using no) (by simp)
  rw [(Finset.mem_filter.mp hp).2] at z
  contradiction

theorem fee_once [Fintype L] (b : ℕ) (I : L → Finset P)
    (linear : ∀ l m, l≠m → (I l ∩ I m).card≤b) (f : Signal P) : (∑ l, fee b (I l) f)≤1 := by
  classical
  apply le_trans _ (OverlapSums.cost_once b I linear (single f))
  apply Finset.sum_le_sum
  intro l _
  by_cases h : Private b (I l) f
  · simp [fee,h,OverlapSums.cost,off_inside _ _ h.1,h.2]
  · simp [fee,h]

def Available (W : List (Signal P)) (T : Finset (Signal P)) := ∀ f ∈ T, f∈W
def Rel (T : Finset (Signal P)) (X Y : Finset P) := ∀ f ∈ T, f X=true → f Y=true
def Covers (F T : Finset (Signal P)) := ∀ X Y, Rel F X Y → Rel T X Y

def Frontier (b : ℕ) (R : Finset P) (W : List (Signal P)) (c : ℕ) (radius : ℕ := 1) :=
  ∀ T, Available W T → ∃ F, Available W F ∧ (∀ f∈F, ¬Private b R f radius) ∧
    F.card≤c+T.card ∧ Covers F T

theorem raw_terminal (b : ℕ) (pos : 1≤b) (R : Finset P) (f : Signal P) (h : IsRaw f) (radius : ℕ := 1) :
    ¬Private b R f radius := by
  rintro ⟨off,big⟩
  rcases h with rfl | rfl | ⟨p,rfl⟩
  · simp [single,zero] at big
  · have bad := off ∅ (by simp) (by simp)
    contradiction
  · have eq : single (variableAt p)={p} := by ext v; simp [single,variableAt,eq_comm]
    rw [eq,Finset.card_singleton] at big; omega

theorem combine_mono (d : Bool) (f g : Signal P) (X Y : Finset P)
    (hf : f X=true → f Y=true) (hg : g X=true → g Y=true) :
    combine d f g X=true → combine d f g Y=true := by
  cases d <;> simp [combine,plus,times,Bool.or_eq_true,Bool.and_eq_true] <;> tauto

theorem step (b radius : ℕ) (R : Finset P) (W : List (Signal P)) (c : ℕ) (old : Frontier b R W c radius)
    (d : Bool) (a e : Signal P) (aa : a∈W) (ee : e∈W) :
    Frontier b R (W++[combine d a e]) (c+fee b R (combine d a e) radius) radius := by
  classical
  let h := combine d a e
  intro T avail
  have before (f : Signal P) (hf : f ∈ T.erase h) : f∈W := by
    obtain ⟨ne,mem⟩ := Finset.mem_erase.mp hf
    rcases List.mem_append.mp (avail f mem) with ok | last
    · exact ok
    · exact False.elim (ne (List.mem_singleton.mp last))
  have extend {F : Finset (Signal P)} (af : Available W F) : Available (W++[h]) F :=
    fun f hf => List.mem_append_left _ (af f hf)
  by_cases used : h∈T
  · have erased := Finset.card_erase_add_one used
    by_cases owned : Private b R h radius
    · let U := insert a (insert e (T.erase h))
      have avU : Available W U := by
        intro f hf
        rcases Finset.mem_insert.mp hf with rfl | hf
        · exact aa
        rcases Finset.mem_insert.mp hf with rfl | hf
        · exact ee
        exact before f hf
      obtain ⟨F,af,terminal,cost,rel⟩ := old U avU
      have c1 := Finset.card_insert_le a (insert e (T.erase h))
      have c2 := Finset.card_insert_le e (T.erase h)
      refine ⟨F,extend af,terminal,?_,?_⟩
      · change F.card≤c+fee b R h radius+T.card
        simp only [fee,owned,ite_true]
        dsimp [U] at cost; omega
      · intro X Y on f hf value
        have inner := rel X Y on
        by_cases same : f=h
        · subst f
          exact combine_mono d a e X Y (inner a (by simp [U])) (inner e (by simp [U])) value
        · exact inner f (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨same,hf⟩))) value
    · obtain ⟨F,af,terminal,cost,rel⟩ := old (T.erase h) before
      refine ⟨insert h F,?_,?_,?_,?_⟩
      · intro f hf
        rcases Finset.mem_insert.mp hf with rfl | m
        · simp [h]
        · exact extend af f m
      · intro f hf
        rcases Finset.mem_insert.mp hf with rfl | m
        · exact owned
        · exact terminal _ m
      · have s := Finset.card_insert_le h F; omega
      · intro X Y on f hf val
        by_cases same : f=h
        · exact on f (Finset.mem_insert.mpr (Or.inl same)) val
        · exact rel X Y (fun g m => on g (Finset.mem_insert_of_mem m)) f
            (Finset.mem_erase.mpr ⟨same,hf⟩) val
  · have avT : Available W T := fun f m => before f (by rwa [Finset.erase_eq_of_notMem used])
    obtain ⟨F,af,terminal,cost,rel⟩ := old T avT
    exact ⟨F,extend af,terminal,by omega,rel⟩

theorem ledger [Fintype L] (b : ℕ) (pos : 1≤b) (I : L → Finset P)
    (linear : ∀ l m, l≠m → (I l ∩ I m).card≤b) (W : List (Signal P)) (k : ℕ) (net : Net W k) :
    ∃ c : L → ℕ, (∑ l, c l)≤k ∧ ∀ l, Frontier b (I l) W (c l) := by
  induction net with
  | raw W raw =>
    refine ⟨fun _ => 0,by simp,?_⟩
    intro l T av
    exact ⟨T,av,fun f hf => raw_terminal b pos (I l) f (raw f (av f hf)),by simp,fun _ _ x => x⟩
  | gate old d a e aa ee ih =>
    obtain ⟨c,spent,front⟩ := ih
    refine ⟨fun l => c l + fee b (I l) (combine d a e),?_,?_⟩
    · rw [Finset.sum_add_distrib]
      exact Nat.add_le_add spent (fee_once b I linear _)
    · exact fun l => step b 1 (I l) _ (c l) (front l) d a e aa ee

#print axioms ledger

end SparseFrontier
