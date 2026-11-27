import JointWidth
import CleanPreparation

/-! A partial version of the disjoint Boolean sums bound. Each output only
needs to reject the complement of its line and accept some of its singleton
points. AND gates and unrestricted fan-out are allowed in the shared network. -/

namespace PartialSums

open JointWidth SharedOrStars CleanPreparation

variable {P L : Type} [Fintype P] [DecidableEq P] [Fintype L]

abbrev Signal (P : Type) := Finset P → Bool
def zero : Signal P := fun _ => false
def one : Signal P := fun _ => true
def variableAt (p : P) : Signal P := fun X => decide (p ∈ X)
def plus (f g : Signal P) : Signal P := fun X => f X || g X
def times (f g : Signal P) : Signal P := fun X => f X && g X

def IsRaw (f : Signal P) := f=zero ∨ f=one ∨ ∃ p, f=variableAt p

inductive Built : List (Signal P) → ℕ → Prop where
  | raw (W : List (Signal P)) (h : ∀ f ∈ W, IsRaw f) : Built W 0
  | sum {W k} (old : Built W k) (f g : Signal P) (hf : f ∈ W) (hg : g ∈ W) :
      Built (W++[plus f g]) (k+1)
  | prod {W k} (old : Built W k) (f g : Signal P) (hf : f ∈ W) (hg : g ∈ W) :
      Built (W++[times f g]) k

def Mono (f : Signal P) := ∀ X Y, X⊆Y → f X=true → f Y=true

omit [Fintype P] in
theorem mono (W : List (Signal P)) (k : ℕ) (net : Built W k) : ∀ f ∈ W, Mono f := by
  induction net with
  | raw W raw =>
    intro f hf X Y sub h
    rcases raw f hf with rfl | rfl | ⟨p,rfl⟩
    · exact h
    · rfl
    · exact decide_eq_true (sub (of_decide_eq_true h))
  | sum old f g hf hg ih =>
    intro t ht
    rcases List.mem_append.mp ht with prev | new
    · exact ih _ prev
    · simp only [List.mem_singleton] at new
      subst t
      intro X Y sub h
      rcases Bool.or_eq_true_iff.mp h with a | b
      · exact Bool.or_eq_true_iff.mpr (Or.inl (ih f hf X Y sub a))
      · exact Bool.or_eq_true_iff.mpr (Or.inr (ih g hg X Y sub b))
  | prod old f g hf hg ih =>
    intro t ht
    rcases List.mem_append.mp ht with prev | new
    · exact ih _ prev
    · simp only [List.mem_singleton] at new
      subst t
      intro X Y sub h
      obtain ⟨a,b⟩ := Bool.and_eq_true_iff.mp h
      exact Bool.and_eq_true_iff.mpr ⟨ih f hf X Y sub a,ih g hg X Y sub b⟩

def single (f : Signal P) := Finset.univ.filter fun p => f {p}=true
def outside (I : L → Finset P) (l : L) := Finset.univ \ I l
def low (I : L → Finset P) (l : L) (f : Signal P) : Finset P :=
  if f (outside I l) then ∅ else single f

omit [Fintype L] in
theorem inside (I : L → Finset P) (l : L) (f : Signal P) (mon : Mono f) (h : f (outside I l)=false) :
    single f ⊆ I l := by
  intro p hp
  by_contra no
  have sub : ({p} : Finset P) ⊆ outside I l :=
    Finset.singleton_subset_iff.mpr (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,no⟩)
  have hit := mon _ _ sub (Finset.mem_filter.mp hp).2
  rw [h] at hit
  contradiction

omit [Fintype L] in
theorem raw_low (I : L → Finset P) (l : L) (f : Signal P) (h : IsRaw f) : (low I l f).card≤1 := by
  rcases h with rfl | rfl | ⟨p,rfl⟩
  · simp [low,zero,single]
  · simp [low,one]
  · by_cases on : p ∈ outside I l
    · simp [low,variableAt,on]
    · have s : single (variableAt p)={p} := by ext a; simp [single,variableAt,eq_comm]
      simp only [low,variableAt,decide_eq_true_eq,on,ite_false]
      simp [s]

omit [Fintype P] in
theorem widen {t u : ℕ} {S : List (Finset P)} (sub : t≤u) (h : Wide t S) : Wide u S :=
  fun J => (h J).trans (Nat.add_le_add_right sub J.card)

def Ledger (I : L → Finset P) (W : List (Signal P)) (k : ℕ) : Prop :=
  ∃ c : L → ℕ, (∑ l,c l)≤k ∧ ∀ l, Wide (c l) (W.map (low I l))

theorem budget (I : L → Finset P) (linear : ∀ l m, l≠m → (I l ∩ I m).card≤1)
    (W : List (Signal P)) (k : ℕ) (net : Built W k) : Ledger I W k := by
  classical
  induction net with
  | raw W raw =>
    refine ⟨fun _ => 0,by simp,?_⟩
    intro l
    apply JointWidth.initial
    intro j
    by_cases hj : j<W.length
    · have mem := List.getElem_mem (l := W) hj
      simpa [List.getD_eq_getElem?_getD,hj] using raw_low I l W[j] (raw _ mem)
    · simp [List.getD_eq_getElem?_getD,hj]
  | @sum W k net f g hf hg ih =>
    obtain ⟨c,old,widths⟩ := ih
    let h := plus f g
    let F := single h
    refine ⟨fun l => c l+fee (I l) F,?_,?_⟩
    · simp only [Finset.sum_add_distrib]
      exact Nat.add_le_add old (fee_once I linear F)
    · intro l
      simp only [List.map_append,List.map_cons,List.map_nil]
      change Wide _ ((W.map (low I l))++[low I l h])
      by_cases small : (low I l h).card≤1
      · exact widen (Nat.le_add_right _ _) (JointWidth.small _ _ (widths l) _ small)
      · have off : h (outside I l)=false := by
          cases q : h (outside I l) <;> first | rfl | simp [low,q] at small
        have mon := mono _ _ (Built.sum net f g hf hg) h (by simp [h])
        have insideF : F⊆I l := inside I l h mon off
        have big : 2≤F.card := by simpa [low,off,F,h] using (show 2≤(low I l h).card by omega)
        have feeOne : fee (I l) F=1 := by simp [fee,insideF,big]
        rw [feeOne]
        obtain ⟨i,hi⟩ := get_of_mem (W.map (low I l)) _ (List.mem_map_of_mem hf)
        obtain ⟨j,hj⟩ := get_of_mem (W.map (low I l)) _ (List.mem_map_of_mem hg)
        apply JointWidth.join _ _ (widths l) _ i j
        rw [hi,hj]
        have both : f (outside I l)=false ∧ g (outside I l)=false := Bool.or_eq_false_iff.mp off
        intro p hp
        simp only [low,off,both.1,both.2,Bool.false_eq_true,ite_false,single,Finset.mem_filter,
          Finset.mem_univ,true_and,Finset.mem_union] at hp ⊢
        exact Bool.or_eq_true_iff.mp hp
  | @prod W k net f g hf hg ih =>
    obtain ⟨c,old,widths⟩ := ih
    refine ⟨c,old,?_⟩
    intro l
    simp only [List.map_append,List.map_cons,List.map_nil]
    let h := times f g
    change Wide _ ((W.map (low I l))++[low I l h])
    by_cases on : h (outside I l)=true
    · exact JointWidth.small _ _ (widths l) _ (by simp [low,on])
    · have off : h (outside I l)=false := by simpa using on
      have side : f (outside I l)=false ∨ g (outside I l)=false := Bool.and_eq_false_iff.mp off
      rcases side with left | right
      · obtain ⟨i,hi⟩ := get_of_mem (W.map (low I l)) _ (List.mem_map_of_mem hf)
        apply JointWidth.dominated _ _ (widths l) _ i
        rw [hi]
        intro p hp
        simp only [low,off,left,Bool.false_eq_true,ite_false,single,Finset.mem_filter,Finset.mem_univ,true_and] at hp ⊢
        exact (Bool.and_eq_true_iff.mp hp).1
      · obtain ⟨i,hi⟩ := get_of_mem (W.map (low I l)) _ (List.mem_map_of_mem hg)
        apply JointWidth.dominated _ _ (widths l) _ i
        rw [hi]
        intro p hp
        simp only [low,off,right,Bool.false_eq_true,ite_false,single,Finset.mem_filter,Finset.mem_univ,true_and] at hp ⊢
        exact (Bool.and_eq_true_iff.mp hp).2

/-- Only the number of binary OR gates is charged, including when outputs
partially recognize prescribed row neighborhoods and contain higher terms. -/
theorem total (I : L → Finset P) (linear : ∀ l m, l≠m → (I l ∩ I m).card≤1)
    (W : List (Signal P)) (k : ℕ) (net : Built W k) (out : L → Signal P)
    (outputs : ∀ l, out l ∈ W) (reject : ∀ l, out l (outside I l)=false) :
    (∑ l, (single (out l)).card)≤k+Fintype.card L := by
  obtain ⟨c,spent,width⟩ := budget I linear W k net
  calc
    _ ≤ ∑ l, (c l+1) := by
      apply Finset.sum_le_sum
      intro l _
      obtain ⟨j,hj⟩ := get_of_mem (W.map (low I l)) _ (List.mem_map_of_mem (outputs l))
      simpa only [hj,low,reject,Bool.false_eq_true,ite_false] using JointWidth.each _ _ (width l) j
    _ ≤ _ := by simpa [Finset.sum_add_distrib] using Nat.add_le_add_right spent (Fintype.card L)

#print axioms total

end PartialSums
