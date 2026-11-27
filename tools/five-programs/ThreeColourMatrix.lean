import ThreeColourGadgets

namespace ThreeColourMatrix

open ThreeColourGadgets
variable {n m : ℕ}

def arc (F : Form n m) (u v : Vertex n m) : Bool :=
  match u with
  | .inl a => match v with
    | .inl b => decide (a≠b)
    | .inr _ => false
  | .inr (.inl (x,b)) => decide (v=pal 2) || (b && decide (v=lit x false))
  | .inr (.inr (i,t,a)) => decide (v=feeds F i t a) || match v with
    | .inr (.inr (j,s,b)) => decide (i=j ∧ t=s ∧ a≠b)
    | _ => false

theorem arcs_iff (F : Form n m) (u v : Vertex n m) : arc F u v=true ↔ Edge F u v := by
  constructor
  · rintro h
    rcases u with a | (⟨x,b⟩ | ⟨i,t,a⟩)
    · rcases v with j | other
      · exact .palette a j (of_decide_eq_true h)
      · simp [arc] at h
    · simp only [arc,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at h
      rcases h with rfl | ⟨rfl,rfl⟩
      · exact .boolean x b
      · exact .opposite x
    · simp only [arc,Bool.or_eq_true,decide_eq_true_eq] at h
      rcases h with rfl | h
      · exact .wire i t a
      · rcases v with j | (other | ⟨j,s,b⟩)
        · contradiction
        · contradiction
        · obtain ⟨rfl,rfl,ne⟩ := of_decide_eq_true h
          exact .triangle _ _ _ _ ne
  · intro edge
    cases edge with
    | palette a b ne => simp [pal,arc,ne]
    | boolean x b => simp [lit,pal,arc]
    | opposite x => simp [lit,arc]
    | triangle i t a b ne => simp [aux,arc,ne]
    | wire i t a => simp [aux,arc]

def bits : Bool ≃ Fin 2 where
  toFun b := if b then 1 else 0
  invFun j := decide (j=1)
  left_inv := by rintro (_|_) <;> rfl
  right_inv := by intro j; fin_cases j <;> rfl

def side (n m : ℕ) := 3 + ((n+m)*2 + m*(2*3))

def numbering (n m : ℕ) : Vertex n m ≃ Fin (side n m) := by
  let xs : Variables n m ≃ Fin (n+m) := finSumFinEquiv
  let lits := (xs.prodCongr bits).trans finProdFinEquiv
  let ends := (bits.prodCongr (Equiv.refl (Fin 3))).trans finProdFinEquiv
  let tris := ((Equiv.refl (Fin m)).prodCongr ends).trans finProdFinEquiv
  exact ((Equiv.refl (Fin 3)).sumCongr ((lits.sumCongr tris).trans finSumFinEquiv)).trans finSumFinEquiv

def entry (F : Form n m) (i j : Fin (side n m)) : Bool :=
  let e := (numbering n m).symm
  arc F (e i) (e j) || arc F (e j) (e i)

def word (F : Form n m) : List Bool := List.ofFn (fun k : Fin (side n m * side n m) =>
  let ij := finProdFinEquiv.symm k
  entry F ij.1 ij.2)

theorem word_length (F : Form n m) : (word F).length=side n m * side n m := by simp [word]

theorem read_entry (F : Form n m) (i j : Fin (side n m)) :
    (word F).getD (i.val*side n m+j.val) false=entry F i j := by
  let k : Fin (side n m * side n m) := finProdFinEquiv (i,j)
  have h : k.val=i.val*side n m+j.val := by simp [k,finProdFinEquiv,Nat.mul_comm,Nat.add_comm]
  rw [← h,List.getD_eq_getElem?_getD]
  unfold word
  rw [List.getElem?_ofFn,dite_eq_left k.isLt]
  change entry F (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2=_
  rw [show finProdFinEquiv.symm k=(i,j) from finProdFinEquiv.symm_apply_apply _]

/-- Exactly the row-major language in L-lib-347, L-lib-348 and L-lib-349. -/
def Accepted (w : List Bool) := ∃ d : ℕ, w.length=d*d ∧ ∃ c : ℕ → Fin 3,
    ∀ i j : ℕ, i<d → j<d → w.getD (i*d+j) false=true → c i≠c j

theorem matrix_iff (F : Form n m) : Sat F ↔ Accepted (word F) := by
  rw [graph_iff]
  let e := numbering n m
  constructor
  · rintro ⟨c,good⟩
    refine ⟨_,word_length F,fun k => if h : k<side n m then c (e.symm ⟨k,h⟩) else 0,?_⟩
    intro i j hi hj edge
    rw [read_entry F ⟨i,hi⟩ ⟨j,hj⟩] at edge
    simp only [hi,hj,dite_true]
    rcases Bool.or_eq_true_iff.mp edge with forward | backward
    · exact good _ _ ((arcs_iff _ _ _).mp forward)
    · exact Ne.symm (good _ _ ((arcs_iff _ _ _).mp backward))
  · rintro ⟨d,len,c,ok⟩
    rw [word_length] at len
    have eq : d=side n m := by nlinarith
    subst d
    refine ⟨fun v => c (e v).val,fun u v edge => ok _ _ (e u).isLt (e v).isLt ?_⟩
    rw [read_entry F (e u) (e v)]
    apply Bool.or_eq_true_iff.mpr
    left
    simpa [e] using (arcs_iff F u v).mpr edge

#print axioms matrix_iff

end ThreeColourMatrix
