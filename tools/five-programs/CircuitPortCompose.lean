import CircuitPortBlock

namespace CircuitPortCompose

open CircuitPortBlock PEqualNP.CircuitLowerBounds

theorem run_append (gs hs : List Gate) (x : W) : run (gs++hs) x=run hs (run gs x) := List.foldl_append

theorem append_legal {g h : List Gate} (a : legal g) (b : legal h) : legal (g++h) :=
  fun gate member => (List.mem_append.mp member).elim (a gate) (b gate)

theorem collect (n m : ℕ) (C : Fin m → Circuit) (basic : ∀ i,legal (C i).gates) :
    ∃ (G : List Gate) (ports : Fin m → ℕ), legal G ∧ G.length=∑ i,((C i).size+1) ∧
      (∀ i,ports i<n+G.length) ∧ ∀ (x : W), x.length=n →
        ∀ i,(run G x).getD (ports i) false=(C i).eval x := by
  induction m with
  | zero =>
    exact ⟨[],Fin.elim0,fun g hg => by simp at hg,by simp,fun i => i.elim0,fun _ _ i => i.elim0⟩
  | succ m ih =>
    obtain ⟨G,pins,good,len,safe,read⟩ := ih (fun i => C i.succ) (fun i => basic i.succ)
    let start := n+G.length
    let K := block n start Fin.val (C 0)
    let positions : Fin (m+1) → ℕ := Fin.cases (start+(C 0).size) pins
    have lk : K.length=(C 0).size+1 := block_length ..
    have ident (j : Fin n) : j.val<start := by dsimp [start]; omega
    refine ⟨G++K,positions,append_legal good (block_legal _ _ _ _ (basic 0)),?_,?_,?_⟩
    · rw [List.length_append,lk,len,Fin.sum_univ_succ,Nat.add_comm]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · change start+(C 0).size<n+(G++K).length
        rw [List.length_append,lk]; dsimp [start]; omega
      · change pins j<n+(G++K).length
        rw [List.length_append]; have := safe j; omega
    · intro x hx i
      rw [run_append]
      refine Fin.cases ?_ (fun j => ?_) i
      · apply block_read n start Fin.val ident (C 0) x (run G x) hx (by simp [length_run,hx,start])
        intro j
        exact stable G x j.val (by rw [hx]; exact j.isLt)
      · change (run K (run G x)).getD (pins j) false=(C j.succ).eval x
        rw [stable _ _ _ (by simpa [length_run,hx] using safe j),read x hx j]

theorem compose (n m : ℕ) (C : Fin m → Circuit) (D : Circuit) (basic : ∀ i,legal (C i).gates) (hd : legal D.gates) :
    ∃ E : Circuit,legal E.gates ∧ E.size=(∑ i,((C i).size+1))+D.size+1 ∧
      ∀ x : W,x.length=n → E.eval x=D.eval (List.ofFn (fun i => (C i).eval x)) := by
  obtain ⟨G,pins,good,len,safe,read⟩ := collect n m C basic
  let start := n+G.length
  let K := block m start pins D
  refine ⟨⟨G++K,start+D.size⟩,append_legal good (block_legal _ _ _ _ hd),?_,?_⟩
  · simp only [Circuit.size,List.length_append,K,block_length,len]; omega
  · intro x hx
    change (run (G++K) x).getD (start+D.size) false=_
    rw [run_append]
    apply block_read m start pins safe D (List.ofFn fun i => (C i).eval x) (run G x)
      (by simp) (by simp [length_run,hx,start])
    intro i
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some] using read x hx i

def Small (n k : ℕ) (f : W → Bool) := ∃ C : Circuit, legal C.gates ∧ C.size≤k ∧ ∀ x : W,x.length=n → C.eval x=f x

theorem mono {n s t : ℕ} {f : W → Bool} (h : Small n s f) (le : s≤t) : Small n t f := by
  obtain ⟨C,hc,sz,eq⟩ := h
  exact ⟨C,hc,sz.trans le,eq⟩

theorem many (n m : ℕ) (limits : Fin m → ℕ) (f : Fin m → W → Bool) (hs : ∀ i,Small n (limits i) (f i))
    (D : Circuit) (leg : legal D.gates) :
    Small n ((∑ i,(limits i+1))+D.size+1) (fun x => D.eval (List.ofFn fun i => f i x)) := by
  choose C hc cost read using hs
  obtain ⟨E,ok,sz,value⟩ := compose n m C D hc leg
  refine ⟨E,ok,?_,?_⟩
  · rw [sz]
    gcongr with i
    exact cost i
  · intro x hx
    rw [value x hx]
    congr 1
    apply congrArg List.ofFn
    funext i
    exact read i x hx

#print axioms many

end CircuitPortCompose
