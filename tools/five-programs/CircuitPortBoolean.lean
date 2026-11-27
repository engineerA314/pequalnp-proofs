import CircuitPortCompose

namespace CircuitPortBoolean

open CircuitPortBlock CircuitPortCompose PEqualNP.CircuitLowerBounds

theorem constant (n : ℕ) (b : Bool) : Small n 1 (fun _ => b) := by
  let gate : Gate := ⟨if b then .and else .or,[]⟩
  refine ⟨⟨[gate],n⟩,?_,by rfl,?_⟩
  · intro g h
    obtain rfl := List.mem_singleton.mp h
    cases b <;> simp [gate]
  · intro x hx
    change (step x gate).getD n false=b
    rw [step,snoc,hx]
    cases b <;> simp [gate,GateOp.eval]

theorem input (n i : ℕ) : Small n 0 (fun x => x.getD i false) :=
  ⟨⟨[],i⟩,fun _ h => by simp at h,le_rfl,fun _ _ => rfl⟩

def twoGate (op : GateOp) : Circuit := ⟨[⟨op,[0,1]⟩],2⟩

theorem binary (n s t : ℕ) (f g : W → Bool) (hf : Small n s f) (hg : Small n t g)
    (op : GateOp) (leg : op∈({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    Small n (s+t+4) (fun x => op.eval [f x,g x]) := by
  let lim : Fin 2 → ℕ := ![s,t]
  let fs : Fin 2 → W → Bool := ![f,g]
  have ok : ∀ i,Small n (lim i) (fs i) := by intro i; fin_cases i; exact hf; exact hg
  have legal2 : legal (twoGate op).gates := by
    intro gate h
    obtain rfl := List.mem_singleton.mp h
    exact ⟨leg,by change 2 ≤ 2; rfl⟩
  obtain ⟨C,legC,sz,read⟩ := many n 2 lim fs ok (twoGate op) legal2
  refine ⟨C,legC,?_,?_⟩
  · have eq : (∑ i : Fin 2,(lim i+1))=s+t+2 := by simp [lim,Fin.sum_univ_two]; omega
    rw [eq] at sz
    change C.size ≤ s+t+2+1+1 at sz
    omega
  · intro x hx
    rw [read x hx]
    rfl

theorem conjunction {n s t : ℕ} {f g : W → Bool} (hf : Small n s f) (hg : Small n t g) :
    Small n (s+t+4) (fun x => f x && g x) := by
  have h := binary n s t f g hf hg .and (by simp)
  simpa [GateOp.eval] using h

theorem disjunction {n s t : ℕ} {f g : W → Bool} (hf : Small n s f) (hg : Small n t g) :
    Small n (s+t+4) (fun x => f x || g x) := by
  have h := binary n s t f g hf hg .or (by simp)
  simpa [GateOp.eval] using h

theorem any_list (n k : ℕ) (is : List ℕ) (f : ℕ → W → Bool) (small : ∀ i∈is,Small n k (f i)) :
    Small n (1+is.length*(k+4)) (fun x => is.any (fun i => f i x)) := by
  induction is with
  | nil => simpa using constant n false
  | cons i is ih =>
    have rest := ih (fun j hj => small j (List.mem_cons_of_mem _ hj))
    have combined := disjunction (small i List.mem_cons_self) rest
    have cost : k+(1+is.length*(k+4))+4=1+(i::is).length*(k+4) := by simp [Nat.add_mul]; ring
    simpa only [List.any_cons,cost] using combined

theorem prefixed (n : ℕ) (prefixBits : W) (D : Circuit) (hd : legal D.gates) :
    Small n (2*(prefixBits.length+n)+D.size+1) (fun x => D.eval (prefixBits++x)) := by
  let m := prefixBits.length+n
  let bits := fun (i : Fin m) (x : W) => (prefixBits++x).getD i.val false
  have access (i : Fin m) : Small n 1 (bits i) := by
    by_cases h : i.val<prefixBits.length
    · simpa only [bits,List.getD_eq_getElem?_getD,List.getElem?_append_left h] using constant n (prefixBits.getD i.val false)
    · have right := mono (input n (i.val-prefixBits.length)) (by decide : 0 ≤ 1)
      simpa only [bits,List.getD_eq_getElem?_getD,List.getElem?_append_right (Nat.le_of_not_gt h)] using right
  obtain ⟨C,legC,cost,read⟩ := many n m (fun _ => 1) bits access D hd
  refine ⟨C,legC,?_,?_⟩
  · simpa [m,Nat.mul_comm] using cost
  · intro x hx
    rw [read x hx]
    apply congrArg D.eval
    apply List.ext_getElem
    · simp [m,hx]
    · intro i h1 h2
      simp only [List.getElem_ofFn,bits,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h2,Option.getD_some]

#print axioms prefixed

end CircuitPortBoolean
