import PEqualNP.Defs.CircuitLowerBounds
import Mathlib

namespace CircuitPortBlock

open PEqualNP.CircuitLowerBounds

abbrev W := List Bool
def step (w : W) (g : Gate) := w++[g.op.eval (g.inputs.map (fun i => w.getD i false))]
def run (gs : List Gate) (x : W) := gs.foldl step x
def legal (gs : List Gate) := ∀ g∈gs,g.op∈({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2

theorem length_run (gs : List Gate) (x : W) : (run gs x).length=x.length+gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (step x g)).length=_
    rw [ih]
    simp [step]; omega

theorem snoc (x : W) (b : Bool) (i : ℕ) : (x++[b]).getD i false=
    if i<x.length then x.getD i false else if i=x.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with l e
  · rw [List.getElem?_append_left l]
  · subst i; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; rfl

theorem stable (gs : List Gate) (x : W) (i : ℕ) (h : i<x.length) :
    (run gs x).getD i false=x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (step x g)).getD i false=_
    rw [ih _ (by simp [step]; omega)]
    rw [step,snoc,ite_eq_left h]

def ren (m start : ℕ) (pin : Fin m → ℕ) (i : ℕ) :=
  if h : i < m then pin ⟨i,h⟩ else start+(i-m)

def lift (m start : ℕ) (pin : Fin m → ℕ) (g : Gate) : Gate :=
  ⟨g.op,g.inputs.map (ren m start pin)⟩

theorem simulate (m start : ℕ) (pin : Fin m → ℕ) (safe : ∀ i,pin i<start) (gs : List Gate)
    (u v : W) (t : ℕ) (hu : u.length=m+t) (hv : v.length=start+t)
    (matchAt : ∀ i,v.getD (ren m start pin i) false=u.getD i false) :
    ∀ i,(run (gs.map (lift m start pin)) v).getD (ren m start pin i) false=(run gs u).getD i false := by
  induction gs generalizing u v t with
  | nil => exact matchAt
  | cons g gs ih =>
    intro i
    change (run (gs.map _) (step v (lift m start pin g))).getD _ false=(run gs (step u g)).getD i false
    apply ih _ _ (t+1) (by simp [step,hu]; omega) (by simp [step,hv]; omega) _ i
    intro j
    have below : ren m start pin j<start+t ↔ j < m+t := by
      unfold ren; split <;> rename_i h
      · have := safe ⟨j,h⟩; omega
      · omega
    have atEnd : ren m start pin j=start+t ↔ j=m+t := by
      unfold ren; split <;> rename_i h
      · have := safe ⟨j,h⟩; omega
      · omega
    have value : (lift m start pin g).op.eval ((lift m start pin g).inputs.map (fun k => v.getD k false)) =
        g.op.eval (g.inputs.map (fun k => u.getD k false)) := by
      unfold lift
      simp only [List.map_map]
      congr 1
      exact List.map_congr_left (fun k _ => matchAt k)
    simp only [step,snoc,hu,hv,below,atEnd,value,matchAt]

def copyGate (j : ℕ) : Gate := ⟨.or,[j]⟩
def block (m start : ℕ) (pins : Fin m → ℕ) (C : Circuit) :=
  C.gates.map (lift m start pins)++[copyGate (ren m start pins C.output)]

theorem block_length (m start : ℕ) (pins : Fin m → ℕ) (C : Circuit) :
    (block m start pins C).length=C.size+1 := by simp [block,Circuit.size]

theorem block_legal (m start : ℕ) (pins : Fin m → ℕ) (C : Circuit) (h : legal C.gates) :
    legal (block m start pins C) := by
  intro g hg
  rcases List.mem_append.mp hg with actual | buffer
  · obtain ⟨gate,hgate,rfl⟩ := List.mem_map.mp actual
    simpa [lift] using h gate hgate
  · obtain rfl := List.mem_singleton.mp buffer
    simp [copyGate]

theorem block_read (m start : ℕ) (pin : Fin m → ℕ) (safe : ∀ i,pin i<start) (C : Circuit)
    (old new : W) (ho : old.length=m) (hn : new.length=start)
    (values : ∀ i : Fin m,new.getD (pin i) false=old.getD i.val false) :
    (run (block m start pin C) new).getD (start+C.size) false=C.eval old := by
  have h0 (i : ℕ) : new.getD (ren m start pin i) false=old.getD i false := by
    by_cases h : i < m
    · simpa [ren,h] using values ⟨i,h⟩
    · simp only [ren,h,dite_false,List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega : old.length ≤ i),
        List.getElem?_eq_none (by omega : new.length ≤ start+(i-m))]
  have h := simulate m start pin safe C.gates old new 0 (by simpa using ho) (by simpa using hn) h0 C.output
  let mid := run (C.gates.map (lift m start pin)) new
  have hm : mid.length=start+C.size := by simp [mid,length_run,hn,Circuit.size]
  change (List.foldl step new (C.gates.map (lift m start pin)++[_])).getD _ false=_
  rw [List.foldl_append]
  change (mid++[(copyGate _).op.eval ((copyGate _).inputs.map (fun i => mid.getD i false))]).getD _ false=_
  rw [snoc,hm]
  simp only [lt_self_iff_false,ite_false,ite_true]
  change ([mid.getD (ren m start pin C.output) false].any id)=(run C.gates old).getD C.output false
  simp only [List.any_cons,List.any_nil,id_eq,Bool.or_false]
  exact h

#print axioms block_read

end CircuitPortBlock
