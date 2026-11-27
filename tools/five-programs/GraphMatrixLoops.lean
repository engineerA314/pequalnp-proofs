import GraphCellMachine

namespace GraphMatrixLoops

open GraphStreamForm GraphStreamRoles GraphCellMachine GraphStreamWords WordMachine ThreeColourGadgets
open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal PEqualNP.Library.SearchHelpers.Tab.StepW

abbrev width (w : W) := 13*B w
def decode {n : ℕ} (k : Fin (13*n)) : Shape × Fin n :=
  let p := finProdFinEquiv.symm k
  (roles p.1,p.2)

def project (w : W) (k : Fin (width w)) := vertex (decode k).1 (decode k).2

theorem onto (w : W) : Function.Surjective (project w) := by
  intro v
  obtain ⟨s,i,eq⟩ := projects w.length v
  obtain ⟨j,rfl⟩ := all_roles s
  refine ⟨finProdFinEquiv (j,i),?_⟩
  simpa [project,decode] using eq

theorem prodFn {a b : ℕ} {α : Type} (f : Fin a → Fin b → α) :
    (List.ofFn (fun k : Fin (a*b) => f (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)) =
      (List.ofFn (fun i : Fin a => List.ofFn (f i))).flatten := by
  rw [List.ofFn_mul]
  congr 1
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have h (hk : i.val*b+j.val<a*b) :
      (⟨i.val*b+j.val,hk⟩ : Fin (a*b))=finProdFinEquiv (i,j) :=
    Fin.ext (by simp [finProdFinEquiv,Nat.mul_comm,Nat.add_comm])
  simp only [h,Equiv.symm_apply_apply]

theorem natFn {α : Type} (n : ℕ) (f : ℕ → α) :
    List.ofFn (fun i : Fin n => f i.val)=(List.range n).map f := by
  apply List.ext_getElem <;> simp

def walkSlots {α : Type} (w : W) (f : Shape → ℕ → List α) : List α :=
  (List.ofFn roles).flatMap fun r => (List.range (B w)).flatMap (f r)

theorem over_eq {α : Type} (w : W) (f : Shape → ℕ → List α) :
    (List.ofFn (fun k : Fin (width w) => f (decode k).1 (decode k).2.val)).flatten=walkSlots w f := by
  unfold decode
  rw [prodFn (fun r : Fin 13 => fun i : Fin (B w) => f (roles r) i.val)]
  simp only [List.flatten_flatten,List.map_ofFn,Function.comp_def,natFn,walkSlots,List.flatMap_def]

def entry (w : W) (i j : Fin (width w)) :=
  adjacent w (decode i).1 (decode i).2.val (decode j).1 (decode j).2.val

def word (w : W) := (List.ofFn (fun k : Fin (width w*width w) =>
  entry w (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2))

theorem loops (w : W) :
    word w=walkSlots w (fun r i => walkSlots w (fun s j => [adjacent w r i s j])) := by
  rw [word,prodFn (entry w)]
  have row (i : Fin (width w)) : List.ofFn (entry w i)=
      walkSlots w (fun s j => [adjacent w (decode i).1 (decode i).2.val s j]) := by
    rw [← over_eq]
    simp only [List.ofFn_eq_map,← List.flatMap_def,flatOne]
    rfl
  simp_rw [row]
  exact over_eq w (fun r i => walkSlots w (fun s j => [adjacent w r i s j]))

theorem finiteCPT {α : Type} (xs : List α) (f : α → W → W) (all : ∀ a,CPT (f a)) :
    CPT (fun s => xs.flatMap (fun a => f a s)) := by
  induction xs with
  | nil => exact cpt_const []
  | cons a xs ih => exact cpt_app2 (all a) ih

theorem overCPT {w : W → W} (hw : CPT w) (f : Shape → ℕ → W → W)
    (hf : ∀ r,CPT (fun s => f r (unpairB s).1.length (unpairB s).2)) :
    CPT (fun e => walkSlots (w e) (fun r i => f r i e)) := by
  apply finiteCPT
  intro r
  have h := cpt_flatMapRange (hf r) (cpt_app2 (cpt_const [true]) hw) cpt_id
  refine changeF h ?_
  intro s
  simp [unpairB_pairB,B,un_length]

theorem wordCPT : CPT word := by
  have result : CPT (fun w => walkSlots w (fun r i => walkSlots w (fun s j => [adjacent w r i s j]))) := by
    apply overCPT cpt_id (fun r i w => walkSlots w (fun s j => [adjacent w r i s j]))
    intro r
    apply overCPT cpt_unpairB2 (fun s j e => [adjacent (unpairB e).2 r (unpairB e).1.length s j])
    intro s
    exact adjacentCPT r s (cpt_unpairB2_1 cpt_unpairB2) (cpt_unpairB1_1 cpt_unpairB2) cpt_unpairB1
  exact changeF result (fun w => (loops w).symm)

#print axioms wordCPT

end GraphMatrixLoops
