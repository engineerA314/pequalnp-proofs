import GridStripMatching

namespace GridOrderCut

open Finset GridStripMatching ResidualInducedMatching

theorem first_row (m : ℕ) (time : Fin (m+1) × Fin (m+1) → ℕ) (unique : Function.Injective time) :
    ∃ t i,(∀ j,time (i,j)≤t) ∧ ∀ u,u≠i → ∃ j,t<time (u,j) := by
  classical
  have peak (i : Fin (m+1)) : ∃ j : Fin (m+1),∀ h,time (i,h)≤time (i,j) := by
    obtain ⟨j,_,max⟩ := Finset.exists_max_image (univ : Finset (Fin (m+1))) (fun j => time (i,j)) univ_nonempty
    exact ⟨j,fun h => max h (mem_univ _)⟩
  choose last maximal using peak
  obtain ⟨i,_,small⟩ := Finset.exists_min_image (univ : Finset (Fin (m+1))) (fun i => time (i,last i)) univ_nonempty
  refine ⟨time (i,last i),i,maximal i,?_⟩
  intro u ne
  refine ⟨last u,lt_of_le_of_ne (small u (mem_univ _)) ?_⟩
  intro eq
  exact ne (congrArg Prod.fst (unique eq)).symm

def pick (k : ℕ) (d : Fin 2) (i : Fin (k+1)) : Fin (2*k+2) := ⟨2*i.val+d.val,by omega⟩

theorem spaced (k : ℕ) (d : Fin 2) (i j : Fin (k+1)) (ne : i≠j) :
    pick k d i≠pick k d j ∧ ¬near (pick k d i) (pick k d j) := by
  have diff : i.val≠j.val := fun eq => ne (Fin.ext eq)
  constructor
  · intro eq
    have := congrArg Fin.val eq
    change 2*i.val+d.val=2*j.val+d.val at this
    omega
  · unfold near pick
    simp only
    omega

def beforeTime (m : ℕ) (time : Fin m × Fin m → ℕ) (t : ℕ) := univ.filter (fun v => time v≤t)

theorem any_order (k : ℕ) (time : Fin (2*k+2) × Fin (2*k+2) → ℕ) (unique : Function.Injective time) :
    ∃ t,Nonempty (CutMatching (grid (2*k+2)) (beforeTime _ time t) (k+1)) := by
  classical
  obtain ⟨t,i,done,incomplete⟩ := first_row (2*k+1) time unique
  let S := beforeTime _ time t
  have mem (u) : u∈S ↔ time u≤t := by simp [S,beforeTime]
  by_cases untouched : ∃ u,∀ j,t<time (u,j)
  · obtain ⟨u,empty⟩ := untouched
    refine ⟨t,⟨matching S true (pick k 0) (spaced k 0) ?_⟩⟩
    intro j
    refine ⟨⟨i,(mem _).mpr (done _)⟩,⟨u,?_⟩⟩
    exact fun h => (not_le_of_gt (empty _)) ((mem _).mp h)
  · push Not at untouched
    let d : Fin 2 := if i.val%2=0 then 1 else 0
    have misses (h : Fin (k+1)) : pick k d h≠i := by
      intro eq
      have e := congrArg Fin.val eq
      change 2*h.val+d.val=i.val at e
      by_cases even : i.val%2=0 <;> simp [d,even] at e <;> omega
    refine ⟨t,⟨matching S false (pick k d) (spaced k d) ?_⟩⟩
    intro h
    obtain ⟨j,yes⟩ := untouched (pick k d h)
    obtain ⟨v,no⟩ := incomplete (pick k d h) (misses h)
    exact ⟨⟨j,(mem _).mpr yes⟩,⟨v,fun h => (not_le_of_gt no) ((mem _).mp h)⟩⟩

#print axioms any_order

end GridOrderCut
