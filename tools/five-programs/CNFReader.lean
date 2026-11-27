import PEqualNP.Defs.Search
import Mathlib

/-! A total parser for the project's binary encoding, including rejection of
non-canonical variable digits and words ending partway through a literal or clause. -/
namespace CNFReader

open PEqualNP.Search

def number (bits : List Bool) : ℕ := bits.foldr Nat.bit 0

theorem read_bits (n : ℕ) : number n.bits=n := by
  induction n using Nat.binaryRec' with
  | zero => simp [number,Nat.zero_bits]
  | bit b n h ih => simp [Nat.bits_append_bit _ _ h,number] at ih ⊢; rw [ih]

structure State where
  digits : List Bool
  literals : Clause
  clauses : CNF

def finishLiteral (s : State) : State :=
  match s.digits.reverse with
  | [] => ⟨[],s.literals,s.clauses⟩
  | b::ds => ⟨[],(number ds,b)::s.literals,s.clauses⟩

def scan : List Bool → State → State
  | true::b::w,s => scan w {s with digits := b::s.digits}
  | false::true::w,s => scan w (finishLiteral s)
  | false::false::w,s => scan w ⟨[],[],s.literals.reverse::s.clauses⟩
  | _,s => s

theorem scan_digits (ds rest : List Bool) (s : State) :
    scan ((ds.flatMap fun b => [true,b])++rest) s=scan rest {s with digits := ds.reverse++s.digits} := by
  induction ds generalizing s with
  | nil => rfl
  | cons b ds ih => simp [scan,ih,List.append_assoc]

theorem scan_literal (l : Literal) (rest : List Bool) (cs : Clause) (F : CNF) :
    scan (encodeLiteral l++rest) ⟨[],cs,F⟩=scan rest ⟨[],l::cs,F⟩ := by
  obtain ⟨i,b⟩ := l
  simp [encodeLiteral,List.append_assoc,scan,scan_digits,finishLiteral,read_bits]

theorem scan_literals (c : Clause) (rest : List Bool) (acc : Clause) (F : CNF) :
    scan (c.flatMap encodeLiteral++rest) ⟨[],acc,F⟩=scan rest ⟨[],c.reverse++acc,F⟩ := by
  induction c generalizing acc with
  | nil => rfl
  | cons l c ih => simp [List.append_assoc,scan_literal,ih]

theorem scan_clause (c : Clause) (rest : List Bool) (F : CNF) :
    scan (encodeClause c++rest) ⟨[],[],F⟩=scan rest ⟨[],[],c::F⟩ := by
  simp [encodeClause,List.append_assoc,scan_literals,scan]

theorem scan_formula (F : CNF) (rest : List Bool) (acc : CNF) :
    scan (encodeCNF F++rest) ⟨[],[],acc⟩=scan rest ⟨[],[],F.reverse++acc⟩ := by
  induction F generalizing acc with
  | nil => rfl
  | cons c F ih =>
    change scan ((encodeClause c++encodeCNF F)++rest) _=_
    rw [List.append_assoc,scan_clause,ih]
    simp [List.append_assoc]

def raw (w : List Bool) : CNF := (scan w ⟨[],[],[]⟩).clauses.reverse

theorem inverse (F : CNF) : raw (encodeCNF F)=F := by
  have read := scan_formula F [] []
  simpa [raw,scan] using congrArg (fun s => s.clauses.reverse) read

def parse (w : List Bool) : Option CNF := if encodeCNF (raw w)=w then some (raw w) else none

theorem parse_iff (w : List Bool) (F : CNF) : parse w=some F ↔ encodeCNF F=w := by
  constructor
  · intro h
    unfold parse at h
    split at h
    next aligned => exact (Option.some.inj h) ▸ aligned
    next => contradiction
  · rintro rfl
    simp [parse,inverse]

theorem rejects (w : List Bool) : parse w=none ↔ ∀ F : CNF,encodeCNF F≠w := by
  constructor
  · intro off F encoded
    have yes := (parse_iff _ _).mpr encoded
    simp_all
  · intro off
    cases h : parse w with
    | none => rfl
    | some F => exact False.elim (off F ((parse_iff _ _).mp h))

#print axioms parse_iff

end CNFReader
