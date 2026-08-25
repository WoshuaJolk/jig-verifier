import Mathlib.Algebra.Module.NatInt
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Prime.Basic

namespace Statements.Erdos200TwoPrimeAP

def IsAPOfLengthWith {α : Type*} [AddCommMonoid α]
    (s : Set α) (l : ℕ∞) (a d : α) : Prop :=
  ENat.card s = l ∧ s = {a + n • d | (n : ℕ) (_ : n < l)}

def IsAPOfLength {α : Type*} [AddCommMonoid α]
    (s : Set α) (l : ℕ∞) : Prop :=
  ∃ a d : α, IsAPOfLengthWith s l a d

/-- The set `{2,3}` is a two-term arithmetic progression of primes. -/
abbrev statement : Prop :=
  IsAPOfLength ({2, 3} : Set ℕ) 2 ∧
    ∀ p ∈ ({2, 3} : Set ℕ), p.Prime

theorem target : statement := sorry

end Statements.Erdos200TwoPrimeAP
