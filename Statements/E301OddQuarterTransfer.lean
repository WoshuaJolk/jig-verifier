import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Ring.Parity
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Card

namespace Statements.E301OddQuarterTransfer

def TripleFree (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A,
    a ≠ b → a ≠ c → b ≠ c →
    (a : ℚ)⁻¹ ≠ (b : ℚ)⁻¹ + (c : ℚ)⁻¹

def OddQuarter (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun n => Odd n ∧ 4 * n ≤ N)

/-- A conditional transfer from upper-third donor constructions; not an
all-length avoidance claim or an answer to either extremal problem. -/
abbrev statement : Prop :=
  ∀ (N : ℕ) (A : Finset ℕ), A ⊆ Finset.Icc 1 N →
    (∀ n ∈ A, (N < 3 * n ∧ 2 * n < N ∧ Odd n) ∨ N ≤ 2 * n) →
    TripleFree A →
    TripleFree (A ∪ OddQuarter N) ∧
    (A ∪ OddQuarter N).card ≥ A.card + N / 8

theorem target : statement := sorry

end Statements.E301OddQuarterTransfer
