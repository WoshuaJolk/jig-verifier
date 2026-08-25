import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Nat.Prime.Basic

namespace Statements.Erdos10DistinctNormalization

abbrev represented (k n : ℕ) : Prop :=
  ∃ (p : ℕ) (exponents : Multiset ℕ),
    p.Prime ∧ exponents.card ≤ k ∧
      n = p + (exponents.map (fun e => (2 : ℕ) ^ e)).sum

abbrev representedDistinct (k n : ℕ) : Prop :=
  ∃ (p : ℕ) (exponents : Multiset ℕ),
    p.Prime ∧ exponents.Nodup ∧ exponents.card ≤ k ∧
      n = p + (exponents.map (fun e => (2 : ℕ) ^ e)).sum

/-- Repeated powers of two can always be carried, without increasing their number. -/
abbrev statement : Prop :=
  ∀ k n : ℕ, represented k n ↔ representedDistinct k n

theorem target : statement := sorry

end Statements.Erdos10DistinctNormalization
