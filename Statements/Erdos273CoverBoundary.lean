import Mathlib.Data.Finset.Basic
import Mathlib.Data.Int.Basic

namespace Statements.Erdos273CoverBoundary

abbrev CongruenceClass := ℤ × ℕ

def Covers (C : Finset CongruenceClass) : Prop :=
  ∀ z : ℤ, ∃ c ∈ C, (c.2 : ℤ) ∣ z - c.1

/-- Coverage is nonvacuous, and one class with a nontrivial modulus
cannot cover all integers. -/
abbrev statement : Prop :=
  (∀ C : Finset CongruenceClass, Covers C → C.Nonempty) ∧
  ∀ (a : ℤ) (m : ℕ), 1 < m → ¬ Covers {(a, m)}

theorem target : statement := sorry

end Statements.Erdos273CoverBoundary
