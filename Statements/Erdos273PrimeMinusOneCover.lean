import Mathlib.Data.Finset.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Prime.Basic

namespace Statements.Erdos273PrimeMinusOneCover

abbrev CongruenceClass := ℤ × ℕ

/-- Every integer belongs to at least one represented residue class. -/
def Covers (C : Finset CongruenceClass) : Prop :=
  ∀ z : ℤ, ∃ c ∈ C, (c.2 : ℤ) ∣ z - c.1

/-- No two classes use the same modulus. -/
def HasDistinctModuli (C : Finset CongruenceClass) : Prop :=
  ∀ ⦃c₁⦄, c₁ ∈ C → ∀ ⦃c₂⦄, c₂ ∈ C →
    c₁.2 = c₂.2 → c₁ = c₂

/-- Every modulus is `p - 1` for a prime `p ≥ 5`. -/
def HasPrimeMinusOneModuli (C : Finset CongruenceClass) : Prop :=
  ∀ c ∈ C, ∃ p : ℕ,
    p.Prime ∧ 5 ≤ p ∧ c.2 = p - 1

/-- The affirmative form of Erdős Problem 273. -/
abbrev statement : Prop :=
  ∃ C : Finset CongruenceClass,
    Covers C ∧ HasDistinctModuli C ∧ HasPrimeMinusOneModuli C

theorem target : statement := sorry

end Statements.Erdos273PrimeMinusOneCover
