import Mathlib.Data.Finset.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Prime.Basic

namespace Statements.Erdos273PrimeMinusOneCoverFromThree

abbrev CongruenceClass := ℤ × ℕ

/-- Every integer belongs to at least one represented residue class. -/
def Covers (C : Finset CongruenceClass) : Prop :=
  ∀ z : ℤ, ∃ c ∈ C, (c.2 : ℤ) ∣ z - c.1

/-- No two classes use the same modulus. -/
def HasDistinctModuli (C : Finset CongruenceClass) : Prop :=
  ∀ ⦃c₁⦄, c₁ ∈ C → ∀ ⦃c₂⦄, c₂ ∈ C →
    c₁.2 = c₂.2 → c₁ = c₂

/-- Every modulus is `p - 1` for a prime `p ≥ 3`. -/
def HasPrimeMinusOneModuliFromThree (C : Finset CongruenceClass) : Prop :=
  ∀ c ∈ C, ∃ p : ℕ,
    p.Prime ∧ 3 ≤ p ∧ c.2 = p - 1

/-- The relaxed form of Erdős Problem 273 in which the prime 3, hence the
modulus 2, is allowed: a distinct covering system exists with every modulus
of the form `p - 1` for a prime `p ≥ 3`. -/
abbrev statement : Prop :=
  ∃ C : Finset CongruenceClass,
    Covers C ∧ HasDistinctModuli C ∧ HasPrimeMinusOneModuliFromThree C

theorem target : statement := sorry

end Statements.Erdos273PrimeMinusOneCoverFromThree
