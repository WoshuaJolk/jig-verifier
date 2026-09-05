import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic
import Mathlib.Data.Nat.Find

namespace Statements.Erdos687CRTFiniteReduction

open scoped BigOperators

def smallPrimes (X : ℕ) : Finset ℕ :=
  (Finset.range (X + 1)).filter Nat.Prime

def primorial (X : ℕ) : ℕ := ∏ p ∈ smallPrimes X, p

def CoversInitialInterval (X y : ℕ) : Prop :=
  ∃ residue : ℕ → ℕ,
    ∀ m : ℕ, 1 ≤ m → m ≤ y →
      ∃ p : ℕ, p.Prime ∧ p ≤ X ∧ m % p = residue p % p

abbrev statement : Prop :=
  (∀ X y : ℕ, CoversInitialInterval X y ↔
    ∃ a < primorial X, ∀ m, 1 ≤ m → m ≤ y →
      ¬ Nat.Coprime (primorial X) (a + m)) ∧
  (∀ X y : ℕ, CoversInitialInterval X y → y < primorial X) ∧
  (∀ X : ℕ, ∃ Y < primorial X, CoversInitialInterval X Y ∧
    ∀ y, CoversInitialInterval X y → y ≤ Y)

theorem target : statement := sorry

end Statements.Erdos687CRTFiniteReduction
