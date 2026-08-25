import Mathlib.Data.Finset.Basic

/-!
# Structural reduction for Erdős problem 864

If unordered pair sums are unique away from one exceptional value `e`, then
the elements on either side of `e/2` separately have completely unique
unordered pair sums.
-/

namespace Statements.Erdos864ExceptionalSplit

def PairUniqueExcept (A : Finset ℕ) (e : ℕ) : Prop :=
  ∀ ⦃a b c d : ℕ⦄,
    a ∈ A → b ∈ A → c ∈ A → d ∈ A →
      a ≤ b → c ≤ d → a + b = c + d → a + b ≠ e →
        a = c ∧ b = d

def PairUnique (A : Finset ℕ) : Prop :=
  ∀ ⦃a b c d : ℕ⦄,
    a ∈ A → b ∈ A → c ∈ A → d ∈ A →
      a ≤ b → c ≤ d → a + b = c + d →
        a = c ∧ b = d

abbrev statement : Prop :=
  ∀ (A : Finset ℕ) (e : ℕ),
    PairUniqueExcept A e →
      PairUnique (A.filter fun a => 2 * a ≤ e) ∧
        PairUnique (A.filter fun a => e < 2 * a)

theorem target : statement := sorry

end Statements.Erdos864ExceptionalSplit
