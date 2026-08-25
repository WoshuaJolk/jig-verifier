import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

open Filter

namespace Statements.Erdos681SemiprimeCriterion

def IsLeastPrimeFactor (p m : ℕ) : Prop :=
  p.Prime ∧ p ∣ m ∧ ∀ q : ℕ, q.Prime ∧ q ∣ m → p ≤ q

def IsComposite (m : ℕ) : Prop := 1 < m ∧ ¬m.Prime

def Witness (n k : ℕ) : Prop :=
  0 < k ∧ IsComposite (n + k) ∧
    ∀ p : ℕ, IsLeastPrimeFactor p (n + k) → k ^ 2 < p

def SemiprimeCore : Prop :=
  ∀ᶠ n : ℕ in atTop, (n + 1).Prime →
    ∃ k p q : ℕ, 0 < k ∧ p.Prime ∧ q.Prime ∧ p ≤ q ∧
      n + k = p * q ∧ k ^ 2 < p

/-- A pointwise balanced-semiprime theorem on prime-successor bases would
supply the exact remaining hard core of Erdős 681, including its quartic
window. -/
abbrev statement : Prop :=
  SemiprimeCore →
    ∀ᶠ n : ℕ in atTop, (n + 1).Prime →
      ∃ k : ℕ, Witness n k ∧ (k ^ 2) ^ 2 < n + k

theorem target : statement := sorry

end Statements.Erdos681SemiprimeCriterion
