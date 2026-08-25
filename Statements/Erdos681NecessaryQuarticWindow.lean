import Mathlib.Data.Nat.Prime.Basic

namespace Statements.Erdos681NecessaryQuarticWindow

def IsLeastPrimeFactor (p m : ℕ) : Prop :=
  p.Prime ∧ p ∣ m ∧ ∀ q : ℕ, q.Prime ∧ q ∣ m → p ≤ q

def IsComposite (m : ℕ) : Prop := 1 < m ∧ ¬m.Prime

/-- Any witness to Erdős 681 must lie in the quartic short window:
if its least prime factor exceeds `k²`, then `(k²)² < n+k`. -/
abbrev statement : Prop :=
  ∀ n k : ℕ, 0 < k → IsComposite (n + k) →
    (∀ p : ℕ, IsLeastPrimeFactor p (n + k) → k ^ 2 < p) →
      (k ^ 2) ^ 2 < n + k

theorem target : statement := sorry

end Statements.Erdos681NecessaryQuarticWindow
