import Mathlib.Data.Nat.Factorization.Basic

namespace Statements.Erdos367FullPartDivides

def fullPart (r n : ℕ) : ℕ :=
  ∏ p ∈ n.factorization.support with r ≤ n.factorization p,
    p ^ n.factorization p

/-- Every `r`-full part is a divisor of the original integer. -/
abbrev statement : Prop :=
  ∀ r n : ℕ, fullPart r n ∣ n

theorem target : statement := sorry

end Statements.Erdos367FullPartDivides
