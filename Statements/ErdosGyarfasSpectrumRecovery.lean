import Mathlib.Data.Finset.Basic

namespace Statements.ErdosGyarfasSpectrumRecovery

/-- A terminal path of length in S closes a dyadic cycle with a fresh path of length q. -/
def responds (S : Finset ℕ) (q : ℕ) : Prop :=
  ∃ x ∈ S, ∃ k : ℕ, 2 ≤ k ∧ q + x = 2 ^ k

/-- Universal dyadic completion-response domination recovers exact spectrum inclusion. -/
def statement : Prop := ∀ (M : ℕ) (S T : Finset ℕ),
    (∀ x ∈ S, 1 ≤ x ∧ x ≤ M) →
    (∀ x ∈ T, 1 ≤ x ∧ x ≤ M) →
    ((∀ q : ℕ, 2 ≤ q → responds S q → responds T q) ↔ S ⊆ T)

end Statements.ErdosGyarfasSpectrumRecovery
