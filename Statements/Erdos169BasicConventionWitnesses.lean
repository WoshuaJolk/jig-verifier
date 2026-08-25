import Mathlib.Data.Set.Basic

namespace Statements.Erdos169BasicConventionWitnesses

def IsAPFree (k : ℕ) (A : Set ℕ) : Prop :=
  (∀ n ∈ A, 1 ≤ n) ∧
    ∀ a d : ℕ, 0 < d → ∃ i < k, a + i * d ∉ A

def ForcesMonochromaticAP (k N : ℕ) : Prop :=
  ∀ color : ℕ → Bool, ∃ a d : ℕ,
    1 ≤ a ∧ 0 < d ∧ a + (k - 1) * d ≤ N ∧
      ∀ i < k, color (a + i * d) = color a

/-- Minimal witnesses for both AP conventions in the Erdős 169 verifier. -/
abbrev statement : Prop :=
  IsAPFree 3 {1} ∧ ForcesMonochromaticAP 1 1

theorem target : statement := sorry

end Statements.Erdos169BasicConventionWitnesses
