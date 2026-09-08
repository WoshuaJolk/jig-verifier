import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Finset.Card
import Mathlib.Topology.Instances.Nat

namespace Statements.Erdos530SidonIntervalUpper

open Filter

def IsSidon (S : Finset ℝ) : Prop :=
  ∀ ⦃a b c d : ℝ⦄,
    a ∈ S → b ∈ S → c ∈ S → d ∈ S →
      a + b = c + d →
        (a = c ∧ b = d) ∨ (a = d ∧ b = c)

def SomeSetHasNoLargerSidon (ε : ℝ) (N : ℕ) : Prop :=
  ∃ A : Finset ℝ, A.card = N ∧
    ∀ S : Finset ℝ, S ⊆ A → IsSidon S →
      S.card ≤ (1 + ε) * Real.sqrt N

/-- Classical sharp asymptotic upper clause of Erdős 530, using integer intervals. -/
abbrev statement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, SomeSetHasNoLargerSidon ε N

theorem target : statement := sorry

end Statements.Erdos530SidonIntervalUpper
