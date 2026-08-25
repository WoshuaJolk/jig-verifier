import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Finset.Card
import Mathlib.Topology.Instances.Nat

namespace Statements.Erdos530SidonSubsetSharpConstant

open Filter

def IsSidon (S : Finset ℝ) : Prop :=
  ∀ ⦃a b c d : ℝ⦄,
    a ∈ S → b ∈ S → c ∈ S → d ∈ S →
      a + b = c + d →
        (a = c ∧ b = d) ∨ (a = d ∧ b = c)

def EverySetHasLargeSidon (ε : ℝ) (N : ℕ) : Prop :=
  ∀ A : Finset ℝ, A.card = N →
    ∃ S : Finset ℝ, S ⊆ A ∧ IsSidon S ∧
      (1 - ε) * Real.sqrt N ≤ S.card

def SomeSetHasNoLargerSidon (ε : ℝ) (N : ℕ) : Prop :=
  ∃ A : Finset ℝ, A.card = N ∧
    ∀ S : Finset ℝ, S ⊆ A → IsSidon S →
      S.card ≤ (1 + ε) * Real.sqrt N

/-- Erdős Problem 530: the guaranteed Sidon-subset size has sharp
asymptotic constant one times `sqrt N`. -/
abbrev statement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    (∀ᶠ N in atTop, EverySetHasLargeSidon ε N) ∧
      (∀ᶠ N in atTop, SomeSetHasNoLargerSidon ε N)

theorem target : statement := sorry

end Statements.Erdos530SidonSubsetSharpConstant
