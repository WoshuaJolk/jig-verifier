import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.Powerset
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Order.Filter.AtTopBot.Basic

namespace Statements.Erdos30SidonAsymptotic

open Filter Real

/-- A finite Sidon set: an equality of two pairwise sums is forced by
commutativity. This is the finite-set specialization of the definition used by
Google DeepMind's formalization of Erdős problem 30. -/
def IsSidon (A : Finset ℕ) : Prop :=
  ∀ ⦃a b c d : ℕ⦄,
    a ∈ A → b ∈ A → c ∈ A → d ∈ A →
      a + b = c + d →
        (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- The maximum cardinality of a Sidon subset of `A`, matching
`Finset.maxSidonSubsetCard` in formal-conjectures. -/
noncomputable def maxSidonSubsetCard (A : Finset ℕ) : ℕ := by
  classical
  exact (A.powerset.filter fun B : Finset ℕ => IsSidon B).sup Finset.card

/-- The Erdős--Turán extremal function on `{1, ..., N}`. -/
noncomputable abbrev h (N : ℕ) : ℕ :=
  maxSidonSubsetCard (Finset.Icc 1 N)

/-- Erdős problem 30: for every positive real exponent, the error in the
maximum size of a Sidon subset of `{1, ..., N}` is `O(N^ε)`. -/
abbrev statement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    (fun N : ℕ => (h N : ℝ) - sqrt N) =O[atTop]
      (fun N : ℕ => (N : ℝ) ^ ε)

theorem target : statement := sorry

end Statements.Erdos30SidonAsymptotic
