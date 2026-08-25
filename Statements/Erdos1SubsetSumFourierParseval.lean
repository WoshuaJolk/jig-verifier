import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset

open scoped BigOperators ComplexConjugate ZMod

namespace Statements.Erdos1SubsetSumFourierParseval

/-- Exact product formula and Parseval identity for the residue distribution of
all subset sums. The right side is the modular collision energy. -/
abbrev statement : Prop :=
  ∀ (q : ℕ) [NeZero q] (A : Finset ℕ),
    (∀ k : ZMod q,
      ∑ S ∈ A.powerset, ZMod.stdAddChar (-(((S.sum id : ℕ) : ZMod q) * k)) =
        ∏ a ∈ A, (1 + ZMod.stdAddChar (-((a : ZMod q) * k)))) ∧
    (∑ k : ZMod q,
        conj (∏ a ∈ A, (1 + ZMod.stdAddChar (-((a : ZMod q) * k)))) *
          ∏ a ∈ A, (1 + ZMod.stdAddChar (-((a : ZMod q) * k))) =
      (q : ℂ) * ∑ r : ZMod q,
        ((((A.powerset.filter fun S =>
          ((S.sum id : ℕ) : ZMod q) = r).card : ℕ) : ℂ) ^ 2))

theorem target : statement := sorry

end Statements.Erdos1SubsetSumFourierParseval
