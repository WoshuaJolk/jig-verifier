import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

namespace Statements.Erdos788ChoiSumAvoidance

open Filter

def InUpperInterval (n : ℕ) (B : Finset ℕ) : Prop :=
  ∀ b ∈ B, 2 * n < b ∧ b < 4 * n

def InLowerInterval (n : ℕ) (C : Finset ℕ) : Prop :=
  ∀ c ∈ C, n < c ∧ c < 2 * n

def AvoidsDistinctSums (B C : Finset ℕ) : Prop :=
  ∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ ≠ c₂ → c₁ + c₂ ∉ B

noncomputable def bestForUpperSet (n : ℕ) (B : Finset ℕ) : ℕ :=
  sSup {m : ℕ | ∃ C : Finset ℕ,
    InLowerInterval n C ∧ AvoidsDistinctSums B C ∧
      m = C.card + B.card}

noncomputable def choiFunction (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ B : Finset ℕ,
    InUpperInterval n B ∧ bestForUpperSet n B = m}

/-- Erdős problem 788: Choi's conjectured square-root upper exponent. -/
abbrev statement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ n : ℕ in atTop,
      (choiFunction n : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 2 + ε)

theorem target : statement := sorry

end Statements.Erdos788ChoiSumAvoidance
