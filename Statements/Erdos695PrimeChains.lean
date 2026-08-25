import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter

namespace Statements.Erdos695PrimeChains

def IsPrimeChain (p : ℕ → ℕ) : Prop :=
  StrictMono p ∧
  (∀ i, (p i).Prime) ∧
  ∀ i, p (i + 1) ≡ 1 [MOD p i]

/-- Erdős 695: every prime chain has superexponential root growth, and
some prime chain has the conjecturally near-minimal upper growth rate. -/
abbrev statement : Prop :=
  (∀ p : ℕ → ℕ, IsPrimeChain p →
    Tendsto
      (fun k : ℕ => (p k : ℝ) ^ ((1 : ℝ) / (k + 1 : ℕ)))
      atTop atTop) ∧
  (∃ p : ℕ → ℕ, IsPrimeChain p ∧
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (nhds 0) ∧
      ∀ᶠ k : ℕ in atTop,
        (p k : ℝ) ≤
          Real.exp ((k + 1 : ℕ) *
            (Real.log (k + 1 : ℕ)) ^ (1 + ε k)))

theorem target : statement := sorry

end Statements.Erdos695PrimeChains
