import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Interval.Set.Nat
import Mathlib.Topology.Instances.Nat

namespace Statements.Erdos962SubpolynomialBlockLength

open Filter Real

def HasLargePrimeBlock (n width : ℕ) : Prop :=
  ∃ start ≤ n, ∀ offset ∈ Set.Icc 1 width,
    ∃ p : ℕ, p.Prime ∧ width < p ∧ p ∣ start + offset

noncomputable def maxWidth (n : ℕ) : ℕ :=
  open scoped Classical in
  Nat.findGreatest (fun width => HasLargePrimeBlock n width) n

/-- Erdős Problem 962: `log(maxWidth n)` is eventually at most
`(log n)^(1/2+o(1))`. -/
abbrev statement : Prop :=
  ∃ error : ℕ → ℝ,
    (∀ δ > 0, ∀ᶠ n in atTop, |error n| < δ) ∧
      ∀ᶠ n : ℕ in atTop,
        log (maxWidth n : ℝ) ≤
          rpow (log n) ((1 : ℝ) / 2 + error n)

theorem target : statement := sorry

end Statements.Erdos962SubpolynomialBlockLength
