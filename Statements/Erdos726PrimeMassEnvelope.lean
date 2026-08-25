import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic

namespace Statements.Erdos726PrimeMassEnvelope

open Nat Finset

noncomputable def selectedMass (n : ℕ) : ℝ :=
  ∑ p ∈ (range (n + 1)).filter
    (fun p : ℕ => p.Prime ∧ (p : ℝ) / 2 < ((n % p : ℕ) : ℝ)),
    (1 : ℝ) / (p : ℝ)

noncomputable def primeMass (n : ℕ) : ℝ :=
  ∑ p ∈ (range (n + 1)).filter Nat.Prime, (1 : ℝ) / (p : ℝ)

/-- The selected mass is pointwise nonnegative and bounded by the full
reciprocal-prime mass appearing in Mertens' estimate. -/
abbrev statement : Prop :=
  ∀ n : ℕ,
    0 ≤
      (∑ p ∈ (range (n + 1)).filter
        (fun p : ℕ => p.Prime ∧ (p : ℝ) / 2 < ((n % p : ℕ) : ℝ)),
        (1 : ℝ) / (p : ℝ)) ∧
    (∑ p ∈ (range (n + 1)).filter
        (fun p : ℕ => p.Prime ∧ (p : ℝ) / 2 < ((n % p : ℕ) : ℝ)),
        (1 : ℝ) / (p : ℝ)) ≤
      ∑ p ∈ (range (n + 1)).filter Nat.Prime, (1 : ℝ) / (p : ℝ)

theorem target : statement := sorry

end Statements.Erdos726PrimeMassEnvelope
