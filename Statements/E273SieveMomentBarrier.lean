import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Statements.E273SieveMomentBarrier

open scoped BigOperators

/-- All allowed moduli with successor prime at most 100000. -/
def pool : Finset ℕ :=
  (Finset.range 100000).filter (fun d => 4 ≤ d ∧ Nat.Prime (d + 1))

def largestPrime (d : ℕ) : ℕ := d.primeFactors.sup id

def cofactor (d : ℕ) : ℕ := d / largestPrime d ^ d.factorization (largestPrime d)

def group (q : ℕ) : Finset ℕ := pool.filter (fun d => largestPrime d = q)

noncomputable def distortion (δ : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∏ r ∈ m.primeFactors, (1 - δ r)⁻¹

/-- Residue-independent first-moment upper bound, not the actual moment. -/
noncomputable def firstBound (δ : ℕ → ℝ) (q : ℕ) : ℝ :=
  ∑ d ∈ group q, distortion δ (cofactor d) / (d : ℝ)

/-- Residue-independent second-moment upper bound, not the actual moment. -/
noncomputable def secondBound (δ : ℕ → ℝ) (q : ℕ) : ℝ :=
  ∑ d ∈ group q, ∑ e ∈ group q,
    distortion δ (Nat.lcm (cofactor d) (cofactor e)) *
      (Nat.gcd (cofactor d) (cofactor e) : ℝ) / ((d : ℝ) * (e : ℝ))

/-- At zero distortion use the first-moment branch. -/
noncomputable def criterion (δ : ℕ → ℝ) : ℝ :=
  ∑ q ∈ pool.image largestPrime,
    if δ q = 0 then firstBound δ q
    else min (firstBound δ q) (secondBound δ q / (4 * δ q * (1 - δ q)))

/-- This particular plugged-in bound cannot certify noncoverage of the full pool. -/
abbrev statement : Prop :=
  ∀ δ : ℕ → ℝ, (∀ q, 0 ≤ δ q ∧ δ q ≤ 1 / 2) → 1 < criterion δ

theorem target : statement := sorry

end Statements.E273SieveMomentBarrier
