import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Prime.Basic

open scoped Pointwise

namespace Statements.Erdos52ValuationMaxPlus

private def scale (c : ℕ) (S : Finset ℕ) : Finset ℕ :=
  S.image fun x => c * x

private def indices (m : ℕ) : Finset (ℕ × ℕ) :=
  Finset.range m ×ˢ Finset.range m

private def totals (m : ℕ) : Finset ℕ :=
  (indices m).image fun p => p.1 + p.2

private def fiber (q m : ℕ) (L : ℕ → Finset ℕ) (k : ℕ) : Finset ℕ :=
  ((indices m).filter fun p => p.1 + p.2 = k).biUnion fun p =>
    scale (q ^ k) (L p.1 * L p.2)

private def profile (m : ℕ) (L : ℕ → Finset ℕ) (k : ℕ) : ℕ :=
  ((indices m).filter fun p => p.1 + p.2 = k).sup fun p =>
    (L p.1 * L p.2).card

private def layeredSet (q m : ℕ) (L : ℕ → Finset ℕ) : Finset ℕ :=
  (Finset.range m).biUnion fun i => scale (q ^ i) (L i)

/--
An arbitrary finite family of `q`-valuation layers decomposes its product set
exactly by total valuation.  Consequently the product set dominates the sum
of the max-plus convolution of the layer product cardinalities.
-/
abbrev statement : Prop :=
  ∀ (q m : ℕ) (L : ℕ → Finset ℕ), q.Prime →
    (∀ i < m, ∀ x ∈ L i, ¬q ∣ x) →
    let A := layeredSet q m L
    let K := totals m
    let F := fiber q m L
    A * A = K.biUnion F ∧
      ∑ k ∈ K, profile m L k ≤ (A * A).card

theorem target : statement := sorry

end Statements.Erdos52ValuationMaxPlus
