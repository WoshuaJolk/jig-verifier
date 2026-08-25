import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Prime.Basic

open scoped Pointwise

namespace Statements.Erdos52CrossLayerAdditive

private def scale (c : ℕ) (S : Finset ℕ) : Finset ℕ :=
  S.image fun x => c * x

private def layeredSet (q m : ℕ) (L : ℕ → Finset ℕ) : Finset ℕ :=
  (Finset.range m).biUnion fun i => scale (q ^ i) (L i)

private def orderedLayers (m : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range m ×ˢ Finset.range m).filter fun p => p.1 < p.2

/--
Fixing one anchor in every nonempty `q`-free valuation layer produces an
injective family of sums from every ordered pair of distinct layers.
-/
abbrev statement : Prop :=
  ∀ (q m : ℕ) (L : ℕ → Finset ℕ) (x : ℕ → ℕ), q.Prime →
    (∀ i < m, ∀ y ∈ L i, ¬q ∣ y) →
    (∀ i < m, x i ∈ L i) →
    let A := layeredSet q m L
    ∑ p ∈ orderedLayers m, (L p.2).card ≤ (A + A).card

theorem target : statement := sorry

end Statements.Erdos52CrossLayerAdditive
