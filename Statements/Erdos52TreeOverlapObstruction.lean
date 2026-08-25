import Mathlib.Algebra.Group.Pointwise.Finset.Basic

open scoped Pointwise

namespace Statements.Erdos52TreeOverlapObstruction

private def upper (n : ℕ) : Finset ℕ :=
  (Finset.range n).image fun k => 3 * k + 1

private def lower (n : ℕ) : Finset ℕ :=
  {1, 2} ∪ (Finset.range n).image fun k => 9 * k + 2

private def crossSums (n : ℕ) : Finset ℕ :=
  (Finset.range n).image fun k => 9 * k + 4

private def scale (c : ℕ) (S : Finset ℕ) : Finset ℕ :=
  S.image fun x => c * x

/--
There are arbitrarily large families of first-separation sums at a
`3`-valuation node which all coincide with sums internal to the lower child.
-/
abbrev statement : Prop :=
  ∀ n : ℕ,
    (∀ x ∈ lower n, ¬3 ∣ x) ∧
    (∀ y ∈ upper n, ¬3 ∣ y) ∧
    (crossSums n).card = n ∧
    crossSums n ⊆ lower n + lower n ∧
    crossSums n ⊆ ({1} : Finset ℕ) + scale 3 (upper n)

theorem target : statement := sorry

end Statements.Erdos52TreeOverlapObstruction
