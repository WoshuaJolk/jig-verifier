import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Statements.J5P407OrderedReserve

open scoped BigOperators

noncomputable def mass {ι : Type*} (w : ι → ℝ) (s : Finset ι) : ℝ := ∑ i ∈ s, w i

noncomputable def upperTail {ι : Type*} (key : ι → ℝ) (q : ℝ) (s : Finset ι) : Finset ι :=
  s.filter fun i => q ≤ key i

/-- Conditional finite weighted-set transfer only; analytic/coloring inputs remain hypotheses. -/
abbrev statement : Prop :=
  ∀ {ι : Type} [DecidableEq ι]
    {w key : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    {O I S T H B R C : Finset ι} {q tau Delta : ℝ}
    (hcover : ∀ i ∈ O, i ∈ I ∨ i ∈ S ∨ i ∈ T ∨ i ∈ H)
    (hlow : ∀ i ∈ H, key i < q)
    (hselected : mass w S < 1) (htop : mass w T < 64 + tau)
    (htau : tau < 1 / 8) (hDelta : Delta < 1 / 8)
    (hRB : R ⊆ B)
    (horder : ∀ i ∈ C, ∀ j ∈ R \ C, key i ≤ key j)
    (hsupply : 1 + Delta < mass w (R \ C))
    (hsmall : mass w (upperTail key q (B \ C)) < 1 + Delta)
    (hbalance : |mass w (upperTail key q B) - mass w (upperTail key q I) / 2| < 1 / 8),
    mass w (upperTail key q O) < 68

end Statements.J5P407OrderedReserve
