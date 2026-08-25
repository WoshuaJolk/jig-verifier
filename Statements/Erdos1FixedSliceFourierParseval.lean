import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Finset.Powerset

open scoped BigOperators ComplexConjugate ZMod Polynomial

namespace Statements.Erdos1FixedSliceFourierParseval

/-- The marker-polynomial formula, Parseval identity, and integral energy floor
for one fixed-cardinality slice of the subset sums. -/
abbrev statement : Prop :=
  ∀ (q : ℕ) [NeZero q] (A : Finset ℕ) (j : ℕ),
    let P : ZMod q → ℂ[X] := fun k =>
      ∏ a ∈ A, (1 + Polynomial.C (ZMod.stdAddChar (-((a : ZMod q) * k))) *
        Polynomial.X)
    let c : ZMod q → ℕ := fun r =>
      ((A.powersetCard j).filter fun S => ((S.sum id : ℕ) : ZMod q) = r).card
    (∀ k : ZMod q, (P k).coeff j =
      ∑ S ∈ A.powersetCard j,
        ZMod.stdAddChar (-(((S.sum id : ℕ) : ZMod q) * k))) ∧
    (∑ k : ZMod q, conj ((P k).coeff j) * (P k).coeff j =
      (q : ℂ) * ∑ r : ZMod q, ((c r : ℂ) ^ 2)) ∧
    (let M := Nat.choose A.card j
     M ^ 2 + (M % q) * (q - M % q) ≤ q * ∑ r : ZMod q, (c r) ^ 2)

theorem target : statement := sorry

end Statements.Erdos1FixedSliceFourierParseval
