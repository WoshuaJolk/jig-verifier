import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum

open scoped BigOperators ComplexConjugate ZMod

namespace Statements.Erdos1CrossSliceFourierEnergy

/-- Averaging the marked subset characteristic-function product over a phase
isolates all cardinality slices. Parseval then gives their total collision
energy and its sharp integral floor. -/
abbrev statement : Prop :=
  ∀ (q : ℕ) [NeZero q] (A : Finset ℕ),
    let m := A.card + 1
    let P : ZMod m → ZMod q → ℂ := fun u k =>
      ∏ a ∈ A, (1 + ZMod.stdAddChar (-u) *
        ZMod.stdAddChar (-((a : ZMod q) * k)))
    let F : ℕ → ZMod q → ℂ := fun j k =>
      ∑ S ∈ A.powersetCard j,
        ZMod.stdAddChar (-(((S.sum id : ℕ) : ZMod q) * k))
    let c : ℕ → ZMod q → ℕ := fun j r =>
      ((A.powersetCard j).filter fun S => ((S.sum id : ℕ) : ZMod q) = r).card
    (∀ k : ZMod q,
      ∑ u : ZMod m, conj (P u k) * P u k =
        (m : ℂ) * ∑ j ∈ Finset.range m, conj (F j k) * F j k) ∧
    (∑ k : ZMod q, ∑ u : ZMod m, conj (P u k) * P u k =
      (m : ℂ) * (q : ℂ) *
        ∑ j ∈ Finset.range m, ∑ r : ZMod q, ((c j r : ℂ) ^ 2)) ∧
    (∑ j ∈ Finset.range m,
        (let M := Nat.choose A.card j
         M ^ 2 + (M % q) * (q - M % q)) ≤
      q * ∑ j ∈ Finset.range m, ∑ r : ZMod q, (c j r) ^ 2) ∧
    (let Q := 2 ^ A.card + 1
     ∑ j ∈ Finset.range m,
        (let M := Nat.choose A.card j
         M ^ 2 + (M % Q) * (Q - M % Q)) = Q * 2 ^ A.card)

theorem target : statement := sorry

end Statements.Erdos1CrossSliceFourierEnergy
