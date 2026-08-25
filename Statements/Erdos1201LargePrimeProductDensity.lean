import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Order.LiminfLimsup

namespace Statements.Erdos1201LargePrimeProductDensity

open Nat Filter Finset

noncomputable def largePrimeSet (ε : ℝ) (k : ℕ) : Set ℕ :=
  {n : ℕ |
    ((sSup {p : ℕ | p.Prime ∧ p ∣ ∏ i ∈ range (k + 1), (n + i)} : ℕ) : ℝ) >
      (n : ℝ) ^ (1 - ε)}

noncomputable def countLarge (ε : ℝ) (k x : ℕ) : ℕ := by
  classical
  exact ((Finset.range x).filter fun n ↦ n ∈ largePrimeSet ε k).card

/-- Erdős Problem 1201: a long enough block almost always has a prime
factor exceeding `n^(1-ε)`. -/
abbrev statement : Prop :=
  ∀ ε > 0, ∀ η > 0, ∃ k : ℕ,
    atTop.liminf (fun x : ℕ ↦
      (((countLarge ε k x : ℝ) / (x : ℝ)) : EReal)) ≥
        (1 - η : EReal)

theorem target : statement := sorry

end Statements.Erdos1201LargePrimeProductDensity
