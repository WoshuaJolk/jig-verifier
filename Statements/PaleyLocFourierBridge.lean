import Commons.PaleyLocalizationTheta
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Exact Fourier extraction for both Paley localization graph sides

For every prime p congruent to 1 modulo 4, choose exact cyclic coordinates on
its nonzero squares once, independently of the side and feasible matrix.
Every real theta-feasible matrix yields a probability on all standard cyclic
characters. Its character sums vanish off the allowed graph mask, and its
objective is m times the trivial-character mass, where m=(p-1)/2.

Here side=false allows paleyLocAdj edges; side=true allows its simple-graph
complement edges. The condition on X is exactly zeros at distinct nonedges.
The Fourier zeros exclude t=0, where the probability sum is 1. Both the
nonzero cyclic order and its coordinates are conclusions, not assumptions.
This is a finite forward reduction; no prime-specific atom estimate, reverse
construction, optimizer attainment or asymptotic bound is asserted.
-/

open Commons

namespace Statements.PaleyLocFourierBridge

abbrev statement : Prop :=
  ∀ (p : ℕ) (hp : Nat.Prime p) (hp4 : p % 4 = 1),
    letI : Fact (Nat.Prime p) := ⟨hp⟩
    letI : NeZero p := NeZero.of_pos hp.pos
    ∃ hn : 0 < (p - 1) / 2,
    letI : NeZero ((p - 1) / 2) := NeZero.of_pos hn
    ∃ e : ZMod ((p - 1) / 2) ≃ PaleyLocV p,
      (e 0 : ZMod p) = 1 ∧
      (∀ a b, (e (a - b) : ZMod p) = (e a : ZMod p) / (e b : ZMod p)) ∧
      ∀ (side : Bool) (X : Matrix (PaleyLocV p) (PaleyLocV p) ℝ),
        X.PosSemidef → X.trace = 1 →
        (∀ u v, u ≠ v →
          ¬ (if side then (u ≠ v ∧ ¬ paleyLocAdj p u v) else paleyLocAdj p u v) →
          X u v = 0) →
        ∃ μ : ZMod ((p - 1) / 2) → ℝ,
          (∀ j, 0 ≤ μ j) ∧ (∑ j, μ j) = 1 ∧
          (∀ t, t ≠ 0 →
            ¬ (if side then ¬ IsNonzeroSq (1 - (e t : ZMod p))
                else IsNonzeroSq (1 - (e t : ZMod p))) →
            (∑ j, (μ j : ℂ) * ZMod.stdAddChar (j*t)) = 0) ∧
          (∑ u, ∑ v, X u v) = (((p - 1) / 2 : ℕ) : ℝ) * μ 0

theorem target : statement := sorry

end Statements.PaleyLocFourierBridge
