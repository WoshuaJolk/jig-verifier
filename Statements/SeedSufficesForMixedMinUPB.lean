import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-!
# SeedSufficesForMixedMinUPB

Scope-corrected replacement for `SeedSufficesForMinUPBFromThree`. The old
conditional conclusion repeated the superseded P14 root and therefore still
claimed a ten-state UPB on eight qubits. This version concludes only the
genuinely mixed-dimensional root.
-/

namespace Statements.SeedSufficesForMixedMinUPB

def pair {k : ℕ} (x y : Fin k → ℂ) : ℂ :=
  ∑ r, star (x r) * y r

def orthGraph {k m : ℕ} (v : Fin m → Fin k → ℂ) :
    SimpleGraph (Fin m) :=
  SimpleGraph.fromRel fun i i' => pair (v i) (v i') = 0

def seedExists (k m : ℕ) : Prop :=
  ∃ v : Fin m → Fin k → ℂ, ∃ N : Fin m → Finset (Fin m),
    (∀ i, v i ≠ 0) ∧
    (∀ i i', pair (v i) (v i') = 0 ↔ i' ∈ N i) ∧
    (∀ i, (N i).card = k) ∧
    (orthGraph v).Connected ∧
    (∀ S : Finset (Fin m), S.card + 1 ≤ k →
      LinearIndependent ℂ fun i : (S : Set (Fin m)) => v i) ∧
    (∀ S : Finset (Fin m), S.card = k + 1 →
      ∀ a : Fin k → ℂ, a ≠ 0 →
      ∃ i ∈ S, pair a (v i) ≠ 0)

abbrev statement : Prop :=
  (∀ k m : ℕ, 3 ≤ k → m % 2 = 0 → 2 * k < m → seedExists k m) →
  ∀ p : ℕ, 2 ≤ p → ∀ d : Fin p → ℕ, (∀ j, 2 ≤ d j) →
    ¬ (p = 2 ∧ ∃ j, d j = 2) →
    ¬ (∀ j, d j = 2) →
    ∃ m : ℕ, m ≤ 2 + ∑ j, (d j - 1) ∧
      ∃ v : Fin m → (j : Fin p) → Fin (d j) → ℂ,
        (∀ i j, v i j ≠ 0) ∧
        (∀ i i', i ≠ i' →
          ∃ j, (∑ r, star (v i j r) * v i' j r) = 0) ∧
        (∀ a : (j : Fin p) → Fin (d j) → ℂ,
          (∀ j, a j ≠ 0) →
          ∃ i, ∀ j, (∑ r, star (v i j r) * a j r) ≠ 0)

theorem target : statement := sorry

end Statements.SeedSufficesForMixedMinUPB
