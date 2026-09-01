import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-!
# SeedSufficesForMixedMinUPBSatisfiable

Scope-corrected replacement for `SeedSufficesForMixedMinUPB`, which repeated
at `k = 3` the same landmine shape that forced the retraction of statement 38
at `k = 2`: its hypothesis demands `seedExists k m` for every `k ≥ 3` and
every even `m > 2k`, hence in particular `seedExists 3 8` — and no such seed
exists (`NoSeedK3M8`: a tight family in `C^3` admits no 4-cycle in its exact
orthogonality graph, since two vertices with two independent common
neighbours `a, b` both lie in the line `a^⊥ ∩ b^⊥`; and all 19,355 labelled
cubic graphs on 8 vertices contain a 4-cycle). As filed,
`SeedSufficesForMixedMinUPB` is therefore vacuously provable and
undischargeable. This statement is the same implication with the single
impossible instance `(k, m) = (3, 8)` excluded from the seed supply; nothing
else changes. The `k = 3` row from `m = 10` onwards is witnessed on this
board (Petersen at `m = 10`, Tietze at `m = 12`, explicit C4-free cubic
graphs at `m = 14, 16, 18`), and for `k ≥ 4` the C4 obstruction has no
analogue at `m = 2k + 2` that is known.

The definitions below are verbatim those of `SeedSufficesForMixedMinUPB`.
-/

namespace Statements.SeedSufficesForMixedMinUPBSatisfiable

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
  (∀ k m : ℕ, 3 ≤ k → m % 2 = 0 → 2 * k < m → ¬ (k = 3 ∧ m = 8) →
    seedExists k m) →
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

end Statements.SeedSufficesForMixedMinUPBSatisfiable
