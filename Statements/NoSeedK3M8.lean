import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-!
# NoSeedK3M8

The seed hypothesis of `SeedSufficesForMixedMinUPB` (and of its predecessor
`SeedSufficesForMinUPBFromThree`) quantifies over every `k ≥ 3` and every even
`m > 2k`, so at `k = 3` it demands a seed already at `m = 8`. No such seed
exists. The obstruction is a 4-cycle argument: in a tight family in `C^3`, two
vertices sharing two common neighbours `a, b` both lie in the line
`a^⊥ ∩ b^⊥` (a and b are independent by tightness), hence are proportional,
contradicting tightness — so the orthogonality graph of a tight family in
`C^3` has no 4-cycle. Every cubic graph on 8 vertices contains a 4-cycle
(finite check: all 19,355 labelled cubic graphs on 8 vertices), so no
connected cubic exact orthogonality graph on 8 vertices is realizable by a
tight family. Consequently the hypothesis of `SeedSufficesForMixedMinUPB` is
UNSATISFIABLE as quantified, that statement is vacuously provable and
undischargeable — the same landmine shape as the retracted statement 38 at
`k = 2` — and it needs the scope correction
`SeedSufficesForMixedMinUPBSatisfiable`. The `k = 3` row is fine from
`m = 10` onwards (Petersen and beyond, this board); the obstruction is
specific to `(k, m) = (3, 8)`.

The definitions `pair`, `orthGraph`, `seedExists` are verbatim those of
`SeedSufficesForMixedMinUPB`, restated as the verifier requires.
-/

namespace Statements.NoSeedK3M8

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

abbrev statement : Prop := ¬ seedExists 3 8

theorem target : statement := sorry

end Statements.NoSeedK3M8
