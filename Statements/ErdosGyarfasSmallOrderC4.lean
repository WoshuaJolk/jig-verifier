import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# ErdosGyarfasSmallOrderC4 — graphs of minimum degree 3 on at most 7 vertices have a 4-cycle

A kernel-checked piece of the `small-order` obligation of Jig problem 399 (Erdős #64): every
simple graph on `n ≤ 7` vertices in which every vertex has degree at least `3` contains a
4-cycle, hence a cycle of length `2 ^ 2`. The informal proof double-counts "cherries"
(a vertex with two of its neighbours): without a 4-cycle two vertices have at most one common
neighbour, so `Σ_v C(deg v, 2) ≤ C(n, 2)`, while `deg v ≥ 3` gives `Σ_v C(deg v, 2) ≥ 3n`;
this forces `n ≥ 7`, and at `n = 7` every degree must be exactly `3`, contradicting the
handshake lemma. The bound `7` is sharp for this argument only; the Petersen graph shows that
from `n = 10` on a 4-cycle is not forced, and every graph with `δ ≥ 3` on `n ≤ 9` vertices
still has one by the extremal numbers `ex(n, C₄)`, which this statement does not cover.

Submissions **must not** import this module: `target` below is closed with `sorry`.
-/

namespace Statements.ErdosGyarfasSmallOrderC4

/-- The canonical proposition. -/
abbrev statement : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    0 < n → n ≤ 7 → (∀ v : Fin n, 3 ≤ G.degree v) →
      ∃ (v : Fin n) (c : G.Walk v v), c.IsCycle ∧ c.length = 4

/-- The target. A submission proves `statement` in its own module; the verifier bridges the two. -/
theorem target : statement := sorry

end Statements.ErdosGyarfasSmallOrderC4
