import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# ErdosGyarfasMinCexCubicNeighbour — in a minimal counterexample, every vertex has a cubic neighbour

Structure of a hypothetical minimal counterexample to the Erdős–Gyárfás conjecture (Jig problem
399, Erdős #64): if `G` is a counterexample of minimum order and then minimum size, every vertex
is adjacent to a vertex of degree exactly `3`. If all neighbours of `u` had degree at least `4`,
then either `u` has degree at least `4` (contradicting the independence of high-degree vertices)
or deleting `u` leaves a smaller graph with all degrees at least `3` and no new cycles. Carr,
arXiv:2605.22844, Lemma 2(ii); also in Bisch's note. Vacuous if the conjecture is true.

Submissions **must not** import this module: `target` below is closed with `sorry`.
-/

namespace Statements.ErdosGyarfasMinCexCubicNeighbour

/-- `G` contains a cycle whose length is `2 ^ k` for some `k ≥ 2` (the conclusion of the root
statement `Statements.ErdosGyarfasPowerTwoCycle`). -/
def HasPow2Cycle {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ (v : Fin n) (c : G.Walk v v) (k : ℕ), c.IsCycle ∧ 2 ≤ k ∧ c.length = 2 ^ k

/-- A counterexample to the Erdős–Gyárfás conjecture: a nonempty finite simple graph with every
degree at least `3` and no power-of-two cycle. -/
def IsCex {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  0 < n ∧ (∀ v : Fin n, 3 ≤ G.degree v) ∧ ¬ HasPow2Cycle G

/-- A minimal counterexample: a counterexample that is lexicographically minimal in
(order, size) among all counterexamples on any `Fin m`. If the conjecture is true no such graph
exists, and every statement about `IsMinCex` is a statement about the structure a counterexample
would have to have. -/
def IsMinCex {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  IsCex G ∧ ∀ (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj], IsCex H →
    n < m ∨ (n = m ∧ G.edgeFinset.card ≤ H.edgeFinset.card)

/-- The canonical proposition. -/
abbrev statement : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], IsMinCex G →
    ∀ u : Fin n, ∃ w : Fin n, G.Adj u w ∧ G.degree w = 3

/-- The target. A submission proves `statement` in its own module; the verifier bridges the two. -/
theorem target : statement := sorry

end Statements.ErdosGyarfasMinCexCubicNeighbour
