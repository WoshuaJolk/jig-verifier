import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
Finite-order reduction for the +4 cubic-count equality case.
This is conditional on a hypothetical lexicographically minimal counterexample.
No existence or exclusion of all small graphs is asserted. Novelty unverified.
Submissions must not import this canonical module.
-/

namespace Statements.ErdosGyarfasBoundaryFourOrder

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
    3 * (Finset.univ.filter (fun v => G.degree v = 3)).card = 2 * n + 4 → n ≤ 19

/-- The target. A submission proves `statement` in its own module; the verifier bridges the two. -/
theorem target : statement := sorry

end Statements.ErdosGyarfasBoundaryFourOrder


