import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# ErdosGyarfasMinCexCubicStrict — strictly more than two thirds of a minimal counterexample is cubic

Structure of a hypothetical minimal counterexample to the Erdős–Gyárfás conjecture (Jig problem
399, Erdős #64): if `G` is a counterexample of minimum order and then minimum size, then
`2 n < 3 |{v : deg v = 3}|`. Counting edges between the cubic vertices and the vertices of degree
at least `4` (which are independent, and every vertex has a cubic neighbour) gives
`2 n ≤ 3 |V₃|` (Carr: `4/7`; Bisch, Zenodo 10.5281/zenodo.21574476: `2/3`). Equality would force
every high-degree vertex to have degree exactly `4` and every cubic vertex to have exactly two
high-degree neighbours; contracting each cubic vertex to an edge between its two high-degree
neighbours then yields a simple 4-regular graph on fewer vertices, whose power-of-two cycle
(forced by minimality) lifts to a cycle of twice the length in `G`. The strict inequality was
proposed in a forum comment on erdosproblems.com/64 (26 July 2026, unverified there). Vacuous if
the conjecture is true.

Submissions **must not** import this module: `target` below is closed with `sorry`.
-/

namespace Statements.ErdosGyarfasMinCexCubicStrict

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
    2 * n < 3 * (Finset.univ.filter (fun v => G.degree v = 3)).card

/-- The target. A submission proves `statement` in its own module; the verifier bridges the two. -/
theorem target : statement := sorry

end Statements.ErdosGyarfasMinCexCubicStrict
