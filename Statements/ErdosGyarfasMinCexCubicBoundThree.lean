import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# ErdosGyarfasMinCexCubicBoundThree — the contraction graph of a minimal counterexample is 2-degenerate

Structure of a hypothetical minimal counterexample to the Erdős–Gyárfás conjecture (Jig problem
399, Erdős #64): if `G` is a counterexample of minimum order and then minimum size, then
`2 n + 3 ≤ 3 |{v : deg v = 3}|`. This sharpens the strict two-thirds bound
(`Statements.ErdosGyarfasMinCexCubicStrict`, `2 n + 1 ≤ 3 |V₃|`) by the following mechanism.
Let `V₄` be the (independent) set of vertices of degree at least `4` and `H` the simple graph on
`V₄` with one edge `u u'` for every cubic vertex `x` whose two high-degree neighbours are `u, u'`
(distinct cubic vertices give distinct pairs, since `G` has no 4-cycle). Every cycle of `H`
lifts to a cycle of twice the length in `G`, so no nonempty induced subgraph of `H` can have all
degrees at least `3` (it would be a smaller graph with `δ ≥ 3`, hence by minimality it would
contain a `2^k`-cycle, which lifts to a `2^(k+1)`-cycle of `G`). Thus `H` is 2-degenerate and
has at most `2 |V₄| - 3` edges when `|V₄| ≥ 2`. Counting the edges between `V₄` and the cubic
vertices then gives `|V₃| ≥ 2 |V₄| + 3`; the cases `|V₄| ≤ 1` follow from `n ≥ 8`
(`Statements.ErdosGyarfasSmallOrderC4`). Proposed by the poser on 2026-09-04 with this informal
proof; not yet kernel-checked. Vacuous if the conjecture is true.

Submissions **must not** import this module: `target` below is closed with `sorry`.
-/

namespace Statements.ErdosGyarfasMinCexCubicBoundThree

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
    2 * n + 3 ≤ 3 * (Finset.univ.filter (fun v => G.degree v = 3)).card

/-- The target. A submission proves `statement` in its own module; the verifier bridges the two. -/
theorem target : statement := sorry

end Statements.ErdosGyarfasMinCexCubicBoundThree
