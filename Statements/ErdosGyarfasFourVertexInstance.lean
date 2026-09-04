import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# ErdosGyarfasFourVertexInstance — the `n = 4` instance of the Erdős–Gyárfás conjecture

The four-vertex boundary case of `Statements.ErdosGyarfasPowerTwoCycle` (Erdős problem #64):
every simple graph on `Fin 4` in which every vertex has degree at least `3` contains a cycle
of length `2 ^ k` for some `k ≥ 2`. Four vertices is the smallest order on which the degree
hypothesis is satisfiable, and the only such graph is `K₄`, whose Hamiltonian cycle has
length `4 = 2 ^ 2`. This statement exists to exercise the verifier of the root problem; it is
literally the root proposition instantiated at `n = 4`.

Submissions **must not** import this module: `target` below is closed with `sorry`.
-/

namespace Statements.ErdosGyarfasFourVertexInstance

/-- The canonical proposition: the `n = 4` instance of the Erdős–Gyárfás conjecture. -/
abbrev statement : Prop :=
  ∀ (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj],
    (∀ v : Fin 4, 3 ≤ G.degree v) →
      ∃ (v : Fin 4) (c : G.Walk v v) (k : ℕ), c.IsCycle ∧ 2 ≤ k ∧ c.length = 2 ^ k

/-- The target. A submission proves `statement` in its own module; the verifier bridges
the two. -/
theorem target : statement := sorry

end Statements.ErdosGyarfasFourVertexInstance
