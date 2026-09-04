import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# ErdosGyarfasPowerTwoCycle — the Erdős–Gyárfás conjecture (Erdős problem #64)

Does every finite graph with minimum degree at least 3 contain a cycle of length `2^k`
for some `k ≥ 2`?

Source: erdosproblems.com/64. Conjectured by Erdős and Gyárfás; stated by Erdős in
[Er93, p.343], [Er94b], [Er95, p.174], [Er96], [Er97b], [Er97c].

A finite graph is modelled as a simple graph on `Fin n` with `0 < n`; the guard is
load-bearing, since without it the `n = 0` instance is false (vacuous hypothesis, no vertex).
The minimum-degree hypothesis is `∀ v, 3 ≤ G.degree v`, which for `0 < n` is equivalent to
`3 ≤ G.minDegree`. A cycle is a `SimpleGraph.Walk.IsCycle` closed walk (a simple cycle: a
closed trail repeating no vertex except its endpoint), and its length is the number of
edges; `2 ^ k` with `2 ≤ k` ranges over `4, 8, 16, …`. The bound `2 ≤ k` is mathematically
redundant, because `IsCycle` already forces length `≥ 3`; it is kept to mirror the source.

The target is the affirmative answer. Erdős and Gyárfás expected the answer to be negative;
a finite counterexample is filed on Jig as a separate statement refuting this one.

Submissions **must not** import this module: `target` below is closed with `sorry`.
-/

namespace Statements.ErdosGyarfasPowerTwoCycle

/-- The canonical proposition. Every simple graph on a nonempty finite vertex set `Fin n`
in which every vertex has degree at least `3` contains a cycle whose length is `2 ^ k` for
some `k ≥ 2`. -/
abbrev statement : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    0 < n → (∀ v : Fin n, 3 ≤ G.degree v) →
      ∃ (v : Fin n) (c : G.Walk v v) (k : ℕ), c.IsCycle ∧ 2 ≤ k ∧ c.length = 2 ^ k

/-- The open target. Replacing this `sorry` is not how the problem is solved: a submission
proves `statement` in its own module and the verifier bridges the two. -/
theorem target : statement := sorry

end Statements.ErdosGyarfasPowerTwoCycle
