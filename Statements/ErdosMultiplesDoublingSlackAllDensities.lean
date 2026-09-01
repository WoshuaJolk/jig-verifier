import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# ErdosMultiplesDoublingSlackAllDensities — no density threshold rescues Conjecture 6.11

Strengthening of `ErdosMultiplesDoublingSparseSlackRefuted`: the union-bound inequality (10)

  `∑_{g ∈ G} ⌊n/g⌋ + |G| ≤ 2 f_G(n)`

of Chojecki (https://www.ulam.ai/research/erdos488.pdf, Prop. 6.5 / Conj. 6.11) fails for primitive
`G` of *arbitrarily small* density `f_G(n)/n`: for every `c ≥ 1` there is a primitive `G` and
`n ≥ max G` with `f_G(n)/n ≤ 1/(4c)` and (10) false.  So the conjecture cannot be repaired by
replacing the sparse threshold `1/2` in his (9) by any smaller positive constant.

Submissions **must not** import this module.
-/

namespace Statements.ErdosMultiplesDoublingSlackAllDensities

/-- For every `c ≥ 1`: a primitive `G ⊆ {2,3,…}` and `n ≥ max G` with density `≤ 1/(4c)` at which
Chojecki's inequality (10) fails. -/
abbrev statement : Prop :=
  ∀ c : ℕ, 0 < c →
    ∃ G : Finset ℕ,
      (∀ g ∈ G, 2 ≤ g) ∧
      (∀ a ∈ G, ∀ b ∈ G, a ∣ b → a = b) ∧
      ∃ n : ℕ, (∀ g ∈ G, g ≤ n) ∧
        4 * c * ((Finset.Icc 1 n).filter (fun k => ∃ g ∈ G, g ∣ k)).card ≤ n ∧
        2 * ((Finset.Icc 1 n).filter (fun k => ∃ g ∈ G, g ∣ k)).card <
          (∑ g ∈ G, n / g) + G.card

theorem target : statement := sorry

end Statements.ErdosMultiplesDoublingSlackAllDensities
