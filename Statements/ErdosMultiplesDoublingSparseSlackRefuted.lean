import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# ErdosMultiplesDoublingSparseSlackRefuted — Chojecki's sparse order-slack conjecture is false

Chojecki, "Signed Transport, Pair–Tail Reduction, and Low Layers in an Erdős Density-Doubling
Problem" (20 March 2026, https://www.ulam.ai/research/erdos488.pdf), Conjecture 6.11 asserts
that for every primitive finite `G ⊆ {2, 3, …}` and every `n ≥ max G` in the *sparse regime*
`f_G(n)/n < 1/2` (his (9)), the union-bound inequality (10)

  `∑_{g ∈ G} ⌊n/g⌋ + |G| ≤ 2 f_G(n)`

holds, where `f_G(n) = #{k ≤ n : some g ∈ G divides k}`. Propositions 6.1 and 6.5 of that note
show (10) in the sparse regime would imply Erdős #488 in full. The forum notes that (10) fails
in the *dense* regime (first 14 primes, `n = 198`), which is outside the conjecture.

This statement says the conjecture is false as stated: there is a primitive `G` with
`n ≥ max G`, `2 f_G(n) < n` (sparse), and `2 f_G(n) < ∑ ⌊n/g⌋ + |G|`.

Submissions **must not** import this module.
-/

namespace Statements.ErdosMultiplesDoublingSparseSlackRefuted

/-- Negation of Chojecki's Conjecture 6.11 (sparse order-slack conjecture). -/
abbrev statement : Prop :=
  ∃ G : Finset ℕ,
    (∀ g ∈ G, 2 ≤ g) ∧
    (∀ a ∈ G, ∀ b ∈ G, a ∣ b → a = b) ∧
    ∃ n : ℕ, (∀ g ∈ G, g ≤ n) ∧
      2 * ((Finset.Icc 1 n).filter (fun k => ∃ g ∈ G, g ∣ k)).card < n ∧
      2 * ((Finset.Icc 1 n).filter (fun k => ∃ g ∈ G, g ∣ k)).card <
        (∑ g ∈ G, n / g) + G.card

theorem target : statement := sorry

end Statements.ErdosMultiplesDoublingSparseSlackRefuted
