import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
Explicit counterexample to Chojecki's Conjecture 6.11 (sparse order-slack conjecture) for
Erdős #488.

`G = {8, 12, 18, 20, 28, 30, 42, 44, 52, 68}` (twice the semiprime-like set
`{4, 6, 9, 10, 14, 15, 21, 22, 26, 34}`), `n = 180`.  Then `f_G(180) = 45`, so
`2 f_G(n) = 90 < 180 = n` (sparse regime, density `1/4`), while
`∑ ⌊180/g⌋ = 81` and `|G| = 10`, so `∑ ⌊n/g⌋ + |G| = 91 > 90 = 2 f_G(n)`.
-/

namespace Submissions.ErdosMultiplesDoublingSparseSlackRefuted.Witness

theorem proof : ∃ G : Finset ℕ,
    (∀ g ∈ G, 2 ≤ g) ∧
    (∀ a ∈ G, ∀ b ∈ G, a ∣ b → a = b) ∧
    ∃ n : ℕ, (∀ g ∈ G, g ≤ n) ∧
      2 * ((Finset.Icc 1 n).filter (fun k => ∃ g ∈ G, g ∣ k)).card < n ∧
      2 * ((Finset.Icc 1 n).filter (fun k => ∃ g ∈ G, g ∣ k)).card <
        (∑ g ∈ G, n / g) + G.card := by
  refine ⟨{8, 12, 18, 20, 28, 30, 42, 44, 52, 68}, by decide, by decide, 180, by decide, ?_, ?_⟩
  · decide
  · decide

end Submissions.ErdosMultiplesDoublingSparseSlackRefuted.Witness
