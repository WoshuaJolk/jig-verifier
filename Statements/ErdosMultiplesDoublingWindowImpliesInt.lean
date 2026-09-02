import Mathlib.Order.Interval.Finset.Nat

/-!
# ErdosMultiplesDoublingWindowImpliesInt — the Window Bound gives #488 at integer ratios

If every length-`n` window `(x, x + n]` holds at most `2 M(n)` multiples of `A`
(`ErdosMultiplesDoublingWindow`), then for `m = j n` with `j ≥ 2`

  `M(jn) = M(n) + ∑_{i=1}^{j-1} #(B ∩ (in, (i+1)n]) ≤ (2j − 1) M(n) < 2j M(n)`,

which is Erdős #488 for `m ∈ n·ℕ`. The hypothesis is restated inline (the verifier forbids
importing `Statements.*`).

Submissions **must not** import this module.
-/

namespace Statements.ErdosMultiplesDoublingWindowImpliesInt

/-- Window Bound ⇒ `n · M(jn) < 2 · jn · M(n)` for all `j ≥ 2`. -/
abbrev statement : Prop :=
  (∀ A : Finset ℕ, A.Nonempty → 0 ∉ A →
    ∀ n x : ℕ, (∀ a ∈ A, a ≤ n) →
      ((Finset.Icc (x + 1) (x + n)).filter (fun k => ∃ a ∈ A, a ∣ k)).card ≤
        2 * ((Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card) →
  ∀ A : Finset ℕ, A.Nonempty → 0 ∉ A →
    ∀ n j : ℕ, (∀ a ∈ A, a ≤ n) → 2 ≤ j →
      n * ((Finset.Icc 1 (j * n)).filter (fun k => ∃ a ∈ A, a ∣ k)).card <
        2 * (j * n) * ((Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card

theorem target : statement := sorry

end Statements.ErdosMultiplesDoublingWindowImpliesInt
