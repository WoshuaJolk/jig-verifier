import Mathlib.Order.Interval.Finset.Nat

/-!
# ErdosMultiplesDoublingTwoShiftDead — the two nearest translates do not prove the Window Bound

The Window Bound (`ErdosMultiplesDoublingWindow`) says `#(B ∩ (x, x+n]) ≤ 2 M(n)`. The
obvious local proof would translate each `k = a·t` in the window back into `[1, n]` by one of
the two nearest multiples of its own generator, `k − a⌊x/a⌋` or `k − a⌈x/a⌉`, and show that
every point of `B ∩ [1, n]` is hit at most twice.

This statement is the theorem that **this rule fails**: there is an instance where the
Window Bound holds, but every map `f` obeying the two-translate rule (with every image in
`B ∩ [1, n]`) sends three window points to the same target. Mechanism: a Hall violator. For
`A = {8, 11, 12, 14, 18, 19, 21, 26}`, `n = 138`, `x = 354`, the points
`483 = 21·23`, `486 = 18·27`, `490 = 14·35` each have a single generator, their `⌊x/a⌋`
translates `147, 144, 140` overshoot `n`, and their `⌈x/a⌉` translates all equal `126`.

What survives (`residual_of`): the Window Bound itself; a proof must use at least three
translates or a global (averaging / matching) argument.

Submissions **must not** import this module.
-/

namespace Statements.ErdosMultiplesDoublingTwoShiftDead

/-- An instance where the Window Bound holds but every two-translate charging has a fiber of
size at least `3`. -/
abbrev statement : Prop :=
  ∃ A : Finset ℕ, A.Nonempty ∧ 0 ∉ A ∧
    ∃ n x : ℕ, (∀ a ∈ A, a ≤ n) ∧
      ((Finset.Icc (x + 1) (x + n)).filter (fun k => ∃ a ∈ A, a ∣ k)).card ≤
        2 * ((Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card ∧
      ∀ f : ℕ → ℕ,
        (∀ k ∈ (Finset.Icc (x + 1) (x + n)).filter (fun k => ∃ a ∈ A, a ∣ k),
          f k ∈ (Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k) ∧
          ∃ a ∈ A, a ∣ k ∧ (f k + a * (x / a) = k ∨ f k + a * ((x + a - 1) / a) = k)) →
        ∃ d ∈ (Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k),
          2 < (((Finset.Icc (x + 1) (x + n)).filter (fun k => ∃ a ∈ A, a ∣ k)).filter
            (fun k => f k = d)).card

theorem target : statement := sorry

end Statements.ErdosMultiplesDoublingTwoShiftDead
