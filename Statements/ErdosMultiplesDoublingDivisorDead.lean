import Mathlib.Order.Interval.Finset.Nat

/-!
# ErdosMultiplesDoublingDivisorDead — charging to divisors cannot prove #488

A natural proof shape for Erdős #488 (`n · M(m) < 2m · M(n)`) is a *charging*: send each
multiple `k ∈ B ∩ [1, m]` to a divisor `d ∣ k` with `d ∈ B ∩ [1, n]`, and show no `d`
receives more than `2m/n` points. The largest-divisor / rough-cofactor bound, the
transfer-lemma route and every Hall-type argument on the divisor graph are instances.

This statement is the theorem that **no such charging exists in general**, even where #488
itself holds. Mechanism: if `a ∈ A` and `q` is a prime in `(n/a, m/a]` not dividing any
generator, then `a·q ≤ m` has exactly one divisor in `B ∩ [1, n]`, namely `a` itself, so
`a` must absorb every such `a·q`, and there are more of them than `2m/n`.

Witness: Chojecki's `G = {8,12,18,20,28,30,42,44,52,68}`, `n = 180`, `m = 360`. The six
numbers `8q`, `q ∈ {23, 29, 31, 37, 41, 43}`, lie in `[1, 360]` and each has `8` as its only
divisor in `B ∩ [1, 180]`, so any divisor-respecting `f` has `#f⁻¹(8) ≥ 6` and
`n · 6 = 1080 > 720 = 2m`; yet `n · M(360) < 2 · 360 · M(180)` holds.

What survives (`residual_of`): `ErdosMultiplesDoublingLocal`, charging to a *scaled*
multiple `a·⌊tn/m⌉` of the same generator rather than to a divisor.

Submissions **must not** import this module.
-/

namespace Statements.ErdosMultiplesDoublingDivisorDead

/-- There are `A, n, m` satisfying #488 for which every map `f` from `B ∩ [1,m]` to
`B ∩ [1,n]` with `f k ∣ k` has a fiber of size `> 2m/n`. -/
abbrev statement : Prop :=
  ∃ A : Finset ℕ, A.Nonempty ∧ 0 ∉ A ∧
    ∃ n m : ℕ, (∀ a ∈ A, a ≤ n) ∧ n < m ∧
      n * ((Finset.Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k)).card <
        2 * m * ((Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card ∧
      ∀ f : ℕ → ℕ,
        (∀ k ∈ (Finset.Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k),
          f k ∣ k ∧ f k ∈ (Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)) →
        ∃ d ∈ (Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k),
          2 * m < n * (((Finset.Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k)).filter
            (fun k => f k = d)).card

theorem target : statement := sorry

end Statements.ErdosMultiplesDoublingDivisorDead
