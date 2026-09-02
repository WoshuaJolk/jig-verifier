import Mathlib.Order.Interval.Finset.Nat

/-!
# ErdosMultiplesDoublingWindow — the translation-invariant Window Bound

Let `A` be a finite nonempty set of positive integers, `B` the set of positive multiples of
elements of `A`, and `M(x) = #(B ∩ [1, x])`. Erdős #488 asks whether `M(m)/m < 2 M(n)/n`
for all `m > n ≥ max A`.

This statement is a *stronger, translation-invariant* conjecture:

  `#(B ∩ (x, x + n]) ≤ 2 · M(n)`  for every `x ≥ 0` and every `n ≥ max A`.

Every window of length `n` carries at most twice the mass of the initial window `[1, n]`.
Summing over the `j` blocks of `[1, jn]` gives `M(jn) ≤ (2j − 1) M(n) < 2j M(n)`, i.e. #488
at integer ratios `m/n` (statement `ErdosMultiplesDoublingWindowImpliesInteger`), and #488 is
*not* known to imply it back. The constant `2` is sharp (`A = {a}`, `n = 2a − 1`, `x = 1`:
the window `(1, 2a]` holds two multiples, `[1, 2a − 1]` one).

Status: open. Numerically it survives hill-climbing over `A, n, x`: the maximum of
window/`M(n)` reached is exactly `2`, only at the trivial configurations above, while the
hard families for #488 (Chojecki's density-1/4 witness at `n = 180`, the 21 smallest primes,
primes in `(n^{1/3}, n^{1/2}]`) sit at `1.006`–`1.09`. No fixed two-shift translation rule
proves it (statement `ErdosMultiplesDoublingTwoShiftDead`).

Submissions **must not** import this module.
-/

namespace Statements.ErdosMultiplesDoublingWindow

/-- The Window Bound: for every finite nonempty `A` of positive integers, every `n ≥ max A`
and every `x`, the number of multiples of `A` in `(x, x + n]` is at most twice the number of
multiples of `A` in `[1, n]`. -/
abbrev statement : Prop :=
  ∀ A : Finset ℕ, A.Nonempty → 0 ∉ A →
    ∀ n x : ℕ, (∀ a ∈ A, a ≤ n) →
      ((Finset.Icc (x + 1) (x + n)).filter (fun k => ∃ a ∈ A, a ∣ k)).card ≤
        2 * ((Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card

theorem target : statement := sorry

end Statements.ErdosMultiplesDoublingWindow
