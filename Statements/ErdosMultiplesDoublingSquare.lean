import Mathlib.Order.Interval.Finset.Nat

/-!
# ErdosMultiplesDoublingSquare — the Square Bound for non-multiples

Let `A` be a finite nonempty set of positive integers, `B` the set of positive multiples of
elements of `A`, and `U(x) = #([1, x] ∖ B)` the number of *non*-multiples up to `x`, so that
`u(x) = U(x)/x` is the proportion of unsieved integers. Erdős #488 asks whether
`M(m)/m < 2 M(n)/n` for all `m > n ≥ max A`, where `M = x − U`.

This statement is the conjecture

  `u(m) ≥ u(n)²`   for all `m > n ≥ max A`,   i.e.   `U(n)² · m ≤ U(m) · n²`.

It implies #488 with the sharper constant `2 − M(n)/n` in place of `2`
(statement `ErdosMultiplesDoublingSquareImplies`): `1 − u(m) ≤ 1 − u(n)² = g(n)(2 − g(n))`
with `g = M/x`. Taking `m` a multiple of `lcm A` gives the asymptotic form
`δ(B) ≤ 1 − u(n)² = g(n)(2 − g(n))`, which is strictly sharper than the asymptotic form of
#488 (Tao's "Cheat 1", `δ(B) ≤ 2 g(n)`). Sharp: `A = {a}`, `n = 2a − 1`, `m = 2a` gives `u(m)/u(n)² = n²/(n² − 1)`.

Status: open. Proved cases: `|A| = 1` (statement `SquareSingleton`) and `A ⊆ (n/2, n]`
(statement `SquareHalf`). Evidence: exact computation on all hard families for #488, on
`c·{primes ≤ K}` families with up to 168 elements, exhaustive primitive `A ⊆ [2, 24]` with
`|A| ≤ 3`, 47 000 structured/random perturbations of the hard families, and hill-climbing over
`(A, n)` (mutations: add/remove/perturb/scale generators, add small primes, move `n`) up to
`n ≈ 3600`, `m ≤ 12n`: no violation; the infimum of `u(m)/u(n)²` is approached only by the
singleton configurations above. The natural
strengthening `U(n)² ≤ n² ∏_{a∈A}(1 − 1/a)` (Heilbronn–Rohrbach product) is FALSE
(statement `SquareHRDead`).

Submissions **must not** import this module.
-/

namespace Statements.ErdosMultiplesDoublingSquare

/-- The Square Bound: for every finite nonempty `A` of positive integers and all
`m > n ≥ max A`, `U(n)² · m ≤ U(m) · n²`, where `U(x)` counts the integers in `[1, x]` that are
multiples of no element of `A`. -/
abbrev statement : Prop :=
  ∀ A : Finset ℕ, A.Nonempty → 0 ∉ A →
    ∀ n m : ℕ, (∀ a ∈ A, a ≤ n) → n < m →
      ((Finset.Icc 1 n).filter (fun k => ¬ ∃ a ∈ A, a ∣ k)).card ^ 2 * m ≤
        ((Finset.Icc 1 m).filter (fun k => ¬ ∃ a ∈ A, a ∣ k)).card * n ^ 2

theorem target : statement := sorry

end Statements.ErdosMultiplesDoublingSquare
