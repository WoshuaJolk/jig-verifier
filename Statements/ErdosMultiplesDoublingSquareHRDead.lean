import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# ErdosMultiplesDoublingSquareHRDead — the Heilbronn–Rohrbach product does not bound `U(n)²`

A tempting route to the asymptotic form of the Square Bound (`ErdosMultiplesDoublingSquare`
with `m` a multiple of `lcm A`, i.e. `1 − δ(B) ≥ u(n)²`) is to combine the classical
Heilbronn–Rohrbach inequality `1 − δ(B) ≥ ∏_{a∈A}(1 − 1/a)` with the *finite* bound

  `U(n)² ≤ n² · ∏_{a∈A} (1 − 1/a)`   for all `n ≥ max A`.     (★)

(★) holds for singletons, for all pairwise coprime `A` tested, and survives hill-climbing on
sets of at most a dozen elements. It is nevertheless FALSE: this statement exhibits `A`, `n`
with `n ≥ max A` and `n² ∏ (a − 1) < U(n)² ∏ a`. The witness is `A = 52 · {primes ≤ 67}`,
`n = 52 · 199`; the mechanism is that for `A = c·S` the non-multiple proportion is
`1 − g_S(N)/c ≈ 1 − 1/c` while the product is `≈ exp(−(1/c)∑_{s∈S} 1/s)`, so any `S` with
`∑ 1/s` large enough (here `∑_{p ≤ 67} 1/p ≈ 1.73` together with the floor effects at
`N = 199`) breaks (★). The route through the HR product is therefore closed; the Square
Bound itself (which uses the true density `1 − δ(B)`, not the product) is not affected: on the
witness `u(m)/u(n)² ≥ 1.0165` for every `m ≤ 60n` and `→ 1.0166` as `m → ∞`.

Submissions **must not** import this module.
-/

namespace Statements.ErdosMultiplesDoublingSquareHRDead

/-- There are `A`, `n ≥ max A` with `U(n)² > n² ∏_{a∈A}(1 − 1/a)`. -/
abbrev statement : Prop :=
  ∃ A : Finset ℕ, A.Nonempty ∧ 0 ∉ A ∧
    ∃ n : ℕ, (∀ a ∈ A, a ≤ n) ∧
      n ^ 2 * (∏ a ∈ A, (a - 1)) <
        ((Finset.Icc 1 n).filter (fun k => ¬ ∃ a ∈ A, a ∣ k)).card ^ 2 * (∏ a ∈ A, a)

theorem target : statement := sorry

end Statements.ErdosMultiplesDoublingSquareHRDead
