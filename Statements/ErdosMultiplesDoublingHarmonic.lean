import Mathlib.Order.Interval.Finset.Nat

/-!
# ErdosMultiplesDoublingHarmonic — the doubling inequality with `n + M(n)` in place of `n`

Let `A` be a finite nonempty set of positive integers and `M(x) = #{k ≤ x : some a ∈ A divides k}`.
Erdős #488 asks whether `n·M(m) < 2m·M(n)` for all `m > n ≥ max A`. This statement is the
sharper conjecture

  `M(m) · (n + M(n)) ≤ 2m · M(n)`   for all `m > n ≥ max A`,

i.e. `M(m)/m ≤ 2M(n)/(n + M(n))`. With `g = M/x` and `u = 1 − g` it reads
`g(m) ≤ 2g(n)/(1 + g(n))`, equivalently `u(m) ≥ u(n)/(2 − u(n))`.

It is the exact envelope of the one-generator case: for `A = {a}`, `n = 2a − 1` and every
`m ∈ a·ℕ`, `m > n`, both sides are equal (`M(m) = m/a`, `n + M(n) = 2a`, `M(n) = 1`). Because
`u/(2 − u) ≥ u²`, it implies the Square Bound (`ErdosMultiplesDoublingSquare`) and hence #488
with a strictly positive surplus (`ErdosMultiplesDoublingHarmonicImplies`). For `A` = all primes
`≤ n` and `m = 2n` it is exactly Bertrand's postulate (`U(2n) ≥ 2`, a prime in `(n, 2n]`), and
for `m = j(2n − 1)` it asks for `j` primes in `(n, m]`; so it is sensitive to the distribution of
primes in a way #488 itself is not (#488 is trivial for that `A`).

Status: open. Proved: `|A| = 1` for all `n ≥ a`, `m > n` (`ErdosMultiplesDoublingHarmonicSingleton`).
Evidence (exact, this session): exhaustive primitive `A ⊆ [2, 24]`, `|A| ≤ 3`, `n ≤ 60`,
`m ≤ 12n` (57 812 cases) and `A ⊆ [2, 32]`, `|A| ≤ 4`, `n ≤ 48`; every hard family for #488
(Chojecki's density-1/4 witness: ratio 1.58; 21 smallest primes at `n = 73`: 1.006; primes in
`(n^{1/3}, n^{1/2}]`: 1.54; `c·{primes ≤ K}`: ≥ 1.0023; all primes `≤ n`: `1 + Θ(1/n)`);
simulated-annealing hill-climbs over `(A, n)` to `n ≈ 3000`: the minimum ratio `1` is attained
only at singleton configurations. The half-range case `A ⊆ (n/2, n]` is NOT covered by the union
bound (already `A = {2, 3}`, `n = 3` needs the overlap term), unlike the Square Bound.

Submissions **must not** import this module.
-/

namespace Statements.ErdosMultiplesDoublingHarmonic

/-- The Harmonic Bound: `M(m)·(n + M(n)) ≤ 2m·M(n)` for all finite nonempty `A` of positive
integers and all `m > n ≥ max A`. -/
abbrev statement : Prop :=
  ∀ A : Finset ℕ, A.Nonempty → 0 ∉ A →
    ∀ n m : ℕ, (∀ a ∈ A, a ≤ n) → n < m →
      ((Finset.Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k)).card *
          (n + ((Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card) ≤
        2 * m * ((Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card

theorem target : statement := sorry

end Statements.ErdosMultiplesDoublingHarmonic
