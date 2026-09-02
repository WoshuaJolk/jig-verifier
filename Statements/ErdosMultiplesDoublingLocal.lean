import Mathlib.Order.Interval.Finset.Nat

/-!
# ErdosMultiplesDoublingLocal — Local Doubling: #488 by charging to scaled multiples

Let `B` be the set of positive multiples of a finite nonempty `A ⊆ ℕ_{>0}`, `n ≥ max A`,
`m > n`. Erdős #488 says `n · #(B ∩ [1,m]) < 2m · #(B ∩ [1,n])`.

This statement conjectures a *local* mechanism behind it. Every `k = a·t ∈ B ∩ [1, m]`
(`a ∈ A`) is charged to a multiple `a·s ∈ B ∩ [1, n]` of the *same* generator whose index
`s` is within distance one of the scaled index `t·n/m`:

  `|s − t n / m| ≤ 1`, i.e. `s m ≤ t n + m` and `t n ≤ s m + m`, with `1 ≤ s`, `a s ≤ n`,

and no target receives more than `2m/n` points: `n · #fiber(d) < 2m` for every `d`.

Summing the fibers gives #488 at once (`ErdosMultiplesDoublingLocalImplies`). The point of
the statement is the *shape* of the charging: mass moves to a scaled copy of `k`, not to a
divisor of `k`. Charging to divisors is provably impossible in general
(`ErdosMultiplesDoublingDivisorDead`, of which this statement is the residual).

Status: open. An exact max-flow computation finds such an `f` in every tested instance
(Chojecki's density-1/4 witness `n = 180`, the 21 smallest primes, primes in
`(n^{1/3}, n^{1/2}]`, the `2²·p` family, `[X/2, X]`, and 900 random `(A, n, m)`), with
maximal load close to `m/n`, half the allowed budget.

Submissions **must not** import this module.
-/

namespace Statements.ErdosMultiplesDoublingLocal

/-- Local Doubling: a charging `f : B ∩ [1,m] → B ∩ [1,n]` sending `a·t` to some `a·s` with
`|s − tn/m| ≤ 1`, every fiber of size `< 2m/n`. -/
abbrev statement : Prop :=
  ∀ A : Finset ℕ, A.Nonempty → 0 ∉ A →
    ∀ n m : ℕ, (∀ a ∈ A, a ≤ n) → n < m →
      ∃ f : ℕ → ℕ,
        (∀ k ∈ (Finset.Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k),
          ∃ a ∈ A, ∃ s : ℕ, a ∣ k ∧ f k = a * s ∧ 1 ≤ s ∧ a * s ≤ n ∧
            s * m ≤ (k / a) * n + m ∧ (k / a) * n ≤ s * m + m) ∧
        (∀ d : ℕ,
          n * (((Finset.Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k)).filter
            (fun k => f k = d)).card < 2 * m)

theorem target : statement := sorry

end Statements.ErdosMultiplesDoublingLocal
