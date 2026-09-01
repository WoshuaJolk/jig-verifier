import Mathlib.Order.Interval.Finset.Nat

/-!
# ErdosMultiplesDoubling — Erdős's density-doubling question for sets of multiples

Erdős problem #488 (erdosproblems.com/488), stated by Erdős in 1961 (Magyar Tud. Akad.
Mat. Kutató Int. Közl. 6, p. 236, with a misprint), in 1966 (Mat. Lapok 17, p. 150,
problem 6) and in 1980 (A survey of problems in combinatorial number theory, p. 112).

Let `A` be a finite nonempty set of positive integers and let `B` be the set of positive
integers divisible by at least one element of `A`.  Writing `M x` for the number of
elements of `B` in `[1, x]`, is it true that for every `m > n ≥ max A`

  `M m / m < 2 * M n / n` ?

The statement below is the same inequality cleared of denominators
(`n * M m < 2 * m * M n`), which is equivalent because `1 ≤ n < m`.

The constant `2` cannot be lowered: `A = {a}`, `n = 2a - 1`, `m = 2a`.

Submissions **must not** import this module (the verifier rejects them if they do),
because `target` below is closed with `sorry`.
-/

namespace Statements.ErdosMultiplesDoubling

/-- The canonical proposition. For every finite nonempty set `A` of positive integers, every
`n ≥ max A` and every `m > n`, the number of multiples of `A` in `[1, m]` times `n` is
strictly less than twice the number of multiples of `A` in `[1, n]` times `m`. -/
abbrev statement : Prop :=
  ∀ A : Finset ℕ, A.Nonempty → 0 ∉ A →
    ∀ n m : ℕ, (∀ a ∈ A, a ≤ n) → n < m →
      n * ((Finset.Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k)).card <
        2 * m * ((Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card

/-- The open target. Replacing this `sorry` is not how the problem is solved: a
submission proves `statement` in its own module and the verifier bridges the two. -/
theorem target : statement := sorry

end Statements.ErdosMultiplesDoubling
