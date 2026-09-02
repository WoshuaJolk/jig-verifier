import Mathlib.Order.Interval.Finset.Nat

/-!
# ErdosMultiplesDoublingRemovable — some generator is always removable

For `a ∈ A` let the *exclusive multiples* of `a` be the multiples of `a` divisible by no other
element of `A`, and `E_a(y)` their number in `[1, y]`. Then `M_A(y) = M_{A ∖ {a}}(y) + E_a(y)`.

This statement conjectures that for every finite nonempty `A` of positive integers and every
`n ≥ max A` there is a generator `a ∈ A` whose exclusive multiples themselves satisfy the
(non-strict) doubling inequality for **all** `m > n`:

  `n · E_a(m) ≤ 2m · E_a(n)`.

Removing such an `a` and inducting on `|A|` proves Erdős #488
(`ErdosMultiplesDoublingRemovableImplies`). The exclusive multiples of `a` are `a·t` with `t`
avoiding the compressed set `P_a = {b / gcd(a,b) : b ∈ A ∖ {a}}`, so the statement is a
self-similar one-generator-at-a-time reduction; it is *not* true for every `a` (the smallest
prime among the 21 smallest primes fails), and the numerically successful choice is
`a = argmax_b b·E_b(n)/n` (maximal exclusive density).

Status: open. Verified in every tested instance: Chojecki's density-1/4 witness, the 21
smallest primes, primes in `(n^{1/3}, n^{1/2}]`, the `2²·p` family, `[X/2, X]`, non-primitive
sets, and 800 random `(A, n)` with `m ≤ 30n`.

Submissions **must not** import this module.
-/

namespace Statements.ErdosMultiplesDoublingRemovable

/-- Some `a ∈ A` has `n · E_a(m) ≤ 2m · E_a(n)` for all `m > n`. -/
abbrev statement : Prop :=
  ∀ A : Finset ℕ, A.Nonempty → 0 ∉ A →
    ∀ n : ℕ, (∀ a ∈ A, a ≤ n) →
      ∃ a ∈ A, ∀ m : ℕ, n < m →
        n * ((Finset.Icc 1 m).filter
              (fun k => a ∣ k ∧ ∀ b ∈ A.erase a, ¬ b ∣ k)).card ≤
          2 * m * ((Finset.Icc 1 n).filter
              (fun k => a ∣ k ∧ ∀ b ∈ A.erase a, ¬ b ∣ k)).card

theorem target : statement := sorry

end Statements.ErdosMultiplesDoublingRemovable
