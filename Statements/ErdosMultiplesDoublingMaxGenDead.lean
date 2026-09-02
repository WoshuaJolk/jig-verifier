import Mathlib.Order.Interval.Finset.Nat

/-!
# ErdosMultiplesDoublingMaxGenDead — the largest generator is not always removable

`ErdosMultiplesDoublingRemovable` conjectures that for every finite `A ⊆ ℕ_{>0}` and `n ≥ max A`
*some* `a ∈ A` is removable: its exclusive multiples `E_a` (multiples of `a` divisible by no other
element of `A`) satisfy `n · E_a(m) ≤ 2m · E_a(n)` for all `m > n`. Peeling such an `a` and
inducting gives Erdős #488 (`ErdosMultiplesDoublingRemovableImplies`).

The obvious candidate is `a = max A`: it is provably removable whenever `n < 2a`
(`⌊n/a⌋ = 1`, so `E_a(n) = 1` and `n · E_a(m) ≤ n ⌊m/a⌋ < 2m`), which is the half-range case.
This statement is the theorem that the choice `a = max A` does **not** work in general, so the
peeling induction cannot be run with a fixed rule: the removable generator must depend on `n`.

Mechanism: `E_a(x) = U_{A'}(⌊x/a⌋)` where `A' = {b / gcd(a,b) : b ∈ A ∖ {a}}` and `U` counts
non-multiples. For `A = {2,3,5,7}`, `a = 7`, `A' = {2,3,5}`: `E_7(48) = #{t ≤ 6 : (t,30)=1} = 1`
but `E_7(91) = #{t ≤ 13 : (t,30)=1} = 4`, and `48 · 4 = 192 > 182 = 2 · 91 · 1`. The
non-multiple density of `A'` at scale `⌊n/a⌋` is far below its density at scale `⌊m/a⌋`, because
the small non-multiples of `{2,3,5}` are exactly `1` and the primes `≥ 7`. The same mechanism with
`A = {primes ≤ 37}`, `n = 740` gives ratio `1.81`, and the failure grows with `n/max A`.

`#488` itself holds at the witness (`48 · M(91) = 3360 < 6552 = 2 · 91 · M(48)`), and the
witness is primitive, so the failure is not an artifact of dominated generators.

Residual: `ErdosMultiplesDoublingRemovable` with a data-dependent choice of `a` (numerically,
`argmax_b b · E_b(n) / n`).

Submissions **must not** import this module.
-/

namespace Statements.ErdosMultiplesDoublingMaxGenDead

/-- There is a primitive `A`, `n ≥ max A` and `m > n` at which #488 holds but the largest
generator `a = max A` violates the removability inequality `n · E_a(m) ≤ 2m · E_a(n)`. -/
abbrev statement : Prop :=
  ∃ A : Finset ℕ, A.Nonempty ∧ 0 ∉ A ∧
    (∀ b ∈ A, ∀ c ∈ A, b ∣ c → b = c) ∧
    ∃ a ∈ A, (∀ b ∈ A, b ≤ a) ∧
    ∃ n m : ℕ, (∀ b ∈ A, b ≤ n) ∧ n < m ∧
      n * ((Finset.Icc 1 m).filter (fun k => ∃ b ∈ A, b ∣ k)).card <
        2 * m * ((Finset.Icc 1 n).filter (fun k => ∃ b ∈ A, b ∣ k)).card ∧
      2 * m * ((Finset.Icc 1 n).filter
              (fun k => a ∣ k ∧ ∀ b ∈ A.erase a, ¬ b ∣ k)).card <
        n * ((Finset.Icc 1 m).filter
              (fun k => a ∣ k ∧ ∀ b ∈ A.erase a, ¬ b ∣ k)).card

theorem target : statement := sorry

end Statements.ErdosMultiplesDoublingMaxGenDead
