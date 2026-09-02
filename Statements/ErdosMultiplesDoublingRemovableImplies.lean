import Mathlib.Order.Interval.Finset.Nat

/-!
# ErdosMultiplesDoublingRemovableImplies — a removable generator at every stage gives #488

Hypothesis (restated inline from `ErdosMultiplesDoublingRemovable`): for every finite nonempty
`A ⊆ ℕ_{>0}` and `n ≥ max A` some `a ∈ A` satisfies `n · E_a(m) ≤ 2m · E_a(n)` for all `m > n`,
where `E_a(y)` counts multiples of `a` in `[1, y]` divisible by no other element of `A`.

Conclusion: Erdős #488. Proof: `M_A(y) = M_{A ∖ {a}}(y) + E_a(y)`; if `A = {a}` the
inequality is the sharp one-generator case (`n · ⌊m/a⌋ < 2m · ⌊n/a⌋`), otherwise induct on
`|A|`, since `max (A ∖ {a}) ≤ n` still holds, and add the removable generator's non-strict
inequality to the strict one for `A ∖ {a}`.

Submissions **must not** import this module.
-/

namespace Statements.ErdosMultiplesDoublingRemovableImplies

/-- Removable generator (for all `A`, `n`) ⇒ Erdős #488. -/
abbrev statement : Prop :=
  (∀ A : Finset ℕ, A.Nonempty → 0 ∉ A →
    ∀ n : ℕ, (∀ a ∈ A, a ≤ n) →
      ∃ a ∈ A, ∀ m : ℕ, n < m →
        n * ((Finset.Icc 1 m).filter
              (fun k => a ∣ k ∧ ∀ b ∈ A.erase a, ¬ b ∣ k)).card ≤
          2 * m * ((Finset.Icc 1 n).filter
              (fun k => a ∣ k ∧ ∀ b ∈ A.erase a, ¬ b ∣ k)).card) →
  ∀ A : Finset ℕ, A.Nonempty → 0 ∉ A →
    ∀ n m : ℕ, (∀ a ∈ A, a ≤ n) → n < m →
      n * ((Finset.Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k)).card <
        2 * m * ((Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card

theorem target : statement := sorry

end Statements.ErdosMultiplesDoublingRemovableImplies
