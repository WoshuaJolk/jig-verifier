import Mathlib.Order.Interval.Finset.Nat

/-!
# ErdosMultiplesDoublingLocalImplies — Local Doubling implies Erdős #488

If every `k ∈ B ∩ [1,m]` can be charged to some `a·s ∈ B ∩ [1,n]` (`a ∈ A`, `a ∣ k`,
`|s − (k/a)·n/m| ≤ 1`) so that every fiber has `n · #fiber < 2m`
(`ErdosMultiplesDoublingLocal`, restated inline), then

  `n · M(m) = ∑_{d ∈ B ∩ [1,n]} n · #fiber(d) < 2m · M(n)`,

which is Erdős #488 in full. Only the fiber bound and the fact that every image lies in
`B ∩ [1, n]` are used; the locality constraint `|s − tn/m| ≤ 1` is carried along untouched.

Submissions **must not** import this module.
-/

namespace Statements.ErdosMultiplesDoublingLocalImplies

/-- Local Doubling ⇒ Erdős #488. -/
abbrev statement : Prop :=
  (∀ A : Finset ℕ, A.Nonempty → 0 ∉ A →
    ∀ n m : ℕ, (∀ a ∈ A, a ≤ n) → n < m →
      ∃ f : ℕ → ℕ,
        (∀ k ∈ (Finset.Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k),
          ∃ a ∈ A, ∃ s : ℕ, a ∣ k ∧ f k = a * s ∧ 1 ≤ s ∧ a * s ≤ n ∧
            s * m ≤ (k / a) * n + m ∧ (k / a) * n ≤ s * m + m) ∧
        (∀ d : ℕ,
          n * (((Finset.Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k)).filter
            (fun k => f k = d)).card < 2 * m)) →
  ∀ A : Finset ℕ, A.Nonempty → 0 ∉ A →
    ∀ n m : ℕ, (∀ a ∈ A, a ≤ n) → n < m →
      n * ((Finset.Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k)).card <
        2 * m * ((Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card

theorem target : statement := sorry

end Statements.ErdosMultiplesDoublingLocalImplies
