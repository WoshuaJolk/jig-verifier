import Mathlib.Order.Interval.Finset.Nat

/-!
# ErdosMultiplesDoublingHarmonicSingleton — the Harmonic Bound for one generator

The case `A = {a}` of `ErdosMultiplesDoublingHarmonic`: for `1 ≤ a ≤ n < m`,

  `⌊m/a⌋ · (n + ⌊n/a⌋) ≤ 2m · ⌊n/a⌋`.

Proof: write `n = qa + r` with `q ≥ 1`, `r ≤ a − 1`; then `n + q ≤ 2qa` because
`r + q ≤ (a − 1) + q ≤ qa`, and `a⌊m/a⌋ ≤ m`. Equality holds exactly when `n = 2a − 1`
(`q = 1`, `r = a − 1`) and `a ∣ m`, for every such `m`: the conjecture is the envelope of this
family and its constant cannot be improved anywhere along it.

Submissions **must not** import this module.
-/

namespace Statements.ErdosMultiplesDoublingHarmonicSingleton

/-- Harmonic Bound for `A = {a}`. -/
abbrev statement : Prop :=
  ∀ a : ℕ, 0 < a → ∀ n m : ℕ, a ≤ n → n < m →
    ((Finset.Icc 1 m).filter (fun k => ∃ b ∈ ({a} : Finset ℕ), b ∣ k)).card *
        (n + ((Finset.Icc 1 n).filter (fun k => ∃ b ∈ ({a} : Finset ℕ), b ∣ k)).card) ≤
      2 * m * ((Finset.Icc 1 n).filter (fun k => ∃ b ∈ ({a} : Finset ℕ), b ∣ k)).card

theorem target : statement := sorry

end Statements.ErdosMultiplesDoublingHarmonicSingleton
