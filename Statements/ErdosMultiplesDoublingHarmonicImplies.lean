import Mathlib.Order.Interval.Finset.Nat

/-!
# ErdosMultiplesDoublingHarmonicImplies — Harmonic Bound ⇒ Square Bound ⇒ Erdős #488

If `M(m)·(n + M(n)) ≤ 2m·M(n)` for all `A`, `m > n ≥ max A` (statement
`ErdosMultiplesDoublingHarmonic`), then

* the Square Bound `U(n)²·m ≤ U(m)·n²` holds (`U = x − M`): with `u = U/x`, the hypothesis is
  `u(m) ≥ u(n)/(2 − u(n))` and `u/(2 − u) − u² = u(1 − u)²/(2 − u) ≥ 0`;
* Erdős #488 holds: `n·M(m) < M(m)·(n + M(n)) ≤ 2m·M(n)` since `M(m) ≥ M(n) ≥ 1`.

Both hypotheses and conclusions are inlined (the verifier forbids importing `Statements.*`).

Submissions **must not** import this module.
-/

namespace Statements.ErdosMultiplesDoublingHarmonicImplies

/-- Harmonic Bound ⇒ (Square Bound ∧ Erdős #488). -/
abbrev statement : Prop :=
  (∀ A : Finset ℕ, A.Nonempty → 0 ∉ A →
    ∀ n m : ℕ, (∀ a ∈ A, a ≤ n) → n < m →
      ((Finset.Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k)).card *
          (n + ((Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card) ≤
        2 * m * ((Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card) →
  (∀ A : Finset ℕ, A.Nonempty → 0 ∉ A →
    ∀ n m : ℕ, (∀ a ∈ A, a ≤ n) → n < m →
      ((Finset.Icc 1 n).filter (fun k => ¬ ∃ a ∈ A, a ∣ k)).card ^ 2 * m ≤
        ((Finset.Icc 1 m).filter (fun k => ¬ ∃ a ∈ A, a ∣ k)).card * n ^ 2) ∧
  (∀ A : Finset ℕ, A.Nonempty → 0 ∉ A →
    ∀ n m : ℕ, (∀ a ∈ A, a ≤ n) → n < m →
      n * ((Finset.Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k)).card <
        2 * m * ((Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card)

theorem target : statement := sorry

end Statements.ErdosMultiplesDoublingHarmonicImplies
