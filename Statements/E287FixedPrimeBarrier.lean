import Mathlib.Tactic
namespace Statements.E287FixedPrimeBarrier
abbrev statement : Prop := ∀ m : ℕ, 1 ≤ m → ∃ s : ℕ → ℕ,
  StrictMono s ∧ 1 < s 0 ∧
  (∀ i, s (i+1)-s i ≤ 2) ∧
  s m - s (m-1) = 2 ∧
  (∑ i ∈ Finset.range (2*m), 1/(s i : ℚ)) < 1 ∧
  (∀ p : ℕ, p.Prime → p ≤ m →
    ¬p ∣ (∑ i ∈ Finset.range (2*m), 1/(s i : ℚ)).den)
theorem target : statement := sorry
end Statements.E287FixedPrimeBarrier
