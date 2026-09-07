import Mathlib.Data.Finset.Card

namespace Statements.Erdos1159LogarithmicBlocking

/-- An explicit coarse form of the known Erdős–Silverman–Stein logarithmic bound. -/
abbrev statement : Prop :=
    ∀ (Point Line : Type) [Fintype Point] [Fintype Line]
      (Incidence : Point → Line → Prop) [DecidableRel Incidence] (q : ℕ),
      2 ≤ q →
      (∀ l : Line, (Finset.univ.filter fun p => Incidence p l).card = q + 1) →
      (∀ p : Point, (Finset.univ.filter fun l => Incidence p l).card = q + 1) →
      (∀ p₁ p₂ : Point, p₁ ≠ p₂ → ∃ l : Line, Incidence p₁ l ∧ Incidence p₂ l) →
      (∀ p₁ p₂ : Point, ∀ l m : Line, p₁ ≠ p₂ →
        Incidence p₁ l → Incidence p₂ l → Incidence p₁ m → Incidence p₂ m → l = m) →
      (∀ l m : Line, l ≠ m → ∃ p : Point, Incidence p l ∧ Incidence p m) →
      (∀ l m : Line, ∀ p₁ p₂ : Point, l ≠ m →
        Incidence p₁ l → Incidence p₁ m → Incidence p₂ l → Incidence p₂ m → p₁ = p₂) →
      ∃ S : Finset Point, ∀ l : Line,
        1 ≤ (S.filter fun p => Incidence p l).card ∧
        (S.filter fun p => Incidence p l).card ≤ 32 * ((2 * (q * q + q + 1)).log2 + 1)

theorem target : statement := sorry

end Statements.Erdos1159LogarithmicBlocking
