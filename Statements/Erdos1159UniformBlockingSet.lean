import Mathlib.Data.Finset.Card

namespace Statements.Erdos1159UniformBlockingSet

/-- Erdős Problem 1159: one constant `C > 1` such that every finite projective
plane has a set of points meeting every line in at least one and at most `C`
points. A plane of order `q ≥ 2` is given by its point and line types, its
incidence relation, `q + 1` points on every line, `q + 1` lines through every
point, and the two projective axioms. -/
abbrev statement : Prop :=
  ∃ C : ℕ, 1 < C ∧
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
        (S.filter fun p => Incidence p l).card ≤ C

theorem target : statement := sorry

end Statements.Erdos1159UniformBlockingSet
