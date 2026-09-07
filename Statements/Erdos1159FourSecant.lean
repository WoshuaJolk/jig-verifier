import Mathlib.Data.Finset.Card

namespace Statements.Erdos1159FourSecant

/-- Bruen–Fisher (1974), Theorem 6(iv), also allowing blockers containing a line. -/
abbrev statement : Prop :=
  ∀ (Point Line : Type) [Fintype Point] [Fintype Line] [Nonempty Line]
    (I : Point → Line → Prop) [DecidableRel I] (q : ℕ),
    5 ≤ q →
    (∀ l : Line, (Finset.univ.filter fun p => I p l).card = q + 1) →
    (∀ p : Point, (Finset.univ.filter fun l => I p l).card = q + 1) →
    (∀ p r : Point, p ≠ r → ∃ l : Line, I p l ∧ I r l) →
    (∀ p r : Point, ∀ l m : Line, p ≠ r →
      I p l → I r l → I p m → I r m → l = m) →
    (∀ l m : Line, l ≠ m → ∃ p : Point, I p l ∧ I p m) →
    (∀ l m : Line, ∀ p r : Point, l ≠ m →
      I p l → I p m → I r l → I r m → p = r) →
    ∀ S : Finset Point,
      (∀ l : Line, 1 ≤ (S.filter fun p => I p l).card) →
      ∃ l : Line, 4 ≤ (S.filter fun p => I p l).card

theorem target : statement := sorry

end Statements.Erdos1159FourSecant
