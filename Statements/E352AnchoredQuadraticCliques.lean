import Mathlib

namespace Statements.E352AnchoredQuadraticCliques

abbrev Point := ℤ × ℤ

def anchors (m : ℕ) : Finset Point :=
  {(0, 0), (60 * (m : ℤ), 60 * (m : ℤ)), (60 * (m : ℤ), 0)}

def inBox (m : ℕ) (p : Point) : Prop :=
  29 * (m : ℤ) ≤ p.1 ∧ p.1 ≤ 31 * (m : ℤ) ∧
  19 * (m : ℤ) ≤ p.2 ∧ p.2 ≤ 21 * (m : ℤ)

def distSq (p q : Point) : ℤ :=
  (p.1 - q.1)^2 + (p.2 - q.2)^2

def twiceArea (a p q : Point) : ℤ :=
  |(p.1 - a.1) * (q.2 - a.2) - (q.1 - a.1) * (p.2 - a.2)|

/-- Quadratically many candidates pass every triple test meeting the three anchors.
    No condition is imposed on triples of three unanchored candidates. -/
abbrev statement : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∃ S : Finset Point,
    (∀ p ∈ S, inBox m p) ∧
    (2 * m + 1)^2 ≤ 1000000000 * S.card ∧
    (∀ p ∈ S ∪ anchors m, ∀ q ∈ S ∪ anchors m,
      distSq p q ≤ 7200 * (m : ℤ)^2) ∧
    (∀ a ∈ anchors m, ∀ p ∈ S ∪ anchors m, ∀ q ∈ S ∪ anchors m,
      180 * (m : ℤ) < |twiceArea a p q - 200 * (m : ℤ)|)

-- Statement transcription only. The written proof is not kernel-checked.
theorem target : statement := sorry

end Statements.E352AnchoredQuadraticCliques
