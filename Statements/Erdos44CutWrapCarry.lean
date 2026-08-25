import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

namespace Statements.Erdos44CutWrapCarry

open Set Finset

def rot (n c x : ℕ) : ℕ := (x + n - c) % n

abbrev Quad := (((ℕ × ℕ) × ℕ) × ℕ)

abbrev ModCollision (n c : ℕ) (p : Quad) : Prop :=
  (rot n c p.1.1.1 + rot n c p.1.1.2) % n =
    (rot n c p.2 + rot n c p.1.2) % n

abbrev IntegerCollision (n c : ℕ) (p : Quad) : Prop :=
  rot n c p.1.1.1 + rot n c p.1.1.2 =
    rot n c p.2 + rot n c p.1.2

abbrev SameCarry (n c : ℕ) (p : Quad) : Prop :=
  (rot n c p.1.1.1 + rot n c p.1.1.2 < n) ↔
    (rot n c p.2 + rot n c p.1.2 < n)

/-- Among modular collision witnesses, precisely those whose two pair sums
have the same carry across the cut survive as integer collisions. -/
abbrev statement : Prop :=
  ∀ (n c : ℕ), 0 < n → ∀ E : Finset Quad,
    (∀ p ∈ E, ModCollision n c p) →
      E.filter (IntegerCollision n c) = E.filter (SameCarry n c)

theorem target : statement := by
  sorry

end Statements.Erdos44CutWrapCarry
