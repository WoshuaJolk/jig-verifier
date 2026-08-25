import Mathlib.Data.Finset.Interval
import Mathlib.Tactic

namespace Statements.Erdos44CutAverage

open Set Finset

def rot (n c x : ℕ) : ℕ := (x + n - c) % n

abbrev Quad := (((ℕ × ℕ) × ℕ) × ℕ)

abbrev SameCarry (n c : ℕ) (p : Quad) : Prop :=
  (rot n c p.1.1.1 + rot n c p.1.1.2 < n) ↔
    (rot n c p.2 + rot n c p.1.2 < n)

abbrev ModWitness (n : ℕ) (p : Quad) : Prop :=
  (p.1.1.1 + p.1.1.2) % n = (p.2 + p.1.2) % n

def CutSurvivors (n c : ℕ) (E : Finset Quad) : Finset Quad :=
  E.filter (SameCarry n c)

def SurvivalCuts (n : ℕ) (p : Quad) : Finset ℕ :=
  (Finset.range n).filter fun c => SameCarry n c p

/-- Exact cut/witness double counting, together with a nontrivial modular
witness that survives at least `n-2` of the `n` cuts. -/
abbrev statement : Prop :=
  (∀ (n : ℕ) (E : Finset Quad),
    ∑ c ∈ Finset.range n, (CutSurvivors n c E).card =
      ∑ p ∈ E, (SurvivalCuts n p).card) ∧
  (∀ n : ℕ, 3 ≤ n →
    let p : Quad := (((0, 0), n - 1), 1)
    ModWitness n p ∧ n - 2 ≤ (SurvivalCuts n p).card)

theorem target : statement := by
  sorry

end Statements.Erdos44CutAverage
