import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Lattice.Nat

namespace Statements.Erdos561OneStarBoundary

open SimpleGraph

abbrev StarVertices {s : ℕ} (a : Fin s → ℕ) :=
  Σ i : Fin s, Fin (a i + 1)

def starForest {s : ℕ} (a : Fin s → ℕ) :
    SimpleGraph (StarVertices a) where
  Adj u v :=
    u.1 = v.1 ∧
      ((u.2.val = 0 ∧ v.2.val ≠ 0) ∨
       (v.2.val = 0 ∧ u.2.val ≠ 0))
  symm := ⟨by
    rintro ⟨i, u⟩ ⟨j, v⟩ ⟨hij, h⟩
    exact ⟨hij.symm, h.elim (fun h ↦ Or.inr ⟨h.1, h.2⟩)
      (fun h ↦ Or.inl ⟨h.1, h.2⟩)⟩⟩
  loopless := ⟨by
    rintro ⟨i, u⟩ ⟨_, h⟩
    exact h.elim (fun h ↦ h.2 h.1) (fun h ↦ h.2 h.1)⟩

/-- The one-component, one-leaf star has its intended center-leaf edge. -/
abbrev statement : Prop :=
  (starForest (fun _ : Fin 1 ↦ 1)).Adj
    ⟨0, 0⟩ ⟨0, 1⟩

theorem target : statement := sorry

end Statements.Erdos561OneStarBoundary
