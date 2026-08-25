import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Lattice.Nat

namespace Statements.Erdos561OneEdgeSizeRamsey

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

noncomputable def sizeRamsey {α β : Type*} (G : SimpleGraph α)
    (H : SimpleGraph β) : ℕ :=
  sInf {m : ℕ | ∃ (n : ℕ) (F : SimpleGraph (Fin n)),
    F.edgeSet.ncard = m ∧
      ∀ (R : SimpleGraph (Fin n)), R ≤ F →
        G.IsContained R ∨ H.IsContained (F \ R)}

/-- The first exact one-component case of Erdős 561: the asymmetric size
Ramsey number of two one-edge stars is one. -/
abbrev statement : Prop :=
  sizeRamsey
      (starForest (fun _ : Fin 1 ↦ 1))
      (starForest (fun _ : Fin 1 ↦ 1)) = 1

theorem target : statement := sorry

end Statements.Erdos561OneEdgeSizeRamsey
