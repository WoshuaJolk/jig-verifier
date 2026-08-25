import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Lattice.Nat

namespace Statements.Erdos561StarForestSizeRamsey

open SimpleGraph

abbrev StarVertices {s : ℕ} (a : Fin s → ℕ) :=
  Σ i : Fin s, Fin (a i + 1)

/-- The disjoint union, indexed by `i`, of stars with `a i` leaves. -/
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

/-- The asymmetric red/blue size Ramsey number. -/
noncomputable def sizeRamsey {α β : Type*} (G : SimpleGraph α)
    (H : SimpleGraph β) : ℕ :=
  sInf {m : ℕ | ∃ (n : ℕ) (F : SimpleGraph (Fin n)),
    F.edgeSet.ncard = m ∧
      ∀ (R : SimpleGraph (Fin n)), R ≤ F →
        G.IsContained R ∨ H.IsContained (F \ R)}

/-- The diagonal maximum `l_k` in the Burr--Erdős--Faudree--Rousseau--Schelp
conjecture. Indices in the source start at one, hence the `+ 2`. -/
noncomputable def diagonalMax {s t : ℕ} (a : Fin s → ℕ)
    (b : Fin t → ℕ) (k : ℕ) : ℕ :=
  sSup {l : ℕ | ∃ i j, i.val + j.val + 2 = k ∧
    l = a i + b j - 1}

/-- Erdős Problem 561: the asymmetric size Ramsey number of two star forests
equals the sum of the diagonal maxima. -/
abbrev statement : Prop :=
  ∀ (s t : ℕ), 0 < s → 0 < t →
    ∀ (a : Fin s → ℕ) (b : Fin t → ℕ),
      Antitone a → Antitone b →
      (∀ i, 1 ≤ a i) → (∀ j, 1 ≤ b j) →
      sizeRamsey (starForest a) (starForest b) =
        ∑ k ∈ Finset.Icc 2 (s + t), diagonalMax a b k

theorem target : statement := sorry

end Statements.Erdos561StarForestSizeRamsey
