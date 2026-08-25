import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

namespace Statements.Erdos668ManyUnitDistanceMaximizers

open Filter

abbrev Point := Fin 2 → ℝ
abbrev Configuration (n : ℕ) := Fin n → Point

def squaredDistance (p q : Point) : ℝ :=
  (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2

noncomputable def unitPairs {n : ℕ} (P : Configuration n) :
    Finset (Fin n × Fin n) :=
  (Finset.univ ×ˢ Finset.univ).filter fun ij =>
    ij.1 < ij.2 ∧ squaredDistance (P ij.1) (P ij.2) = 1

def IsMaximizer {n : ℕ} (P : Configuration n) : Prop :=
  Function.Injective P ∧
    ∀ Q : Configuration n, Function.Injective Q →
      (unitPairs Q).card ≤ (unitPairs P).card

def Congruent {n : ℕ} (P Q : Configuration n) : Prop :=
  ∃ e : Fin n ≃ Fin n, ∀ i j : Fin n,
    squaredDistance (P i) (P j) =
      squaredDistance (Q (e i)) (Q (e j))

/-- Erdős problem 668: maximizers of the planar unit-distance problem
    have unboundedly many congruence classes. -/
abbrev statement : Prop :=
  ∀ M : ℕ, ∀ᶠ n : ℕ in atTop,
    ∃ family : Fin M → Configuration n,
      (∀ a, IsMaximizer (family a)) ∧
        ∀ a b, a ≠ b → ¬ Congruent (family a) (family b)

theorem target : statement := sorry

end Statements.Erdos668ManyUnitDistanceMaximizers
