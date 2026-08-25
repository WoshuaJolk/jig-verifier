import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

namespace Statements.Erdos217DistanceMultiplicityFinite

open Filter

def sqDist (p q : ℝ × ℝ) : ℝ :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

def Collinear (p q r : ℝ × ℝ) : Prop :=
  (q.1 - p.1) * (r.2 - p.2) = (q.2 - p.2) * (r.1 - p.1)

def Concyclic (p q r s : ℝ × ℝ) : Prop :=
  ∃ center : ℝ × ℝ,
    sqDist center p = sqDist center q ∧
    sqDist center p = sqDist center r ∧
    sqDist center p = sqDist center s

noncomputable def pairs (n : ℕ) : Finset (Fin n × Fin n) := by
  classical
  exact Finset.univ.filter fun ij ↦ ij.1 < ij.2

noncomputable def multiplicity {n : ℕ} (P : Fin n → ℝ × ℝ) (d : ℝ) : ℕ := by
  classical
  exact ((pairs n).filter fun ij ↦ sqDist (P ij.1) (P ij.2) = d).card

def IsConfiguration {n : ℕ} (P : Fin n → ℝ × ℝ) : Prop :=
  Function.Injective P ∧
  (∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    ¬Collinear (P i) (P j) (P k)) ∧
  (∀ i j k l, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
    ¬Concyclic (P i) (P j) (P k) (P l)) ∧
  ∃ distance : Fin (n - 1) → ℝ,
    Function.Injective distance ∧
    (∀ rank, multiplicity P (distance rank) = rank.1 + 1) ∧
    ∀ ij ∈ pairs n, ∃ rank, sqDist (P ij.1) (P ij.2) = distance rank

/-- Erdős Problem 217: only finitely many sizes admit a general-position
planar point set whose `n-1` distances occur with multiplicities
`1,2,...,n-1`. -/
abbrev statement : Prop :=
  ∀ᶠ n : ℕ in atTop, ¬∃ P : Fin n → ℝ × ℝ, IsConfiguration P

theorem target : statement := sorry

end Statements.Erdos217DistanceMultiplicityFinite
