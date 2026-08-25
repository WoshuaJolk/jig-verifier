import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

namespace Statements.Erdos560BalancedBipartiteSizeRamsey

open Filter

abbrev FiniteGraph (N : ℕ) := Finset (Finset (Fin N))

def IsSimpleGraph {N : ℕ} (E : FiniteGraph N) : Prop :=
  ∀ e ∈ E, e.card = 2

def HasMonochromaticKnn {N : ℕ} (n : ℕ) (E : FiniteGraph N)
    (color : Finset (Fin N) → Bool) : Prop :=
  ∃ A B : Finset (Fin N), A.card = n ∧ B.card = n ∧ Disjoint A B ∧
    ∃ c : Bool, ∀ a ∈ A, ∀ b ∈ B,
      ({a, b} : Finset (Fin N)) ∈ E ∧ color {a, b} = c

def IsRamseyForKnn {N : ℕ} (n : ℕ) (E : FiniteGraph N) : Prop :=
  IsSimpleGraph E ∧ ∀ color : Finset (Fin N) → Bool,
    HasMonochromaticKnn n E color

noncomputable def sizeRamseyKnn (n : ℕ) : ℕ :=
  sSup {m : ℕ |
    (∃ N : ℕ, ∃ E : FiniteGraph N,
      IsRamseyForKnn n E ∧ E.card = m) ∧
    ∀ N : ℕ, ∀ E : FiniteGraph N,
      IsRamseyForKnn n E → m ≤ E.card}

/-- Erdős problem 560: the balanced complete-bipartite size Ramsey number
    has order `n^3 2^n`. -/
abbrev statement : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ᶠ n : ℕ in atTop,
      c * n ^ 3 * 2 ^ n ≤ sizeRamseyKnn n ∧
        (sizeRamseyKnn n : ℝ) ≤ C * n ^ 3 * 2 ^ n

theorem target : statement := sorry

end Statements.Erdos560BalancedBipartiteSizeRamsey
