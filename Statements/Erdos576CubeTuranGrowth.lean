import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Card
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter

/-!
# Erdős problem 576

Is the Turán number of the three-dimensional cube of order `n^(8/5)`?
-/

namespace Statements.Erdos576CubeTuranGrowth

abbrev CubeVertex := Fin 3 → Bool

def CubeAdj (x y : CubeVertex) : Prop :=
  ∃ i : Fin 3, x i ≠ y i ∧ ∀ j : Fin 3, j ≠ i → x j = y j

def ContainsCube {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ f : CubeVertex → V,
    Function.Injective f ∧
      ∀ ⦃x y⦄, CubeAdj x y → G.Adj (f x) (f y)

noncomputable def cubeExtremal (n : ℕ) : ℕ :=
  sSup {e : ℕ | ∃ G : SimpleGraph (Fin n),
    ¬ ContainsCube G ∧ e = Set.ncard G.edgeSet}

abbrev statement : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ^ (8 / 5 : ℝ) ≤ cubeExtremal n ∧
        (cubeExtremal n : ℝ) ≤ C * (n : ℝ) ^ (8 / 5 : ℝ)

theorem target : statement := sorry

end Statements.Erdos576CubeTuranGrowth
