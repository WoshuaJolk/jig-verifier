import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter

/-!
# Erdős problem 159

Is `R(C₄,K_n) = O(n^(2-c))` for some absolute `c > 0`?
-/

namespace Statements.Erdos159C4CliqueRamsey

def ContainsCopy {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ f : V → W, Function.Injective f ∧
    ∀ ⦃u v⦄, G.Adj u v → H.Adj (f u) (f v)

def RamseyAtMost {V W : Type*}
    (G : SimpleGraph V) (K : SimpleGraph W) (N : ℕ) : Prop :=
  ∀ H : SimpleGraph (Fin N), ContainsCopy G H ∨ ContainsCopy K Hᶜ

noncomputable def ramseyNumber {V W : Type*}
    (G : SimpleGraph V) (K : SimpleGraph W) : ℕ :=
  sInf {N : ℕ | RamseyAtMost G K N}

noncomputable def c4CliqueRamsey (n : ℕ) : ℕ :=
  ramseyNumber (SimpleGraph.cycleGraph 4) (⊤ : SimpleGraph (Fin n))

abbrev statement : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ᶠ n : ℕ in atTop,
      (c4CliqueRamsey n : ℝ) ≤ C * (n : ℝ) ^ (2 - c)

theorem target : statement := sorry

end Statements.Erdos159C4CliqueRamsey
