import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter

/-!
# Erdős problem 87

For every fixed positive `ε`, does every sufficiently high-chromatic finite
graph have diagonal Ramsey number greater than
`(1-ε)^k R(K_k)`?
-/

namespace Statements.Erdos87ChromaticRamseyLower

def ContainsCopy {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ f : V → W, Function.Injective f ∧
    ∀ ⦃u v⦄, G.Adj u v → H.Adj (f u) (f v)

def RamseyAtMost {V : Type*} (G : SimpleGraph V) (N : ℕ) : Prop :=
  ∀ H : SimpleGraph (Fin N), ContainsCopy G H ∨ ContainsCopy G Hᶜ

noncomputable def ramseyNumber {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {N : ℕ | RamseyAtMost G N}

noncomputable def cliqueRamsey (k : ℕ) : ℕ :=
  ramseyNumber (⊤ : SimpleGraph (Fin k))

abbrev statement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ k : ℕ in atTop,
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
        G.chromaticNumber = (k : ℕ∞) →
          (1 - ε) ^ k * cliqueRamsey k < ramseyNumber G

theorem target : statement := sorry

end Statements.Erdos87ChromaticRamseyLower
