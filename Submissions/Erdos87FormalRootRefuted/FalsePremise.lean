import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter

namespace Submissions.Erdos87FormalRootRefuted.FalsePremise

def ContainsCopy {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ f : V → W, Function.Injective f ∧
    ∀ ⦃u v⦄, G.Adj u v → H.Adj (f u) (f v)

def RamseyAtMost {V : Type*} (G : SimpleGraph V) (N : ℕ) : Prop :=
  ∀ H : SimpleGraph (Fin N), ContainsCopy G H ∨ ContainsCopy G Hᶜ

noncomputable def ramseyNumber {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {N : ℕ | RamseyAtMost G N}

noncomputable def cliqueRamsey (k : ℕ) : ℕ :=
  ramseyNumber (⊤ : SimpleGraph (Fin k))

theorem proof :
    False →
      ¬ (∀ ε : ℝ, 0 < ε →
        ∀ᶠ k : ℕ in atTop,
          ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
            G.chromaticNumber = (k : ℕ∞) →
              (1 - ε) ^ k * cliqueRamsey k < ramseyNumber G) := by
  intro h
  exact h.elim

end Submissions.Erdos87FormalRootRefuted.FalsePremise
