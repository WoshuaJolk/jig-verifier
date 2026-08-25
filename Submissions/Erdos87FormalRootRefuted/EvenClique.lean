import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic

open Filter

namespace Submissions.Erdos87FormalRootRefuted.EvenClique

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
    ¬ (∀ ε : ℝ, 0 < ε →
      ∀ᶠ k : ℕ in atTop,
        ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
          G.chromaticNumber = (k : ℕ∞) →
            (1 - ε) ^ k * cliqueRamsey k < ramseyNumber G) := by
  intro h
  have hε := h 2 (by norm_num)
  rw [eventually_atTop] at hε
  obtain ⟨K, hK⟩ := hε
  let k : ℕ := 2 * (K + 1)
  have hKk : K ≤ k := by
    dsimp [k]
    omega
  have hbad := hK k hKk k (⊤ : SimpleGraph (Fin k))
  have hchrom :
      (⊤ : SimpleGraph (Fin k)).chromaticNumber = (k : ℕ∞) := by
    simp [SimpleGraph.chromaticNumber_top]
  specialize hbad hchrom
  have hpow : (1 - (2 : ℝ)) ^ k = 1 := by
    dsimp [k]
    rw [pow_mul]
    norm_num
  rw [hpow, one_mul] at hbad
  exact lt_irrefl _ hbad

end Submissions.Erdos87FormalRootRefuted.EvenClique
