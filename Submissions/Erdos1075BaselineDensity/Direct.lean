import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Tactic

namespace Submissions.Erdos1075BaselineDensity.Direct

open Filter

def InducedEdgeCount {V : Type} [DecidableEq V]
    (F : Finset (Finset V)) (S : Finset V) : ℕ :=
  (F.filter fun A => A ⊆ S).card

theorem proof :
    ∀ r : ℕ, 3 ≤ r → ∀ ε : ℝ, 0 < ε → ∀ K : ℕ,
      ∀ᶠ n : ℕ in atTop,
        ∀ F : Finset (Finset (Fin n)),
          (1 + ε) * ((n : ℝ) / (r : ℝ)) ^ r ≤ (F.card : ℝ) →
          ∃ S : Finset (Fin n), K ≤ S.card ∧
            (1 / (r : ℝ) ^ r) * (S.card : ℝ) ^ r ≤
              (InducedEdgeCount F S : ℝ) := by
  intro r hr ε hε K
  filter_upwards [eventually_ge_atTop K] with n hn
  intro F hF
  refine ⟨Finset.univ, by simpa using hn, ?_⟩
  simp only [Finset.card_univ, Fintype.card_fin]
  have hr0 : (0 : ℝ) < r := by positivity
  have hbase : 0 ≤ ((n : ℝ) / (r : ℝ)) ^ r := by positivity
  calc
    (1 / (r : ℝ) ^ r) * (n : ℝ) ^ r =
        ((n : ℝ) / (r : ℝ)) ^ r := by
          rw [div_pow]
          field_simp
    _ ≤ (1 + ε) * ((n : ℝ) / (r : ℝ)) ^ r := by
          nlinarith
    _ ≤ (F.card : ℝ) := hF
    _ = (InducedEdgeCount F (Finset.univ : Finset (Fin n)) : ℕ) := by
          simp [InducedEdgeCount]

end Submissions.Erdos1075BaselineDensity.Direct
