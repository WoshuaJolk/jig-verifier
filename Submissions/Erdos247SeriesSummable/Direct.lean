import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

namespace Submissions.Erdos247SeriesSummable.Direct

theorem proof :
    ∀ n : ℕ → ℕ, StrictMono n →
      Summable (fun k => (1 : ℝ) / 2 ^ n k) := by
  intro n hn
  have hgeo : Summable (fun k : ℕ => ((1 : ℝ) / 2) ^ k) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  apply hgeo.of_nonneg_of_le
  · intro k
    positivity
  · intro k
    simpa only [one_div_pow, id_eq] using
      (pow_le_pow_of_le_one (a := (1 : ℝ) / 2)
        (by norm_num) (by norm_num) (hn.id_le k))

end Submissions.Erdos247SeriesSummable.Direct
