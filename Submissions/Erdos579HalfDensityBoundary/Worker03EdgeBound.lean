import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Topology.Instances.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Filter SimpleGraph
open scoped Classical

namespace Submissions.Erdos579HalfDensityBoundary.Worker03EdgeBound

abbrev octahedron : SimpleGraph (Σ _ : Fin 3, Fin 2) :=
  completeMultipartiteGraph (fun _ : Fin 3 ↦ Fin 2)

theorem proof :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      ∀ G : SimpleGraph (Fin n), octahedron.Free G →
        (1 / 2 : ℝ) * (n : ℝ) ^ 2 ≤ G.edgeFinset.card →
          c * n ≤ (G.indepNum : ℝ) := by
  refine ⟨1, by norm_num, Filter.Eventually.of_forall ?_⟩
  intro n G _ hedge
  by_cases hn : n = 0
  · subst n
    norm_num
  have hcardNat : G.edgeFinset.card ≤ n.choose 2 := by
    simpa using G.card_edgeFinset_le_card_choose_two
  have hcard : (G.edgeFinset.card : ℝ) ≤ (n.choose 2 : ℕ) := by
    exact_mod_cast hcardNat
  have hchooseHalf :
      ((n.choose 2 : ℕ) : ℝ) < (n : ℝ) ^ 2 / (2 : ℕ).factorial := by
    exact Nat.choose_lt_pow_div hn (by norm_num)
  exfalso
  norm_num at hchooseHalf
  linarith

end Submissions.Erdos579HalfDensityBoundary.Worker03EdgeBound
