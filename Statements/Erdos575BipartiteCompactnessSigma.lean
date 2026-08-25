import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter SimpleGraph

namespace Statements.Erdos575BipartiteCompactnessSigma

noncomputable section

/-- Erdős 575 has a negative answer: a finite family containing a
bipartite graph need not be controlled by any bipartite member.

The dependent pair is a public structural graph type. All predicates are
inlined so a standalone submission can state this exact proposition without
importing the canonical `Statements` module. -/
abbrev statement : Prop := by
  classical
  exact
    ∃ family : Finset (Σ n : ℕ, SimpleGraph (Fin n)),
      family.Nonempty ∧
      (∃ forbidden ∈ family, forbidden.2.IsBipartite) ∧
      ¬ ∃ forbidden ∈ family, forbidden.2.IsBipartite ∧
        ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
          (extremalNumber n forbidden.2 : ℝ) ≤ C *
            (((Finset.univ.filter fun host : SimpleGraph (Fin n) =>
                ∀ member ∈ family, member.2.Free host).sup
              fun host : SimpleGraph (Fin n) => host.edgeFinset.card : ℕ) : ℝ)

theorem target : statement := sorry

end

end Statements.Erdos575BipartiteCompactnessSigma
