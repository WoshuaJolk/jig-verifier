import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Order.Filter.AtTopBot.Basic

namespace Statements.Erdos133OptimalTriangleFreeDiameterTwo

open Filter

noncomputable def vertexDegree {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : ℕ :=
  Set.ncard (G.neighborSet v)

def IsTriangleFree {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ u v w, G.Adj u v → G.Adj v w → ¬G.Adj w u

def HasDiameterAtMostTwo {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ u v, u = v ∨ G.Adj u v ∨ ∃ w, G.Adj u w ∧ G.Adj w v

/-- The remaining sharp form of Erdős Problem 133, attributed on the current
problem page to Alon: asymptotically Moore-optimal triangle-free diameter-two
graphs exist. -/
abbrev statement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ n : ℕ in atTop, ∃ G : SimpleGraph (Fin n),
      IsTriangleFree G ∧ HasDiameterAtMostTwo G ∧
        ∀ v, (vertexDegree G v : ℝ) ≤ (1 + ε) * Real.sqrt n

theorem target : statement := sorry

end Statements.Erdos133OptimalTriangleFreeDiameterTwo
