import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Real.Basic

namespace Statements.Erdos836LinearEdgeIntersection

abbrev Hypergraph (N : ℕ) := Finset (Finset (Fin N))

def IsUniform {N : ℕ} (r : ℕ) (G : Hypergraph N) : Prop :=
  ∀ e ∈ G, e.card = r

def IsIntersecting {N : ℕ} (G : Hypergraph N) : Prop :=
  ∀ e ∈ G, ∀ f ∈ G, (e ∩ f).Nonempty

def HasProperColoring {N : ℕ} (k : ℕ) (G : Hypergraph N) : Prop :=
  ∃ color : Fin N → Fin k, ∀ e ∈ G,
    ∃ x ∈ e, ∃ y ∈ e, color x ≠ color y

def HasChromaticNumberThree {N : ℕ} (G : Hypergraph N) : Prop :=
  HasProperColoring 3 G ∧ ¬ HasProperColoring 2 G

/-- The unresolved linear-intersection question in Erdős problem 836. -/
abbrev statement : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ r : ℕ, 2 ≤ r → ∀ N : ℕ, ∀ G : Hypergraph N,
      IsUniform r G → IsIntersecting G → HasChromaticNumberThree G →
        ∃ e ∈ G, ∃ f ∈ G, e ≠ f ∧ c * r ≤ (e ∩ f).card

theorem target : statement := sorry

end Statements.Erdos836LinearEdgeIntersection
