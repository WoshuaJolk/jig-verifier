import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Topology.Instances.Nat

namespace Statements.Erdos1178BrownErdosSosThreshold

open Filter Finset
open scoped Topology

abbrev Hypergraph (n : ℕ) := Finset (Finset (Fin n))

def IsUniform (r : ℕ) {n : ℕ} (G : Hypergraph n) : Prop :=
  ∀ edge ∈ G, edge.card = r

def HasCopy {d n : ℕ} (F : Hypergraph d) (G : Hypergraph n) : Prop :=
  ∃ f : Fin d ↪ Fin n,
    ∀ edge ∈ F, edge.image f ∈ G

def AvoidsFamily (r d e n : ℕ) (G : Hypergraph n) : Prop :=
  IsUniform r G ∧
    ∀ F : Hypergraph d,
      IsUniform r F → F.card = e → ¬HasCopy F G

noncomputable def extremal (r d e n : ℕ) : ℕ :=
  open scoped Classical in
    Finset.univ.sup fun G : Hypergraph n =>
      if AvoidsFamily r d e n G then G.card else 0

def HasQuadraticVanishing (r d e : ℕ) : Prop :=
  (fun n => (extremal r d e n : ℝ)) =o[atTop]
    (fun n => (n : ℝ) ^ 2)

/-- Erdős Problem 1178 (Brown–Erdős–Sós): the first vertex count
forcing `o(n²)` extremal growth is `(r-2)e+3`. -/
abbrev statement : Prop :=
  ∀ r e : ℕ, 3 ≤ r → 3 ≤ e →
    let threshold := (r - 2) * e + 3
    HasQuadraticVanishing r threshold e ∧
      ∀ d < threshold, ¬HasQuadraticVanishing r d e

theorem target : statement := sorry

end Statements.Erdos1178BrownErdosSosThreshold
