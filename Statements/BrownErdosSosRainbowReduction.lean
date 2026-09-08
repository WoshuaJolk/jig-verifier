import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Topology.Instances.Nat
import Mathlib.Combinatorics.SimpleGraph.Triangle.Tripartite

/-!
Known tripartite/rainbow reformulations of Brown–Erdős–Sós, with the finite
three-projection obstruction made explicit. Credit: Gyárfás–Sárközy (2023),
Proposition 1.6, and the Mathlib and prior Ruzsa–Szemerédi formalizations
documented in the accompanying proof. This statement does not assert the
remaining density bound or resolve the full Brown–Erdős–Sós question.
-/

namespace Statements.BrownErdosSosRainbowReduction

open Filter Finset SimpleGraph.TripartiteFromTriangles
open scoped Topology

abbrev Hypergraph (n : ℕ) := Finset (Finset (Fin n))

def IsUniform (r : ℕ) {n : ℕ} (G : Hypergraph n) : Prop :=
  ∀ edge ∈ G, edge.card = r

def HasCopy {d n : ℕ} (F : Hypergraph d) (G : Hypergraph n) : Prop :=
  ∃ f : Fin d ↪ Fin n, ∀ edge ∈ F, edge.image f ∈ G

def AvoidsFamily (r d e n : ℕ) (G : Hypergraph n) : Prop :=
  IsUniform r G ∧
    ∀ F : Hypergraph d, IsUniform r F → F.card = e → ¬HasCopy F G

noncomputable def extremal (r d e n : ℕ) : ℕ :=
  open scoped Classical in
    Finset.univ.sup fun G : Hypergraph n =>
      if AvoidsFamily r d e n G then G.card else 0

def HasQuadraticVanishing (r d e : ℕ) : Prop :=
  (fun n => (extremal r d e n : ℝ)) =o[atTop]
    (fun n => (n : ℝ) ^ 2)

def coordinateSupport {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (T : Finset (α × β × γ)) : ℕ :=
  (T.image Prod.fst).card + (T.image fun p => p.2.1).card +
    (T.image fun p => p.2.2).card

def TripartiteRelationBound (e : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n ≥ N,
    ∀ T : Finset (Fin n × Fin n × Fin n), ExplicitDisjoint T →
      (∀ S ⊆ T, S.card = e → e + 3 < coordinateSupport S) →
      (T.card : ℝ) ≤ δ * (n : ℝ) ^ 2

section

variable {α β γ δ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-- A repeated diagonal color; properness additionally follows from `ExplicitDisjoint`. -/
def RepeatedRectangle (T : Finset (α × β × γ)) : Prop :=
  ∃ a a' b b' c₀₀ c₀₁ c₁₀ c₁₁,
    a ≠ a' ∧ b ≠ b' ∧
    (a, b, c₀₀) ∈ T ∧ (a, b', c₀₁) ∈ T ∧
    (a', b, c₁₀) ∈ T ∧ (a', b', c₁₁) ∈ T ∧
    (c₀₀ = c₁₁ ∨ c₀₁ = c₁₀)

def rotateTriples (T : Finset (α × β × γ)) : Finset (β × γ × α) :=
  T.image fun p => (p.2.1, p.2.2, p.1)

end

/-- Under `ExplicitDisjoint`, every four-cycle in each projection has four different colors. -/
def AllRectanglesRainbow {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (T : Finset (α × β × γ)) : Prop :=
  ¬ RepeatedRectangle T ∧ ¬ RepeatedRectangle (rotateTriples T) ∧
    ¬ RepeatedRectangle (rotateTriples (rotateTriples T))

def RainbowDensityBound : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n ≥ N,
    ∀ T : Finset (Fin n × Fin n × Fin n), ExplicitDisjoint T →
      AllRectanglesRainbow T → (T.card : ℝ) ≤ δ * (n : ℝ) ^ 2

def twoProjectionTrap : Finset (Fin 3 × Fin 3 × Fin 3) :=
  {(0, 0, 0), (0, 1, 1), (1, 0, 2), (1, 1, 0)}

abbrev statement : Prop :=
  (∀ e : ℕ, 3 ≤ e →
    (HasQuadraticVanishing 3 (e + 3) e ↔ TripartiteRelationBound e)) ∧
  (HasQuadraticVanishing 3 7 4 ↔ RainbowDensityBound) ∧
  SimpleGraph.TripartiteFromTriangles.ExplicitDisjoint twoProjectionTrap ∧
  (twoProjectionTrap.card = 4 ∧ coordinateSupport twoProjectionTrap = 7) ∧
  (RepeatedRectangle twoProjectionTrap ∧
    ¬RepeatedRectangle (rotateTriples twoProjectionTrap) ∧
    ¬RepeatedRectangle (rotateTriples (rotateTriples twoProjectionTrap)))

theorem target : statement := sorry

end Statements.BrownErdosSosRainbowReduction
