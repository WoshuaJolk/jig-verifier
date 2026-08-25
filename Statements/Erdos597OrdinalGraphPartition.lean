import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Ordinal.Arithmetic

open Cardinal SimpleGraph
open scoped Ordinal

namespace Statements.Erdos597OrdinalGraphPartition

/-- The first uncountable ordinal. -/
noncomputable def omegaOne : Ordinal.{0} := Ordinal.omega 1

/-- The source order type `ω₁²`. -/
noncomputable def source : Ordinal.{0} := omegaOne ^ (2 : ℕ)

/-- The red target order type `ω₁·ω`. -/
noncomputable def redTarget : Ordinal.{0} :=
  omegaOne * Ordinal.omega0

/-- A binary function represents a coloring of unordered pairs when it is
symmetric. Its diagonal values are ignored. -/
def Symmetric {α : Type*} (color : α → α → Bool) : Prop :=
  ∀ x y, color x y = color y x

/-- `α → (β, G)²`: every red/blue coloring of the unordered pairs of `α`
has either a red set of order type `β` or a blue (not necessarily induced)
copy of `G`. False is the red color and true is the blue color. -/
def OrdinalGraphPartition {V : Type}
    (α β : Ordinal.{0}) (G : SimpleGraph V) : Prop :=
  ∀ color : α.ToType → α.ToType → Bool,
    Symmetric color →
      (∃ H : Set α.ToType,
        typeLT H = β ∧
          ∀ x ∈ H, ∀ y ∈ H, x ≠ y → color x y = false) ∨
      (∃ copy : V ↪ α.ToType,
        ∀ ⦃x y : V⦄, G.Adj x y → color (copy x) (copy y) = true)

/-- `G` contains a copy of `K_{ℵ₀,ℵ₀}` exactly when it has two disjoint
countably infinite vertex sets with all cross-edges present. Edges inside the
two classes are irrelevant because the copy need not be induced. -/
def HasCountableBiclique {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ L R : Set V,
    Disjoint L R ∧ #L = ℵ₀ ∧ #R = ℵ₀ ∧
      ∀ l ∈ L, ∀ r ∈ R, G.Adj l r

/-- Erdős Problem 597. Every graph on at most `ℵ₁` vertices containing
neither `K₄` nor `K_{ℵ₀,ℵ₀}` satisfies
`ω₁² → (ω₁·ω, G)²`. This is the first, general question in the source;
the separately printed finite-graph question is its special case. -/
abbrev statement : Prop :=
  ∀ (V : Type) (G : SimpleGraph V),
    #V ≤ aleph 1 →
    (completeGraph (Fin 4)).Free G →
    ¬HasCountableBiclique G →
    OrdinalGraphPartition source redTarget G

theorem target : statement := sorry

end Statements.Erdos597OrdinalGraphPartition
