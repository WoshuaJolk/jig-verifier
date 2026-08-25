import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic

namespace Statements.Erdos560OneEdgeRamsey

abbrev FiniteGraph (N : ℕ) := Finset (Finset (Fin N))

def IsSimpleGraph {N : ℕ} (E : FiniteGraph N) : Prop :=
  ∀ e ∈ E, e.card = 2

def HasMonochromaticKnn {N : ℕ} (n : ℕ) (E : FiniteGraph N)
    (color : Finset (Fin N) → Bool) : Prop :=
  ∃ A B : Finset (Fin N), A.card = n ∧ B.card = n ∧ Disjoint A B ∧
    ∃ c : Bool, ∀ a ∈ A, ∀ b ∈ B,
      ({a, b} : Finset (Fin N)) ∈ E ∧ color {a, b} = c

def IsRamseyForKnn {N : ℕ} (n : ℕ) (E : FiniteGraph N) : Prop :=
  IsSimpleGraph E ∧ ∀ color : Finset (Fin N) → Bool,
    HasMonochromaticKnn n E color

def oneEdge : FiniteGraph 2 := {{(0 : Fin 2), (1 : Fin 2)}}

/-- A single edge is Ramsey for `K_{1,1}`. -/
abbrev statement : Prop := IsRamseyForKnn 1 oneEdge

theorem target : statement := sorry

end Statements.Erdos560OneEdgeRamsey
