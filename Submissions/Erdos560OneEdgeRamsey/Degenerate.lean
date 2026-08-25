import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic

namespace Submissions.Erdos560OneEdgeRamsey.Degenerate

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

/-- Must-fail control: adds an impossible hypothesis. -/
theorem proof : False → IsRamseyForKnn 1 oneEdge := False.elim

end Submissions.Erdos560OneEdgeRamsey.Degenerate
