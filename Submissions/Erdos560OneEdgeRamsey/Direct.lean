import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

namespace Submissions.Erdos560OneEdgeRamsey.Direct

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

theorem proof : IsRamseyForKnn 1 oneEdge := by
  constructor
  · intro e he
    simp only [oneEdge, Finset.mem_singleton] at he
    subst e
    decide
  · intro color
    refine ⟨{0}, {1}, by simp, by simp, by simp, color {0, 1}, ?_⟩
    intro a ha b hb
    simp only [Finset.mem_singleton] at ha hb
    subst a
    subst b
    exact ⟨by simp [oneEdge], rfl⟩

end Submissions.Erdos560OneEdgeRamsey.Direct
