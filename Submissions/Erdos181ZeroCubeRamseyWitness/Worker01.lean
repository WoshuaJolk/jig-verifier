import Mathlib.Tactic

namespace Submissions.Erdos181ZeroCubeRamseyWitness.Worker01

def CubeAdj {n : ℕ} (u v : Fin n → Bool) : Prop :=
  ∃ coordinate, u coordinate ≠ v coordinate ∧
    ∀ i, i ≠ coordinate → u i = v i

def EveryColoringContainsCube (n N : ℕ) : Prop :=
  ∀ color : Fin N → Fin N → Bool,
    (∀ u v, color u v = color v u) →
      ∃ embedding : (Fin n → Bool) → Fin N,
        Function.Injective embedding ∧
          ∃ cubeColor : Bool, ∀ u v, CubeAdj u v →
            color (embedding u) (embedding v) = cubeColor

theorem proof : EveryColoringContainsCube 0 1 := by
  intro color _
  let embedding : (Fin 0 → Bool) → Fin 1 := fun _ ↦ 0
  refine ⟨embedding, ?_, false, ?_⟩
  · intro u v _
    funext i
    exact Fin.elim0 i
  · intro u v huv
    obtain ⟨i, _⟩ := huv
    exact Fin.elim0 i

end Submissions.Erdos181ZeroCubeRamseyWitness.Worker01
