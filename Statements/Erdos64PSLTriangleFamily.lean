import Mathlib.Combinatorics.SimpleGraph.Cayley
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Statements.Erdos64PSLTriangleFamily
open Matrix
open scoped MatrixGroups

abbrev statement : Prop :=
  ∀ (p : ℕ) [Fact (Nat.Prime p)], 5 ≤ p →
    ∃ (k : ℕ) (v : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))
      (walk : (SimpleGraph.mulCayley
        ({(QuotientGroup.mk
            (⟨!![0, -1; 1, 1], by simp [Matrix.det_fin_two]⟩ :
              Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :
              Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)),
          (QuotientGroup.mk
            (⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩ :
              Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :
              Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))} :
          Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)))).Walk v v),
      2 ≤ k ∧ walk.IsCycle ∧ walk.length = 2 ^ k ∧ walk.length < 8 * p

end Statements.Erdos64PSLTriangleFamily
