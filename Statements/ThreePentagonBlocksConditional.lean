import Commons.SetPairSystem
import Mathlib.Data.Fin.Basic

namespace Statements.ThreePentagonBlocksConditional

/-- The published small-case bound, explicitly an antecedent. -/
def SmallCaseBound : Prop :=
  ∀ (m : ℕ) (A B : Fin m → Finset ℕ),
    Commons.OneCrossSPS 3 3 m A B → m ≤ 10

/-- Four outer points and three disjoint inner pentagons use nineteen points. -/
def blockA (x : Fin 19 → ℕ) (g : Fin 3) (j : Fin 5) : Finset ℕ :=
  {x ⟨g.val, by omega⟩,
   x ⟨g.val + 1, by omega⟩,
   x ⟨4 + 5 * g.val + j.val, by omega⟩,
   x ⟨4 + 5 * g.val + ((j.val + 1) % 5), by omega⟩}

/-- Only A sets are prescribed; all B sets and all remaining indices are free. -/
def ContainsThreeBlocks {m : ℕ} (A : Fin m → Finset ℕ) : Prop :=
  ∃ (x : Fin 19 → ℕ) (ι : Fin 3 × Fin 5 → Fin m),
    Function.Injective x ∧ Function.Injective ι ∧
      ∀ (g : Fin 3) (j : Fin 5), A (ι (g, j)) = blockA x g j

abbrev statement : Prop :=
  SmallCaseBound →
    ∀ (m : ℕ) (A B : Fin m → Finset ℕ),
      Commons.OneCrossSPS 4 4 m A B → ContainsThreeBlocks A → m ≤ 25

/-- Proposed statement only. The written proof is not a Lean proof artifact. -/
theorem target : statement := sorry

end Statements.ThreePentagonBlocksConditional
