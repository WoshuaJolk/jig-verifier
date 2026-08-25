import Mathlib

/-!
# ClutchedVandermondeRanks

A rational normal curve remains maximally independent after its constant and
top-degree coordinates are clutched together.  The theorem records the two
uniform rank properties needed by the nodal elliptic seed construction.
-/

namespace Statements.ClutchedVandermondeRanks

noncomputable def clutch (k : ℕ) (tau z : ℂ) : Fin k → ℂ := fun q =>
  if q.val = 0 then 1 + tau * z ^ k else z ^ q.val

abbrev statement : Prop :=
  ∀ (k n : ℕ), 2 ≤ k → ∀ (tau : ℂ) (z : Fin n → ℂ),
    Function.Injective z →
      ((∀ (_hnz : ∀ i, z i ≠ 0) (f : Fin (k - 1) → Fin n),
          Function.Injective f →
            LinearIndependent ℂ (fun i => clutch k tau (z (f i)))) ∧
       (∀ (f : Fin (k + 1) → Fin n), Function.Injective f →
          Submodule.span ℂ (Set.range fun i => clutch k tau (z (f i))) = ⊤))

theorem target : statement := sorry

end Statements.ClutchedVandermondeRanks
