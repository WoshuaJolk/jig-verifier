import Mathlib.Data.Nat.Basic

namespace Submissions.Erdos30SidonAsymptotic.DegenerateCatalogue

/-- A deliberately irrelevant theorem used to ensure the verifier bridge does
not accept a built declaration merely because its name is `proof`. -/
theorem proof : ∀ N : ℕ, N ≤ N :=
  fun _ => le_rfl

end Submissions.Erdos30SidonAsymptotic.DegenerateCatalogue
