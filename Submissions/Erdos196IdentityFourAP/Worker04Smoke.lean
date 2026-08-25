import Mathlib.Algebra.Module.NatInt

namespace Submissions.Erdos196IdentityFourAP.Worker04Smoke

def ListIsAPOfLengthWith (s : List ℕ) (k a d : ℕ) : Prop :=
  s = (List.range k).map (fun n ↦ a + n • d) ∨
  s = (List.range k).reverse.map (fun n ↦ a + n • d)

def ListIsAPOfLength (s : List ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, ListIsAPOfLengthWith s k a d

def HasMonotoneAP (f : ℕ → ℕ) (k : ℕ) : Prop :=
  ∃ l : List ℕ, ListIsAPOfLength (l.map f) k ∧ l.Pairwise (· < ·)

theorem proof : HasMonotoneAP (Equiv.refl ℕ) 4 := by
  refine ⟨[0, 1, 2, 3], ⟨0, 1, Or.inl (by decide)⟩, by decide⟩

end Submissions.Erdos196IdentityFourAP.Worker04Smoke
