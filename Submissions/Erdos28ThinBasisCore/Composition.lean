import Mathlib.Algebra.Group.Pointwise.Set.Finite
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.LiminfLimsup

open Filter Set
open scoped Pointwise

namespace Submissions.Erdos28ThinBasisCore.Composition

noncomputable def representationCount (A : Set ℕ) (n : ℕ) : ℕ := by
  classical
  exact ((Finset.antidiagonal n).filter fun (p : ℕ × ℕ) =>
    p.1 ∈ A ∧ p.2 ∈ A).card

def Root : Prop :=
  ∀ A : Set ℕ, (A + A)ᶜ.Finite →
    limsup (fun n : ℕ => (representationCount A n : ℕ∞)) atTop = (⊤ : ℕ∞)

def RepresentationPositive : Prop :=
  ∀ (A : Set ℕ) (n : ℕ),
    0 < representationCount A n ↔ n ∈ A + A

def CofiniteLimsup : Prop :=
  ∀ A : Set ℕ, Aᶜ.Finite →
    limsup (fun n : ℕ => (representationCount A n : ℕ∞)) atTop = (⊤ : ℕ∞)

def ThinCore : Prop :=
  ∀ A : Set ℕ, (A + A)ᶜ.Finite → ¬ Aᶜ.Finite →
    (limsup (fun n : ℕ => (representationCount A n : ℕ∞)) atTop =
        (⊤ : ℕ∞)) ∧
      ∀ n : ℕ, 0 < representationCount A n ↔ n ∈ A + A

abbrev statement : Prop :=
  RepresentationPositive → CofiniteLimsup → (Root ↔ ThinCore)

theorem proof : statement := by
  intro hPositive hCofinite
  constructor
  · intro hRoot A hBasis hThin
    exact ⟨hRoot A hBasis, hPositive A⟩
  · intro hThin A hBasis
    by_cases hCof : Aᶜ.Finite
    · exact hCofinite A hCof
    · exact (hThin A hBasis hCof).1

end Submissions.Erdos28ThinBasisCore.Composition
