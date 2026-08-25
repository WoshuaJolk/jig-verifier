import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.QuotientGroup.Finite

namespace Submissions.Erdos117FiniteStemAssembly.ThirdWorker

open QuotientGroup Subgroup

universe u v

theorem proof :
    ∀ (G : Type u) (H : Type v) (_ : Group G) (_ : Group H),
      Finite (G ⧸ center G) →
      Finite (commutator G) →
      ((G ⧸ center G) ≃* (H ⧸ center H)) →
      (commutator G ≃* commutator H) →
      center H ≤ commutator H →
      Finite H := by
  intro G H _ _ hGQuot hGDer α β hstem
  letI : Finite (G ⧸ center G) := hGQuot
  letI : Finite (commutator G) := hGDer
  letI : Finite (H ⧸ center H) :=
    Finite.of_equiv (G ⧸ center G) α.toEquiv
  letI : Finite (commutator H) :=
    Finite.of_equiv (commutator G) β.toEquiv
  letI : Finite (center H) :=
    Finite.of_injective (Subgroup.inclusion hstem)
      (Subgroup.inclusion_injective hstem)
  exact Finite.of_subgroup_quotient (center H)

end Submissions.Erdos117FiniteStemAssembly.ThirdWorker
