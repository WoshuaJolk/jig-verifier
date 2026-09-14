import Mathlib.Algebra.Module.Submodule.Defs

namespace Statements.J5P26RectangularGluing

universe uR uU uO uK

variable {R U O K : Type*} [Ring R] [AddCommGroup U] [Module R U]
variable [AddCommGroup O] [Module R O]

def Cover (D A B C : Submodule R U) : Prop :=
  ∀ h, h ∈ D → ∃ x y, x ∈ D ∧ x ∈ A ∧ y ∈ D ∧ y ∈ B ∧ y ∈ C ∧ h = x + y

abbrev statement : Prop :=
  (∀ {R : Type uR} {U : Type uU} {K : Type uK} [Ring R] [AddCommGroup U] [Module R U] [AddCommGroup K]
    (D A1 A2 A3 : Submodule R U) (f1 f2 f3 : U → K)
    (f1a : ∀ x y, f1 (x + y) = f1 x + f1 y)
    (f2a : ∀ x y, f2 (x + y) = f2 x + f2 y)
    (f3a : ∀ x y, f3 (x + y) = f3 x + f3 y)
    (dmem : ∀ u, u ∈ D ↔ f1 u = 0 ∧ f2 u = 0 ∧ f3 u = 0)
    (v1 : ∀ u, u ∈ A1 → f1 u = 0)
    (v2 : ∀ u, u ∈ A2 → f2 u = 0)
    (v3 : ∀ u, u ∈ A3 → f3 u = 0)
    (raw : ∀ h, h ∈ D → ∃ x y, x ∈ A1 ∧ y ∈ A2 ∧ y ∈ A3 ∧ h = x + y), Cover D A1 A2 A3) ∧
  (∀ {R : Type uR} {U : Type uU} {O : Type uO} {K : Type uK} [Ring R] [AddCommGroup U] [Module R U] [AddCommGroup O] [Module R O] [AddCommGroup K]
    (D A1 A2 A3 : Submodule R U) (W1 W2 W3 : Submodule R O)
    (c1 : Cover D A1 A2 A3) (c2 : Cover D A2 A1 A3)
    (Q : U → O → K)
    (qa : ∀ x y z, Q (x + y) z = Q x z + Q y z)
    (qz : ∀ h x y, Q h (x + y) = Q h x + Q h y)
    (w12 : ∀ z, ∃ x y, x ∈ W1 ∧ y ∈ W2 ∧ z = x + y)
    (w13 : ∀ z, ∃ x y, x ∈ W1 ∧ y ∈ W3 ∧ z = x + y)
    (w23 : ∀ z, ∃ x y, x ∈ W2 ∧ y ∈ W3 ∧ z = x + y)
    (v1 : ∀ h, h ∈ D → h ∈ A1 → ∀ z, z ∈ W1 → Q h z = 0)
    (v2 : ∀ h, h ∈ D → h ∈ A2 → ∀ z, z ∈ W2 → Q h z = 0)
    (v3 : ∀ h, h ∈ D → h ∈ A3 → ∀ z, z ∈ W3 → Q h z = 0)
    (h : U) (hd : h ∈ D) (z : O), Q h z = 0)

end Statements.J5P26RectangularGluing
