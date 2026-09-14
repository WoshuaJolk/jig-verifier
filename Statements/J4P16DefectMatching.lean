import Init

namespace Statements.J4P16DefectMatching

def Defect {I X : Type} (R : I → I → X → Prop) (s : I) (x : X) : Prop :=
  ∃ i j, i ≠ j ∧ R s i x ∧ R s j x

def Family {I X : Type} (A : X → Prop) (R : I → I → X → Prop) : Option I → X → Prop
  | none => A
  | some i => R i i


def statement : Prop :=
(∀ {I X : Type}
    (A C : X → Prop) (R : I → I → X → Prop)
    (trace : ∀ s i x, (R s i x ∧ A x) ↔ C x)
    (compatible : ∀ s t i j x, R s i x → R t j x → R s j x)
    (disjoint : ∀ s t, s ≠ t → ∀ x, ¬ A x → Defect R s x → Defect R t x → False)
    (outside : ∀ i, ∃ x, R i i x ∧ ¬ A x),
(∀ u v, Family A R u = Family A R v → u = v) ∧
    (∀ u v, u ≠ v → ∀ x,
      (Family A R u x ∧ Family A R v x) ↔ C x))

end Statements.J4P16DefectMatching
