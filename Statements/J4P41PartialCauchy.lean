import Init

namespace Statements.J4P41PartialCauchy

namespace P41PartialCauchy

def Consistent {G : Type} (add : G → G → G) (D : G → Prop)
    (φ : G → Int) : Prop :=
  ∀ a b c d, D a → D b → D c → D d → add a b = add c d →
    φ a + φ b = φ c + φ d

def extend {G : Type} (φ : G → Int) (l r : G → G) (x : G) : Int :=
  φ (l x) + φ (r x)

end P41PartialCauchy

abbrev statement : Prop :=
  (∀ {G : Type} (add : G → G → G)
    (D : G → Prop) (φ : G → Int)
    (local_add : ∀ x y, D x → D y → D (add x y) → φ (add x y) = φ x + φ y)
    (bridge : ∀ a b c d, D a → D b → D c → D d → add a b = add c d →
      ∃ t u v w, D t ∧ D u ∧ D v ∧ D w ∧
        add t u = a ∧ add t v = c ∧ add u b = w ∧ add v d = w),
    P41PartialCauchy.Consistent add D φ) ∧
  (∀ {G : Type} (add : G → G → G) (neg : G → G)
    (D : G → Prop) (φ : G → Int) (l r : G → G)
    (hl : ∀ x, D (l x)) (hr : ∀ x, D (r x))
    (split : ∀ x, add (l x) (r x) = x) (consistent : P41PartialCauchy.Consistent add D φ)
    (antisymmetric : ∀ t, D t → φ t + φ (neg t) = 0)
    (merge : ∀ x y, ∃ t a b, D t ∧ D a ∧ D b ∧ D (neg t) ∧
      add t a = x ∧ add b (neg t) = y ∧ add a b = add x y)
    (x y : G),
    P41PartialCauchy.extend φ l r (add x y) = P41PartialCauchy.extend φ l r x + P41PartialCauchy.extend φ l r y)

theorem target : statement := sorry

end Statements.J4P41PartialCauchy
