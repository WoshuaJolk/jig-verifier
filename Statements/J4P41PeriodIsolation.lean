import Init

namespace Statements.J4P41PeriodIsolation


namespace P41PeriodIsolation

def ModularSidon (A : Int → Prop) (m : Int) : Prop :=
  ∀ a b c d, A a → A b → A c → A d →
    (a + b) % m = (c + d) % m →
    (a = c ∧ b = d) ∨ (a = d ∧ b = c)

end P41PeriodIsolation

abbrev statement : Prop :=
  (∀ {D : Int → Prop} {v w d₀ d₁ : Int}
    (_hv : 0 < v) (hw : 0 < w) (hw2 : w < 2 * v) (hwv : w ≠ v)
    (h₀ : 0 ≤ d₀) (h₁ : d₀ < d₁) (h₂ : d₁ < v)
    (hs : P41PeriodIsolation.ModularSidon D v) (hd₀ : D d₀) (hd₁ : D d₁),
    ¬ (D ((w + d₀) % v) ∧ D ((w + d₁) % v))) ∧
  (∀ {D A : Int → Prop} {v w d₀ d₁ : Int}
    (hv : 0 < v) (hw : 0 < w) (hw2 : w < 2 * v) (hwv : w ≠ v)
    (h₀ : 0 ≤ d₀) (h₁ : d₀ < d₁) (h₂ : d₁ < v)
    (hsD : P41PeriodIsolation.ModularSidon D v) (hsub : ∀ x, A x → D x)
    (hd₀ : A d₀) (hd₁ : A d₁)
    (survive : ∀ d, (d = d₀ ∨ d = d₁) → ¬ D ((w + d) % v) →
      ∃ a b c, A a ∧ A b ∧ A c ∧ a + b = (w + d) + c),
    ¬ P41PeriodIsolation.ModularSidon A w)

theorem target : statement := sorry

end Statements.J4P41PeriodIsolation
