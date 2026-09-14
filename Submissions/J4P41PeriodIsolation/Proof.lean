import Init


namespace Submissions.J4P41PeriodIsolation.Proof.P41PeriodIsolation

def ModularSidon (A : Int → Prop) (m : Int) : Prop :=
  ∀ a b c d, A a → A b → A c → A d →
    (a + b) % m = (c + d) % m →
    (a = c ∧ b = d) ∨ (a = d ∧ b = c)

theorem no_copy_triple {A : Int → Prop} {m a b c d : Int}
    (hm : 0 < m) (hs : ModularSidon A m)
    (ha : A a) (hb : A b) (hc : A c) (hd : A d)
    (heq : a + b = (m + d) + c) : False := by
  have hmod : (a + b) % m = (d + c) % m := by
    rw [heq]
    simp [Int.add_assoc, Int.add_emod]
  rcases hs a b d c ha hb hd hc hmod with h | h
  · omega
  · omega

theorem two_shift_hits {D : Int → Prop} {v w d₀ d₁ : Int}
    (_hv : 0 < v) (hw : 0 < w) (hw2 : w < 2 * v) (hwv : w ≠ v)
    (h₀ : 0 ≤ d₀) (h₁ : d₀ < d₁) (h₂ : d₁ < v)
    (hs : ModularSidon D v) (hd₀ : D d₀) (hd₁ : D d₁) :
    ¬ (D ((w + d₀) % v) ∧ D ((w + d₁) % v)) := by
  intro h
  have hm : (((w + d₁) % v) + d₀) % v =
      (d₁ + ((w + d₀) % v)) % v := by
    simp only [Int.emod_add_emod, Int.add_emod_emod]
    congr 1
    omega
  rcases hs ((w + d₁) % v) d₀ d₁ ((w + d₀) % v)
      h.2 hd₀ hd₁ h.1 hm with he | he
  · have hemod : (w + d₀) % v = d₀ := he.2.symm
    have hc : (w + d₀) % v = (0 + d₀) % v := by
      simpa [Int.emod_eq_of_lt h₀ (by omega : d₀ < v)] using hemod
    have hwmod : w % v = 0 := by
      simpa using (Int.emod_add_cancel_right d₀).mp hc
    by_cases hsmall : w < v
    · rw [Int.emod_eq_of_lt (by omega) hsmall] at hwmod
      omega
    · have hz : (w - v) % v = 0 := by simp [hwmod]
      rw [Int.emod_eq_of_lt (by omega) (by omega)] at hz
      omega
  · omega

theorem shifted_survival_excludes_period {D A : Int → Prop} {v w d₀ d₁ : Int}
    (hv : 0 < v) (hw : 0 < w) (hw2 : w < 2 * v) (hwv : w ≠ v)
    (h₀ : 0 ≤ d₀) (h₁ : d₀ < d₁) (h₂ : d₁ < v)
    (hsD : ModularSidon D v) (hsub : ∀ x, A x → D x)
    (hd₀ : A d₀) (hd₁ : A d₁)
    (survive : ∀ d, (d = d₀ ∨ d = d₁) → ¬ D ((w + d) % v) →
      ∃ a b c, A a ∧ A b ∧ A c ∧ a + b = (w + d) + c) :
    ¬ ModularSidon A w := by
  intro hsA
  have escape := two_shift_hits hv hw hw2 hwv h₀ h₁ h₂ hsD
    (hsub d₀ hd₀) (hsub d₁ hd₁)
  by_cases hhit : D ((w + d₀) % v)
  · have hmiss : ¬ D ((w + d₁) % v) := by
      intro h; exact escape ⟨hhit, h⟩
    obtain ⟨a,b,c,ha,hb,hc,heq⟩ := survive d₁ (Or.inr rfl) hmiss
    exact no_copy_triple hw hsA ha hb hc hd₁ heq
  · obtain ⟨a,b,c,ha,hb,hc,heq⟩ := survive d₀ (Or.inl rfl) hhit
    exact no_copy_triple hw hsA ha hb hc hd₀ heq


end Submissions.J4P41PeriodIsolation.Proof.P41PeriodIsolation

namespace Submissions.J4P41PeriodIsolation.Proof

theorem proof :
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
    ¬ P41PeriodIsolation.ModularSidon A w) :=
  ⟨@P41PeriodIsolation.two_shift_hits, @P41PeriodIsolation.shifted_survival_excludes_period⟩

end Submissions.J4P41PeriodIsolation.Proof
