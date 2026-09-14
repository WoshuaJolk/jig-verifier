import Init

namespace Submissions.J4P41WeightedExtraction.Proof.P41WeightedSource

theorem collision_above_cap (D a b c d : Int) (hD : 0 < D)
    (ha : 3*D ≤ 4*a) (hb : 3*D ≤ 4*b)
    (hc : 3*D ≤ 4*c) (hd : 3*D ≤ 4*d) :
    D*D < a*b+c*d := by
  have hab := Int.mul_le_mul ha hb (show 0 ≤ 3*D by omega)
    (show 0 ≤ 4*a by omega)
  have hcd := Int.mul_le_mul hc hd (show 0 ≤ 3*D by omega)
    (show 0 ≤ 4*c by omega)
  have hDD := Int.mul_pos hD hD
  grind

def UniquePosDiff (A : Int → Prop) : Prop :=
  ∀ a b c d, A a → A b → A c → A d → b < a → d < c →
    a-b = c-d → a=c ∧ b=d

theorem threshold_unique_differences (A : Int → Prop) (w : Int → Int)
    (D : Int) (hD : 0 < D)
    (hcap : ∀ a b c d, A a → A b → A c → A d → b<a → d<c →
      a-b=c-d → ¬ (a=c ∧ b=d) → w a*w b+w c*w d ≤ D*D) :
    UniquePosDiff (fun x => A x ∧ 3*D ≤ 4*w x) := by
  intro a b c d ha hb hc hd hab hcd heq
  by_cases same : a=c ∧ b=d
  · exact same
  · have hlo := collision_above_cap D (w a) (w b) (w c) (w d)
      hD ha.2 hb.2 hc.2 hd.2
    have hhi := hcap a b c d ha.1 hb.1 hc.1 hd.1 hab hcd heq same
    omega

def OrdinarySidon (A : Int → Prop) : Prop :=
  ∀ a b c d, A a → A b → A c → A d → a+b=c+d →
    (a=c ∧ b=d) ∨ (a=d ∧ b=c)

theorem unique_differences_ordinary_sidon (A : Int → Prop)
    (h : UniquePosDiff A) : OrdinarySidon A := by
  intro a b c d ha hb hc hd heq
  by_cases hac : a=c
  · exact Or.inl ⟨hac, by omega⟩
  · by_cases hca : c<a
    · have hh := h a c d b ha hc hd hb hca (by omega) (by omega)
      exact Or.inr ⟨hh.1, by omega⟩
    · have hh := h c a b d hc ha hb hd (by omega) (by omega) (by omega)
      exact Or.inr ⟨hh.2, by omega⟩

end Submissions.J4P41WeightedExtraction.Proof.P41WeightedSource

namespace Submissions.J4P41WeightedExtraction.Proof

theorem proof :
  (∀ (A : Int → Prop) (w : Int → Int)
    (D : Int) (hD : 0 < D)
    (hcap : ∀ a b c d, A a → A b → A c → A d → b<a → d<c →
      a-b=c-d → ¬ (a=c ∧ b=d) → w a*w b+w c*w d ≤ D*D),
    P41WeightedSource.OrdinarySidon (fun x => A x ∧ 3*D ≤ 4*w x)) :=
  by
  intro A w D hD hcap
  exact P41WeightedSource.unique_differences_ordinary_sidon _ (P41WeightedSource.threshold_unique_differences A w D hD hcap)

end Submissions.J4P41WeightedExtraction.Proof
