import Init

namespace Statements.J4P41WeightedExtraction

namespace P41WeightedSource

def UniquePosDiff (A : Int → Prop) : Prop :=
  ∀ a b c d, A a → A b → A c → A d → b < a → d < c →
    a-b = c-d → a=c ∧ b=d

def OrdinarySidon (A : Int → Prop) : Prop :=
  ∀ a b c d, A a → A b → A c → A d → a+b=c+d →
    (a=c ∧ b=d) ∨ (a=d ∧ b=c)

end P41WeightedSource

abbrev statement : Prop :=
  (∀ (A : Int → Prop) (w : Int → Int)
    (D : Int) (hD : 0 < D)
    (hcap : ∀ a b c d, A a → A b → A c → A d → b<a → d<c →
      a-b=c-d → ¬ (a=c ∧ b=d) → w a*w b+w c*w d ≤ D*D),
    P41WeightedSource.OrdinarySidon (fun x => A x ∧ 3*D ≤ 4*w x))

theorem target : statement := sorry

end Statements.J4P41WeightedExtraction
