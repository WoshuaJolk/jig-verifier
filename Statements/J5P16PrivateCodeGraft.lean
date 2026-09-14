import Init

namespace Statements.J5P16PrivateCodeGraft

def Two (p q r : Prop) : Prop :=
  (p ∧ q ∧ ¬r) ∨ (p ∧ ¬q ∧ r) ∨ (¬p ∧ q ∧ r)

def ThreeFree {W P : Type} (privateSet : W → P → Prop) : Prop :=
  ∀ u v w, u ≠ v → u ≠ w → v ≠ w →
    ∃ x, Two (privateSet u x) (privateSet v x) (privateSet w x)

def OuterSeparates {I O : Type} (outer : I → O → Prop) : Prop :=
  ∀ i j k, ¬(i = j ∧ j = k) →
    ∃ x, Two (outer i x) (outer j x) (outer k x)

def Graft {I W O P E : Type}
    (outer : I → O → Prop) (privateSet : W → P → Prop)
    (shared : W → E → Prop) (i : I) (w : W) :
    Sum O (Sum (I × P) E) → Prop
  | Sum.inl x => outer i x
  | Sum.inr (Sum.inl x) => i = x.1 ∧ privateSet w x.2
  | Sum.inr (Sum.inr x) => shared w x

-- The shared code has NO hypotheses: existing multiplicity-two witnesses survive.

abbrev statement : Prop :=
  ∀ {I W O P E : Type} [DecidableEq I]
    (outer : I → O → Prop) (privateSet : W → P → Prop)
    (shared : W → E → Prop)
    (ho : OuterSeparates outer) (hp : ThreeFree privateSet)
    (i j k : I) (u v w : W)
    (huv : i = j → u ≠ v) (huw : i = k → u ≠ w)
    (hvw : j = k → v ≠ w), ∃ x, Two (Graft outer privateSet shared i u x)
      (Graft outer privateSet shared j v x)
      (Graft outer privateSet shared k w x)

end Statements.J5P16PrivateCodeGraft
