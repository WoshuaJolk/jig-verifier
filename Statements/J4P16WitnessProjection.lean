import Init

namespace Statements.J4P16WitnessProjection

def Two (p q r : Prop) : Prop :=
  (p ∧ q ∧ ¬r) ∨ (p ∧ ¬q ∧ r) ∨ (¬p ∧ q ∧ r)

def Project {I X : Type} (family : I → X → Prop) (keep : X → Prop)
    (i : I) (x : X) : Prop := keep x ∧ family i x

def RetainsWitnesses {I X : Type} (family : I → X → Prop) (keep : X → Prop) : Prop :=
  ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    ∃ x, keep x ∧ Two (family i x) (family j x) (family k x)

def StrongThreeFree {I X : Type} (family : I → X → Prop) : Prop :=
  ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    ∃ x, Two (family i x) (family j x) (family k x)


def statement : Prop :=
(∀ {I X : Type}
    (family : I → X → Prop) (keep : X → Prop)
    (h : RetainsWitnesses family keep),
StrongThreeFree (Project family keep)) ∧
(∀ {I X : Type}
    (family : I → X → Prop) (keep : X → Prop)
    (h : RetainsWitnesses family keep)
    (i j k : I) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (eqij : ∀ x, Project family keep i x ↔ Project family keep j x)
    (eqik : ∀ x, Project family keep i x ↔ Project family keep k x),
False)

end Statements.J4P16WitnessProjection
