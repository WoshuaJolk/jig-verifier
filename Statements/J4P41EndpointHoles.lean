import Init

namespace Statements.J4P41EndpointHoles

namespace P41Endpoint

def PosDiff (A : Int → Prop) (h : Int) : Prop :=
  0 < h ∧ ∃ a b, A a ∧ A b ∧ b-a=h

def label (V d : Int) : Int := if 0 < d then d else V+d

def CyclicUnique (A : Int → Prop) (V : Int) : Prop :=
  ∀ a b c d, A a → A b → A c → A d → a ≠ b → c ≠ d →
    label V (b-a) = label V (d-c) → a=c ∧ b=d

def CyclicComplete (A : Int → Prop) (V : Int) : Prop :=
  ∀ h, 0 < h → h < V → ∃ a b, A a ∧ A b ∧ a ≠ b ∧ label V (b-a)=h

end P41Endpoint

abbrev statement : Prop :=
  (∀ (V d : Int) (hd : -V < d ∧ d < V) (hne : d ≠ 0),
    P41Endpoint.label V d = d % V) ∧
  (∀ (A : Int → Prop) (V h : Int)
    (hu : P41Endpoint.CyclicUnique A V) (hc : P41Endpoint.CyclicComplete A V)
    (hh : 0 < h) (hv : h < V),
    (¬ P41Endpoint.PosDiff A h) ↔ P41Endpoint.PosDiff A (V-h)) ∧
  (∀ (A : Int → Prop) (V L G h : Int)
    (hV : V=L+G) (hh : h < V),
    P41Endpoint.PosDiff A (V-h) ↔ ∃ a b, A a ∧ A b ∧ a+(L-b)=h-G) ∧
  (∀ (A : Int → Prop) (V L G : Int)
    (hu : P41Endpoint.CyclicUnique A V) (hc : P41Endpoint.CyclicComplete A V)
    (hV : V=L+G) (hL : 0 < L) (hG : 0 < G)
    (h0 : A 0) (hmax : A L) (hbound : ∀ a, A a → 0 ≤ a ∧ a ≤ L),
    (¬ P41Endpoint.PosDiff A G) ∧ (∀ h, 0 < h → h < G → P41Endpoint.PosDiff A h))

theorem target : statement := sorry

end Statements.J4P41EndpointHoles
