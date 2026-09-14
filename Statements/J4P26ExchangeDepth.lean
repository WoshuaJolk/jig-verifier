import Init

namespace Statements.J4P26ExchangeDepth

def card (m : Nat) : Nat :=
  ((List.range 15).filter (fun x => m.testBit x)).length

def removed (m : Nat) : Nat :=
  ([0, 1, 2, 4, 5, 9, 10, 12, 14].filter (fun x => !(m.testBit x))).length

abbrev APFree (m : Nat) : Prop :=
  ∀ a : Fin 15, ∀ d : Fin 5, 0 < d.val → a.val + 3*d.val < 15 →
    (m.testBit a.val && m.testBit (a.val+d.val) &&
      m.testBit (a.val+2*d.val) && m.testBit (a.val+3*d.val)) = false


def statement : Prop :=
(∀ (m : Fin 32768),
10 ≤ card m.val → APFree m.val → m.val = 27099 ∨ m.val = 28107) ∧
(∀ (m : Fin 32768) (hf : APFree m.val),
card m.val ≤ 10) ∧
(∀ (m : Fin 32768) (hf : APFree m.val)
    (hc : 9 < card m.val),
removed m.val = 5) ∧
(APFree 22071 ∧ card 22071 = 9 ∧
    APFree 28107 ∧ card 28107 = 10 ∧ removed 28107 = 5 ∧
    (∀ x : Fin 15, (22071).testBit x.val = [0, 1, 2, 4, 5, 9, 10, 12, 14].contains x.val))

end Statements.J4P26ExchangeDepth
