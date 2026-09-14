import Init

namespace Statements.J4P26StateObstruction

def Ramsey (Q : Type) (B k : Nat) : Prop :=
  ∀ c : Fin B → Q, ∃ a d : Nat, ∃ q : Q, 0 < d ∧
    ∀ j : Fin k, ∃ t : Fin B, t.val = a+j.val*d ∧ c t = q

def APFree (A : Nat → Prop) (k : Nat) : Prop :=
  ∀ a d : Nat, 0 < d → ¬ (∀ j : Fin k, A (a+j.val*d))


def statement : Prop :=
(∀ {Q : Type} {B k C M : Nat}
    (hk : 0 < k) (hM : 0 < M) (ramsey : Ramsey Q B k)
    (A : Nat → Prop) (free : APFree A k)
    (reach : Fin B → Q → Prop) (suffix : Q → Nat → Prop)
    (join : ∀ t q s, reach t q → suffix q s → A (C+M*t.val+s)),
¬ (∀ t : Fin B, ∃ q : Q, reach t q ∧ ∃ s : Nat, suffix q s))

end Statements.J4P26StateObstruction
