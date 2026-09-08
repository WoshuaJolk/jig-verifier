import Init

namespace Statements.Erdos44MovingOffset

def rot (n c x : Int) : Int := (x - c) % n
def rotNat (n c x : Nat) : Nat := (x + n - c) % n

def base (i : Fin 5) : Nat :=
  match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 4
  | 3 => 14
  | _ => 16

def block (i : Fin 5) : Nat := rotNat 21 17 (base i)

def SidonIndexed (s : Fin 5 → Nat) : Prop :=
  ∀ i j k l, s i + s j = s k + s l →
    (i = k ∧ j = l) ∨ (i = l ∧ j = k)

def ZeroFixedFamily : Prop :=
  ∀ i j k : Fin 5, (base i + base j) % 21 = (9 + base k) % 21 →
    block i + block j ≠ rotNat 21 17 9 + block k

abbrev statement : Prop :=
    (∀ n c t a d x y z : Int,
      (x + y) % n = (d + z) % n →
      (t + rot n c x) + (t + rot n c y) = a + (t + rot n c z) →
      (d + t) % n = (a + c) % n) ∧
    (∀ n a t d c₁ c₂ : Int, 0 ≤ c₁ ∧ c₁ < n → 0 ≤ c₂ ∧ c₂ < n →
      (d + t) % n = (a + c₁) % n → (d + t) % n = (a + c₂) % n → c₁ = c₂) ∧
    (∀ n c x : Nat, c ≤ n → (rotNat n c x : Int) = rot (n : Int) c x) ∧
    (SidonIndexed block ∧ (∀ i : Fin 5, 2 ≤ block i ∧ block i ≤ 20) ∧
      ZeroFixedFamily ∧ rotNat 21 17 9 = 13 ∧
      1 + block 2 = block 0 + block 1 ∧ 1 ≠ block 0 ∧ 1 ≠ block 1)

theorem target : statement := by sorry

end Statements.Erdos44MovingOffset
