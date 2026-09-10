import Init

namespace Submissions.Erdos44MovingOffset.Main

def rot (n c x : Int) : Int := (x - c) % n

theorem rotation_pair (n c t x y : Int) :
    ((t + rot n c x) + (t + rot n c y)) % n =
      (t + x + t + y - 2 * c) % n := by
  unfold rot
  have rearrange : t + (x - c) % n + (t + (y - c) % n) =
      ((x - c) % n + (y - c) % n) + (t + t) := by omega
  rw [rearrange]
  have pair : ((x - c) % n + (y - c) % n) % n = ((x - c) + (y - c)) % n :=
    (Int.add_emod _ _ _).symm
  have hp := Int.add_emod_eq_add_emod_right (t + t) pair
  have arithmetic : (x - c) + (y - c) + (t + t) = t + x + t + y - 2 * c := by omega
  simpa only [Int.emod_add_emod, arithmetic] using hp

theorem rotation_mixed (n c t a z : Int) :
    (a + (t + rot n c z)) % n = (a + t + z - c) % n := by
  unfold rot
  rw [show a + (t + (z - c) % n) = a + t + (z - c) % n by omega,
    Int.add_emod_emod]
  congr 1
  omega

/-- A fixed old integer uses a cut-dependent modular offset. -/
theorem moving_offset (n c t a x y z : Int)
    (collision : (t + rot n c x) + (t + rot n c y) = a + (t + rot n c z)) :
    (x + y + t) % n = (a + c + z) % n := by
  have h := congrArg (fun q : Int => q % n) collision
  rw [rotation_pair, rotation_mixed] at h
  have shifted := Int.add_emod_eq_add_emod_right (2 * c - t) h
  have left : t + x + t + y - 2 * c + (2 * c - t) = x + y + t := by omega
  have right : a + t + z - c + (2 * c - t) = a + c + z := by omega
  rwa [left, right] at shifted

theorem fixed_family_offset (n c t a d x y z : Int)
    (family : (x + y) % n = (d + z) % n)
    (collision : (t + rot n c x) + (t + rot n c y) = a + (t + rot n c z)) :
    (d + t) % n = (a + c) % n := by
  have h := moving_offset n c t a x y z collision
  have hf := Int.add_emod_eq_add_emod_right t family
  have hz : ((d + t) + z) % n = ((a + c) + z) % n := by
    rw [show d + t + z = d + z + t by omega]
    exact hf.symm.trans h
  exact (Int.emod_add_cancel_right z).mp hz

/-- With the old point, translation and modular family fixed, at most one
canonical cut can be compatible. This is a restriction on that method only. -/
theorem unique_compatible_cut (n a t d c₁ c₂ : Int)
    (hc₁ : 0 ≤ c₁ ∧ c₁ < n) (hc₂ : 0 ≤ c₂ ∧ c₂ < n)
    (h₁ : (d + t) % n = (a + c₁) % n)
    (h₂ : (d + t) % n = (a + c₂) % n) : c₁ = c₂ := by
  have h : c₁ % n = c₂ % n := Int.emod_add_cancel_left.mp (h₁.symm.trans h₂)
  rwa [Int.emod_eq_of_lt hc₁.1 hc₁.2, Int.emod_eq_of_lt hc₂.1 hc₂.2] at h

def rotNat (n c x : Nat) : Nat := (x + n - c) % n

/-- Exact agreement with the board's natural-number rotation. -/
theorem natural_rotation (n c x : Nat) (hc : c ≤ n) :
    (rotNat n c x : Int) = rot (n : Int) c x := by
  unfold rotNat rot
  rw [Int.natCast_emod]
  have hcast : ((x + n - c : Nat) : Int) = (x : Int) - c + n := by omega
  rw [hcast, Int.add_emod_right]

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

/-- An admissible Sidon block has no survivors for offset 9, but it cannot
be adjoined to the fixed singleton {1}: 1+8=4+5. -/
theorem finite_control :
    SidonIndexed block ∧
    (∀ i : Fin 5, 2 ≤ block i ∧ block i ≤ 20) ∧
    ZeroFixedFamily ∧
    rotNat 21 17 9 = 13 ∧
      1 + block 2 = block 0 + block 1 ∧ 1 ≠ block 0 ∧ 1 ≠ block 1 := by
  unfold SidonIndexed ZeroFixedFamily
  decide

theorem proof :
    (∀ n c t a d x y z : Int,
      (x + y) % n = (d + z) % n →
      (t + rot n c x) + (t + rot n c y) = a + (t + rot n c z) →
      (d + t) % n = (a + c) % n) ∧
    (∀ n a t d c₁ c₂ : Int, 0 ≤ c₁ ∧ c₁ < n → 0 ≤ c₂ ∧ c₂ < n →
      (d + t) % n = (a + c₁) % n → (d + t) % n = (a + c₂) % n → c₁ = c₂) ∧
    (∀ n c x : Nat, c ≤ n → (rotNat n c x : Int) = rot (n : Int) c x) ∧
    (SidonIndexed block ∧ (∀ i : Fin 5, 2 ≤ block i ∧ block i ≤ 20) ∧
      ZeroFixedFamily ∧ rotNat 21 17 9 = 13 ∧
      1 + block 2 = block 0 + block 1 ∧ 1 ≠ block 0 ∧ 1 ≠ block 1) :=
  ⟨fixed_family_offset, unique_compatible_cut, natural_rotation, finite_control⟩

end Submissions.Erdos44MovingOffset.Main

#print axioms Submissions.Erdos44MovingOffset.Main.moving_offset
#print axioms Submissions.Erdos44MovingOffset.Main.fixed_family_offset
#print axioms Submissions.Erdos44MovingOffset.Main.unique_compatible_cut
#print axioms Submissions.Erdos44MovingOffset.Main.natural_rotation
#print axioms Submissions.Erdos44MovingOffset.Main.finite_control
#print axioms Submissions.Erdos44MovingOffset.Main.proof
