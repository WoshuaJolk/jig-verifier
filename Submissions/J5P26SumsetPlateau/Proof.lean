import Init

namespace Submissions.J5P26SumsetPlateau.Proof

def good7 (x : Nat) : Prop := x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 4

instance (x : Nat) : Decidable (good7 x) := inferInstanceAs (Decidable (x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 4))

def digit7 (x : Nat) : Prop := good7 (x % 7)

def digits7 : Nat → Nat → Prop :=
  Nat.rec (motive := fun _ => Nat → Prop)
    (fun _ => True)
    (fun _ ih a => digit7 a ∧ ih (a / 7))

theorem base_four_free : ∀ (a d : Fin 7),
    good7 a.val → good7 ((a.val+d.val)%7) →
    good7 ((a.val+2*d.val)%7) → good7 ((a.val+3*d.val)%7) → d.val = 0 := by
  decide

theorem base_sum_covers : ∀ t : Fin 7, ∃ a b : Fin 7,
    good7 a.val ∧ good7 b.val ∧ (a.val+b.val)%7 = t.val := by
  decide

theorem first_digit_step (a d : Nat) (h0 : digit7 a)
    (h1 : digit7 (a+d)) (h2 : digit7 (a+2*d))
    (h3 : digit7 (a+3*d)) : 7 ∣ d := by
  have hm := base_four_free ⟨a%7, Nat.mod_lt a (by decide)⟩
    ⟨d%7, Nat.mod_lt d (by decide)⟩
  have he1 : (a+d)%7 = (a%7+d%7)%7 := by omega
  have he2 : (a+2*d)%7 = (a%7+2*(d%7))%7 := by omega
  have he3 : (a+3*d)%7 = (a%7+3*(d%7))%7 := by omega
  have hz : d%7 = 0 := hm h0
    (by simpa only [digit7, he1] using h1)
    (by simpa only [digit7, he2] using h2)
    (by simpa only [digit7, he3] using h3)
  exact Nat.dvd_of_mod_eq_zero hz

theorem digits_step_divisible (n a d : Nat) (h0 : digits7 n a)
    (h1 : digits7 n (a+d)) (h2 : digits7 n (a+2*d))
    (h3 : digits7 n (a+3*d)) : 7^n ∣ d := by
  induction n generalizing a d with
  | zero => simp
  | succ n ih =>
    change digit7 a ∧ digits7 n (a/7) at h0
    change digit7 (a+d) ∧ digits7 n ((a+d)/7) at h1
    change digit7 (a+2*d) ∧ digits7 n ((a+2*d)/7) at h2
    change digit7 (a+3*d) ∧ digits7 n ((a+3*d)/7) at h3
    obtain ⟨e, he⟩ := first_digit_step a d h0.1 h1.1 h2.1 h3.1
    subst d
    have hd (i : Nat) : (a+i*(7*e))/7 = a/7+i*e := by
      rw [show i*(7*e) = 7*(i*e) by simp only [Nat.mul_left_comm]]
      exact Nat.add_mul_div_left a (i*e) (by decide)
    have ht1 : digits7 n (a/7+e) := by
      simpa only [Nat.add_mul_div_left a e (by decide : 0 < 7)] using h1.2
    have ht2 : digits7 n (a/7+2*e) := by
      simpa only [hd] using h2.2
    have ht3 : digits7 n (a/7+3*e) := by
      simpa only [hd] using h3.2
    obtain ⟨u, hu⟩ := ih (a/7) e h0.2 ht1 ht2 ht3
    refine ⟨u, ?_⟩
    rw [hu, Nat.pow_succ]
    simp only [Nat.mul_comm, Nat.mul_left_comm]

def digitList : List Nat := [0,1,2,4]

def sumList : List Nat := digitList.flatMap fun a => digitList.map fun b => (a+b)%7

def convolution7 (t : Nat) : Nat :=
  ((digitList.flatMap fun a => digitList.map fun b => (a+b+7-t)%7).filter
    fun z => sumList.contains z).length

theorem base_flat_convolution : ∀ t : Fin 7, convolution7 t.val = 16 := by
  decide

theorem solves :
  (∀ (a d : Fin 7),
    good7 a.val → good7 ((a.val+d.val)%7) →
    good7 ((a.val+2*d.val)%7) → good7 ((a.val+3*d.val)%7) → d.val = 0) ∧
  (∀ t : Fin 7, ∃ a b : Fin 7,
    good7 a.val ∧ good7 b.val ∧ (a.val+b.val)%7 = t.val) ∧
  (∀ (n a d : Nat), digits7 n a → digits7 n (a+d) → digits7 n (a+2*d) → digits7 n (a+3*d) → 7^n ∣ d) ∧
  (∀ t : Fin 7, convolution7 t.val = 16) := by
  exact ⟨@base_four_free, @base_sum_covers, @digits_step_divisible, @base_flat_convolution⟩

end Submissions.J5P26SumsetPlateau.Proof
