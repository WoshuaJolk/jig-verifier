import Init

namespace Submissions.J4P26StateObstruction.Proof

def Ramsey (Q : Type) (B k : Nat) : Prop :=
  ∀ c : Fin B → Q, ∃ a d : Nat, ∃ q : Q, 0 < d ∧
    ∀ j : Fin k, ∃ t : Fin B, t.val = a+j.val*d ∧ c t = q

def APFree (A : Nat → Prop) (k : Nat) : Prop :=
  ∀ a d : Nat, 0 < d → ¬ (∀ j : Fin k, A (a+j.val*d))

theorem affine_identity (C M a d s j : Nat) :
    C+M*(a+j*d)+s = (C+M*a+s)+j*(M*d) := by
  have hmul : M*(j*d) = j*(M*d) := by
    rw [← Nat.mul_assoc, Nat.mul_comm M j, Nat.mul_assoc]
  simp only [Nat.mul_add]
  rw [hmul]
  omega

theorem common_state_obstruction {Q : Type} {B k C M : Nat}
    (hk : 0 < k) (hM : 0 < M) (ramsey : Ramsey Q B k)
    (A : Nat → Prop) (free : APFree A k)
    (reach : Fin B → Q → Prop) (suffix : Q → Nat → Prop)
    (join : ∀ t q s, reach t q → suffix q s → A (C+M*t.val+s)) :
    ¬ (∀ t : Fin B, ∃ q : Q, reach t q ∧ ∃ s : Nat, suffix q s) := by
  intro cover
  let c : Fin B → Q := fun t => Classical.choose (cover t)
  have hc (t : Fin B) : reach t (c t) ∧ ∃ s, suffix (c t) s :=
    Classical.choose_spec (cover t)
  obtain ⟨a,d,q,hd,hmono⟩ := ramsey c
  obtain ⟨t0,_,ht0⟩ := hmono ⟨0,hk⟩
  obtain ⟨s,hs⟩ := (hc t0).2
  have hqs : suffix q s := ht0 ▸ hs
  apply free (C+M*a+s) (M*d) (Nat.mul_pos hM hd)
  intro j
  obtain ⟨t,ht,hcolor⟩ := hmono j
  have hreach : reach t q := hcolor ▸ (hc t).1
  have hA := join t q s hreach hqs
  rw [ht, affine_identity] at hA
  exact hA

def levels (children : Nat → Nat → List Nat) : Nat → List Nat
  | 0 => [0]
  | n+1 => (levels children n).flatMap (children n)

theorem flatMap_bound (xs : List Nat) (f : Nat → List Nat) (C : Nat)
    (h : ∀ x ∈ xs, (f x).length ≤ C) :
    (xs.flatMap f).length ≤ xs.length*C := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have hr : ∀ y ∈ xs, (f y).length ≤ C := by
      intro y hy
      exact h y (by simp [hy])
    have hi := ih hr
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    rw [Nat.add_mul]
    simp only [Nat.one_mul]
    omega

theorem prefix_count_bound (children : Nat → Nat → List Nat) (C : Nat)
    (h : ∀ n x, x ∈ levels children n → (children n x).length ≤ C) :
    ∀ n, (levels children n).length ≤ C^n := by
  intro n
  induction n with
  | zero => simp [levels]
  | succ n ih =>
    have hb := flatMap_bound (levels children n) (children n) C (h n)
    exact Nat.le_trans hb (by simpa [Nat.pow_succ] using Nat.mul_le_mul_right C ih)

def colorMask (m i : Nat) : Bool := (m / 2^i) % 2 == 1

theorem binary_nine : ∀ u : Fin 16, ∀ v : Fin 32,
    ∃ a : Fin 9, ∃ d : Fin 5,
      0 < d.val ∧ a.val+2*d.val < 9 ∧
      colorMask (u.val+16*v.val) a.val = colorMask (u.val+16*v.val) (a.val+d.val) ∧
      colorMask (u.val+16*v.val) a.val = colorMask (u.val+16*v.val) (a.val+2*d.val) := by
  decide

theorem solves :
(∀ {Q : Type} {B k C M : Nat}
    (hk : 0 < k) (hM : 0 < M) (ramsey : Ramsey Q B k)
    (A : Nat → Prop) (free : APFree A k)
    (reach : Fin B → Q → Prop) (suffix : Q → Nat → Prop)
    (join : ∀ t q s, reach t q → suffix q s → A (C+M*t.val+s)),
¬ (∀ t : Fin B, ∃ q : Q, reach t q ∧ ∃ s : Nat, suffix q s)) := by
  exact @common_state_obstruction

end Submissions.J4P26StateObstruction.Proof

