import Mathlib.Tactic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.ModEq

set_option autoImplicit false
set_option maxHeartbeats 0

namespace SidonFiberAudit

def IsSidon (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

theorem difference_unique {A : Finset ℕ} (hA : IsSidon A)
    {a b c d : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A)
    (hba : b < a) (hdc : d < c) (heq : a - b = c - d) :
    a = c ∧ b = d := by
  have hs : a + d = c + b := by omega
  rcases hA a ha d hd c hc b hb hs with h | h
  · exact ⟨h.1, h.2.symm⟩
  · omega

/-- Each reuse of a label consumes a different positive difference.
The label function is arbitrary; no modular Sidon assumption is present. -/
theorem card_le_image_add_difference_budget {β : Type*} [DecidableEq β]
    (A : Finset ℕ) (f : ℕ → β) (T : Finset ℕ) (hA : IsSidon A)
    (hT : ∀ x ∈ A, ∀ y ∈ A, x < y → f x = f y → y - x ∈ T) :
    A.card ≤ (A.image f).card + T.card := by
  induction A using Finset.induction_on_max generalizing T with
  | empty => simp
  | @insert a A hmax ih =>
    have hnot : a ∉ A := by
      intro h
      exact (Nat.lt_irrefl a) (hmax a h)
    have hsub : IsSidon A := by
      intro x hx y hy z hz w hw hs
      exact hA x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy)
        z (Finset.mem_insert_of_mem hz) w (Finset.mem_insert_of_mem hw) hs
    by_cases hf : f a ∈ A.image f
    · obtain ⟨b, hb, hab⟩ := Finset.mem_image.mp hf
      have hba : b < a := hmax b hb
      have ht : a - b ∈ T := hT b (Finset.mem_insert_of_mem hb)
        a (Finset.mem_insert_self a A) hba hab
      have hbudget : ∀ x ∈ A, ∀ y ∈ A, x < y → f x = f y →
          y - x ∈ T.erase (a - b) := by
        intro x hx y hy hxy hfxy
        refine Finset.mem_erase.mpr ⟨?_, ?_⟩
        · intro heq
          have hc := difference_unique hA
            (Finset.mem_insert_of_mem hy) (Finset.mem_insert_of_mem hx)
            (Finset.mem_insert_self a A) (Finset.mem_insert_of_mem hb)
            hxy hba heq
          exact hnot (hc.1 ▸ hy)
        · exact hT x (Finset.mem_insert_of_mem hx) y
            (Finset.mem_insert_of_mem hy) hxy hfxy
      have hind := ih (T.erase (a - b)) hsub hbudget
      rw [Finset.card_insert_of_notMem hnot, Finset.image_insert,
        Finset.insert_eq_of_mem hf]
      have hcard := Finset.card_erase_add_one ht
      omega
    · have hbudget : ∀ x ∈ A, ∀ y ∈ A, x < y → f x = f y → y - x ∈ T := by
        intro x hx y hy hxy hfxy
        exact hT x (Finset.mem_insert_of_mem hx) y
          (Finset.mem_insert_of_mem hy) hxy hfxy
      have hind := ih T hsub hbudget
      rw [Finset.card_insert_of_notMem hnot, Finset.image_insert,
        Finset.card_insert_of_notMem hf]
      omega

/-- The general fiber bound for every interval Sidon set. -/
theorem card_le_residue_card_add_blocks (A : Finset ℕ) (M L : ℕ)
    (hM : 0 < M) (hA : IsSidon A) (hbox : ∀ a ∈ A, a < L * M) :
    A.card ≤ (A.image (fun a => a % M)).card + (L - 1) := by
  let T : Finset ℕ := (Finset.Ico 1 L).image (fun i => i * M)
  have hT : ∀ x ∈ A, ∀ y ∈ A, x < y → x % M = y % M → y - x ∈ T := by
    intro x hx y hy hxy hf
    have hz := (show Nat.ModEq M x y from hf).dvd
    rw [← Int.ofNat_sub hxy.le] at hz
    have hdvd : M ∣ y - x := by exact_mod_cast hz
    have hmul := Nat.mul_div_cancel' hdvd
    have htpos : 1 ≤ (y - x) / M := by
      by_contra hn
      have ht0 : (y - x) / M = 0 := Nat.eq_zero_of_not_pos (fun hh => hn hh)
      rw [ht0, mul_zero] at hmul
      omega
    have hdiff : y - x < L * M := by have := hbox y hy; omega
    have htlt : (y - x) / M < L := (Nat.div_lt_iff_lt_mul hM).mpr hdiff
    apply Finset.mem_image.mpr
    refine ⟨(y - x) / M, ?_, ?_⟩
    · exact Finset.mem_Ico.mpr ⟨htpos, htlt⟩
    · simpa only [Nat.mul_comm] using hmul
  have hb := card_le_image_add_difference_budget A (fun a => a % M) T hA hT
  have hc : T.card ≤ L - 1 := by
    calc
      T.card ≤ (Finset.Ico 1 L).card := Finset.card_image_le
      _ = L - 1 := by simp
  omega

/-- A fixed residue set permits only one additional point in two blocks. -/
theorem two_block_one_extra (A D : Finset ℕ) (M : ℕ)
    (hM : 0 < M) (hA : IsSidon A) (hbox : ∀ a ∈ A, a < 2 * M)
    (hres : ∀ a ∈ A, a % M ∈ D) : A.card ≤ D.card + 1 := by
  have hb := card_le_residue_card_add_blocks A M 2 hM hA hbox
  have hc : (A.image (fun a => a % M)).card ≤ D.card := by
    apply Finset.card_le_card
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    exact hres a ha
  omega

theorem digit_rectangle_not_sidon (M : ℕ) (hM : 2 ≤ M) :
    ¬ IsSidon ({0, 1, M, M + 1} : Finset ℕ) := by
  intro h
  have hs := h 0 (by simp) (M+1) (by simp) 1 (by simp) M (by simp) (by omega)
  rcases hs with hs | hs <;> omega

#print axioms card_le_image_add_difference_budget
#print axioms card_le_residue_card_add_blocks
#print axioms two_block_one_extra
#print axioms digit_rectangle_not_sidon

end SidonFiberAudit

namespace Submissions.Erdos30SidonFiberBudget.Declan
def IsSidon (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

theorem proof : ∀ (A : Finset ℕ) (M L : ℕ), 0 < M → IsSidon A →
  (∀ a ∈ A, a < L * M) →
  A.card ≤ (A.image (fun a => a % M)).card + (L - 1) := by
  intro A M L hM hA hbox
  exact SidonFiberAudit.card_le_residue_card_add_blocks A M L hM hA hbox
end Submissions.Erdos30SidonFiberBudget.Declan
