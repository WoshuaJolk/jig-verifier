import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-!
Formalization of woshuajolk's balanced-complementary-rectangle construction
in Jig problem 1, statement 8. The theorem establishes exact fractional
coverage and loads for every positive k. It does not claim the stronger
optimality assertions in the board prose or solve the parent problem.
-/

namespace Submissions.LPRelaxationBlind.BalancedWeights

open scoped BigOperators

def denominator (k : ℕ) : ℕ := Nat.choose (2 * k - 2) (k - 1)

def weight (k : ℕ) (S : Finset (Fin (2 * k))) : ℚ :=
  if S.card = k then 1 / (denominator k : ℚ) else 0

theorem sum_weight_eq_card {α : Type*} [Fintype α] [DecidableEq α]
    (k : ℕ) (p : Finset α → Prop) [DecidablePred p] (a : ℚ) :
    (∑ S ∈ Finset.univ.filter p, if S.card = k then a else 0) =
      ((Finset.univ.filter (fun S : Finset α => p S ∧ S.card = k)).card : ℚ) * a := by
  rw [← Finset.sum_filter]
  simp [Finset.filter_filter]

theorem denom_pos (k : ℕ) (hk : 0 < k) :
    0 < Nat.choose (2 * k - 2) (k - 1) := by
  apply Nat.choose_pos
  omega

theorem choose_middle (k : ℕ) (hk : 0 < k) :
    Nat.choose (2 * k - 1) k = Nat.choose (2 * k - 1) (k - 1) := by
  apply Nat.choose_symm_of_eq_add
  omega

theorem choose_ratio (k : ℕ) (hk : 0 < k) :
    (Nat.choose (2 * k - 1) (k - 1) : ℚ) /
        (Nat.choose (2 * k - 2) (k - 1) : ℚ) = 2 - 1 / (k : ℚ) := by
  have hD : (Nat.choose (2 * k - 2) (k - 1) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (denom_pos k hk))
  have hK : (k : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hnat := Nat.choose_mul_succ_eq (2 * k - 2) (k - 1)
  have heq : 2 * k - 2 + 1 = 2 * k - 1 := by omega
  rw [heq] at hnat
  have hsub : 2 * k - 1 - (k - 1) = k := by omega
  rw [hsub] at hnat
  have hcast : (Nat.choose (2 * k - 2) (k - 1) : ℚ) * (2 * (k : ℚ) - 1) =
      (Nat.choose (2 * k - 1) (k - 1) : ℚ) * (k : ℚ) := by
    have hcast' := congrArg (fun n : ℕ => (n : ℚ)) hnat
    push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * k)] at hcast'
    exact hcast'
  field_simp
  nlinarith [hcast]

theorem weight_nonneg (k : ℕ) (S : Finset (Fin (2 * k))) : 0 ≤ weight k S := by
  unfold weight
  split_ifs <;> positivity

theorem load_lt_two (k : ℕ) (hk : 0 < k) : (2 : ℚ) - 1 / (k : ℚ) < 2 := by
  have hkq : (0 : ℚ) < (k : ℚ) := by exact_mod_cast hk
  have hpos : (0 : ℚ) < 1 / (k : ℚ) := by positivity
  linarith

variable {α : Type*} [DecidableEq α]

theorem card_mem (t : Finset α) (i : α) (hi : i ∈ t) (k : ℕ) (hk : 0 < k) :
    ((t.powersetCard k).filter (fun S => i ∈ S)).card =
      Nat.choose (t.card - 1) (k - 1) := by
  simpa using Finset.card_filter_powersetCard_subset {i} t k
    (by simpa using hi) (by simpa using Nat.succ_le_iff.mpr hk)

theorem filter_not_mem (t : Finset α) (j : α) (k : ℕ) :
    (t.powersetCard k).filter (fun S => j ∉ S) = (t.erase j).powersetCard k := by
  ext S
  simp only [Finset.mem_filter, Finset.mem_powersetCard]
  constructor
  · rintro ⟨⟨hst, hcard⟩, hj⟩
    exact ⟨fun x hx => Finset.mem_erase.mpr ⟨fun h => hj (h ▸ hx), hst hx⟩, hcard⟩
  · rintro ⟨hst, hcard⟩
    exact ⟨⟨fun x hx => (Finset.mem_erase.mp (hst hx)).2, hcard⟩,
      fun hj => (Finset.mem_erase.mp (hst hj)).1 rfl⟩

theorem card_not_mem (t : Finset α) (j : α) (hj : j ∈ t) (k : ℕ) :
    ((t.powersetCard k).filter (fun S => j ∉ S)).card =
      Nat.choose (t.card - 1) k := by
  rw [filter_not_mem, Finset.card_powersetCard, Finset.card_erase_of_mem hj]

theorem card_mem_not_mem (t : Finset α) (i j : α)
    (hi : i ∈ t) (hj : j ∈ t) (hij : i ≠ j) (k : ℕ) (hk : 0 < k) :
    ((t.powersetCard k).filter (fun S => i ∈ S ∧ j ∉ S)).card =
      Nat.choose (t.card - 2) (k - 1) := by
  have eq : (t.powersetCard k).filter (fun S => i ∈ S ∧ j ∉ S) =
      ((t.erase j).powersetCard k).filter (fun S => i ∈ S) := by
    rw [← filter_not_mem]
    ext S
    simp only [Finset.mem_filter]
    tauto
  rw [eq, card_mem (t.erase j) i (Finset.mem_erase.mpr ⟨hij, hi⟩) k hk,
    Finset.card_erase_of_mem hj, Nat.sub_sub]

theorem card_row (n k : ℕ) (hk : 0 < k) (i : Fin n) :
    ((Finset.univ : Finset (Finset (Fin n))).filter
      (fun S => S.card = k ∧ i ∈ S)).card = Nat.choose (n - 1) (k - 1) := by
  have eq : ((Finset.univ : Finset (Finset (Fin n))).filter
      (fun S => S.card = k ∧ i ∈ S)) =
      ((Finset.univ : Finset (Fin n)).powersetCard k).filter (fun S => i ∈ S) := by
    ext S
    simp
  rw [eq, card_mem _ i (Finset.mem_univ _) k hk]
  simp

theorem card_column (n k : ℕ) (j : Fin n) :
    ((Finset.univ : Finset (Finset (Fin n))).filter
      (fun S => S.card = k ∧ j ∉ S)).card = Nat.choose (n - 1) k := by
  have eq : ((Finset.univ : Finset (Finset (Fin n))).filter
      (fun S => S.card = k ∧ j ∉ S)) =
      ((Finset.univ : Finset (Fin n)).powersetCard k).filter (fun S => j ∉ S) := by
    ext S
    simp
  rw [eq, card_not_mem _ j (Finset.mem_univ _) k]
  simp

theorem card_cell (n k : ℕ) (hk : 0 < k) (i j : Fin n) (hij : i ≠ j) :
    ((Finset.univ : Finset (Finset (Fin n))).filter
      (fun S => S.card = k ∧ i ∈ S ∧ j ∉ S)).card =
        Nat.choose (n - 2) (k - 1) := by
  have eq : ((Finset.univ : Finset (Finset (Fin n))).filter
      (fun S => S.card = k ∧ i ∈ S ∧ j ∉ S)) =
      ((Finset.univ : Finset (Fin n)).powersetCard k).filter (fun S => i ∈ S ∧ j ∉ S) := by
    ext S
    simp
  rw [eq, card_mem_not_mem _ i j (Finset.mem_univ _) (Finset.mem_univ _) hij k hk]
  simp

theorem card_row' (n k : ℕ) (hk : 0 < k) (i : Fin n) :
    ((Finset.univ : Finset (Finset (Fin n))).filter
      (fun S => i ∈ S ∧ S.card = k)).card = Nat.choose (n - 1) (k - 1) := by
  simpa only [and_comm] using card_row n k hk i

theorem card_column' (n k : ℕ) (j : Fin n) :
    ((Finset.univ : Finset (Finset (Fin n))).filter
      (fun S => j ∉ S ∧ S.card = k)).card = Nat.choose (n - 1) k := by
  simpa only [and_comm] using card_column n k j

theorem card_cell' (n k : ℕ) (hk : 0 < k) (i j : Fin n) (hij : i ≠ j) :
    ((Finset.univ : Finset (Finset (Fin n))).filter
      (fun S => (i ∈ S ∧ j ∉ S) ∧ S.card = k)).card =
        Nat.choose (n - 2) (k - 1) := by
  simpa only [and_comm] using card_cell n k hk i j hij

theorem proof :
  ∀ k : ℕ, 0 < k → ∃ w : Finset (Fin (2 * k)) → ℚ,
    (∀ S, 0 ≤ w S) ∧
    (∀ i j : Fin (2 * k), i ≠ j →
      (∑ S ∈ Finset.univ.filter (fun S : Finset (Fin (2 * k)) => i ∈ S ∧ j ∉ S), w S) = 1) ∧
    (∀ i : Fin (2 * k),
      (∑ S ∈ Finset.univ.filter (fun S : Finset (Fin (2 * k)) => i ∈ S), w S)
        = 2 - 1 / (k : ℚ)) ∧
    (∀ j : Fin (2 * k),
      (∑ S ∈ Finset.univ.filter (fun S : Finset (Fin (2 * k)) => j ∉ S), w S)
        = 2 - 1 / (k : ℚ)) ∧
    (2 : ℚ) - 1 / (k : ℚ) < 2 := by
  intro k hk
  refine ⟨weight k, weight_nonneg k, ?_, ?_, ?_, load_lt_two k hk⟩
  · intro i j hij
    unfold weight
    rw [sum_weight_eq_card, card_cell' (2 * k) k hk i j hij]
    have hD : (Nat.choose (2 * k - 2) (k - 1) : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (denom_pos k hk))
    simp [denominator, hD]
  · intro i
    unfold weight
    rw [sum_weight_eq_card, card_row' (2 * k) k hk i]
    simpa [denominator, div_eq_mul_inv] using choose_ratio k hk
  · intro j
    unfold weight
    rw [sum_weight_eq_card, card_column' (2 * k) k j, choose_middle k hk]
    simpa [denominator, div_eq_mul_inv] using choose_ratio k hk

end Submissions.LPRelaxationBlind.BalancedWeights
