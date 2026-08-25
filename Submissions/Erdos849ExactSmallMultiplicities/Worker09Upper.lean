import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Set.Card
import Mathlib.Tactic

namespace Submissions.Erdos849ExactSmallMultiplicities.Worker09Upper

def occurrences (a : ℕ) : Set (ℕ × ℕ) :=
  {(n, k) | 1 ≤ k ∧ 2 * k ≤ n ∧ Nat.choose n k = a}

theorem row_le_choose {n k : ℕ} (hk : 1 ≤ k) (hhalf : 2 * k ≤ n) :
    n ≤ Nat.choose n k := by
  have hkhalf : k ≤ n / 2 := by omega
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hmonoAux : ∀ j : ℕ, 1 + j ≤ n / 2 →
      Nat.choose n 1 ≤ Nat.choose n (1 + j) := by
    intro j hj
    induction j with
    | zero => rfl
    | succ j ih =>
        exact (ih (by omega)).trans
          (Nat.choose_le_succ_of_lt_half_left (by omega))
  simpa using hmonoAux j hkhalf

theorem occurrences_two : occurrences 2 = {(2, 1)} := by
  ext x
  rcases x with ⟨n, k⟩
  simp only [occurrences, Set.mem_setOf_eq, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨hk, hhalf, hchoose⟩
    have hn : n ≤ 2 := (row_le_choose hk hhalf).trans_eq hchoose
    constructor <;> omega
  · rintro ⟨rfl, rfl⟩
    norm_num [Nat.choose]

theorem occurrences_six : occurrences 6 = {(4, 2), (6, 1)} := by
  ext x
  rcases x with ⟨n, k⟩
  simp only [occurrences, Set.mem_setOf_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · intro h
    obtain ⟨hk, hhalf, hchoose⟩ := h
    have hn : n ≤ 6 := (row_le_choose hk hhalf).trans_eq hchoose
    have hk3 : k ≤ 3 := by omega
    interval_cases n <;> interval_cases k <;> norm_num [Nat.choose] at hchoose
    all_goals simp
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num [Nat.choose]

theorem proof : (occurrences 2).ncard = 1 ∧ (occurrences 6).ncard = 2 := by
  rw [occurrences_two, occurrences_six]
  norm_num

end Submissions.Erdos849ExactSmallMultiplicities.Worker09Upper
