import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic

namespace Submissions.Erdos18SevenCarryBase.Direct

def exceptionalQuotients : Finset ℕ :=
  {67, 71, 79, 97, 101, 103, 107, 109, 111, 113, 115, 118, 119}

def carryA : ℕ → ℕ
  | 67 => 105
  | 71 => 315
  | 79 => 504
  | 97 => 315
  | 101 => 560
  | 103 => 630
  | 107 => 28
  | 109 => 42
  | 111 => 56
  | 113 => 70
  | 115 => 84
  | 118 => 105
  | 119 => 112
  | _ => 1

def carryB : ℕ → ℕ
  | 67 => 360
  | 71 => 180
  | 79 => 48
  | 97 => 360
  | 101 => 144
  | 103 => 90
  | 107 => 720
  | 109 => 720
  | 111 => 720
  | 113 => 720
  | 115 => 720
  | 118 => 720
  | 119 => 720
  | _ => 1

def carryC : ℕ → ℕ
  | 67 => 4
  | 71 => 2
  | 79 => 1
  | 97 => 4
  | 101 => 3
  | 103 => 1
  | 107 => 1
  | 109 => 1
  | 111 => 1
  | 113 => 1
  | 115 => 1
  | 118 => 1
  | 119 => 1
  | _ => 1

theorem proof :
    ∀ q ∈ exceptionalQuotients, ∀ r : ℕ, r < 7 →
      let D : Finset ℕ := {carryA q, carryB q, carryC q + r}
      D ⊆ (Nat.factorial 7).divisors ∧
        D.card = 3 ∧
        q * 7 + r = D.sum id := by
  intro q hq r hr
  simp only [exceptionalQuotients, Finset.mem_insert,
    Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    interval_cases r <;>
      norm_num [carryA, carryB, carryC, Finset.subset_iff, Nat.mem_divisors]

end Submissions.Erdos18SevenCarryBase.Direct
