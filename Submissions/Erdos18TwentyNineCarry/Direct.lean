import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic

namespace Submissions.Erdos18TwentyNineCarry.Direct

def carryB : ℕ → ℕ
  | 0 => 918
  | 5 => 667
  | 8 => 3230
  | 9 => 2639
  | 12 => 2210
  | 15 => 845
  | 19 => 1029
  | 20 => 850
  | 23 => 1183
  | 27 => 945
  | r => 74 + r

def carryC : ℕ → ℕ
  | 0 => 526592
  | 5 => 526848
  | 8 => 524288
  | 9 => 524880
  | 12 => 525312
  | 15 => 526680
  | 19 => 526500
  | 20 => 526680
  | 23 => 526350
  | 27 => 526592
  | _ => 527436

theorem proof :
    ∀ r : ℕ, r < 29 →
      let D : Finset ℕ := {29, carryB r, carryC r}
      D ⊆ (Nat.factorial 29).divisors ∧
        D.card = 3 ∧
        18191 * 29 + r = D.sum id := by
  intro r hr
  interval_cases r <;>
    norm_num [carryB, carryC, Finset.subset_iff, Nat.mem_divisors]

end Submissions.Erdos18TwentyNineCarry.Direct
