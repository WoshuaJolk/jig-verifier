import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Tactic

open Filter

namespace Submissions.Erdos208ExponentOne.Worker04

noncomputable def squarefreeNumber (n : ℕ) : ℕ :=
  Nat.nth Squarefree n

theorem squarefree_infinite : Set.Infinite {n : ℕ | Squarefree n} :=
  Nat.infinite_setOfPred_prime.mono fun _ hn => hn.squarefree

theorem strictMono_squarefreeNumber : StrictMono squarefreeNumber :=
  Nat.nth_strictMono squarefree_infinite

theorem next_le_two_mul (n : ℕ) :
    squarefreeNumber (n + 1) ≤ 2 * squarefreeNumber n := by
  have hmem : Squarefree (squarefreeNumber n) :=
    Nat.nth_mem_of_infinite squarefree_infinite n
  obtain ⟨p, hp, hlt, hle⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (squarefreeNumber n) hmem.ne_zero
  have hguard : ∀ hf : Set.Finite {n : ℕ | Squarefree n}, n + 1 < hf.toFinset.card := by
    intro hf
    exact (squarefree_infinite hf).elim
  have hnext : squarefreeNumber (n + 1) ≤ p := by
    apply (Nat.isLeast_nth (p := Squarefree) hguard).2
    refine ⟨hp.squarefree, ?_⟩
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp hk
    exact (strictMono_squarefreeNumber.monotone hkn).trans_lt hlt
  exact hnext.trans hle

theorem gap_le_self (n : ℕ) :
    (squarefreeNumber (n + 1) : ℝ) - squarefreeNumber n ≤ squarefreeNumber n := by
  have h := next_le_two_mul n
  have hr : (squarefreeNumber (n + 1) : ℝ) ≤ 2 * squarefreeNumber n := by
    exact_mod_cast h
  linarith

theorem proof :
    (fun n : ℕ => (squarefreeNumber (n + 1) : ℝ) - squarefreeNumber n) =O[atTop]
      (fun n : ℕ => (squarefreeNumber n : ℝ) ^ (1 : ℝ)) := by
  apply Asymptotics.isBigO_of_le atTop
  intro n
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.rpow_one]
  rw [abs_of_nonneg (sub_nonneg.mpr (by
    exact_mod_cast strictMono_squarefreeNumber.monotone (Nat.le_add_right n 1)))]
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  exact gap_le_self n

end Submissions.Erdos208ExponentOne.Worker04
