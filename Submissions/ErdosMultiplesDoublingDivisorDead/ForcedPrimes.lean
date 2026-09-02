import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith

/-!
Charging multiples to divisors cannot prove Erdős #488.

Witness `G = {8,12,18,20,28,30,42,44,52,68}`, `n = 180`, `m = 360`. The six numbers
`8q`, `q ∈ {23,29,31,37,41,43}`, lie in `B_G ∩ [1, 360]`, and the only divisor of `8q` in
`B_G ∩ [1, 180]` is `8` (the divisors are `1,2,4,8,q,2q,4q,8q`; none but `8` is a multiple of
an element of `G`, and `8q > 180`). Hence any `f` with `f k ∣ k`, `f k ∈ B_G ∩ [1,180]` sends
all six to `8`, so `n · #f⁻¹(8) ≥ 1080 > 720 = 2m`, while `n · M(360) < 2m · M(180)` holds.
-/

namespace Submissions.ErdosMultiplesDoublingDivisorDead.ForcedPrimes

open Finset

abbrev G : Finset ℕ := {8, 12, 18, 20, 28, 30, 42, 44, 52, 68}

abbrev K0 : Finset ℕ := {184, 232, 248, 296, 328, 344}

lemma K0_sub : K0 ⊆ (Icc 1 360).filter (fun k => ∃ a ∈ G, a ∣ k) := by decide

lemma forced : ∀ k ∈ K0, ∀ d ∈ (Icc 1 180).filter (fun k => ∃ a ∈ G, a ∣ k), d ∣ k → d = 8 := by
  decide

theorem proof :
    ∃ A : Finset ℕ, A.Nonempty ∧ 0 ∉ A ∧
      ∃ n m : ℕ, (∀ a ∈ A, a ≤ n) ∧ n < m ∧
        n * ((Finset.Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k)).card <
          2 * m * ((Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card ∧
        ∀ f : ℕ → ℕ,
          (∀ k ∈ (Finset.Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k),
            f k ∣ k ∧ f k ∈ (Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)) →
          ∃ d ∈ (Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k),
            2 * m < n * (((Finset.Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k)).filter
              (fun k => f k = d)).card := by
  refine ⟨G, by decide, by decide, 180, 360, by decide, by norm_num, by decide, ?_⟩
  intro f hf
  refine ⟨8, by decide, ?_⟩
  have hsub : K0 ⊆ ((Icc 1 360).filter (fun k => ∃ a ∈ G, a ∣ k)).filter (fun k => f k = 8) := by
    intro k hk
    have hkB := K0_sub hk
    obtain ⟨hdiv, hmem⟩ := hf k hkB
    rw [mem_filter]
    exact ⟨hkB, forced k hk (f k) hmem hdiv⟩
  have hcard := Finset.card_le_card hsub
  have hK0 : K0.card = 6 := by decide
  omega

end Submissions.ErdosMultiplesDoublingDivisorDead.ForcedPrimes
