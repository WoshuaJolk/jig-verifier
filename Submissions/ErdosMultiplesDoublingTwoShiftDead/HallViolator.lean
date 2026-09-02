import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith

/-!
The two-translate charging rule does not prove the Window Bound.

`A = {8, 11, 12, 14, 18, 19, 21, 26}`, `n = 138`, `x = 354`. The window `(354, 492]` holds
`52` multiples of `A` and `[1, 138]` holds `56`, so the Window Bound `52 ≤ 112` is true.
But `483 = 21·23`, `486 = 18·27`, `490 = 14·35` each have exactly one generator; their
`⌊x/a⌋`-translates `147, 144, 140` leave `[1, 138]`, and their `⌈x/a⌉`-translates are all
`126`. So every two-translate `f` has `#f⁻¹(126) ≥ 3`.
-/

namespace Submissions.ErdosMultiplesDoublingTwoShiftDead.HallViolator

open Finset

abbrev A : Finset ℕ := {8, 11, 12, 14, 18, 19, 21, 26}

abbrev K1 : Finset ℕ := {483, 486, 490}

lemma K1_sub : K1 ⊆ (Icc (354 + 1) (354 + 138)).filter (fun k => ∃ a ∈ A, a ∣ k) := by decide

lemma forced : ∀ k ∈ K1, ∀ d ∈ (Icc 1 138).filter (fun k => ∃ a ∈ A, a ∣ k),
    (∃ a ∈ A, a ∣ k ∧ (d + a * (354 / a) = k ∨ d + a * ((354 + a - 1) / a) = k)) → d = 126 := by
  decide

theorem proof :
    ∃ A : Finset ℕ, A.Nonempty ∧ 0 ∉ A ∧
      ∃ n x : ℕ, (∀ a ∈ A, a ≤ n) ∧
        ((Finset.Icc (x + 1) (x + n)).filter (fun k => ∃ a ∈ A, a ∣ k)).card ≤
          2 * ((Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card ∧
        ∀ f : ℕ → ℕ,
          (∀ k ∈ (Finset.Icc (x + 1) (x + n)).filter (fun k => ∃ a ∈ A, a ∣ k),
            f k ∈ (Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k) ∧
            ∃ a ∈ A, a ∣ k ∧ (f k + a * (x / a) = k ∨ f k + a * ((x + a - 1) / a) = k)) →
          ∃ d ∈ (Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k),
            2 < (((Finset.Icc (x + 1) (x + n)).filter (fun k => ∃ a ∈ A, a ∣ k)).filter
              (fun k => f k = d)).card := by
  refine ⟨A, by decide, by decide, 138, 354, by decide, by decide, ?_⟩
  intro f hf
  refine ⟨126, by decide, ?_⟩
  have hsub : K1 ⊆ ((Icc (354 + 1) (354 + 138)).filter (fun k => ∃ a ∈ A, a ∣ k)).filter
      (fun k => f k = 126) := by
    intro k hk
    have hkW := K1_sub hk
    obtain ⟨hmem, hrule⟩ := hf k hkW
    rw [mem_filter]
    exact ⟨hkW, forced k hk (f k) hmem hrule⟩
  have hcard := Finset.card_le_card hsub
  have hK1 : K1.card = 3 := by decide
  omega

end Submissions.ErdosMultiplesDoublingTwoShiftDead.HallViolator
