import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Removable generator (for every `A`, `n`) ⇒ Erdős #488.

`M_A(y) = M_{A∖{a}}(y) + E_a(y)` where `E_a` counts the multiples of `a` divisible by no other
element of `A`. If `A = {a}` the claim is the sharp singleton inequality
`n · ⌊m/a⌋ < 2m · ⌊n/a⌋`; otherwise pick the removable `a`, apply the induction hypothesis to
`A ∖ {a}` (still nonempty, still `≤ n`), and add `n · E_a(m) ≤ 2m · E_a(n)`.
-/

namespace Submissions.ErdosMultiplesDoublingRemovableImplies.Peel

open Finset

/-- `M_A(y) = M_{A ∖ {a}}(y) + E_a(y)`. -/
lemma M_erase (A : Finset ℕ) (a : ℕ) (ha : a ∈ A) (y : ℕ) :
    ((Icc 1 y).filter (fun k => ∃ b ∈ A, b ∣ k)).card =
      ((Icc 1 y).filter (fun k => ∃ b ∈ A.erase a, b ∣ k)).card +
      ((Icc 1 y).filter (fun k => a ∣ k ∧ ∀ b ∈ A.erase a, ¬ b ∣ k)).card := by
  rw [← card_union_of_disjoint]
  · congr 1
    ext k
    simp only [mem_filter, mem_union]
    constructor
    · rintro ⟨hk, b, hb, hbk⟩
      by_cases hQ : ∃ c ∈ A.erase a, c ∣ k
      · exact Or.inl ⟨hk, hQ⟩
      · right
        refine ⟨hk, ?_, ?_⟩
        · by_cases hba : b = a
          · exact hba ▸ hbk
          · exact absurd ⟨b, mem_erase.mpr ⟨hba, hb⟩, hbk⟩ hQ
        · intro c hc hck
          exact hQ ⟨c, hc, hck⟩
    · rintro (⟨hk, b, hb, hbk⟩ | ⟨hk, hak, -⟩)
      · exact ⟨hk, b, mem_of_mem_erase hb, hbk⟩
      · exact ⟨hk, a, ha, hak⟩
  · rw [Finset.disjoint_left]
    intro k hk hk'
    simp only [mem_filter] at hk hk'
    obtain ⟨-, b, hb, hbk⟩ := hk
    exact hk'.2.2 b hb hbk

lemma card_filter_singleton (a x : ℕ) :
    ((Finset.Icc 1 x).filter (fun k => ∃ b ∈ ({a} : Finset ℕ), b ∣ k)).card = x / a := by
  have h : ((Finset.Icc 1 x).filter (fun k => ∃ b ∈ ({a} : Finset ℕ), b ∣ k)) =
      (Finset.Ioc 0 x).filter (fun k => a ∣ k) := by
    rw [← Finset.Icc_add_one_left_eq_Ioc]
    ext k
    simp
  rw [h, Nat.Ioc_filter_dvd_card_eq_div]

lemma singleton_case (a : ℕ) (ha : 0 < a) (n m : ℕ) (han : a ≤ n) (hnm : n < m) :
    n * ((Finset.Icc 1 m).filter (fun k => ∃ b ∈ ({a} : Finset ℕ), b ∣ k)).card <
      2 * m * ((Finset.Icc 1 n).filter (fun k => ∃ b ∈ ({a} : Finset ℕ), b ∣ k)).card := by
  rw [card_filter_singleton, card_filter_singleton]
  have hq : 1 ≤ n / a := (Nat.one_le_div_iff ha).mpr han
  have h1 : n < a * (n / a + 1) := by
    have := Nat.lt_div_mul_add (a := n) ha
    rw [Nat.mul_comm] at this
    linarith [Nat.mul_succ a (n / a)]
  have h2 : a * (n / a + 1) ≤ 2 * a * (n / a) := by nlinarith
  have h3 : a * (m / a) ≤ m := Nat.mul_div_le m a
  have h4 : a * (n * (m / a)) ≤ n * m := by
    calc a * (n * (m / a)) = n * (a * (m / a)) := by ring
      _ ≤ n * m := Nat.mul_le_mul_left n h3
  have h5 : n * m < a * (2 * m * (n / a)) := by
    calc n * m < (2 * a * (n / a)) * m := Nat.mul_lt_mul_of_pos_right (lt_of_lt_of_le h1 h2)
            (lt_of_le_of_lt (Nat.zero_le n) hnm)
      _ = a * (2 * m * (n / a)) := by ring
  exact Nat.lt_of_mul_lt_mul_left (lt_of_le_of_lt h4 h5)

theorem proof :
    (∀ A : Finset ℕ, A.Nonempty → 0 ∉ A →
      ∀ n : ℕ, (∀ a ∈ A, a ≤ n) →
        ∃ a ∈ A, ∀ m : ℕ, n < m →
          n * ((Finset.Icc 1 m).filter
                (fun k => a ∣ k ∧ ∀ b ∈ A.erase a, ¬ b ∣ k)).card ≤
            2 * m * ((Finset.Icc 1 n).filter
                (fun k => a ∣ k ∧ ∀ b ∈ A.erase a, ¬ b ∣ k)).card) →
    ∀ A : Finset ℕ, A.Nonempty → 0 ∉ A →
      ∀ n m : ℕ, (∀ a ∈ A, a ≤ n) → n < m →
        n * ((Finset.Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k)).card <
          2 * m * ((Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card := by
  intro H
  suffices key : ∀ N : ℕ, ∀ A : Finset ℕ, A.card = N → A.Nonempty → 0 ∉ A →
      ∀ n m : ℕ, (∀ a ∈ A, a ≤ n) → n < m →
        n * ((Finset.Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k)).card <
          2 * m * ((Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card by
    intro A; exact key A.card A rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro A hcard hA h0 n m hn hnm
    obtain ⟨a, ha, hrem⟩ := H A hA h0 n hn
    have ha0 : 0 < a := Nat.pos_of_ne_zero (fun h => h0 (h ▸ ha))
    by_cases hE : A.erase a = ∅
    · have hAa : A = {a} := by
        rw [← Finset.insert_erase ha, hE]
        rfl
      subst hAa
      exact singleton_case a ha0 n m (hn a ha) hnm
    · have hne : (A.erase a).Nonempty := Finset.nonempty_iff_ne_empty.mpr hE
      have hlt : (A.erase a).card < N := by
        rw [← hcard]; exact Finset.card_erase_lt_of_mem ha
      have h0' : 0 ∉ A.erase a := fun h => h0 (Finset.mem_of_mem_erase h)
      have hn' : ∀ b ∈ A.erase a, b ≤ n := fun b hb => hn b (Finset.mem_of_mem_erase hb)
      have ih' := ih _ hlt (A.erase a) rfl hne h0' n m hn' hnm
      have hEm := hrem m hnm
      rw [M_erase A a ha m, M_erase A a ha n, mul_add, mul_add]
      omega

end Submissions.ErdosMultiplesDoublingRemovableImplies.Peel
