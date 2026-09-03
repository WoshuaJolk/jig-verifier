import Mathlib

/-!
Erdős #488 restricted to sets `A` containing the generator `2` (no primitivity assumed,
`0 ∉ A`, arbitrary cardinality). Three cases on `A`:

* `1 ∈ A`: every `k ≥ 1` is counted, so `F(x) = x` and the inequality is `n*m < 2*m*n`,
  immediate from `n, m > 0`.
* `1 ∉ A` and every element of `A` is even: the multiples of `A` are exactly the multiples
  of `2` (every `a ∈ A` divides `k` only if `2 ∣ a ∣ k`, and `2 ∈ A` gives the converse), so
  `F(x) = x / 2` and this is the singleton bound for `a = 2`.
* `1 ∉ A` and some `b ∈ A` is odd: then `F(n) ≥ n/2 + 1` (the multiples of `2` in `[1,n]`
  together with the extra point `b`, which is odd hence not already a multiple of `2`), so
  `2*F(n) ≥ n + 1`; and `F(m) ≤ m - 1` since `1 ∉ A` means no generator divides `1`. Combining
  the two bounds with `n < m` gives the result.

Prior art: this is exactly the two-case split (`2 ∈ A` singleton bound; `2` together with an
odd generator) given informally at
https://www.erdosproblems.com/forum/thread/488#post-5163 (MalekZ, 21:13 on 31 Mar 2026), stated
there for primitive `A`. The primitivity hypothesis turns out to be unnecessary: the argument
goes through verbatim for arbitrary `A ∋ 2` with `0 ∉ A`, which is the (stronger) statement
proved here.
-/

namespace Submissions.ErdosMultiplesDoublingMinTwo.MinTwoProof

open Finset

/-- The multiples-of-`A` counting function, same vocabulary as the parent statement. -/
noncomputable def F (A : Finset ℕ) (x : ℕ) : ℕ :=
  ((Finset.Icc 1 x).filter (fun k => ∃ a ∈ A, a ∣ k)).card

lemma card_mult (a x : ℕ) : ((Icc 1 x).filter (fun k => a ∣ k)).card = x / a := by
  have h : (Icc 1 x) = Ioc 0 x := by
    have h' := Icc_add_one_left_eq_Ioc (0 : ℕ) x
    simpa using h'
  rw [h, Nat.Ioc_filter_dvd_card_eq_div]

/-- The singleton doubling inequality `n * (m / a) < 2 * m * (n / a)` for `1 ≤ a ≤ n < m`. -/
lemma singleton_ineq (a n m : ℕ) (ha : 0 < a) (han : a ≤ n) (hnm : n < m) :
    n * (m / a) < 2 * m * (n / a) := by
  have hq : 1 ≤ n / a := (Nat.one_le_div_iff ha).mpr han
  have h1 : n < a * (n / a + 1) := by
    have := Nat.lt_div_mul_add (a := n) ha
    rw [Nat.mul_comm] at this
    linarith [Nat.mul_succ a (n / a)]
  have h2 : a * (n / a + 1) ≤ 2 * a * (n / a) := by nlinarith
  have h3 : n < 2 * a * (n / a) := lt_of_lt_of_le h1 h2
  have h4 : a * (m / a) ≤ m := Nat.mul_div_le m a
  have h5 : n * (a * (m / a)) ≤ n * m := Nat.mul_le_mul_left n h4
  have h6 : n * m < 2 * a * (n / a) * m := by
    have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le n) hnm
    exact Nat.mul_lt_mul_of_pos_right h3 hm
  have h7 : a * (n * (m / a)) < a * (2 * m * (n / a)) := by
    calc a * (n * (m / a)) = n * (a * (m / a)) := by ring
      _ ≤ n * m := h5
      _ < 2 * a * (n / a) * m := h6
      _ = a * (2 * m * (n / a)) := by ring
  exact Nat.lt_of_mul_lt_mul_left h7

theorem proof : ∀ A : Finset ℕ, A.Nonempty → 0 ∉ A → 2 ∈ A →
    ∀ n m : ℕ, (∀ a ∈ A, a ≤ n) → n < m →
      n * ((Finset.Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k)).card <
        2 * m * ((Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card := by
  intro A _ h0 h2A n m hbound hnm
  have hn2 : 2 ≤ n := hbound 2 h2A
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn2
  have hm0 : 0 < m := lt_trans hn0 hnm
  by_cases h1 : (1 : ℕ) ∈ A
  · -- trivial case: every k ≥ 1 is a multiple, F(x) = x
    have hFeq : ∀ x : ℕ, (Finset.Icc 1 x).filter (fun k => ∃ a ∈ A, a ∣ k) = Finset.Icc 1 x := by
      intro x
      apply Finset.filter_true_of_mem
      intro k _
      exact ⟨1, h1, one_dvd k⟩
    rw [hFeq m, hFeq n, Nat.card_Icc, Nat.card_Icc]
    have hmm : m + 1 - 1 = m := by omega
    have hnn : n + 1 - 1 = n := by omega
    rw [hmm, hnn]
    nlinarith
  · by_cases h2 : ∀ a ∈ A, 2 ∣ a
    · -- all elements even: F(x) = x / 2
      have hFeq : ∀ x : ℕ, (Finset.Icc 1 x).filter (fun k => ∃ a ∈ A, a ∣ k) =
          (Finset.Icc 1 x).filter (fun k => 2 ∣ k) := by
        intro x
        ext k
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hk, a, haA, had⟩
          exact ⟨hk, dvd_trans (h2 a haA) had⟩
        · rintro ⟨hk, hdk⟩
          exact ⟨hk, 2, h2A, hdk⟩
      rw [hFeq m, hFeq n, card_mult, card_mult]
      exact singleton_ineq 2 n m (by norm_num) hn2 hnm
    · -- some odd generator b ∈ A besides possibly others
      push_neg at h2
      obtain ⟨b, hbA, hb2⟩ := h2
      have hb0 : 0 < b := Nat.pos_of_ne_zero (fun h => h0 (h ▸ hbA))
      have hbn : b ≤ n := hbound b hbA
      -- lower bound: F(n) ≥ n/2 + 1
      have hsub : insert b ((Finset.Icc 1 n).filter (fun k => 2 ∣ k)) ⊆
          (Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k) := by
        intro k hk
        rcases Finset.mem_insert.mp hk with heq | hk'
        · rw [heq]
          exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hb0, hbn⟩, b, hbA, dvd_refl b⟩
        · obtain ⟨hkIcc, hkdvd⟩ := Finset.mem_filter.mp hk'
          exact Finset.mem_filter.mpr ⟨hkIcc, 2, h2A, hkdvd⟩
      have hnotmem : b ∉ (Finset.Icc 1 n).filter (fun k => 2 ∣ k) := by
        intro hmem
        exact hb2 (Finset.mem_filter.mp hmem).2
      have hcard : ((Finset.Icc 1 n).filter (fun k => 2 ∣ k)).card + 1 ≤
          ((Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card := by
        have := Finset.card_le_card hsub
        rwa [Finset.card_insert_of_notMem hnotmem] at this
      rw [card_mult] at hcard
      have hlow : n + 1 ≤ 2 * ((Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card := by
        have hdm := Nat.div_add_mod n 2
        have hmod : n % 2 < 2 := Nat.mod_lt n (by norm_num)
        omega
      -- upper bound: F(m) ≤ m - 1, since 1 is never a multiple
      have hnotone : (1 : ℕ) ∉ (Finset.Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k) := by
        intro hmem
        obtain ⟨_, a, haA, had⟩ := Finset.mem_filter.mp hmem
        have : a = 1 := Nat.dvd_one.mp had
        exact h1 (this ▸ haA)
      have hsubm : (Finset.Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k) ⊆
          (Finset.Icc 1 m).erase 1 := by
        intro k hk
        have hne : k ≠ 1 := by
          intro heq
          exact hnotone (heq ▸ hk)
        exact Finset.mem_erase.mpr ⟨hne, Finset.filter_subset _ _ hk⟩
      have hcardm : ((Finset.Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k)).card ≤ m - 1 := by
        have h1mem : (1 : ℕ) ∈ Finset.Icc 1 m := Finset.mem_Icc.mpr ⟨le_refl 1, hm0⟩
        have := Finset.card_le_card hsubm
        rwa [Finset.card_erase_of_mem h1mem, Nat.card_Icc] at this
      have hup : ((Finset.Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k)).card + 1 ≤ m := by omega
      -- combine
      set Fn := ((Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card with hFn
      set Fm := ((Finset.Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k)).card with hFm
      have hu2 : n * (Fm + 1) ≤ n * m := Nat.mul_le_mul_left n hup
      have hl2 : m * (n + 1) ≤ m * (2 * Fn) := Nat.mul_le_mul_left m hlow
      nlinarith [hu2, hl2, hm0]

end Submissions.ErdosMultiplesDoublingMinTwo.MinTwoProof
