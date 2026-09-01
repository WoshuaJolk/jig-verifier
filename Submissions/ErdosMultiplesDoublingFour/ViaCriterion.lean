import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
Chojecki's inequality (10) for primitive 4-sets `G = {a < b < c < d}`:

  `n/a + n/b + n/c + n/d + 4 ≤ 2 M(n)`.

Write `deg k = #{g ∈ G : g ∣ k}` and `N_j = #{k ≤ n : deg k = j}`.  Pointwise
`2·[deg ≥ 1] + [deg = 3] + 2·[deg = 4] = deg + [deg = 1]`, so summing,
`2 M(n) + N_3 + 2 N_4 = ∑ ⌊n/g⌋ + N_1`, and the claim is `N_1 ≥ 4 + N_3 + 2 N_4`.
`N_1` contains `a, b, c, d` plus three pairwise disjoint injective images:

* `k ↦ k - a` and `k ↦ k - b` on `S_4` (all of `G` divides `k`): `g ∣ k - a` and `g ∣ k` force
  `g ∣ a`, so `k - a` is divisible by `a` alone;
* on `S_3` (exactly one `h ∈ G` misses `k`), with `g₁` the least divisor of `k` in `G`:
  `k ↦ k - g₁` if `h ∤ k - g₁`, else `k ↦ k - 2g₁` (then `k ≡ g₁ (mod h)`, so `h ∤ k - 2g₁`,
  and `g ∣ 2g₁` is impossible for `g > g₁` by primitivity).

Every image `x` is divisible by exactly one `g ∈ G`, and `x + g` or `x + 2g` recovers the source;
a collision `k' = k + g` between two sources of degree `≥ 3` would give an element `e ≠ g` of `G`
dividing both, hence `e ∣ g`, contradicting `e > g` or primitivity.
-/

namespace Submissions.ErdosMultiplesDoublingFour.ViaCriterion

open Finset

lemma card_mult (a x : ℕ) : ((Icc 1 x).filter (fun k => a ∣ k)).card = x / a := by
  have : (Icc 1 x) = Ioc 0 x := by
    have h := Icc_add_one_left_eq_Ioc (0 : ℕ) x
    simpa using h
  rw [this, Nat.Ioc_filter_dvd_card_eq_div]

/-- `b ∤ 2a` for `a < b` unless `a ∣ b`. -/
lemma not_dvd_two_mul {a b : ℕ} (ha : 0 < a) (hab : a < b) (hnd : ¬ a ∣ b) : ¬ b ∣ 2 * a := by
  rintro ⟨j, hj⟩
  rcases Nat.lt_or_ge j 2 with hj2 | hj2
  · interval_cases j
    · omega
    · exact hnd ⟨2, by omega⟩
  · have : b * 2 ≤ b * j := Nat.mul_le_mul_left b hj2
    omega

lemma not_dvd_of_lt {a e : ℕ} (ha : 0 < a) (h : a < e) : ¬ e ∣ a :=
  fun hd => absurd (Nat.le_of_dvd ha hd) (by omega)

/-- `e ∣ k`, `e ∣ k - a`, `a ≤ k` give `e ∣ a`. -/
lemma dvd_of_dvd_sub {e k a : ℕ} (hk : e ∣ k) (hs : e ∣ k - a) (h : a ≤ k) : e ∣ a := by
  have := Nat.dvd_sub hk hs
  rwa [Nat.sub_sub_self h] at this

/-- `e ∣ k`, `e ∣ k - 2a`, `2a ≤ k` give `e ∣ 2a`. -/
lemma dvd_two_of_dvd_sub {e k a : ℕ} (hk : e ∣ k) (hs : e ∣ k - 2 * a) (h : 2 * a ≤ k) :
    e ∣ 2 * a := by
  have := Nat.dvd_sub hk hs
  rwa [Nat.sub_sub_self h] at this

/-- `e ∣ k - a`, `e ∣ k - 2a`, `2a ≤ k` give `e ∣ a`. -/
lemma dvd_of_dvd_sub_sub {e k a : ℕ} (h1 : e ∣ k - a) (h2 : e ∣ k - 2 * a) (h : 2 * a ≤ k) :
    e ∣ a := by
  have := Nat.dvd_sub h1 h2
  have heq : k - a - (k - 2 * a) = a := by omega
  rwa [heq] at this

/-- A common multiple `k ≥ 1` of `g < e` with `e ∤ g` is at least `2g`. -/
lemma two_mul_le {g e k : ℕ} (hg : 0 < g) (hge : g < e) (hgk : g ∣ k) (hek : e ∣ k)
    (hk : 0 < k) : 2 * g ≤ k := by
  obtain ⟨t, rfl⟩ := hgk
  rcases t with _ | _ | t
  · omega
  · exact absurd (Nat.le_of_dvd hg (by simpa using hek)) (by omega)
  · have := Nat.mul_le_mul_left g (show 2 ≤ t + 1 + 1 by omega)
    omega

/-- A common multiple `k ≥ 1` of `g < e` with `e ∤ g`, `e ∤ 2g` is at least `3g`. -/
lemma three_mul_le {g e k : ℕ} (hg : 0 < g) (hge : g < e) (hgk : g ∣ k) (hek : e ∣ k)
    (hk : 0 < k) (h2 : ¬ e ∣ 2 * g) : 3 * g ≤ k := by
  obtain ⟨t, rfl⟩ := hgk
  rcases t with _ | _ | _ | t
  · omega
  · exact absurd (Nat.le_of_dvd hg (by simpa using hek)) (by omega)
  · exact absurd (by simpa [mul_comm] using hek) h2
  · have := Nat.mul_le_mul_left g (show 3 ≤ t + 1 + 1 + 1 by omega)
    omega

/-- No two elements `a < e < e'` of a primitive set both divide `3a`. -/
lemma not_both_dvd_three_mul {a e e' : ℕ} (ha : 0 < a) (hae : a < e) (hee : e < e')
    (hnae : ¬ a ∣ e) (hnae' : ¬ a ∣ e') (he : e ∣ 3 * a) (he' : e' ∣ 3 * a) : False := by
  obtain ⟨t, ht⟩ := he
  obtain ⟨s, hs⟩ := he'
  rcases t with _ | _ | _ | t
  · omega
  · exact hnae ⟨3, by omega⟩
  · rcases s with _ | _ | s
    · omega
    · exact hnae' ⟨3, by omega⟩
    · have := Nat.mul_le_mul_left e' (show 2 ≤ s + 1 + 1 by omega)
      omega
  · have := Nat.mul_le_mul_left e (show 3 ≤ t + 1 + 1 + 1 by omega)
    omega

section

variable {a b c d n : ℕ} (ha : 0 < a) (hab : a < b) (hbc : b < c) (hcd : c < d)
  (hnab : ¬ a ∣ b) (hnac : ¬ a ∣ c) (hnad : ¬ a ∣ d)
  (hnbc : ¬ b ∣ c) (hnbd : ¬ b ∣ d) (hncd : ¬ c ∣ d) (hdn : d ≤ n)

/-- Number of elements of `{a,b,c,d}` dividing `k`. -/
def dg (a b c d k : ℕ) : ℕ :=
  (if a ∣ k then 1 else 0) + (if b ∣ k then 1 else 0) +
    (if c ∣ k then 1 else 0) + (if d ∣ k then 1 else 0)

lemma pointwise (k : ℕ) :
    2 * (if a ∣ k ∨ b ∣ k ∨ c ∣ k ∨ d ∣ k then 1 else 0) +
        (if dg a b c d k = 3 then 1 else 0) + 2 * (if dg a b c d k = 4 then 1 else 0) =
      ((if a ∣ k then 1 else 0) + (if b ∣ k then 1 else 0) +
        (if c ∣ k then 1 else 0) + (if d ∣ k then 1 else 0)) +
        (if dg a b c d k = 1 then 1 else 0) := by
  unfold dg
  by_cases h1 : a ∣ k <;> by_cases h2 : b ∣ k <;> by_cases h3 : c ∣ k <;> by_cases h4 : d ∣ k <;>
    simp [h1, h2, h3, h4]

lemma sum_identity :
    2 * ((Icc 1 n).filter (fun k => a ∣ k ∨ b ∣ k ∨ c ∣ k ∨ d ∣ k)).card +
        ((Icc 1 n).filter (fun k => dg a b c d k = 3)).card +
        2 * ((Icc 1 n).filter (fun k => dg a b c d k = 4)).card =
      (n / a + n / b + n / c + n / d) + ((Icc 1 n).filter (fun k => dg a b c d k = 1)).card := by
  rw [← card_mult a n, ← card_mult b n, ← card_mult c n, ← card_mult d n]
  simp only [card_filter]
  rw [mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib,
    ← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
  exact sum_congr rfl (fun k _ => pointwise k)

lemma dg4 {k : ℕ} (h : dg a b c d k = 4) : a ∣ k ∧ b ∣ k ∧ c ∣ k ∧ d ∣ k := by
  by_cases h1 : a ∣ k <;> by_cases h2 : b ∣ k <;> by_cases h3 : c ∣ k <;> by_cases h4 : d ∣ k <;>
    simp_all [dg]

lemma dg3_a {k : ℕ} (h : dg a b c d k = 3) (hak : a ∣ k) :
    (b ∣ k ∧ c ∣ k ∧ ¬ d ∣ k) ∨ (b ∣ k ∧ ¬ c ∣ k ∧ d ∣ k) ∨ (¬ b ∣ k ∧ c ∣ k ∧ d ∣ k) := by
  by_cases h2 : b ∣ k <;> by_cases h3 : c ∣ k <;> by_cases h4 : d ∣ k <;>
    simp_all [dg]

lemma dg3_na {k : ℕ} (h : dg a b c d k = 3) (hak : ¬ a ∣ k) : b ∣ k ∧ c ∣ k ∧ d ∣ k := by
  by_cases h2 : b ∣ k <;> by_cases h3 : c ∣ k <;> by_cases h4 : d ∣ k <;>
    simp_all [dg]

lemma dg_one_of_a {x : ℕ} (h1 : a ∣ x) (h2 : ¬ b ∣ x) (h3 : ¬ c ∣ x) (h4 : ¬ d ∣ x) :
    dg a b c d x = 1 := by simp [dg, h1, h2, h3, h4]

lemma dg_one_of_b {x : ℕ} (h1 : ¬ a ∣ x) (h2 : b ∣ x) (h3 : ¬ c ∣ x) (h4 : ¬ d ∣ x) :
    dg a b c d x = 1 := by simp [dg, h1, h2, h3, h4]

lemma dg1_ab {x : ℕ} (h : dg a b c d x = 1) (h1 : a ∣ x) (h2 : b ∣ x) : False := by
  by_cases h3 : c ∣ x <;> by_cases h4 : d ∣ x <;> simp_all [dg]

/-- The `S₃` shift: `g` the least `G`-divisor of `k`, `e < e'` the other two, `h` missing. -/
lemma shift3 {g e e' h k x : ℕ} (hg : 0 < g) (hge : g < e) (hee : e < e')
    (hnge : ¬ g ∣ e) (hnge' : ¬ g ∣ e') (hnhg : ¬ h ∣ g)
    (hk1 : 1 ≤ k) (hgk : g ∣ k) (hek : e ∣ k) (he'k : e' ∣ k)
    (hx : x = if h ∣ k - g then k - 2 * g else k - g) :
    1 ≤ x ∧ x ≤ k ∧ g ∣ x ∧ ¬ e ∣ x ∧ ¬ e' ∣ x ∧ ¬ h ∣ x ∧ x ≠ g := by
  subst hx
  have h2g : 2 * g ≤ k := two_mul_le hg hge hgk hek hk1
  have hne2 : ¬ e ∣ 2 * g := not_dvd_two_mul hg hge hnge
  have hne'2 : ¬ e' ∣ 2 * g := not_dvd_two_mul hg (by omega) hnge'
  have hne1 : ¬ e ∣ g := not_dvd_of_lt hg hge
  have hne'1 : ¬ e' ∣ g := not_dvd_of_lt hg (by omega)
  have h3g : 3 * g ≤ k := three_mul_le hg hge hgk hek hk1 hne2
  split_ifs with hh
  · refine ⟨by omega, by omega, Nat.dvd_sub hgk (dvd_mul_left g 2), ?_, ?_, ?_, ?_⟩
    · exact fun h' => hne2 (dvd_two_of_dvd_sub hek h' h2g)
    · exact fun h' => hne'2 (dvd_two_of_dvd_sub he'k h' h2g)
    · exact fun h' => hnhg (dvd_of_dvd_sub_sub hh h' h2g)
    · intro hx
      have hk3 : k = 3 * g := by omega
      rw [hk3] at hek he'k
      exact not_both_dvd_three_mul hg hge hee hnge hnge' hek he'k
  · refine ⟨by omega, by omega, Nat.dvd_sub hgk dvd_rfl, ?_, ?_, hh, ?_⟩
    · exact fun h' => hne1 (dvd_of_dvd_sub hek h' (by omega))
    · exact fun h' => hne'1 (dvd_of_dvd_sub he'k h' (by omega))
    · intro hx
      have hk2 : k = 2 * g := by omega
      rw [hk2] at hek
      exact hne2 hek

/-- The `S₄` shift `k ↦ k - g`; `e, e', e''` are the other three elements. -/
lemma shift4 {g e e' e'' k : ℕ} (hg : 0 < g) (hge : g < e) (hnge : ¬ g ∣ e)
    (hne : ¬ e ∣ g) (hne' : ¬ e' ∣ g) (hne'' : ¬ e'' ∣ g)
    (hk1 : 1 ≤ k) (hgk : g ∣ k) (hek : e ∣ k) (he'k : e' ∣ k) (he''k : e'' ∣ k) :
    1 ≤ k - g ∧ g ∣ k - g ∧ ¬ e ∣ k - g ∧ ¬ e' ∣ k - g ∧ ¬ e'' ∣ k - g ∧ k - g ≠ g := by
  have h2g : 2 * g ≤ k := two_mul_le hg hge hgk hek hk1
  have hne2 : ¬ e ∣ 2 * g := not_dvd_two_mul hg hge hnge
  refine ⟨by omega, Nat.dvd_sub hgk dvd_rfl, ?_, ?_, ?_, ?_⟩
  · exact fun h' => hne (dvd_of_dvd_sub hek h' (by omega))
  · exact fun h' => hne' (dvd_of_dvd_sub he'k h' (by omega))
  · exact fun h' => hne'' (dvd_of_dvd_sub he''k h' (by omega))
  · intro hx
    have hk2 : k = 2 * g := by omega
    rw [hk2] at hek
    exact hne2 hek

/-- `bad k`: the element of `{b,c,d}` missing `k` divides `k - a`. -/
def bad (a b c d k : ℕ) : Prop :=
  (¬ b ∣ k ∧ b ∣ k - a) ∨ (¬ c ∣ k ∧ c ∣ k - a) ∨ (¬ d ∣ k ∧ d ∣ k - a)

instance (a b c d k : ℕ) : Decidable (bad a b c d k) := by unfold bad; infer_instance

/-- The injection `S₃ → S₁ \ G`. -/
def φ (a b c d k : ℕ) : ℕ :=
  if a ∣ k then (if bad a b c d k then k - 2 * a else k - a)
  else (if a ∣ k - b then k - 2 * b else k - b)

include ha hab hbc hcd hnab hnac hnad hnbc hnbd in
lemma phi_mem {k : ℕ} (hk : k ∈ (Icc 1 n).filter (fun k => dg a b c d k = 3)) :
    φ a b c d k ∈ (Icc 1 n).filter (fun k => dg a b c d k = 1) ∧
      φ a b c d k ∉ ({a, b, c, d} : Finset ℕ) ∧
      (a ∣ k → a ∣ φ a b c d k) ∧ (¬ a ∣ k → b ∣ φ a b c d k) := by
  rw [mem_filter, mem_Icc] at hk
  obtain ⟨⟨hk1, hkn⟩, hk3⟩ := hk
  rw [mem_filter, mem_Icc, mem_insert, mem_insert, mem_insert, mem_singleton]
  simp only [not_or]
  by_cases hak : a ∣ k
  · rcases dg3_a hk3 hak with ⟨hb, hc, hnd⟩ | ⟨hb, hnc, hd⟩ | ⟨hnb, hc, hd⟩
    · have hφ : φ a b c d k = if d ∣ k - a then k - 2 * a else k - a := by
        unfold φ bad; simp [hak, hb, hc, hnd]
      obtain ⟨h1, h2, hga, hne, hne', hnh, hxg⟩ :=
        shift3 ha hab hbc hnab hnac (not_dvd_of_lt ha (by omega)) hk1 hak hb hc hφ
      refine ⟨⟨⟨h1, by omega⟩, dg_one_of_a hga hne hne' hnh⟩, ⟨hxg, ?_, ?_, ?_⟩,
        fun _ => hga, fun h => absurd hak h⟩
      · intro hx; exact hne (by rw [hx])
      · intro hx; exact hne' (by rw [hx])
      · intro hx; exact hnh (by rw [hx])
    · have hφ : φ a b c d k = if c ∣ k - a then k - 2 * a else k - a := by
        unfold φ bad; simp [hak, hb, hnc, hd]
      obtain ⟨h1, h2, hga, hne, hne', hnh, hxg⟩ :=
        shift3 ha hab (by omega) hnab hnad (not_dvd_of_lt ha (by omega)) hk1 hak hb hd hφ
      refine ⟨⟨⟨h1, by omega⟩, dg_one_of_a hga hne hnh hne'⟩, ⟨hxg, ?_, ?_, ?_⟩,
        fun _ => hga, fun h => absurd hak h⟩
      · intro hx; exact hne (by rw [hx])
      · intro hx; exact hnh (by rw [hx])
      · intro hx; exact hne' (by rw [hx])
    · have hφ : φ a b c d k = if b ∣ k - a then k - 2 * a else k - a := by
        unfold φ bad; simp [hak, hnb, hc, hd]
      obtain ⟨h1, h2, hga, hne, hne', hnh, hxg⟩ :=
        shift3 ha (by omega) hcd hnac hnad (not_dvd_of_lt ha hab) hk1 hak hc hd hφ
      refine ⟨⟨⟨h1, by omega⟩, dg_one_of_a hga hnh hne hne'⟩, ⟨hxg, ?_, ?_, ?_⟩,
        fun _ => hga, fun h => absurd hak h⟩
      · intro hx; exact hnh (by rw [hx])
      · intro hx; exact hne (by rw [hx])
      · intro hx; exact hne' (by rw [hx])
  · obtain ⟨hb, hc, hd⟩ := dg3_na hk3 hak
    have hφ : φ a b c d k = if a ∣ k - b then k - 2 * b else k - b := by
      unfold φ; simp [hak]
    obtain ⟨h1, h2, hgb, hne, hne', hnh, hxg⟩ :=
      shift3 (by omega) hbc hcd hnbc hnbd hnab hk1 hb hc hd hφ
    refine ⟨⟨⟨h1, by omega⟩, dg_one_of_b hnh hgb hne hne'⟩, ⟨?_, hxg, ?_, ?_⟩,
      fun h => absurd h hak, fun _ => hgb⟩
    · intro hx; exact hnh (by rw [hx])
    · intro hx; exact hne (by rw [hx])
    · intro hx; exact hne' (by rw [hx])

include ha hab hbc hcd hnab in
lemma psi_a_mem {k : ℕ} (hk : k ∈ (Icc 1 n).filter (fun k => dg a b c d k = 4)) :
    k - a ∈ (Icc 1 n).filter (fun k => dg a b c d k = 1) ∧
      k - a ∉ ({a, b, c, d} : Finset ℕ) ∧ a ∣ k - a := by
  rw [mem_filter, mem_Icc] at hk
  obtain ⟨⟨hk1, hkn⟩, hk4⟩ := hk
  obtain ⟨hak, hbk, hck, hdk⟩ := dg4 hk4
  obtain ⟨h1, hga, hne, hne', hne'', hxg⟩ :=
    shift4 ha hab hnab (not_dvd_of_lt ha hab) (not_dvd_of_lt ha (by omega))
      (not_dvd_of_lt ha (by omega)) hk1 hak hbk hck hdk
  rw [mem_filter, mem_Icc, mem_insert, mem_insert, mem_insert, mem_singleton]
  simp only [not_or]
  refine ⟨⟨⟨h1, by omega⟩, dg_one_of_a hga hne hne' hne''⟩, ⟨hxg, ?_, ?_, ?_⟩, hga⟩
  · intro hx; exact hne (by rw [hx])
  · intro hx; exact hne' (by rw [hx])
  · intro hx; exact hne'' (by rw [hx])

include ha hab hbc hcd hnab hnbc in
lemma psi_b_mem {k : ℕ} (hk : k ∈ (Icc 1 n).filter (fun k => dg a b c d k = 4)) :
    k - b ∈ (Icc 1 n).filter (fun k => dg a b c d k = 1) ∧
      k - b ∉ ({a, b, c, d} : Finset ℕ) ∧ b ∣ k - b := by
  rw [mem_filter, mem_Icc] at hk
  obtain ⟨⟨hk1, hkn⟩, hk4⟩ := hk
  obtain ⟨hak, hbk, hck, hdk⟩ := dg4 hk4
  obtain ⟨h1, hgb, hne, hne', hne'', hxg⟩ :=
    shift4 (by omega) hbc hnbc (not_dvd_of_lt (by omega) hbc) hnab
      (not_dvd_of_lt (by omega) (by omega)) hk1 hbk hck hak hdk
  rw [mem_filter, mem_Icc, mem_insert, mem_insert, mem_insert, mem_singleton]
  simp only [not_or]
  refine ⟨⟨⟨h1, by omega⟩, dg_one_of_b hne' hgb hne hne''⟩, ⟨?_, hxg, ?_, ?_⟩, hgb⟩
  · intro hx; exact hne' (by rw [hx])
  · intro hx; exact hne (by rw [hx])
  · intro hx; exact hne'' (by rw [hx])

include ha hab hbc hcd hnab hnac hnad hnbc hnbd hncd hdn in
lemma abcd_subset :
    ({a, b, c, d} : Finset ℕ) ⊆ (Icc 1 n).filter (fun k => dg a b c d k = 1) := by
  intro x hx
  simp only [mem_insert, mem_singleton] at hx
  simp only [mem_filter, mem_Icc]
  rcases hx with rfl | rfl | rfl | rfl
  · refine ⟨⟨ha, by omega⟩, dg_one_of_a dvd_rfl ?_ ?_ ?_⟩ <;>
      exact not_dvd_of_lt ha (by omega)
  · refine ⟨⟨by omega, by omega⟩, dg_one_of_b hnab dvd_rfl ?_ ?_⟩ <;>
      exact not_dvd_of_lt (by omega) (by omega)
  · exact ⟨⟨by omega, by omega⟩, by simp [dg, hnac, hnbc, not_dvd_of_lt (by omega : 0 < x) hcd]⟩
  · exact ⟨⟨by omega, hdn⟩, by simp [dg, hnad, hnbd, hncd]⟩

/-- Two sources of degree `≥ 3` cannot differ by `g` when `g` divides both. -/
lemma dvd_of_shift {e k k' g : ℕ} (hek : e ∣ k) (hek' : e ∣ k') (h : k' = k + g) : e ∣ g := by
  subst h
  exact (Nat.dvd_add_right hek).mp hek'

include ha hab hbc hcd hnab hnac hnad hnbc hnbd in
lemma phi_injOn :
    Set.InjOn (φ a b c d) ((Icc 1 n).filter (fun k => dg a b c d k = 3) : Set ℕ) := by
  intro k hk k' hk' heq
  have hm := phi_mem ha hab hbc hcd hnab hnac hnad hnbc hnbd (mem_coe.mp hk)
  have hm' := phi_mem ha hab hbc hcd hnab hnac hnad hnbc hnbd (mem_coe.mp hk')
  rw [mem_coe, mem_filter, mem_Icc] at hk hk'
  obtain ⟨⟨hk1, hkn⟩, hk3⟩ := hk
  obtain ⟨⟨hk1', hkn'⟩, hk3'⟩ := hk'
  have hdg1 : dg a b c d (φ a b c d k) = 1 := (mem_filter.mp hm.1).2
  by_cases hak : a ∣ k <;> by_cases hak' : a ∣ k'
  · -- both divisible by `a`: images `k - a` or `k - 2a`
    have h2 : 2 * a ≤ k := by
      rcases dg3_a hk3 hak with ⟨hb, -, -⟩ | ⟨hb, -, -⟩ | ⟨-, hc, -⟩
      · exact two_mul_le ha hab hak hb hk1
      · exact two_mul_le ha hab hak hb hk1
      · exact two_mul_le ha (by omega) hak hc hk1
    have h2' : 2 * a ≤ k' := by
      rcases dg3_a hk3' hak' with ⟨hb, -, -⟩ | ⟨hb, -, -⟩ | ⟨-, hc, -⟩
      · exact two_mul_le ha hab hak' hb hk1'
      · exact two_mul_le ha hab hak' hb hk1'
      · exact two_mul_le ha (by omega) hak' hc hk1'
    -- a common element of `{b,c,d}` dividing both `k` and `k'`
    have hcommon : ∃ e, a < e ∧ e ∣ k ∧ e ∣ k' := by
      rcases dg3_a hk3 hak with ⟨hb, hc, -⟩ | ⟨hb, -, hd⟩ | ⟨-, hc, hd⟩ <;>
        rcases dg3_a hk3' hak' with ⟨hb', hc', -⟩ | ⟨hb', -, hd'⟩ | ⟨-, hc', hd'⟩
      · exact ⟨b, hab, hb, hb'⟩
      · exact ⟨b, hab, hb, hb'⟩
      · exact ⟨c, by omega, hc, hc'⟩
      · exact ⟨b, hab, hb, hb'⟩
      · exact ⟨b, hab, hb, hb'⟩
      · exact ⟨d, by omega, hd, hd'⟩
      · exact ⟨c, by omega, hc, hc'⟩
      · exact ⟨d, by omega, hd, hd'⟩
      · exact ⟨c, by omega, hc, hc'⟩
    obtain ⟨e, hae, hek, hek'⟩ := hcommon
    unfold φ at heq
    rw [if_pos hak, if_pos hak'] at heq
    split_ifs at heq with hb1 hb2 hb2
    · omega
    · have : k = k' + a := by omega
      exact absurd (dvd_of_shift hek' hek this) (not_dvd_of_lt ha hae)
    · have : k' = k + a := by omega
      exact absurd (dvd_of_shift hek hek' this) (not_dvd_of_lt ha hae)
    · omega
  · exact absurd (dg1_ab hdg1 (hm.2.2.1 hak) (heq ▸ hm'.2.2.2 hak')) id
  · exact absurd (dg1_ab hdg1 (heq ▸ hm'.2.2.1 hak') (hm.2.2.2 hak)) id
  · obtain ⟨hb, hc, hd⟩ := dg3_na hk3 hak
    obtain ⟨hb', hc', hd'⟩ := dg3_na hk3' hak'
    have h2 : 2 * b ≤ k := two_mul_le (by omega) hbc hb hc hk1
    have h2' : 2 * b ≤ k' := two_mul_le (by omega) hbc hb' hc' hk1'
    unfold φ at heq
    rw [if_neg hak, if_neg hak'] at heq
    split_ifs at heq with hb1 hb2 hb2
    · omega
    · have : k = k' + b := by omega
      exact absurd (dvd_of_shift hc' hc this) (not_dvd_of_lt (by omega) hbc)
    · have : k' = k + b := by omega
      exact absurd (dvd_of_shift hc hc' this) (not_dvd_of_lt (by omega) hbc)
    · omega

lemma sub_injOn (g : ℕ) (S : Finset ℕ) (hS : ∀ k ∈ S, g ∣ k ∧ 1 ≤ k) :
    Set.InjOn (fun k => k - g) (S : Set ℕ) := by
  intro k hk k' hk' heq
  have h1 := hS k (mem_coe.mp hk)
  have h2 := hS k' (mem_coe.mp hk')
  have := Nat.le_of_dvd h1.2 h1.1
  have := Nat.le_of_dvd h2.2 h2.1
  simp only at heq
  omega

end

theorem criterion : ∀ a b c d : ℕ, 0 < a → a < b → b < c → c < d →
    ¬ a ∣ b → ¬ a ∣ c → ¬ a ∣ d → ¬ b ∣ c → ¬ b ∣ d → ¬ c ∣ d →
    ∀ n : ℕ, d ≤ n →
    n / a + n / b + n / c + n / d + 4 ≤
      2 * ((Finset.Icc 1 n).filter (fun k => ∃ x ∈ ({a, b, c, d} : Finset ℕ), x ∣ k)).card := by
  intro a b c d ha hab hbc hcd hnab hnac hnad hnbc hnbd hncd n hdn
  have hfilt : (Finset.Icc 1 n).filter (fun k => ∃ x ∈ ({a, b, c, d} : Finset ℕ), x ∣ k) =
      (Icc 1 n).filter (fun k => a ∣ k ∨ b ∣ k ∨ c ∣ k ∨ d ∣ k) := by
    apply filter_congr
    intro k _
    simp [mem_insert, mem_singleton, or_and_right, exists_or]
  rw [hfilt]
  have hid := sum_identity (a := a) (b := b) (c := c) (d := d) (n := n)
  set S1 := (Icc 1 n).filter (fun k => dg a b c d k = 1) with hS1
  set S3 := (Icc 1 n).filter (fun k => dg a b c d k = 3) with hS3
  set S4 := (Icc 1 n).filter (fun k => dg a b c d k = 4) with hS4
  set G : Finset ℕ := {a, b, c, d} with hG
  set I3 := S3.image (φ a b c d) with hI3
  set Ia := S4.image (fun k => k - a) with hIa
  set Ib := S4.image (fun k => k - b) with hIb
  have hS4' : ∀ k ∈ S4, (a ∣ k ∧ b ∣ k ∧ c ∣ k ∧ d ∣ k) ∧ 1 ≤ k := by
    intro k hk
    rw [hS4, mem_filter, mem_Icc] at hk
    exact ⟨dg4 hk.2, hk.1.1⟩
  have hsub : G ∪ I3 ∪ Ia ∪ Ib ⊆ S1 := by
    intro x hx
    rcases mem_union.mp hx with hx | hx
    · rcases mem_union.mp hx with hx | hx
      · rcases mem_union.mp hx with hx | hx
        · exact abcd_subset ha hab hbc hcd hnab hnac hnad hnbc hnbd hncd hdn hx
        · obtain ⟨k, hk, rfl⟩ := mem_image.mp hx
          exact (phi_mem ha hab hbc hcd hnab hnac hnad hnbc hnbd hk).1
      · obtain ⟨k, hk, rfl⟩ := mem_image.mp hx
        exact (psi_a_mem ha hab hbc hcd hnab hk).1
    · obtain ⟨k, hk, rfl⟩ := mem_image.mp hx
      exact (psi_b_mem ha hab hbc hcd hnab hnbc hk).1
  -- pairwise disjointness
  have hGI3 : Disjoint G I3 := by
    rw [disjoint_right]
    intro x hx hxG
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hx
    exact (phi_mem ha hab hbc hcd hnab hnac hnad hnbc hnbd hk).2.1 hxG
  have hGIa : Disjoint G Ia := by
    rw [disjoint_right]
    intro x hx hxG
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hx
    exact (psi_a_mem ha hab hbc hcd hnab hk).2.1 hxG
  have hGIb : Disjoint G Ib := by
    rw [disjoint_right]
    intro x hx hxG
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hx
    exact (psi_b_mem ha hab hbc hcd hnab hnbc hk).2.1 hxG
  have hI3Ia : Disjoint I3 Ia := by
    rw [disjoint_left]
    intro x hx hx'
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hx
    obtain ⟨k', hk', heq⟩ := mem_image.mp hx'
    have hm := phi_mem ha hab hbc hcd hnab hnac hnad hnbc hnbd hk
    have hm' := psi_a_mem ha hab hbc hcd hnab hk'
    have hdg1 : dg a b c d (φ a b c d k) = 1 := (mem_filter.mp hm.1).2
    obtain ⟨⟨hak', hbk', hck', hdk'⟩, hk1'⟩ := hS4' k' hk'
    rw [hS3, mem_filter, mem_Icc] at hk
    obtain ⟨⟨hk1, hkn⟩, hk3⟩ := hk
    by_cases hak : a ∣ k
    · have h2 : 2 * a ≤ k := by
        rcases dg3_a hk3 hak with ⟨hb, -, -⟩ | ⟨hb, -, -⟩ | ⟨-, hc, -⟩
        · exact two_mul_le ha hab hak hb hk1
        · exact two_mul_le ha hab hak hb hk1
        · exact two_mul_le ha (by omega) hak hc hk1
      have hcommon : ∃ e, a < e ∧ e ∣ k ∧ e ∣ k' := by
        rcases dg3_a hk3 hak with ⟨hb, -, -⟩ | ⟨hb, -, -⟩ | ⟨-, hc, -⟩
        · exact ⟨b, hab, hb, hbk'⟩
        · exact ⟨b, hab, hb, hbk'⟩
        · exact ⟨c, by omega, hc, hck'⟩
      obtain ⟨e, hae, hek, hek'⟩ := hcommon
      have hak'le : a ≤ k' := Nat.le_of_dvd hk1' hak'
      unfold φ at heq
      rw [if_pos hak] at heq
      split_ifs at heq with hb1
      · have : k = k' + a := by omega
        exact absurd (dvd_of_shift hek' hek this) (not_dvd_of_lt ha hae)
      · have : k = k' := by omega
        subst this
        rw [hS4, mem_filter] at hk'
        omega
    · exact dg1_ab hdg1 (heq ▸ hm'.2.2) (hm.2.2.2 hak)
  have hI3Ib : Disjoint I3 Ib := by
    rw [disjoint_left]
    intro x hx hx'
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hx
    obtain ⟨k', hk', heq⟩ := mem_image.mp hx'
    have hm := phi_mem ha hab hbc hcd hnab hnac hnad hnbc hnbd hk
    have hm' := psi_b_mem ha hab hbc hcd hnab hnbc hk'
    have hdg1 : dg a b c d (φ a b c d k) = 1 := (mem_filter.mp hm.1).2
    obtain ⟨⟨hak', hbk', hck', hdk'⟩, hk1'⟩ := hS4' k' hk'
    rw [hS3, mem_filter, mem_Icc] at hk
    obtain ⟨⟨hk1, hkn⟩, hk3⟩ := hk
    by_cases hak : a ∣ k
    · exact dg1_ab hdg1 (hm.2.2.1 hak) (heq ▸ hm'.2.2)
    · obtain ⟨hb, hc, hd⟩ := dg3_na hk3 hak
      have h2 : 2 * b ≤ k := two_mul_le (by omega) hbc hb hc hk1
      have hbk'le : b ≤ k' := Nat.le_of_dvd hk1' hbk'
      unfold φ at heq
      rw [if_neg hak] at heq
      split_ifs at heq with hb1
      · have : k = k' + b := by omega
        exact absurd (dvd_of_shift hck' hc this) (not_dvd_of_lt (by omega) hbc)
      · have : k = k' := by omega
        subst this
        rw [hS4, mem_filter] at hk'
        omega
  have hIaIb : Disjoint Ia Ib := by
    rw [disjoint_left]
    intro x hx hx'
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hx
    obtain ⟨k', hk', heq⟩ := mem_image.mp hx'
    have hm := psi_a_mem ha hab hbc hcd hnab hk
    have hm' := psi_b_mem ha hab hbc hcd hnab hnbc hk'
    have hdg1 : dg a b c d (k - a) = 1 := (mem_filter.mp hm.1).2
    exact dg1_ab hdg1 hm.2.2 (heq ▸ hm'.2.2)
  have hcardG : G.card = 4 := by
    rw [hG, card_insert_of_notMem, card_insert_of_notMem, card_insert_of_notMem, card_singleton]
    · simp only [mem_singleton]; omega
    · simp only [mem_insert, mem_singleton, not_or]; omega
    · simp only [mem_insert, mem_singleton, not_or]; omega
  have hcardI3 : I3.card = S3.card :=
    card_image_of_injOn (phi_injOn ha hab hbc hcd hnab hnac hnad hnbc hnbd)
  have hcardIa : Ia.card = S4.card :=
    card_image_of_injOn (sub_injOn a S4 (fun k hk => ⟨(hS4' k hk).1.1, (hS4' k hk).2⟩))
  have hcardIb : Ib.card = S4.card :=
    card_image_of_injOn (sub_injOn b S4
      (fun k hk => ⟨(hS4' k hk).1.2.1, (hS4' k hk).2⟩))
  have hunion : (G ∪ I3 ∪ Ia ∪ Ib).card = 4 + S3.card + S4.card + S4.card := by
    rw [card_union_of_disjoint, card_union_of_disjoint, card_union_of_disjoint hGI3,
      hcardG, hcardI3, hcardIa, hcardIb]
    · exact disjoint_union_left.mpr ⟨hGIa, hI3Ia⟩
    · exact disjoint_union_left.mpr ⟨disjoint_union_left.mpr ⟨hGIb, hI3Ib⟩, hIaIb⟩
  have hle : 4 + S3.card + S4.card + S4.card ≤ S1.card := hunion ▸ card_le_card hsub
  omega

lemma card_le_four (a b c d x : ℕ) :
    ((Icc 1 x).filter (fun k => ∃ y ∈ ({a, b, c, d} : Finset ℕ), y ∣ k)).card ≤
      x / a + x / b + x / c + x / d := by
  have hfilt : (Icc 1 x).filter (fun k => ∃ y ∈ ({a, b, c, d} : Finset ℕ), y ∣ k) =
      (Icc 1 x).filter (fun k => a ∣ k) ∪ (Icc 1 x).filter (fun k => b ∣ k) ∪
        (Icc 1 x).filter (fun k => c ∣ k) ∪ (Icc 1 x).filter (fun k => d ∣ k) := by
    rw [← filter_or, ← filter_or, ← filter_or]
    apply filter_congr
    intro k _
    simp [mem_insert, mem_singleton, or_and_right, exists_or, or_assoc]
  rw [hfilt, ← card_mult a x, ← card_mult b x, ← card_mult c x, ← card_mult d x]
  exact le_trans (card_union_le _ _) (Nat.add_le_add_right
    (le_trans (card_union_le _ _) (Nat.add_le_add_right (card_union_le _ _) _)) _)

lemma cross (n m x : ℕ) (hx : 0 < x) (hm : 0 < m) : n * (m / x) < m * (n / x + 1) := by
  have h1 : x * (n * (m / x)) ≤ n * m := by
    rw [mul_left_comm]
    exact Nat.mul_le_mul_left n (Nat.mul_div_le m x)
  have h2 : n * m < x * (m * (n / x + 1)) := by
    rw [mul_left_comm, mul_comm n m]
    exact Nat.mul_lt_mul_of_pos_left (Nat.lt_mul_div_succ n hx) hm
  exact Nat.lt_of_mul_lt_mul_left (lt_of_le_of_lt h1 h2)

theorem proof : ∀ a b c d : ℕ, 0 < a → a < b → b < c → c < d →
    ¬ a ∣ b → ¬ a ∣ c → ¬ a ∣ d → ¬ b ∣ c → ¬ b ∣ d → ¬ c ∣ d →
    ∀ n m : ℕ, d ≤ n → n < m →
    n * ((Finset.Icc 1 m).filter (fun k => ∃ x ∈ ({a, b, c, d} : Finset ℕ), x ∣ k)).card <
      2 * m * ((Finset.Icc 1 n).filter (fun k => ∃ x ∈ ({a, b, c, d} : Finset ℕ), x ∣ k)).card := by
  intro a b c d ha hab hbc hcd hnab hnac hnad hnbc hnbd hncd n m hdn hnm
  have hcrit := criterion a b c d ha hab hbc hcd hnab hnac hnad hnbc hnbd hncd n hdn
  have hMm := card_le_four a b c d m
  set Mm := ((Finset.Icc 1 m).filter (fun k => ∃ x ∈ ({a, b, c, d} : Finset ℕ), x ∣ k)).card
  set Mn := ((Finset.Icc 1 n).filter (fun k => ∃ x ∈ ({a, b, c, d} : Finset ℕ), x ∣ k)).card
  have hm : 0 < m := by omega
  have h1 : n * Mm ≤ n * (m / a + m / b + m / c + m / d) := Nat.mul_le_mul_left n hMm
  have ha' := cross n m a ha hm
  have hb' := cross n m b (by omega) hm
  have hc' := cross n m c (by omega) hm
  have hd' := cross n m d (by omega) hm
  have h2 : m * (n / a + n / b + n / c + n / d + 4) ≤ m * (2 * Mn) := Nat.mul_le_mul_left m hcrit
  nlinarith [h1, ha', hb', hc', hd', h2]

end Submissions.ErdosMultiplesDoublingFour.ViaCriterion
