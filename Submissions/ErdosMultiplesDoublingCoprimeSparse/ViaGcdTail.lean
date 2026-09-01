import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
Erdős #488 for pairwise coprime `A` with `min A > 2(|A|-1)`, via the gcd-weighted tail condition `∑_{b ∈ A, b > a} gcd(a,b)/b < 1/2` (all `a ∈ A`).

Write `M_A(x) = #{k ≤ x : ∃ a ∈ A, a ∣ k}`. Peeling off the least element `a` of `A = {a} ∪ s`:

  `M_A(n) = M_s(n) + #{t ≤ n/a : no b ∈ s divides a t}`,

and `b ∣ a t ↔ (b / gcd(a,b)) ∣ t`, so the number of `t ≤ X := n/a` that *are* hit is at most
`∑_{b ∈ s} X / (b / gcd(a,b)) ≤ X · ∑_{b ∈ s} gcd(a,b)/b < X/2`. Hence the new term contributes
at least `(X+1)/2`, i.e. `2 M_A(n) ≥ 2 M_s(n) + n/a + 1`. Induction on `|A|` (least element
first) gives the order-slack criterion

  `∑_{a ∈ A} n/a + |A| ≤ 2 M_A(n)`      for all `n ≥ max A`,

and the doubling inequality follows from the union bound `M_A(m) ≤ ∑ m/a` together with the
strict floor inequality `n · (m/a) < m · (n/a + 1)`.

For pairwise coprime `A` with every element `> 2(|A|-1)` the tail condition is automatic: each
`gcd(a,b)/b = 1/b ≤ 1/(2(|A|-1)+1)` and there are at most `|A|-1` tail terms.
-/

namespace Submissions.ErdosMultiplesDoublingCoprimeSparse.ViaGcdTail

open Finset

/-- `M_A(x) = #{k ∈ [1,x] : ∃ a ∈ A, a ∣ k}`. -/
abbrev M (A : Finset ℕ) (x : ℕ) : ℕ := ((Icc 1 x).filter (fun k => ∃ a ∈ A, a ∣ k)).card

lemma card_mult (a x : ℕ) : ((Icc 1 x).filter (fun k => a ∣ k)).card = x / a := by
  have : (Icc 1 x) = Ioc 0 x := by
    have h := Icc_add_one_left_eq_Ioc (0 : ℕ) x
    simpa using h
  rw [this, Nat.Ioc_filter_dvd_card_eq_div]

lemma filter_biUnion (A : Finset ℕ) (x : ℕ) :
    (Icc 1 x).filter (fun k => ∃ a ∈ A, a ∣ k) =
      A.biUnion (fun a => (Icc 1 x).filter (fun k => a ∣ k)) := by
  ext k
  simp only [mem_filter, mem_biUnion]
  constructor
  · rintro ⟨hk, a, ha, hd⟩
    exact ⟨a, ha, hk, hd⟩
  · rintro ⟨a, ha, hk, hd⟩
    exact ⟨hk, a, ha, hd⟩

lemma union_bound (A : Finset ℕ) (x : ℕ) : M A x ≤ ∑ a ∈ A, x / a := by
  unfold M
  rw [filter_biUnion]
  refine card_biUnion_le.trans (le_of_eq ?_)
  exact sum_congr rfl (fun a _ => card_mult a x)

/-- `b ∣ a * t ↔ b / gcd a b ∣ t` for positive `a`. -/
lemma dvd_mul_iff_div_gcd {a b : ℕ} (ha : 0 < a) (t : ℕ) :
    b ∣ a * t ↔ b / Nat.gcd a b ∣ t := by
  set g := Nat.gcd a b with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left b ha
  obtain ⟨a', ha'⟩ : g ∣ a := Nat.gcd_dvd_left a b
  obtain ⟨b', hb'⟩ : g ∣ b := Nat.gcd_dvd_right a b
  have hcop : Nat.Coprime b' a' := by
    have h := Nat.coprime_div_gcd_div_gcd (m := b) (n := a) (by rw [Nat.gcd_comm]; exact hgpos)
    rw [Nat.gcd_comm, ← hg] at h
    have e1 : b / g = b' := by rw [hb', Nat.mul_div_cancel_left _ hgpos]
    have e2 : a / g = a' := by rw [ha', Nat.mul_div_cancel_left _ hgpos]
    rwa [e1, e2] at h
  have e1 : b / g = b' := by rw [hb', Nat.mul_div_cancel_left _ hgpos]
  rw [e1]
  constructor
  · intro h
    rw [hb', ha', mul_assoc] at h
    have h' : b' ∣ a' * t := (Nat.mul_dvd_mul_iff_left hgpos).mp h
    exact (Nat.Coprime.dvd_mul_left hcop).mp h'
  · intro h
    rw [hb', ha', mul_assoc]
    exact Nat.mul_dvd_mul_left g (Dvd.dvd.mul_left h a')

/-- Peeling off `a`: `M (insert a s) n = M s n + #{t ≤ n/a : ¬ ∃ b ∈ s, b ∣ a t}`. -/
lemma M_insert {a : ℕ} (ha : 0 < a) (s : Finset ℕ) (n : ℕ) :
    M (insert a s) n = M s n +
      ((Icc 1 (n / a)).filter (fun t => ¬ ∃ b ∈ s, b ∣ a * t)).card := by
  unfold M
  have hsplit : (Icc 1 n).filter (fun k => ∃ x ∈ insert a s, x ∣ k) =
      (Icc 1 n).filter (fun k => ∃ x ∈ s, x ∣ k) ∪
        (Icc 1 n).filter (fun k => a ∣ k ∧ ¬ ∃ x ∈ s, x ∣ k) := by
    ext k
    simp only [mem_filter, mem_union, mem_insert]
    constructor
    · rintro ⟨hk, x, hx | hx, hd⟩
      · by_cases h : ∃ x ∈ s, x ∣ k
        · exact Or.inl ⟨hk, h⟩
        · exact Or.inr ⟨hk, hx ▸ hd, h⟩
      · exact Or.inl ⟨hk, x, hx, hd⟩
    · rintro (⟨hk, x, hx, hd⟩ | ⟨hk, hd, _⟩)
      · exact ⟨hk, x, Or.inr hx, hd⟩
      · exact ⟨hk, a, Or.inl rfl, hd⟩
  have hdisj : Disjoint ((Icc 1 n).filter (fun k => ∃ x ∈ s, x ∣ k))
      ((Icc 1 n).filter (fun k => a ∣ k ∧ ¬ ∃ x ∈ s, x ∣ k)) := by
    rw [disjoint_left]
    intro k hk hk'
    simp only [mem_filter] at hk hk'
    exact hk'.2.2 hk.2
  have himg : (Icc 1 n).filter (fun k => a ∣ k ∧ ¬ ∃ x ∈ s, x ∣ k) =
      ((Icc 1 (n / a)).filter (fun t => ¬ ∃ b ∈ s, b ∣ a * t)).image (fun t => a * t) := by
    ext k
    simp only [mem_filter, mem_image, mem_Icc]
    constructor
    · rintro ⟨⟨hk1, hkn⟩, ⟨t, rfl⟩, hns⟩
      refine ⟨t, ⟨⟨?_, ?_⟩, hns⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos t with h | h
        · subst h; omega
        · exact h
      · exact (Nat.le_div_iff_mul_le ha).mpr (by rw [mul_comm]; exact hkn)
    · rintro ⟨t, ⟨⟨ht1, htn⟩, hns⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, ⟨t, rfl⟩, hns⟩
      · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero ha.ne' (by omega))
      · have := (Nat.le_div_iff_mul_le ha).mp htn
        rw [mul_comm] at this
        exact this
  rw [hsplit, card_union_of_disjoint hdisj, himg,
    card_image_of_injective _ (fun x y (h : a * x = a * y) => Nat.eq_of_mul_eq_mul_left ha h)]

/-- The hit count is at most the gcd-weighted union bound, in `ℚ`. -/
lemma hit_bound {a : ℕ} {s : Finset ℕ} (ha : 0 < a) (hs : ∀ b ∈ s, 0 < b) (X : ℕ) :
    ((((Icc 1 X).filter (fun t => ∃ b ∈ s, b ∣ a * t)).card : ℕ) : ℚ) ≤
      (X : ℚ) * ∑ b ∈ s, (Nat.gcd a b : ℚ) / b := by
  have hfilt : (Icc 1 X).filter (fun t => ∃ b ∈ s, b ∣ a * t) =
      s.biUnion (fun b => (Icc 1 X).filter (fun t => b / Nat.gcd a b ∣ t)) := by
    ext t
    simp only [mem_filter, mem_biUnion]
    constructor
    · rintro ⟨ht, b, hb, hd⟩
      exact ⟨b, hb, ht, (dvd_mul_iff_div_gcd ha t).mp hd⟩
    · rintro ⟨b, hb, ht, hd⟩
      exact ⟨ht, b, hb, (dvd_mul_iff_div_gcd ha t).mpr hd⟩
  have h1 : ((Icc 1 X).filter (fun t => ∃ b ∈ s, b ∣ a * t)).card ≤
      ∑ b ∈ s, X / (b / Nat.gcd a b) := by
    rw [hfilt]
    refine card_biUnion_le.trans (le_of_eq ?_)
    exact sum_congr rfl (fun b _ => card_mult _ X)
  have h2 : ((∑ b ∈ s, X / (b / Nat.gcd a b) : ℕ) : ℚ) ≤
      (X : ℚ) * ∑ b ∈ s, (Nat.gcd a b : ℚ) / b := by
    rw [Nat.cast_sum, mul_sum]
    refine sum_le_sum (fun b hbs => ?_)
    have hb := hs b hbs
    have hgpos : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b ha
    have hgdvd : Nat.gcd a b ∣ b := Nat.gcd_dvd_right a b
    have hq : ((b / Nat.gcd a b : ℕ) : ℚ) = (b : ℚ) / (Nat.gcd a b : ℚ) :=
      Nat.cast_div hgdvd (by exact_mod_cast hgpos.ne')
    have hqpos : (0 : ℚ) < (b : ℚ) / (Nat.gcd a b : ℚ) := by positivity
    calc ((X / (b / Nat.gcd a b) : ℕ) : ℚ) ≤ (X : ℚ) / ((b / Nat.gcd a b : ℕ) : ℚ) :=
          Nat.cast_div_le
      _ = (X : ℚ) / ((b : ℚ) / (Nat.gcd a b : ℚ)) := by rw [hq]
      _ = (X : ℚ) * ((Nat.gcd a b : ℚ) / b) := by
          rw [div_div_eq_mul_div, mul_div_assoc]
  have h1' : ((((Icc 1 X).filter (fun t => ∃ b ∈ s, b ∣ a * t)).card : ℕ) : ℚ) ≤
      ((∑ b ∈ s, X / (b / Nat.gcd a b) : ℕ) : ℚ) := by exact_mod_cast h1
  exact h1'.trans h2

/-- Under the tail condition, more than half of `[1, X]` is missed: `X + 1 ≤ 2 · #miss`. -/
lemma tail_sparse {a : ℕ} {s : Finset ℕ} (ha : 0 < a) (hs : ∀ b ∈ s, 0 < b)
    (hsum : (∑ b ∈ s, (Nat.gcd a b : ℚ) / b) < 1 / 2) {X : ℕ} (hX : 1 ≤ X) :
    X + 1 ≤ 2 * ((Icc 1 X).filter (fun t => ¬ ∃ b ∈ s, b ∣ a * t)).card := by
  have hsplit := card_filter_add_card_filter_not (s := Icc 1 X) (fun t => ∃ b ∈ s, b ∣ a * t)
  rw [Nat.card_Icc, Nat.add_sub_cancel] at hsplit
  have hhit := hit_bound ha hs (s := s) X
  have hXq : (0 : ℚ) < X := by exact_mod_cast hX
  have hlt : ((((Icc 1 X).filter (fun t => ∃ b ∈ s, b ∣ a * t)).card : ℕ) : ℚ) * 2 < X := by
    have : (X : ℚ) * ∑ b ∈ s, (Nat.gcd a b : ℚ) / b < (X : ℚ) * (1 / 2) :=
      mul_lt_mul_of_pos_left hsum hXq
    linarith
  have hlt' : ((Icc 1 X).filter (fun t => ∃ b ∈ s, b ∣ a * t)).card * 2 < X := by
    exact_mod_cast hlt
  omega

/-- The order-slack criterion `∑ n/a + |A| ≤ 2 M_A(n)` for all `n ≥ max A`. -/
theorem criterion : ∀ A : Finset ℕ, (∀ a ∈ A, 0 < a) →
    (∀ a ∈ A, (∑ b ∈ A.filter (fun b => a < b), (Nat.gcd a b : ℚ) / b) < 1 / 2) →
    ∀ n : ℕ, (∀ a ∈ A, a ≤ n) → (∑ a ∈ A, n / a) + A.card ≤ 2 * M A n := by
  intro A
  induction A using Finset.induction_on_min with
  | empty => intro _ _ n _; simp
  | insert a s hlt ih =>
    intro hpos hsum n hle
    have has : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have ha : 0 < a := hpos a (mem_insert_self a s)
    have hs_pos : ∀ b ∈ s, 0 < b := fun b hb => hpos b (mem_insert_of_mem hb)
    have hs_sum : ∀ b ∈ s,
        (∑ c ∈ s.filter (fun c => b < c), (Nat.gcd b c : ℚ) / c) < 1 / 2 := by
      intro b hb
      have h := hsum b (mem_insert_of_mem hb)
      rwa [filter_insert, if_neg (not_lt.mpr (hlt b hb).le)] at h
    have ih' := ih hs_pos hs_sum n (fun b hb => hle b (mem_insert_of_mem hb))
    have ha_sum : (∑ b ∈ s, (Nat.gcd a b : ℚ) / b) < 1 / 2 := by
      have h := hsum a (mem_insert_self a s)
      rwa [filter_insert, if_neg (lt_irrefl a), filter_true_of_mem (fun b hb => hlt b hb)] at h
    have hX : 1 ≤ n / a := (Nat.one_le_div_iff ha).mpr (hle a (mem_insert_self a s))
    have hts := tail_sparse ha hs_pos ha_sum hX
    rw [sum_insert has, card_insert_of_notMem has, M_insert ha]
    omega

lemma cross (n m x : ℕ) (hx : 0 < x) (hm : 0 < m) : n * (m / x) < m * (n / x + 1) := by
  have h1 : x * (n * (m / x)) ≤ n * m := by
    rw [mul_left_comm]
    exact Nat.mul_le_mul_left n (Nat.mul_div_le m x)
  have h2 : n * m < x * (m * (n / x + 1)) := by
    rw [mul_left_comm, mul_comm n m]
    exact Nat.mul_lt_mul_of_pos_left (Nat.lt_mul_div_succ n hx) hm
  exact Nat.lt_of_mul_lt_mul_left (lt_of_le_of_lt h1 h2)

theorem gcdTail : ∀ A : Finset ℕ, A.Nonempty → 0 ∉ A →
    (∀ a ∈ A, (∑ b ∈ A.filter (fun b => a < b), (Nat.gcd a b : ℚ) / b) < 1 / 2) →
    ∀ n m : ℕ, (∀ a ∈ A, a ≤ n) → n < m →
    n * ((Finset.Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k)).card <
      2 * m * ((Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card := by
  intro A hne h0 hsum n m hle hnm
  have hpos : ∀ a ∈ A, 0 < a := fun a ha => Nat.pos_of_ne_zero (fun h => h0 (h ▸ ha))
  have hcrit := criterion A hpos hsum n hle
  have hMm : M A m ≤ ∑ a ∈ A, m / a := union_bound A m
  have hm : 0 < m := by omega
  have hcross : ∑ a ∈ A, n * (m / a) < ∑ a ∈ A, m * (n / a + 1) :=
    sum_lt_sum_of_nonempty hne (fun a ha => cross n m a (hpos a ha) hm)
  have hsum' : ∑ a ∈ A, m * (n / a + 1) = m * ((∑ a ∈ A, n / a) + A.card) := by
    rw [← mul_sum, sum_add_distrib, sum_const, smul_eq_mul, mul_one]
  change n * M A m < 2 * m * M A n
  calc n * M A m ≤ n * ∑ a ∈ A, m / a := Nat.mul_le_mul_left n hMm
    _ = ∑ a ∈ A, n * (m / a) := mul_sum _ _ _
    _ < ∑ a ∈ A, m * (n / a + 1) := hcross
    _ = m * ((∑ a ∈ A, n / a) + A.card) := hsum'
    _ ≤ m * (2 * M A n) := Nat.mul_le_mul_left m hcrit
    _ = 2 * m * M A n := by ring



lemma tail_lt_half (A : Finset ℕ)
    (hcop : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → Nat.Coprime a b)
    (hmin : ∀ a ∈ A, 2 * (A.card - 1) < a) {a : ℕ} (ha : a ∈ A) :
    (∑ b ∈ A.filter (fun b => a < b), (Nat.gcd a b : ℚ) / b) < 1 / 2 := by
  set r : ℕ := A.card - 1 with hr
  set T := A.filter (fun b => a < b) with hT
  have hTcard : T.card ≤ r := by
    have hsub : T ⊂ A := by
      refine Finset.filter_ssubset.mpr ⟨a, ha, lt_irrefl a⟩
    have := card_lt_card hsub
    omega
  have hterm : ∀ b ∈ T, (Nat.gcd a b : ℚ) / b ≤ 1 / ((2 * r + 1 : ℕ) : ℚ) := by
    intro b hb
    rw [hT, mem_filter] at hb
    obtain ⟨hbA, hab⟩ := hb
    have hg : Nat.gcd a b = 1 := hcop a ha b hbA (ne_of_lt hab)
    rw [hg, Nat.cast_one]
    have hb' : 2 * r + 1 ≤ b := by have := hmin a ha; omega
    have hpos : (0 : ℚ) < ((2 * r + 1 : ℕ) : ℚ) := by positivity
    exact one_div_le_one_div_of_le hpos (by exact_mod_cast hb')
  calc (∑ b ∈ T, (Nat.gcd a b : ℚ) / b)
      ≤ ∑ _b ∈ T, (1 : ℚ) / ((2 * r + 1 : ℕ) : ℚ) := sum_le_sum hterm
    _ = (T.card : ℚ) * (1 / ((2 * r + 1 : ℕ) : ℚ)) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (r : ℚ) * (1 / ((2 * r + 1 : ℕ) : ℚ)) := by
        gcongr
    _ < 1 / 2 := by
        have hpos : (0 : ℚ) < ((2 * r + 1 : ℕ) : ℚ) := by positivity
        rw [mul_one_div, div_lt_iff₀ hpos]
        push_cast
        linarith

theorem proof : ∀ A : Finset ℕ, A.Nonempty → 0 ∉ A →
    (∀ a ∈ A, ∀ b ∈ A, a ≠ b → Nat.Coprime a b) →
    (∀ a ∈ A, 2 * (A.card - 1) < a) →
    ∀ n m : ℕ, (∀ a ∈ A, a ≤ n) → n < m →
    n * ((Finset.Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k)).card <
      2 * m * ((Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card := by
  intro A hne h0 hcop hmin
  exact gcdTail A hne h0 (fun a ha => tail_lt_half A hcop hmin ha)

end Submissions.ErdosMultiplesDoublingCoprimeSparse.ViaGcdTail
