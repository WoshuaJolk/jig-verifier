import Mathlib

/- Consolidated from F061.PositiveSieveProduct. -/

open Filter
open scoped Topology BigOperators

/-- A summable sequence of numbers in `[0,1)` has finite products
`∏_{n<N}(1-x_n)` eventually bounded below by a fixed positive constant. -/
theorem eventually_pos_le_prod_one_sub_of_summable
    (x : ℕ → ℝ) (hs : Summable x)
    (hx0 : ∀ n, 0 ≤ x n) (hx1 : ∀ n, x n < 1) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ᶠ N : ℕ in atTop, ρ ≤ ∏ n ∈ Finset.range N, (1 - x n) := by
  let f : ℕ → ℝ := fun n => -x n
  have hnorm : Summable (fun n => ‖f n‖) := by
    have h := hs.norm
    apply h.congr
    intro n
    simp only [f, norm_neg, Real.norm_eq_abs, abs_of_nonneg (hx0 n)]
  have hmult : Multipliable (fun n => 1 + f n) :=
    multipliable_one_add_of_summable hnorm
  have hne : ∀ n, 1 + f n ≠ 0 := by
    intro n
    dsimp [f]
    linarith [hx1 n]
  have htne : (∏' n : ℕ, (1 + f n)) ≠ 0 :=
    tprod_one_add_ne_zero_of_summable hne hnorm
  have htend : Tendsto (fun N => ∏ n ∈ Finset.range N, (1 + f n))
      atTop (𝓝 (∏' n : ℕ, (1 + f n))) :=
    hmult.hasProd.tendsto_prod_nat
  have hprod0 : ∀ N, 0 ≤ ∏ n ∈ Finset.range N, (1 + f n) := by
    intro N
    apply Finset.prod_nonneg
    intro n hn
    dsimp [f]
    linarith [hx1 n]
  have ht0 : 0 ≤ ∏' n : ℕ, (1 + f n) :=
    ge_of_tendsto htend (Filter.Eventually.of_forall hprod0)
  have htpos : 0 < ∏' n : ℕ, (1 + f n) := lt_of_le_of_ne ht0 (Ne.symm htne)
  let ρ : ℝ := (∏' n : ℕ, (1 + f n)) / 2
  refine ⟨ρ, by dsimp [ρ]; positivity, ?_⟩
  have hρlt : ρ < ∏' n : ℕ, (1 + f n) := by
    dsimp [ρ]
    linarith
  have hev : ∀ᶠ N : ℕ in atTop,
      ρ < ∏ n ∈ Finset.range N, (1 + f n) :=
    (tendsto_order.1 htend).1 ρ hρlt
  filter_upwards [hev] with N hN
  have heq : (∏ n ∈ Finset.range N, (1 + f n)) =
      ∏ n ∈ Finset.range N, (1 - x n) := by
    apply Finset.prod_congr rfl
    intro n hn
    simp [f, sub_eq_add_neg]
  rw [← heq]
  exact hN.le

/-- Reciprocal specialization used for divisor sieves. -/
theorem eventually_pos_le_reciprocal_sieve_product
    (a : ℕ → ℕ) (ha2 : ∀ n, 2 ≤ a n)
    (hs : Summable fun n => ((a n : ℝ)⁻¹)) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ᶠ N : ℕ in atTop,
        ρ ≤ ∏ n ∈ Finset.range N, (1 - (a n : ℝ)⁻¹) := by
  apply eventually_pos_le_prod_one_sub_of_summable
    (fun n => ((a n : ℝ)⁻¹)) hs
  · intro n
    positivity
  · intro n
    have ha : (1 : ℝ) < a n := by exact_mod_cast ha2 n
    exact inv_lt_one_of_one_lt₀ ha

/- Consolidated from F061.ParameterSelection. -/

/-- Mertens-free parameter selection for the affine progression argument.
The factorial progression modulus contains every small prime; choosing `C`
by an Archimedean ceiling preserves the cancellation of its square in the
coprime-pair error. -/
theorem exists_affine_sieve_parameters
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ Y Q C : ℕ,
      0 < Y ∧ 1 < Q ∧ 0 < C ∧
      (∀ p, Nat.Prime p → p ≤ Y → p ∣ Q) ∧
      (4 : ℝ) / (C : ℝ) ≤ ρ / (2 * (Q : ℝ)) ∧
      64 * C ^ 2 ≤ Q ^ 2 * Y := by
  obtain ⟨y, hy⟩ := exists_nat_ge (10000 / ρ ^ 2)
  let Y := max 2 y
  let Q := Y.factorial
  let C := ⌈(8 * (Q : ℝ)) / ρ⌉₊
  have hY2 : 2 ≤ Y := le_max_left 2 y
  have hY : 0 < Y := by omega
  have hQ : 1 < Q := by
    dsimp [Q]
    exact Nat.one_lt_factorial.mpr (by omega)
  have hQ0 : 0 < Q := hQ.trans' Nat.zero_lt_one
  have hYn : 10000 / ρ ^ 2 ≤ (Y : ℝ) := by
    exact hy.trans (by exact_mod_cast le_max_right 2 y)
  have hx0 : 0 ≤ (8 * (Q : ℝ)) / ρ := by positivity
  have hxpos : 0 < (8 * (Q : ℝ)) / ρ := by positivity
  have hceilLower : (8 * (Q : ℝ)) / ρ ≤ (C : ℝ) := by
    dsimp [C]
    exact Nat.le_ceil _
  have hC : 0 < C := by
    have hCR : (0 : ℝ) < C := hxpos.trans_le hceilLower
    exact_mod_cast hCR
  have hCposR : (0 : ℝ) < C := by exact_mod_cast hC
  have hsmall : ∀ p, Nat.Prime p → p ≤ Y → p ∣ Q := by
    intro p hp hpY
    dsimp [Q]
    exact Nat.dvd_factorial hp.pos hpY
  have hdensity : (4 : ℝ) / (C : ℝ) ≤ ρ / (2 * (Q : ℝ)) := by
    rw [div_le_div_iff₀ hCposR (by positivity : (0 : ℝ) < 2 * Q)]
    have hc := (div_le_iff₀ hρ).mp hceilLower
    nlinarith
  have hceilUpper : (C : ℝ) < (8 * (Q : ℝ)) / ρ + 1 := by
    dsimp [C]
    exact Nat.ceil_lt_add_one hx0
  have hρQ : ρ ≤ (Q : ℝ) := by
    have hQone : (1 : ℝ) ≤ Q := by exact_mod_cast (show 1 ≤ Q by omega)
    exact hρ1.trans hQone
  have hone : (1 : ℝ) ≤ (Q : ℝ) / ρ :=
    (le_div_iff₀ hρ).2 (by simpa using hρQ)
  have hCupperDiv : (C : ℝ) ≤ 10 * (Q : ℝ) / ρ := by
    have h8 : (8 * (Q : ℝ)) / ρ = 8 * ((Q : ℝ) / ρ) := by ring
    have h10 : (10 * (Q : ℝ)) / ρ = 10 * ((Q : ℝ) / ρ) := by ring
    rw [h8] at hceilUpper
    rw [h10]
    have hratio0 : 0 ≤ (Q : ℝ) / ρ := by positivity
    linarith
  have hCupper : ρ * (C : ℝ) ≤ 10 * (Q : ℝ) := by
    have := (le_div_iff₀ hρ).mp hCupperDiv
    nlinarith
  have hCupper0 : 0 ≤ ρ * (C : ℝ) := by positivity
  have hQupper0 : 0 ≤ 10 * (Q : ℝ) := by positivity
  have hCsq : ρ ^ 2 * (C : ℝ) ^ 2 ≤ 100 * (Q : ℝ) ^ 2 := by
    have hs := (sq_le_sq₀ hCupper0 hQupper0).2 hCupper
    nlinarith
  have hYrho : (10000 : ℝ) ≤ (Y : ℝ) * ρ ^ 2 := by
    exact (div_le_iff₀ (sq_pos_of_pos hρ)).mp hYn
  have hleft := mul_le_mul_of_nonneg_left hCsq (show (0 : ℝ) ≤ 100 by positivity)
  have hright := mul_le_mul_of_nonneg_right hYrho
    (show (0 : ℝ) ≤ (Q : ℝ) ^ 2 by positivity)
  have hchain : ρ ^ 2 * (100 * (C : ℝ) ^ 2) ≤
      ρ ^ 2 * ((Q : ℝ) ^ 2 * (Y : ℝ)) := by
    calc
      ρ ^ 2 * (100 * (C : ℝ) ^ 2) =
          100 * (ρ ^ 2 * (C : ℝ) ^ 2) := by ring
      _ ≤ 100 * (100 * (Q : ℝ) ^ 2) := hleft
      _ = 10000 * (Q : ℝ) ^ 2 := by ring
      _ ≤ ((Y : ℝ) * ρ ^ 2) * (Q : ℝ) ^ 2 := hright
      _ = ρ ^ 2 * ((Q : ℝ) ^ 2 * (Y : ℝ)) := by ring
  have h100 : 100 * (C : ℝ) ^ 2 ≤ (Q : ℝ) ^ 2 * (Y : ℝ) :=
    le_of_mul_le_mul_left hchain (sq_pos_of_pos hρ)
  have h64R : (64 : ℝ) * (C : ℝ) ^ 2 ≤
      (Q : ℝ) ^ 2 * (Y : ℝ) := by
    have hC2 : (0 : ℝ) ≤ (C : ℝ) ^ 2 := by positivity
    nlinarith
  have h64 : 64 * C ^ 2 ≤ Q ^ 2 * Y := by exact_mod_cast h64R
  exact ⟨Y, Q, C, hY, hQ, hC, hsmall, hdensity, h64⟩

/- Consolidated from F061.TailMass. -/

open Filter
open scoped Topology BigOperators

/-- The shifted tail sum of a summable real sequence tends to zero. -/
theorem tendsto_tsum_nat_add_zero
    (f : ℕ → ℝ) (hf : Summable f) :
    Tendsto (fun R : ℕ => ∑' n : ℕ, f (n + R)) atTop (𝓝 0) := by
  have hpartial := hf.tendsto_sum_tsum_nat
  have hsub : Tendsto
      (fun R : ℕ => (∑' n, f n) - ∑ n ∈ Finset.range R, f n)
      atTop (𝓝 ((∑' n, f n) - ∑' n, f n)) :=
    tendsto_const_nhds.sub hpartial
  have heq : ∀ R : ℕ,
      (∑' n : ℕ, f (n + R)) =
        (∑' n, f n) - ∑ n ∈ Finset.range R, f n := by
    intro R
    have h := hf.sum_add_tsum_nat_add R
    linarith
  simpa only [heq, sub_self] using hsub

/-- Every finite subset of a sufficiently remote nonnegative summable tail has
small total mass. -/
theorem eventually_finset_tail_sum_le_of_summable
    (f : ℕ → ℝ) (hf : Summable f) (hf0 : ∀ n, 0 ≤ f n)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ R : ℕ in atTop, ∀ T : Finset ℕ,
      (∀ r ∈ T, R ≤ r) → (∑ r ∈ T, f r) ≤ ε := by
  have htend := tendsto_tsum_nat_add_zero f hf
  have hev : ∀ᶠ R : ℕ in atTop, (∑' n : ℕ, f (n + R)) < ε :=
    (tendsto_order.1 htend).2 ε hε
  filter_upwards [hev] with R hR
  intro T hTR
  let U := T.image fun r => r - R
  have hinj : Set.InjOn (fun r => r - R) (T : Set ℕ) := by
    intro r hr s hs hrs
    have hrR := hTR r hr
    have hsR := hTR s hs
    calc
      r = (r - R) + R := (Nat.sub_add_cancel hrR).symm
      _ = (s - R) + R := congrArg (fun n => n + R) hrs
      _ = s := Nat.sub_add_cancel hsR
  have hsum : (∑ n ∈ U, f (n + R)) = ∑ r ∈ T, f r := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Nat.sub_add_cancel (hTR r hr)]
  have hshift : Summable (fun n => f (n + R)) :=
    (summable_nat_add_iff R).2 hf
  have hle : (∑ n ∈ U, f (n + R)) ≤ ∑' n : ℕ, f (n + R) :=
    hshift.sum_le_tsum U (fun n hn => hf0 (n + R))
  rw [hsum] at hle
  exact hle.trans hR.le

/- Consolidated from F061.HeilbronnRohrbach. -/

open scoped BigOperators
open Finset

namespace Erdos489

/-- Number of residues below `N` avoiding every modulus in a list. -/
def avoidCount (l : List ℕ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter fun n => ∀ a ∈ l, ¬ a ∣ n).card

lemma periodic_filter_card_mul (f : ℕ → Prop) [DecidablePred f] {P : ℕ}
    (hf : Function.Periodic f P) (k : ℕ) :
    ((Finset.range (k * P)).filter f).card =
      k * ((Finset.range P).filter f).card := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.succ_mul, Finset.card_filter, Finset.sum_range_add]
      rw [Finset.card_filter] at ih
      rw [ih]
      have hshift : ∀ i, (if f (k * P + i) then 1 else 0) =
          (if f i then 1 else 0) := by
        intro i
        have hi := hf.nat_mul k i
        simp only [Nat.cast_id] at hi
        rw [Nat.add_comm] at hi
        simpa only [hi]
      simp_rw [hshift]
      rw [← Finset.card_filter f (Finset.range P)]
      change k * ((Finset.range P).filter f).card +
          ((Finset.range P).filter f).card =
        (k + 1) * ((Finset.range P).filter f).card
      rw [Nat.add_mul]
      simp

/-- Avoiding a finite list of divisors is periodic with period the product of
that list.  The zero residue is intentionally included. -/
lemma avoidList_periodic (l : List ℕ) :
    Function.Periodic (fun n : ℕ => ∀ a ∈ l, ¬ a ∣ n) l.prod := by
  intro n
  apply propext
  constructor
  · intro hn a ha han
    apply hn a ha
    exact (Nat.dvd_add_iff_left (List.dvd_prod ha)).1 han
  · intro hn a ha han
    apply hn a ha
    exact (Nat.dvd_add_iff_left (List.dvd_prod ha)).2 han

lemma avoidCount_mul_prod (l : List ℕ) (k : ℕ) :
    avoidCount l (k * l.prod) = k * avoidCount l l.prod := by
  exact periodic_filter_card_mul (fun n => ∀ a ∈ l, ¬ a ∣ n)
    (avoidList_periodic l) k

/-- Adding one modulus `a` removes at most one old survivor per old period.
The injection sends an old survivor divisible by `a` to its quotient by `a`. -/
lemma sub_one_mul_avoidCount_le_cons (a : ℕ) (l : List ℕ) (ha : 0 < a) :
    (a - 1) * avoidCount l l.prod ≤ avoidCount (a :: l) (a * l.prod) := by
  let old : Finset ℕ :=
    (Finset.range (a * l.prod)).filter fun n => ∀ c ∈ l, ¬ c ∣ n
  let bad : Finset ℕ := old.filter fun n => a ∣ n
  let base : Finset ℕ :=
    (Finset.range l.prod).filter fun n => ∀ c ∈ l, ¬ c ∣ n
  have hbad : bad.card ≤ base.card := by
    apply Finset.card_le_card_of_injOn (fun n => n / a)
    · intro n hn
      have hnb : n ∈ bad := hn
      obtain ⟨hnold, hna⟩ := Finset.mem_filter.mp hnb
      obtain ⟨hnrange, hnl⟩ := Finset.mem_filter.mp hnold
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr ?_, ?_⟩
      · apply (Nat.div_lt_iff_lt_mul ha).2
        simpa [Nat.mul_comm] using hnrange
      · intro c hc hcd
        apply hnl c hc
        rw [← Nat.div_mul_cancel hna]
        exact dvd_mul_of_dvd_left hcd a
    · intro n hn m hm hnm
      have hnb : n ∈ bad := hn
      have hmb : m ∈ bad := hm
      have hna : a ∣ n := (Finset.mem_filter.mp hnb).2
      have hma : a ∣ m := (Finset.mem_filter.mp hmb).2
      change n / a = m / a at hnm
      calc
        n = n / a * a := (Nat.div_mul_cancel hna).symm
        _ = m / a * a := by rw [hnm]
        _ = m := Nat.div_mul_cancel hma
  have hpartition :
      avoidCount (a :: l) (a * l.prod) + bad.card = old.card := by
    have h := Finset.card_filter_add_card_filter_not
      (s := old) (p := fun n => ¬ a ∣ n)
    have hnew : old.filter (fun n => ¬ a ∣ n) =
        (Finset.range (a * l.prod)).filter
          (fun n => ∀ c ∈ a :: l, ¬ c ∣ n) := by
      ext n
      simp only [old, Finset.mem_filter, Finset.mem_range, List.mem_cons]
      constructor
      · rintro ⟨⟨hn, hl⟩, hna⟩
        exact ⟨hn, fun c hc => hc.elim (fun hca => hca ▸ hna) (hl c)⟩
      · rintro ⟨hn, hall⟩
        exact ⟨⟨hn, fun c hc => hall c (Or.inr hc)⟩,
          hall a (Or.inl rfl)⟩
    have hbad' : old.filter (fun n => ¬ ¬ a ∣ n) = bad := by
      ext n
      simp [bad]
    rw [hbad'] at h
    rw [hnew] at h
    simpa only [avoidCount] using h
  have hold : old.card = a * base.card := by
    simpa only [old, base, avoidCount] using avoidCount_mul_prod l a
  have hbase : base.card = avoidCount l l.prod := by rfl
  rw [hold, hbase] at hpartition
  rw [hbase] at hbad
  have ha_split : a = (a - 1) + 1 := by omega
  have hnum : a * avoidCount l l.prod =
      (a - 1) * avoidCount l l.prod + avoidCount l l.prod := by
    calc
      a * avoidCount l l.prod = ((a - 1) + 1) * avoidCount l l.prod :=
        congrArg (fun z => z * avoidCount l l.prod) ha_split
      _ = (a - 1) * avoidCount l l.prod + avoidCount l l.prod := by
        rw [Nat.add_mul, one_mul]
  rw [hnum] at hpartition
  omega

/-- Finite Heilbronn--Rohrbach product-density inequality, in exact integral
form.  Over the product period, the number of residues avoiding every modulus
is at least the product of the individual survivor counts `a-1`. -/
theorem heilbronn_rohrbach_count (l : List ℕ) (hl : ∀ a ∈ l, 1 < a) :
    (l.map fun a => a - 1).prod ≤ avoidCount l l.prod := by
  induction l with
  | nil => simp [avoidCount]
  | cons a l ih =>
      have ha : 0 < a := (hl a (by simp)).trans' Nat.zero_lt_one
      have htail : ∀ c ∈ l, 1 < c := by
        intro c hc
        exact hl c (by simp [hc])
      have hrec := sub_one_mul_avoidCount_le_cons a l ha
      rw [List.map_cons, List.prod_cons, List.prod_cons]
      exact (Nat.mul_le_mul_left (a - 1) (ih htail)).trans hrec

end Erdos489

/- Consolidated from F061.AffineSieveDensity. -/

open scoped BigOperators

namespace Erdos489

/-- Number of parameters `k<N` for which `Q*k+1` avoids every modulus in `l`. -/
def affineAvoidCount (l : List ℕ) (Q N : ℕ) : ℕ :=
  ((Finset.range N).filter fun k => ∀ a ∈ l, ¬a ∣ Q * k + 1).card

/-- Multiplication by a number coprime to `P`, followed by translation by one,
permutes the residue classes modulo `P`. -/
lemma affine_mod_permutes_range (Q P : ℕ) (hP : 0 < P)
    (hcop : Nat.Coprime Q P) :
    Finset.image (fun k => (Q * k + 1) % P) (Finset.range P) =
      Finset.range P := by
  let f : ℕ → ℕ := fun k => (Q * k + 1) % P
  have hinj : Set.InjOn f (Finset.range P : Set ℕ) := by
    intro x hx y hy hxyf
    have hxP : x < P := Finset.mem_range.mp hx
    have hyP : y < P := Finset.mem_range.mp hy
    change (Q * x + 1) % P = (Q * y + 1) % P at hxyf
    have hmod : Nat.ModEq P (Q * x + 1) (Q * y + 1) := hxyf
    have hmulmod : Nat.ModEq P (Q * x) (Q * y) :=
      Nat.ModEq.add_right_cancel' 1 hmod
    rcases le_total x y with hxy | hyx
    · have hQxy : Q * x ≤ Q * y := Nat.mul_le_mul_left Q hxy
      have hd : P ∣ Q * y - Q * x :=
        (Nat.modEq_iff_dvd' hQxy).mp hmulmod
      rw [← Nat.mul_sub_left_distrib] at hd
      have hPd : P ∣ y - x := hcop.symm.dvd_of_dvd_mul_left hd
      have hdlt : y - x < P := by omega
      have hz := Nat.eq_zero_of_dvd_of_lt hPd hdlt
      omega
    · have hQyx : Q * y ≤ Q * x := Nat.mul_le_mul_left Q hyx
      have hd : P ∣ Q * x - Q * y :=
        (Nat.modEq_iff_dvd' hQyx).mp hmulmod.symm
      rw [← Nat.mul_sub_left_distrib] at hd
      have hPd : P ∣ x - y := hcop.symm.dvd_of_dvd_mul_left hd
      have hdlt : x - y < P := by omega
      have hz := Nat.eq_zero_of_dvd_of_lt hPd hdlt
      omega
  have hsubset : Finset.image f (Finset.range P) ⊆ Finset.range P := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨k, hk, rfl⟩
    exact Finset.mem_range.mpr (Nat.mod_lt _ hP)
  apply Finset.eq_of_subset_of_card_le hsubset
  rw [Finset.card_range, Finset.card_image_iff.mpr hinj, Finset.card_range]

/-- Divisibility by a modulus `a|P` is unchanged on replacing a number by its
remainder modulo `P`. -/
lemma dvd_affine_mod_iff (a Q k P : ℕ) (haP : a ∣ P) :
    a ∣ (Q * k + 1) % P ↔ a ∣ Q * k + 1 := by
  simp only [Nat.dvd_iff_mod_eq_zero]
  rw [Nat.mod_mod_of_dvd _ haP]

/-- The affine map identifies the finite affine sieve with the ordinary sieve
on a full product period. -/
lemma affineAvoidCount_eq_avoidCount (l : List ℕ) (Q : ℕ)
    (hl : ∀ a ∈ l, 0 < a) (hcop : Nat.Coprime Q l.prod) :
    affineAvoidCount l Q l.prod = avoidCount l l.prod := by
  let P := l.prod
  let f : ℕ → ℕ := fun k => (Q * k + 1) % P
  let A : Finset ℕ :=
    (Finset.range P).filter fun k => ∀ a ∈ l, ¬a ∣ Q * k + 1
  let O : Finset ℕ :=
    (Finset.range P).filter fun n => ∀ a ∈ l, ¬a ∣ n
  have hP : 0 < P := List.prod_pos hl
  have hperm : Finset.image f (Finset.range P) = Finset.range P := by
    exact affine_mod_permutes_range Q P hP hcop
  have hpred : ∀ k, (∀ a ∈ l, ¬a ∣ Q * k + 1) ↔
      (∀ a ∈ l, ¬a ∣ f k) := by
    intro k
    constructor
    · intro hk a ha haf
      apply hk a ha
      exact (dvd_affine_mod_iff a Q k P (List.dvd_prod ha)).mp haf
    · intro hk a ha haf
      apply hk a ha
      exact (dvd_affine_mod_iff a Q k P (List.dvd_prod ha)).mpr haf
  have hinj : Set.InjOn f (Finset.range P : Set ℕ) := by
    have hcard := congrArg Finset.card hperm
    exact Finset.card_image_iff.mp (by simpa using hcard)
  have hAO : Finset.image f A = O := by
    apply Finset.Subset.antisymm
    · intro n hn
      rcases Finset.mem_image.mp hn with ⟨k, hkA, rfl⟩
      have hk := Finset.mem_filter.mp hkA
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr (Nat.mod_lt _ hP), (hpred k).mp hk.2⟩
    · intro n hnO
      have hnrange : n ∈ Finset.range P := (Finset.mem_filter.mp hnO).1
      rw [← hperm] at hnrange
      rcases Finset.mem_image.mp hnrange with ⟨k, hk, hkf⟩
      apply Finset.mem_image.mpr
      refine ⟨k, Finset.mem_filter.mpr ⟨hk, ?_⟩, hkf⟩
      exact (hpred k).mpr (hkf ▸ (Finset.mem_filter.mp hnO).2)
  have hcardA : A.card = O.card := by
    rw [← hAO, Finset.card_image_iff.mpr (hinj.mono (Finset.filter_subset _ _))]
  exact hcardA

/-- Affine finite Heilbronn--Rohrbach density.  If `Q` is coprime to every
modulus (equivalently here to their product), then over the product period at
least `∏(a-1)` parameters `k` have `Qk+1` avoiding every modulus. -/
theorem affine_heilbronn_rohrbach_count (l : List ℕ) (Q : ℕ)
    (hl : ∀ a ∈ l, 1 < a) (hcop : Nat.Coprime Q l.prod) :
    (l.map fun a => a - 1).prod ≤ affineAvoidCount l Q l.prod := by
  rw [affineAvoidCount_eq_avoidCount l Q (fun a ha => (hl a ha).trans' Nat.zero_lt_one) hcop]
  exact heilbronn_rohrbach_count l hl

end Erdos489

/- Consolidated from F061.PeriodicIntervalDensity. -/

/-- Every interval of diameter `G` contains at least `G/P-2` disjoint full
copies of each good residue of a predicate with positive period `P`. -/
theorem periodic_interval_count_lower
    (f : ℕ → Prop) [DecidablePred f] (P L G : ℕ) (hP : 0 < P)
    (hf : Function.Periodic f P) :
    (G / P - 2) * ((Finset.range P).filter f).card ≤
      ((Finset.Icc L (L + G)).filter f).card := by
  let S := (Finset.range P).filter f
  let q := G / P - 2
  let D := S ×ˢ Finset.range q
  let F : (ℕ × ℕ) → ℕ := fun z => (L / P + 1 + z.2) * P + z.1
  have hmap : Set.MapsTo F (D : Set (ℕ × ℕ))
      (((Finset.Icc L (L + G)).filter f : Finset ℕ) : Set ℕ) := by
    intro z hz
    have hzD : z ∈ D := hz
    have hzS : z.1 ∈ S := (Finset.mem_product.mp hzD).1
    have hzq : z.2 < q := Finset.mem_range.mp (Finset.mem_product.mp hzD).2
    have hzr : z.1 < P := Finset.mem_range.mp (Finset.mem_filter.mp hzS).1
    have hzf : f z.1 := (Finset.mem_filter.mp hzS).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩
    · have hLlt : L < (L / P + 1) * P := by
        simpa [Nat.mul_comm] using Nat.lt_mul_div_succ L hP
      have hblock : (L / P + 1) * P ≤ (L / P + 1 + z.2) * P :=
        Nat.mul_le_mul_right P (Nat.le_add_right _ _)
      dsimp [F]
      omega
    · have hj : z.2 + 2 ≤ G / P := by omega
      have hmul : (z.2 + 2) * P ≤ G :=
        (Nat.mul_le_mul_right P hj).trans (Nat.div_mul_le_self G P)
      have hbase : (L / P) * P ≤ L := Nat.div_mul_le_self L P
      have hrlt : z.1 < P := hzr
      dsimp [F]
      nlinarith
    · have hper := hf.nat_mul (L / P + 1 + z.2) z.1
      simp only [Nat.cast_id] at hper
      dsimp [F]
      rw [Nat.add_comm]
      exact hper.mpr hzf
  have hinj : Set.InjOn F (D : Set (ℕ × ℕ)) := by
    intro z hz w hw hEq
    have hzD : z ∈ D := hz
    have hwD : w ∈ D := hw
    have hzr : z.1 < P := Finset.mem_range.mp
      (Finset.mem_filter.mp (Finset.mem_product.mp hzD).1).1
    have hwr : w.1 < P := Finset.mem_range.mp
      (Finset.mem_filter.mp (Finset.mem_product.mp hwD).1).1
    have hrem := congrArg (fun n => n % P) hEq
    have hzrem : F z % P = z.1 := by
      dsimp [F]
      simp [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hzr]
    have hwrem : F w % P = w.1 := by
      dsimp [F]
      simp [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hwr]
    rw [hzrem, hwrem] at hrem
    have hfirst : z.1 = w.1 := hrem
    have hmul : (L / P + 1 + z.2) * P =
        (L / P + 1 + w.2) * P := by
      dsimp [F] at hEq
      omega
    have hblock : L / P + 1 + z.2 = L / P + 1 + w.2 :=
      Nat.eq_of_mul_eq_mul_right hP hmul
    apply Prod.ext hfirst
    omega
  have hcard := Finset.card_le_card_of_injOn F hmap hinj
  rw [Finset.card_product, Finset.card_range] at hcard
  simpa [S, q, D, Nat.mul_comm] using hcard

/- Consolidated from F061.AffineCandidateDensity. -/

namespace Erdos489

/-- Integers in the residue class `1 mod Q` which avoid a finite list of
moduli. -/
def affineCandidates (l : List ℕ) (Q : ℕ) (n : ℕ) : Prop :=
  Nat.ModEq Q n 1 ∧ ∀ a ∈ l, ¬a ∣ n

noncomputable instance affineCandidates_decidable (l : List ℕ) (Q : ℕ) :
    DecidablePred (affineCandidates l Q) := Classical.decPred _

/-- The affine candidate predicate has period `Q * ∏l`. -/
theorem affineCandidates_periodic (l : List ℕ) (Q : ℕ) :
    Function.Periodic (affineCandidates l Q) (Q * l.prod) := by
  intro n
  apply propext
  constructor
  · rintro ⟨hmod, hav⟩
    constructor
    · simpa [Nat.ModEq, Nat.add_mod] using hmod
    · intro a ha hadiv
      apply hav a ha
      have haP : a ∣ Q * l.prod := dvd_mul_of_dvd_right (List.dvd_prod ha) Q
      exact (Nat.dvd_add_iff_left haP).1 hadiv
  · rintro ⟨hmod, hav⟩
    constructor
    · simpa [Nat.ModEq, Nat.add_mod] using hmod
    · intro a ha hadiv
      apply hav a ha
      have haP : a ∣ Q * l.prod := dvd_mul_of_dvd_right (List.dvd_prod ha) Q
      exact (Nat.dvd_add_iff_left haP).2 hadiv

/-- One affine parameter `k` gives one candidate integer `Qk+1` in the full
period. -/
theorem affineAvoidCount_le_candidate_period_count
    (l : List ℕ) (Q : ℕ) (hQ : 1 < Q) :
    affineAvoidCount l Q l.prod ≤
      ((Finset.range (Q * l.prod)).filter (affineCandidates l Q)).card := by
  let A : Finset ℕ :=
    (Finset.range l.prod).filter fun k => ∀ a ∈ l, ¬a ∣ Q * k + 1
  let C : Finset ℕ :=
    (Finset.range (Q * l.prod)).filter (affineCandidates l Q)
  let F : ℕ → ℕ := fun k => Q * k + 1
  have hmap : Set.MapsTo F (A : Set ℕ) (C : Set ℕ) := by
    intro k hk
    have hkA : k ∈ A := hk
    have hkr : k < l.prod := Finset.mem_range.mp (Finset.mem_filter.mp hkA).1
    have hkav := (Finset.mem_filter.mp hkA).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_, ⟨?_, hkav⟩⟩
    · dsimp [F]
      have hQ0 : 0 < Q := by omega
      have hle : k + 1 ≤ l.prod := by omega
      have hmul := Nat.mul_le_mul_left Q hle
      nlinarith
    · dsimp [F]
      simp [Nat.ModEq]
  have hinj : Set.InjOn F (A : Set ℕ) := by
    intro x hx y hy hxy
    dsimp [F] at hxy
    have : Q * x = Q * y := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega) this
  have hcard := Finset.card_le_card_of_injOn F hmap hinj
  simpa [affineAvoidCount, A, C] using hcard

/-- Product-density lower bound for affine candidates in one full period. -/
theorem affineCandidates_period_count_lower
    (l : List ℕ) (Q : ℕ) (hQ : 1 < Q)
    (hl : ∀ a ∈ l, 1 < a) (hcop : Nat.Coprime Q l.prod) :
    (l.map fun a => a - 1).prod ≤
      ((Finset.range (Q * l.prod)).filter (affineCandidates l Q)).card := by
  exact (affine_heilbronn_rohrbach_count l Q hl hcop).trans
    (affineAvoidCount_le_candidate_period_count l Q hQ)

/-- Uniform product-density supply in every interval. -/
theorem affineCandidates_interval_count_lower
    (l : List ℕ) (Q L G : ℕ) (hQ : 1 < Q)
    (hl : ∀ a ∈ l, 1 < a) (hcop : Nat.Coprime Q l.prod) :
    (G / (Q * l.prod) - 2) * (l.map fun a => a - 1).prod ≤
      ((Finset.Icc L (L + G)).filter (affineCandidates l Q)).card := by
  have hperiod := periodic_interval_count_lower (affineCandidates l Q)
    (Q * l.prod) L G (Nat.mul_pos (by omega) (List.prod_pos
      (fun a ha => (hl a ha).trans' Nat.zero_lt_one)))
    (affineCandidates_periodic l Q)
  have hone := affineCandidates_period_count_lower l Q hQ hl hcop
  exact (Nat.mul_le_mul_left (G / (Q * l.prod) - 2) hone).trans hperiod

end Erdos489

/- Consolidated from F061.CandidateAvoidance. -/

namespace Erdos489

/-- Keep only those moduli coprime to the progression modulus `Q`. -/
def coprimePart (l : List ℕ) (Q : ℕ) : List ℕ :=
  l.filter fun a => decide (Nat.Coprime Q a)

/-- A number congruent to one modulo `Q` cannot be divisible by a modulus
having a nontrivial common factor with `Q`. -/
theorem not_dvd_of_modEq_one_of_not_coprime
    (Q a n : ℕ) (hmod : Nat.ModEq Q n 1) (hncop : ¬Nat.Coprime Q a) :
    ¬a ∣ n := by
  intro han
  obtain ⟨p, hp, hpQ, hpa⟩ := Nat.Prime.not_coprime_iff_dvd.mp hncop
  have hpn : p ∣ n := hpa.trans han
  have hp1 : p ∣ 1 := (hmod.dvd_iff hpQ).mp hpn
  exact hp.ne_one (Nat.dvd_one.mp hp1)

/-- Affine candidates avoiding the coprime part of a list automatically avoid
the whole list. -/
theorem affineCandidates_coprimePart_avoid_all
    (l : List ℕ) (Q n : ℕ)
    (hn : affineCandidates (coprimePart l Q) Q n) :
    ∀ a ∈ l, ¬a ∣ n := by
  intro a ha
  by_cases hcop : Nat.Coprime Q a
  · apply hn.2 a
    exact List.mem_filter.mpr ⟨ha, decide_eq_true hcop⟩
  · exact not_dvd_of_modEq_one_of_not_coprime Q a n hn.1 hcop

/-- Every element of the filtered list is coprime to `Q`. -/
theorem coprimePart_all_coprime (l : List ℕ) (Q : ℕ) :
    ∀ a ∈ coprimePart l Q, Nat.Coprime Q a := by
  intro a ha
  exact of_decide_eq_true (List.mem_filter.mp ha).2

/-- Consequently `Q` is coprime to the product of the filtered list. -/
theorem coprime_coprimePart_prod (l : List ℕ) (Q : ℕ) :
    Nat.Coprime Q (coprimePart l Q).prod := by
  induction l with
  | nil => simp [coprimePart]
  | cons a l ih =>
      change Nat.Coprime Q
        (List.filter (fun b => decide (Nat.Coprime Q b)) (a :: l)).prod
      change Nat.Coprime Q
        (List.filter (fun b => decide (Nat.Coprime Q b)) l).prod at ih
      rw [List.filter_cons]
      by_cases hcop : Nat.Coprime Q a
      · rw [if_pos (decide_eq_true hcop), List.prod_cons]
        exact hcop.mul_right ih
      · have hd : decide (Nat.Coprime Q a) ≠ true :=
          fun h => hcop (of_decide_eq_true h)
        rw [if_neg hd]
        exact ih

end Erdos489

/- Consolidated from F061.QuantitativeCandidateSupply. -/

open scoped BigOperators

namespace Erdos489

/-- Product density attached to a finite list of divisor moduli. -/
noncomputable def sieveDensity (l : List ℕ) : ℝ :=
  (l.map fun a => 1 - (a : ℝ)⁻¹).prod

lemma sieveFactor_nonneg {a : ℕ} (ha : 2 ≤ a) :
    0 ≤ 1 - (a : ℝ)⁻¹ := by
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast (show 1 ≤ a by omega)
  have hinv := inv_le_one_of_one_le₀ haR
  linarith

lemma sieveFactor_le_one (a : ℕ) : 1 - (a : ℝ)⁻¹ ≤ 1 := by
  have hinv : (0 : ℝ) ≤ (a : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg a)
  linarith

lemma sieveDensity_nonneg (l : List ℕ) (hl : ∀ a ∈ l, 2 ≤ a) :
    0 ≤ sieveDensity l := by
  induction l with
  | nil => simp [sieveDensity]
  | cons a l ih =>
      unfold sieveDensity
      apply mul_nonneg
      · exact sieveFactor_nonneg (hl a (by simp))
      · apply ih
        intro b hb
        exact hl b (by simp [hb])

/-- Deleting factors from a finite sieve can only increase its density. -/
theorem sieveDensity_le_coprimePart
    (l : List ℕ) (Q : ℕ) (hl : ∀ a ∈ l, 2 ≤ a) :
    sieveDensity l ≤ sieveDensity (coprimePart l Q) := by
  induction l with
  | nil => simp [sieveDensity, coprimePart]
  | cons a l ih =>
      have ha : 2 ≤ a := hl a (by simp)
      have htail : ∀ b ∈ l, 2 ≤ b := by
        intro b hb
        exact hl b (by simp [hb])
      have hih := ih htail
      have hfac0 := sieveFactor_nonneg ha
      have hfac1 := sieveFactor_le_one a
      have htail0 : 0 ≤ sieveDensity l := sieveDensity_nonneg l htail
      unfold sieveDensity
      unfold coprimePart
      rw [List.filter_cons]
      by_cases hcop : Nat.Coprime Q a
      · rw [if_pos (decide_eq_true hcop)]
        exact mul_le_mul_of_nonneg_left hih hfac0
      · have hd : decide (Nat.Coprime Q a) ≠ true :=
          fun h => hcop (of_decide_eq_true h)
        rw [if_neg hd]
        exact (mul_le_of_le_one_left htail0 hfac1).trans hih

/-- The integral product used by Heilbronn--Rohrbach divided by the modulus
product is exactly the real sieve density. -/
theorem cast_sub_prod_div_prod_eq_sieveDensity
    (l : List ℕ) (hl : ∀ a ∈ l, 2 ≤ a) :
    (((l.map fun a => a - 1).prod : ℕ) : ℝ) / (l.prod : ℝ) =
      sieveDensity l := by
  induction l with
  | nil => simp [sieveDensity]
  | cons a l ih =>
      have ha : 2 ≤ a := hl a (by simp)
      have htail : ∀ b ∈ l, 2 ≤ b := by
        intro b hb
        exact hl b (by simp [hb])
      have hapos : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
      have hlprodNat : 0 < l.prod := List.prod_pos (fun b hb => by
        have := htail b hb
        omega)
      have hlprod : (0 : ℝ) < l.prod := by exact_mod_cast hlprodNat
      rw [List.map_cons, List.prod_cons, List.prod_cons]
      norm_num only [Nat.cast_mul]
      rw [mul_div_mul_comm, ih htail]
      unfold sieveDensity
      congr 1
      rw [Nat.cast_sub (by omega)]
      field_simp [ne_of_gt hapos] <;> norm_num

/-- A positive lower bound for the full list density is also a cross-multiplied
lower bound for the integral density numerator of its coprime part. -/
theorem density_mul_coprimePart_prod_le_sub_prod
    (l : List ℕ) (Q : ℕ) (hl : ∀ a ∈ l, 2 ≤ a)
    (ρ : ℝ) (hρ : ρ ≤ sieveDensity l) :
    ρ * ((coprimePart l Q).prod : ℝ) ≤
      (((coprimePart l Q).map fun a => a - 1).prod : ℕ) := by
  let c := coprimePart l Q
  have hc : ∀ a ∈ c, 2 ≤ a := by
    intro a ha
    exact hl a (List.mem_of_mem_filter ha)
  have hprodposNat : 0 < c.prod := List.prod_pos (fun a ha => by
    have := hc a ha
    omega)
  have hprodpos : (0 : ℝ) < c.prod := by exact_mod_cast hprodposNat
  have hdens : ρ ≤ sieveDensity c :=
    hρ.trans (sieveDensity_le_coprimePart l Q hl)
  have hid := cast_sub_prod_div_prod_eq_sieveDensity c hc
  rw [← hid] at hdens
  exact (le_div_iff₀ hprodpos).mp hdens

/-- Once an interval contains at least five full candidate periods, a finite
sieve density lower bound `ρ` yields at least `ρ G/(2Q)` affine candidates. -/
theorem affineCandidates_coprimePart_linear_supply
    (l : List ℕ) (Q L G : ℕ) (hQ : 1 < Q)
    (hl : ∀ a ∈ l, 2 ≤ a) (ρ : ℝ) (hρ0 : 0 ≤ ρ)
    (hρ : ρ ≤ sieveDensity l)
    (hG : 5 * (Q * (coprimePart l Q).prod) ≤ G) :
    ρ * (G : ℝ) / (2 * (Q : ℝ)) ≤
      (((Finset.Icc L (L + G)).filter
        (affineCandidates (coprimePart l Q) Q)).card : ℝ) := by
  let c := coprimePart l Q
  let P := c.prod
  let M := Q * P
  let E := (c.map fun a => a - 1).prod
  let q := G / M
  have hc : ∀ a ∈ c, 1 < a := by
    intro a ha
    exact (hl a (List.mem_of_mem_filter ha))
  have hP : 0 < P := by
    dsimp [P]
    exact List.prod_pos (fun a ha => by
      have := hc a ha
      omega)
  have hM : 0 < M := Nat.mul_pos (by omega) hP
  have hbase := affineCandidates_interval_count_lower c Q L G hQ hc
    (by simpa [c] using coprime_coprimePart_prod l Q)
  have hG' : 5 * M ≤ G := by simpa [M, P, c] using hG
  have hq5 : 5 ≤ q := by
    dsimp [q]
    exact (Nat.le_div_iff_mul_le hM).2 hG'
  have hGlt : G < M * (q + 1) := by
    simpa [q] using Nat.lt_mul_div_succ G hM
  have hGbound : (G : ℝ) ≤ 2 * (M : ℝ) * ((q : ℝ) - 2) := by
    have hGltR : (G : ℝ) < ((M * (q + 1) : ℕ) : ℝ) := by exact_mod_cast hGlt
    norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hGltR
    have hqR : (5 : ℝ) ≤ q := by exact_mod_cast hq5
    have hMR : (0 : ℝ) ≤ M := by positivity
    nlinarith
  have hcross := density_mul_coprimePart_prod_le_sub_prod l Q hl ρ hρ
  change ρ * (P : ℝ) ≤ (E : ℕ) at hcross
  have hq2R : (2 : ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
  have hqsub : (0 : ℝ) ≤ (q : ℝ) - 2 := by linarith
  have hfirst := mul_le_mul_of_nonneg_left hGbound
    (show 0 ≤ ρ / (2 * (Q : ℝ)) by positivity)
  have hsecond := mul_le_mul_of_nonneg_right hcross hqsub
  have htarget : ρ * (G : ℝ) / (2 * (Q : ℝ)) ≤
      ((q : ℝ) - 2) * (E : ℝ) := by
    have hQR : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
    dsimp [M] at hfirst
    norm_num only [Nat.cast_mul] at hfirst
    calc
      ρ * (G : ℝ) / (2 * (Q : ℝ)) =
          (ρ / (2 * (Q : ℝ))) * (G : ℝ) := by ring
      _ ≤ (ρ / (2 * (Q : ℝ))) *
          (2 * ((Q : ℝ) * (P : ℝ)) * ((q : ℝ) - 2)) := hfirst
      _ = (ρ * (P : ℝ)) * ((q : ℝ) - 2) := by field_simp <;> ring
      _ ≤ (E : ℝ) * ((q : ℝ) - 2) := hsecond
      _ = ((q : ℝ) - 2) * (E : ℝ) := by ring
  have hbaseR : ((((q - 2) * E : ℕ)) : ℝ) ≤
      (((Finset.Icc L (L + G)).filter
        (affineCandidates c Q)).card : ℝ) := by
    exact_mod_cast (by simpa [q, M, P, E] using hbase)
  norm_num only [Nat.cast_mul, Nat.cast_sub (show 2 ≤ q by omega)] at hbaseR
  exact htarget.trans (by simpa [c] using hbaseR)

end Erdos489

/- Consolidated from F061.SieveParameterBundle. -/

open Filter
open scoped Topology BigOperators

namespace Erdos489

lemma list_range_prod_eq_finset_prod (f : ℕ → ℝ) (R : ℕ) :
    ((List.range R).map f).prod = ∏ n ∈ Finset.range R, f n := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [List.range_succ, List.map_append, List.prod_append,
      Finset.prod_range_succ, ih]
    simp

lemma sieveDensity_map_range (a : ℕ → ℕ) (R : ℕ) :
    sieveDensity ((List.range R).map a) =
      ∏ n ∈ Finset.range R, (1 - (a n : ℝ)⁻¹) := by
  induction R with
  | zero => simp [sieveDensity]
  | succ R ih =>
    rw [List.range_succ, List.map_append, Finset.prod_range_succ]
    simp only [List.map_singleton]
    rw [show sieveDensity (List.map a (List.range R) ++ [a R]) =
      sieveDensity (List.map a (List.range R)) * (1 - (a R : ℝ)⁻¹) by
        simp [sieveDensity]]
    rw [ih]

/-- All fixed parameters needed by the affine-gap argument can be selected
from positivity and reciprocal summability alone. -/
theorem exists_sieve_parameter_bundle
    (a : ℕ → ℕ) (ha2 : ∀ n, 2 ≤ a n)
    (hs : Summable fun n => ((a n : ℝ)⁻¹)) :
    ∃ ρ : ℝ, ∃ Y Q C R : ℕ,
      0 < ρ ∧ ρ ≤ 1 ∧ 0 < Y ∧ 1 < Q ∧ 0 < C ∧
      (∀ p, Nat.Prime p → p ≤ Y → p ∣ Q) ∧
      (4 : ℝ) / (C : ℝ) ≤ ρ / (2 * (Q : ℝ)) ∧
      64 * C ^ 2 ≤ Q ^ 2 * Y ∧
      ρ ≤ sieveDensity ((List.range R).map a) ∧
      (∀ T : Finset ℕ, (∀ r ∈ T, R ≤ r) →
        (∑ r ∈ T, ((a r : ℝ)⁻¹)) ≤ 1 / (C : ℝ)) := by
  obtain ⟨ρ, hρpos, hprod⟩ :=
    eventually_pos_le_reciprocal_sieve_product a ha2 hs
  have hρ1 : ρ ≤ 1 := by
    obtain ⟨N, hN⟩ := hprod.exists
    have hle : (∏ n ∈ Finset.range N, (1 - (a n : ℝ)⁻¹)) ≤ 1 := by
      apply Finset.prod_le_one
      · intro n hn
        exact sieveFactor_nonneg (ha2 n)
      · intro n hn
        exact sieveFactor_le_one (a n)
    exact hN.trans hle
  obtain ⟨Y, Q, C, hY, hQ, hC, hsmall, hdensity, hCY⟩ :=
    exists_affine_sieve_parameters ρ hρpos hρ1
  have htailEv := eventually_finset_tail_sum_le_of_summable
    (fun n => ((a n : ℝ)⁻¹)) hs (fun n => by positivity)
    (1 / (C : ℝ)) (by positivity)
  have hboth : ∀ᶠ R : ℕ in atTop,
      ρ ≤ sieveDensity ((List.range R).map a) ∧
      (∀ T : Finset ℕ, (∀ r ∈ T, R ≤ r) →
        (∑ r ∈ T, ((a r : ℝ)⁻¹)) ≤ 1 / (C : ℝ)) := by
    filter_upwards [hprod, htailEv] with R hRprod hRtail
    exact ⟨by simpa [sieveDensity_map_range] using hRprod, hRtail⟩
  obtain ⟨R, hRdensity, hRtail⟩ := hboth.exists
  exact ⟨ρ, Y, Q, C, R, hρpos, hρ1, hY, hQ, hC, hsmall,
    hdensity, hCY, hRdensity, hRtail⟩

end Erdos489

/- Consolidated from F061.BoundaryInterior. -/

/-- Removing both endpoints from a finite set in `[L,U]` loses at most two
points. -/
theorem interval_interior_card_add_two
    (S : Finset ℕ) (L U : ℕ)
    (hinterval : ∀ n ∈ S, L ≤ n ∧ n ≤ U) :
    S.card ≤ (S.filter fun n => L < n ∧ n < U).card + 2 := by
  let I := S.filter fun n => L < n ∧ n < U
  let E := S.filter fun n => ¬(L < n ∧ n < U)
  have hEsub : E ⊆ {L, U} := by
    intro n hn
    have hnS := (Finset.mem_filter.mp hn).1
    have hnnot := (Finset.mem_filter.mp hn).2
    have hnI := hinterval n hnS
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have hEcard : E.card ≤ 2 := by
    calc
      E.card ≤ ({L, U} : Finset ℕ).card := Finset.card_le_card hEsub
      _ ≤ 2 := by
        simpa using Finset.card_insert_le L ({U} : Finset ℕ)
  have hpart := Finset.card_filter_add_card_filter_not
    (s := S) (fun n => L < n ∧ n < U)
  change (S.filter fun n => L < n ∧ n < U).card + E.card = S.card at hpart
  omega

/-- Real-valued rearrangement used with density bounds. -/
theorem interval_interior_card_cast_lower
    (S : Finset ℕ) (L U : ℕ)
    (hinterval : ∀ n ∈ S, L ≤ n ∧ n ≤ U)
    (D : ℝ) (hdense : D ≤ (S.card : ℝ)) :
    D - 2 ≤ ((S.filter fun n => L < n ∧ n < U).card : ℝ) := by
  have hnat := interval_interior_card_add_two S L U hinterval
  have hcast : (S.card : ℝ) ≤
      ((S.filter fun n => L < n ∧ n < U).card : ℝ) + 2 := by
    exact_mod_cast hnat
  linarith

/- Consolidated from F061.DivisorWitness. -/

/-- A chosen divisor satisfying `p`, defaulting to zero if none exists. -/
noncomputable def divisorWitness (p : ℕ → Prop) (n : ℕ) : ℕ := by
  classical
  exact if h : ∃ a, p a ∧ a ∣ n then Classical.choose h else 0

/-- The rank of the chosen divisor in the increasing enumeration of `p`. -/
noncomputable def divisorWitnessRank (p : ℕ → Prop) [DecidablePred p]
    (n : ℕ) : ℕ :=
  Nat.count p (divisorWitness p n)

theorem divisorWitness_spec (p : ℕ → Prop) (n : ℕ)
    (h : ∃ a, p a ∧ a ∣ n) :
    p (divisorWitness p n) ∧ divisorWitness p n ∣ n := by
  rw [divisorWitness, dif_pos h]
  exact Classical.choose_spec h

/-- Whenever a witness exists, enumerating at its count recovers it exactly. -/
theorem nth_divisorWitnessRank (p : ℕ → Prop) [DecidablePred p]
    (n : ℕ) (h : ∃ a, p a ∧ a ∣ n) :
    Nat.nth p (divisorWitnessRank p n) = divisorWitness p n := by
  exact Nat.nth_count (divisorWitness_spec p n h).1

/-- Hence the modulus at the chosen rank divides the covered integer. -/
theorem nth_divisorWitnessRank_dvd (p : ℕ → Prop) [DecidablePred p]
    (n : ℕ) (h : ∃ a, p a ∧ a ∣ n) :
    Nat.nth p (divisorWitnessRank p n) ∣ n := by
  rw [nth_divisorWitnessRank p n h]
  exact (divisorWitness_spec p n h).2

/-- Avoiding the first `R` enumerated moduli forces the chosen divisor rank to
be at least `R`. -/
theorem le_divisorWitnessRank_of_avoid_prefix
    (p : ℕ → Prop) [DecidablePred p] (n R : ℕ)
    (hcov : ∃ a, p a ∧ a ∣ n)
    (havoid : ∀ a ∈ (List.range R).map (Nat.nth p), ¬a ∣ n) :
    R ≤ divisorWitnessRank p n := by
  by_contra hnot
  have hr : divisorWitnessRank p n < R := by omega
  apply havoid (Nat.nth p (divisorWitnessRank p n))
  · exact List.mem_map.mpr ⟨divisorWitnessRank p n,
      List.mem_range.mpr hr, rfl⟩
  · exact nth_divisorWitnessRank_dvd p n hcov

/- Consolidated from F061.RoughCoprimePairs. -/

open scoped BigOperators

/-- Ordered pairs of distinct elements of `S` which are not coprime. -/
def noncoprimeOrderedPairs (S : Finset ℕ) : Finset (ℕ × ℕ) :=
  (S ×ˢ S).filter fun z => z.1 ≠ z.2 ∧ ¬Nat.Coprime z.1 z.2

/-- Elements of `S` divisible by `d`. -/
def multiplesIn (S : Finset ℕ) (d : ℕ) : Finset ℕ :=
  S.filter fun n => d ∣ n

/-- An interval of diameter `G` contains at most `G / p + 1` multiples of a
positive integer `p`. -/
theorem multiplesIn_interval_card_le
    (S : Finset ℕ) (L G p : ℕ) (hp : 0 < p)
    (hinterval : ∀ n ∈ S, L ≤ n ∧ n ≤ L + G) :
    (multiplesIn S p).card ≤ G / p + 1 := by
  let M := multiplesIn S p
  let f : ℕ → ℕ := fun n => (n - L) / p
  have hinj : Set.InjOn f (M : Set ℕ) := by
    intro x hx y hy heq
    have hxS : x ∈ S := (Finset.mem_filter.mp hx).1
    have hyS : y ∈ S := (Finset.mem_filter.mp hy).1
    have hpx : p ∣ x := (Finset.mem_filter.mp hx).2
    have hpy : p ∣ y := (Finset.mem_filter.mp hy).2
    have hxL := (hinterval x hxS).1
    have hyL := (hinterval y hyS).1
    rcases le_total x y with hxy | hyx
    · have hpdiv : p ∣ y - x := Nat.dvd_sub hpy hpx
      have hxlow : p * ((x - L) / p) ≤ x - L := Nat.mul_div_le _ _
      have hyup : y - L < p * ((y - L) / p + 1) := Nat.lt_mul_div_succ _ hp
      have hdiffshift : (y - L) - (x - L) = y - x := by omega
      have hdiff : y - x < p := by
        dsimp [f] at heq
        rw [← heq, Nat.mul_add] at hyup
        simp only [mul_one] at hyup
        rw [← hdiffshift]
        omega
      have hz : y - x = 0 := Nat.eq_zero_of_dvd_of_lt hpdiv hdiff
      omega
    · exact (by
        apply Eq.symm
        apply Nat.le_antisymm hyx
        have hpdiv : p ∣ x - y := Nat.dvd_sub hpx hpy
        have hylow : p * ((y - L) / p) ≤ y - L := Nat.mul_div_le _ _
        have hxup : x - L < p * ((x - L) / p + 1) := Nat.lt_mul_div_succ _ hp
        have hdiffshift : (x - L) - (y - L) = x - y := by omega
        have hdiff : x - y < p := by
          dsimp [f] at heq
          rw [heq, Nat.mul_add] at hxup
          simp only [mul_one] at hxup
          rw [← hdiffshift]
          omega
        have hz : x - y = 0 := Nat.eq_zero_of_dvd_of_lt hpdiv hdiff
        omega)
  have himage : M.image f ⊆ Finset.range (G / p + 1) := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨n, hn, rfl⟩
    have hnS : n ∈ S := (Finset.mem_filter.mp hn).1
    have hnL := (hinterval n hnS).1
    have hnG := (hinterval n hnS).2
    apply Finset.mem_range.mpr
    dsimp [f]
    have hsub : n - L ≤ G := by omega
    have := (Nat.div_le_div_right hsub : (n - L) / p ≤ G / p)
    omega
  calc
    M.card = (M.image f).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (Finset.range (G / p + 1)).card := Finset.card_le_card himage
    _ = G / p + 1 := Finset.card_range _

/-- If all prime factors of elements of `S` exceed `Y` and `S` has diameter at
most `G`, every noncoprime distinct pair is covered by a prime `p` in `(Y,G]`.
Consequently any bounds on the number of multiples of each such prime give a
union-bound estimate for the number of bad ordered pairs. -/
theorem noncoprimeOrderedPairs_card_le_primeFiber_sum
    (S : Finset ℕ) (Y G : ℕ) (cap : ℕ → ℕ)
    (hrough : ∀ n ∈ S, ∀ p, Nat.Prime p → p ∣ n → Y < p)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, Nat.dist x y ≤ G)
    (hcap : ∀ p ∈ (G + 1).primesBelow \ (Y + 1).primesBelow,
      (multiplesIn S p).card ≤ cap p) :
    (noncoprimeOrderedPairs S).card ≤
      ∑ p ∈ (G + 1).primesBelow \ (Y + 1).primesBelow, (cap p) ^ 2 := by
  let P := (G + 1).primesBelow \ (Y + 1).primesBelow
  let U : Finset (ℕ × ℕ) := P.biUnion fun p => multiplesIn S p ×ˢ multiplesIn S p
  have hcover : noncoprimeOrderedPairs S ⊆ U := by
    intro z hz
    rcases z with ⟨x, y⟩
    have hz' := Finset.mem_filter.mp hz
    have hxS : x ∈ S := (Finset.mem_product.mp hz'.1).1
    have hyS : y ∈ S := (Finset.mem_product.mp hz'.1).2
    have hxy : x ≠ y := hz'.2.1
    have hgcd1 : Nat.gcd x y ≠ 1 := by
      exact fun h => hz'.2.2 (Nat.coprime_iff_gcd_eq_one.mpr h)
    let p := (Nat.gcd x y).minFac
    have hpprime : Nat.Prime p := Nat.minFac_prime hgcd1
    have hpdvdgcd : p ∣ Nat.gcd x y := Nat.minFac_dvd _
    have hpdx : p ∣ x := hpdvdgcd.trans (Nat.gcd_dvd_left x y)
    have hpdy : p ∣ y := hpdvdgcd.trans (Nat.gcd_dvd_right x y)
    have hpY : Y < p := hrough x hxS p hpprime hpdx
    have hpdist : p ∣ Nat.dist x y := by
      rcases le_total x y with hle | hle
      · rw [Nat.dist_eq_sub_of_le hle]
        exact Nat.dvd_sub hpdy hpdx
      · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hle]
        exact Nat.dvd_sub hpdx hpdy
    have hdistpos : 0 < Nat.dist x y := Nat.dist_pos_of_ne hxy
    have hpG : p ≤ G := (Nat.le_of_dvd hdistpos hpdist).trans (hdiam x hxS y hyS)
    have hpP : p ∈ P := by
      apply Finset.mem_sdiff.mpr
      constructor
      · exact Nat.mem_primesBelow.mpr ⟨by omega, hpprime⟩
      · intro hp
        have hplt := (Nat.mem_primesBelow.mp hp).1
        omega
    apply Finset.mem_biUnion.mpr
    refine ⟨p, hpP, ?_⟩
    apply Finset.mem_product.mpr
    constructor
    · exact Finset.mem_filter.mpr ⟨hxS, hpdx⟩
    · exact Finset.mem_filter.mpr ⟨hyS, hpdy⟩
  calc
    (noncoprimeOrderedPairs S).card ≤ U.card := Finset.card_le_card hcover
    _ ≤ ∑ p ∈ P, (multiplesIn S p ×ˢ multiplesIn S p).card :=
      Finset.card_biUnion_le
    _ = ∑ p ∈ P, ((multiplesIn S p).card) ^ 2 := by
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.card_product, pow_two]
    _ ≤ ∑ p ∈ P, (cap p) ^ 2 := by
      apply Finset.sum_le_sum
      intro p hp
      exact Nat.pow_le_pow_left (hcap p hp) 2

/-- Direct interval form of the rough-pair union bound. -/
theorem noncoprimeOrderedPairs_card_le_interval_prime_sum
    (S : Finset ℕ) (L G Y : ℕ)
    (hinterval : ∀ n ∈ S, L ≤ n ∧ n ≤ L + G)
    (hrough : ∀ n ∈ S, ∀ p, Nat.Prime p → p ∣ n → Y < p) :
    (noncoprimeOrderedPairs S).card ≤
      ∑ p ∈ (G + 1).primesBelow \ (Y + 1).primesBelow, (G / p + 1) ^ 2 := by
  apply noncoprimeOrderedPairs_card_le_primeFiber_sum S Y G
    (fun p => G / p + 1) hrough
  · intro x hx y hy
    have hxI := hinterval x hx
    have hyI := hinterval y hy
    rcases le_total x y with hxy | hyx
    · rw [Nat.dist_eq_sub_of_le hxy]
      omega
    · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hyx]
      omega
  · intro p hp
    have hpprime := (Nat.mem_primesBelow.mp (Finset.mem_sdiff.mp hp).1).2
    exact multiplesIn_interval_card_le S L G p hpprime.pos hinterval

/-- A positive integral ray contains at most one primitive lattice point. -/
theorem nat_pair_eq_of_proportional_of_coprime
    (x₁ y₁ x₂ y₂ : ℕ)
    (hprop : x₁ * y₂ = y₁ * x₂)
    (hc₁ : Nat.Coprime x₁ y₁) (hc₂ : Nat.Coprime x₂ y₂) :
    x₁ = x₂ ∧ y₁ = y₂ := by
  have hx₁x₂ : x₁ ∣ x₂ := by
    apply hc₁.dvd_of_dvd_mul_left
    exact ⟨y₂, hprop.symm⟩
  have hx₂x₁ : x₂ ∣ x₁ := by
    apply hc₂.dvd_of_dvd_mul_left
    refine ⟨y₁, ?_⟩
    calc
      y₂ * x₁ = x₁ * y₂ := mul_comm _ _
      _ = y₁ * x₂ := hprop
      _ = x₂ * y₁ := mul_comm _ _
  have hy₁y₂ : y₁ ∣ y₂ := by
    apply hc₁.symm.dvd_of_dvd_mul_right
    refine ⟨x₂, ?_⟩
    calc
      y₂ * x₁ = x₁ * y₂ := mul_comm _ _
      _ = y₁ * x₂ := hprop
  have hy₂y₁ : y₂ ∣ y₁ := by
    apply hc₂.symm.dvd_of_dvd_mul_right
    refine ⟨x₁, ?_⟩
    calc
      y₁ * x₂ = x₁ * y₂ := hprop.symm
      _ = y₂ * x₁ := mul_comm _ _
  exact ⟨Nat.dvd_antisymm hx₁x₂ hx₂x₁, Nat.dvd_antisymm hy₁y₂ hy₂y₁⟩

/- Consolidated from F061.DistinctWitnesses. -/

open scoped BigOperators

/-- Points in a short interval labelled by divisors force many distinct labels,
unless those labels carry large reciprocal mass. -/
theorem interval_label_card_le_reciprocal_mass
    (S : Finset ℕ) (L G : ℕ) (a label : ℕ → ℕ)
    (ha : ∀ r, 0 < a r)
    (hinterval : ∀ n ∈ S, L ≤ n ∧ n ≤ L + G)
    (hdiv : ∀ n ∈ S, a (label n) ∣ n) :
    (S.card : ℝ) ≤
      (G : ℝ) * (∑ r ∈ S.image label, (a r : ℝ)⁻¹) +
        ((S.image label).card : ℝ) := by
  let T := S.image label
  have hmaps : Set.MapsTo label (S : Set ℕ) (T : Set ℕ) := by
    intro n hn
    exact Finset.mem_image.mpr ⟨n, hn, rfl⟩
  have hfiber : ∀ r ∈ T,
      ((S.filter fun n => label n = r).card : ℝ) ≤
        (G : ℝ) * (a r : ℝ)⁻¹ + 1 := by
    intro r hr
    have hsubset : (S.filter fun n => label n = r) ⊆ multiplesIn S (a r) := by
      intro n hn
      have hnS := (Finset.mem_filter.mp hn).1
      have hnr := (Finset.mem_filter.mp hn).2
      apply Finset.mem_filter.mpr
      exact ⟨hnS, hnr ▸ hdiv n hnS⟩
    have hnat : (S.filter fun n => label n = r).card ≤ G / a r + 1 :=
      (Finset.card_le_card hsubset).trans
        (multiplesIn_interval_card_le S L G (a r) (ha r) hinterval)
    have hcast : (((S.filter fun n => label n = r).card : ℕ) : ℝ) ≤
        ((G / a r + 1 : ℕ) : ℝ) := by exact_mod_cast hnat
    have hq : ((G / a r : ℕ) : ℝ) ≤ (G : ℝ) / (a r : ℝ) := Nat.cast_div_le
    norm_num only [Nat.cast_add, Nat.cast_one] at hcast
    calc
      ((S.filter fun n => label n = r).card : ℝ) ≤
          (G / a r : ℕ) + 1 := hcast
      _ ≤ (G : ℝ) / (a r : ℝ) + 1 := by linarith
      _ = (G : ℝ) * (a r : ℝ)⁻¹ + 1 := by rw [div_eq_mul_inv]
  have hcard : S.card = ∑ r ∈ T, (S.filter fun n => label n = r).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  rw [hcard]
  norm_num only [Nat.cast_sum]
  calc
    (∑ r ∈ T, ((S.filter fun n => label n = r).card : ℝ)) ≤
        ∑ r ∈ T, ((G : ℝ) * (a r : ℝ)⁻¹ + 1) :=
      Finset.sum_le_sum hfiber
    _ = (G : ℝ) * (∑ r ∈ T, (a r : ℝ)⁻¹) + (T.card : ℝ) := by
      rw [Finset.sum_add_distrib]
      simp [Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]

/-- Rearranged form: if label reciprocal mass is at most `ε`, then the number
of distinct labels is at least `#S-Gε`. -/
theorem image_label_card_lower_of_reciprocal_mass
    (S : Finset ℕ) (L G : ℕ) (a label : ℕ → ℕ)
    (ha : ∀ r, 0 < a r)
    (hinterval : ∀ n ∈ S, L ≤ n ∧ n ≤ L + G)
    (hdiv : ∀ n ∈ S, a (label n) ∣ n)
    (ε : ℝ) (hmass : (∑ r ∈ S.image label, (a r : ℝ)⁻¹) ≤ ε) :
    (S.card : ℝ) - (G : ℝ) * ε ≤ ((S.image label).card : ℝ) := by
  have h := interval_label_card_le_reciprocal_mass
    S L G a label ha hinterval hdiv
  have hG : (0 : ℝ) ≤ G := by positivity
  have hm := mul_le_mul_of_nonneg_left hmass hG
  linarith

/- Consolidated from F061.Representatives. -/

/-- A finite map has a transversal: one representative of every value in its
image, contained in the original set and with injective restricted map. -/
theorem Finset.exists_subset_injOn_card_eq_image
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (f : α → β) :
    ∃ T : Finset α, T ⊆ S ∧ Set.InjOn f (T : Set α) ∧
      T.card = (S.image f).card := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨∅, by simp⟩
  | insert a s ha ih =>
      obtain ⟨T, hTs, hinj, hcard⟩ := ih
      by_cases him : f a ∈ s.image f
      · refine ⟨T, hTs.trans (Finset.subset_insert a s), hinj, ?_⟩
        rw [Finset.image_insert, Finset.card_insert_of_mem him]
        exact hcard
      · refine ⟨insert a T, ?_, ?_, ?_⟩
        · intro y hy
          rcases Finset.mem_insert.mp hy with rfl | hyT
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (hTs hyT)
        · intro y hy z hz heq
          rcases Finset.mem_insert.mp hy with rfl | hyT
          · rcases Finset.mem_insert.mp hz with rfl | hzT
            · rfl
            · exfalso
              apply him
              exact Finset.mem_image.mpr ⟨z, hTs hzT, heq.symm⟩
          · rcases Finset.mem_insert.mp hz with rfl | hzT
            · exfalso
              apply him
              exact Finset.mem_image.mpr ⟨y, hTs hyT, heq⟩
            · exact hinj hyT hzT heq
        · rw [Finset.card_insert_of_notMem]
          · rw [Finset.image_insert, Finset.card_insert_of_notMem him, hcard]
          · intro haT
            exact ha (hTs haT)

/- Consolidated from F061.HighRank. -/

/-- If distinct objects carry distinct nonnegative ranks, at most `t` of them
can have rank below `t`.  Equivalently, all but at most `t` objects have rank
at least `t`. -/
theorem card_le_card_rank_ge_add
    {α : Type*} [DecidableEq α] (s : Finset α) (rank : α → ℕ)
    (hinj : Set.InjOn rank (s : Set α)) (t : ℕ) :
    s.card ≤ (s.filter (fun x => t ≤ rank x)).card + t := by
  classical
  let low : Finset α := s.filter (fun x => rank x < t)
  have hilow : Set.InjOn rank (low : Set α) :=
    hinj.mono (by
      intro x hx
      exact (Finset.mem_filter.mp hx).1)
  have hcardimage : (low.image rank).card = low.card :=
    Finset.card_image_iff.mpr hilow
  have himage : low.image rank ⊆ Finset.range t := by
    intro r hr
    rcases Finset.mem_image.mp hr with ⟨x, hx, rfl⟩
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hx).2
  have hlow : low.card ≤ t := by
    rw [← hcardimage]
    simpa using Finset.card_le_card himage
  have hpart : low.card + (s.filter (fun x => t ≤ rank x)).card = s.card := by
    have h := Finset.card_filter_add_card_filter_not
      (s := s) (fun x => rank x < t)
    simpa [low, Nat.not_lt] using h
  omega

/-- In particular, if there are at least `2t` distinctly ranked objects, at
least `t` of them have rank at least `t`. -/
theorem card_rank_ge_of_twice_le_card
    {α : Type*} [DecidableEq α] (s : Finset α) (rank : α → ℕ)
    (hinj : Set.InjOn rank (s : Set α)) (t : ℕ)
    (hcard : 2 * t ≤ s.card) :
    t ≤ (s.filter (fun x => t ≤ rank x)).card := by
  have h := card_le_card_rank_ge_add s rank hinj t
  omega

/- Consolidated from F061.HighRankRepresentatives. -/

open scoped BigOperators

/-- A dense set of divisor-labelled interval points with small reciprocal mass
has a linearly large transversal carrying high distinct ranks. -/
theorem exists_high_rank_divisor_representatives
    (S : Finset ℕ) (L G C : ℕ) (a label : ℕ → ℕ)
    (hC : 0 < C) (ha : ∀ r, 0 < a r)
    (hinterval : ∀ n ∈ S, L ≤ n ∧ n ≤ L + G)
    (hdiv : ∀ n ∈ S, a (label n) ∣ n)
    (hdense : 4 * (G : ℝ) / (C : ℝ) ≤ (S.card : ℝ))
    (hmass : (∑ r ∈ S.image label, (a r : ℝ)⁻¹) ≤
      1 / (C : ℝ)) :
    ∃ T : Finset ℕ,
      T ⊆ S ∧ Set.InjOn label (T : Set ℕ) ∧
      G / C ≤ T.card ∧ ∀ n ∈ T, G / C ≤ label n := by
  have hbasic := interval_label_card_le_reciprocal_mass
    S L G a label ha hinterval hdiv
  have hG0 : (0 : ℝ) ≤ G := by positivity
  have hmassmul := mul_le_mul_of_nonneg_left hmass hG0
  have hCpos : (0 : ℝ) < C := by exact_mod_cast hC
  have himageR : 3 * (G : ℝ) / (C : ℝ) ≤
      ((S.image label).card : ℝ) := by
    have hrewrite : (G : ℝ) * (1 / (C : ℝ)) = (G : ℝ) / C := by
      simp [div_eq_mul_inv]
    rw [hrewrite] at hmassmul
    ring_nf at hdense hmassmul ⊢
    linarith
  let t := G / C
  have htcast : (t : ℝ) ≤ (G : ℝ) / (C : ℝ) := by
    dsimp [t]
    exact Nat.cast_div_le
  have htwiceR : ((2 * t : ℕ) : ℝ) ≤ ((S.image label).card : ℝ) := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    calc
      2 * (t : ℝ) ≤ 2 * ((G : ℝ) / (C : ℝ)) := by linarith
      _ ≤ 3 * (G : ℝ) / (C : ℝ) := by
        have hratio : 0 ≤ (G : ℝ) / (C : ℝ) := by positivity
        ring_nf
        ring_nf at hratio
        linarith
      _ ≤ ((S.image label).card : ℝ) := himageR
  have htwice : 2 * t ≤ (S.image label).card := by exact_mod_cast htwiceR
  obtain ⟨U, hUS, hinjU, hUcard⟩ :=
    Finset.exists_subset_injOn_card_eq_image S label
  let T := U.filter fun n => t ≤ label n
  have hlarge : t ≤ T.card := by
    apply card_rank_ge_of_twice_le_card U label hinjU t
    rwa [hUcard]
  refine ⟨T, ?_, ?_, hlarge, ?_⟩
  · exact (Finset.filter_subset _ _).trans hUS
  · exact hinjU.mono (by
      intro n hn
      exact (Finset.mem_filter.mp hn).1)
  · intro n hn
    exact (Finset.mem_filter.mp hn).2

/-- Endpoint-robust variant: losing two candidate points still leaves the same
`G/C` high-rank transversal once `G≥2C`. -/
theorem exists_high_rank_divisor_representatives_sub_two
    (S : Finset ℕ) (L G C : ℕ) (a label : ℕ → ℕ)
    (hC : 0 < C) (hGC : 2 * C ≤ G) (ha : ∀ r, 0 < a r)
    (hinterval : ∀ n ∈ S, L ≤ n ∧ n ≤ L + G)
    (hdiv : ∀ n ∈ S, a (label n) ∣ n)
    (hdense : 4 * (G : ℝ) / (C : ℝ) - 2 ≤ (S.card : ℝ))
    (hmass : (∑ r ∈ S.image label, (a r : ℝ)⁻¹) ≤
      1 / (C : ℝ)) :
    ∃ T : Finset ℕ,
      T ⊆ S ∧ Set.InjOn label (T : Set ℕ) ∧
      G / C ≤ T.card ∧ ∀ n ∈ T, G / C ≤ label n := by
  have hbasic := interval_label_card_le_reciprocal_mass
    S L G a label ha hinterval hdiv
  have hmassmul := mul_le_mul_of_nonneg_left hmass
    (show (0 : ℝ) ≤ G by positivity)
  have hrewrite : (G : ℝ) * (1 / (C : ℝ)) = (G : ℝ) / C := by
    simp [div_eq_mul_inv]
  rw [hrewrite] at hmassmul
  have himageR : 3 * (G : ℝ) / (C : ℝ) - 2 ≤
      ((S.image label).card : ℝ) := by
    ring_nf at hdense hmassmul ⊢
    linarith
  let t := G / C
  have htcast : (t : ℝ) ≤ (G : ℝ) / (C : ℝ) := by
    dsimp [t]
    exact Nat.cast_div_le
  have hCposR : (0 : ℝ) < C := by exact_mod_cast hC
  have hratio2 : (2 : ℝ) ≤ (G : ℝ) / (C : ℝ) := by
    apply (le_div_iff₀ hCposR).2
    exact_mod_cast hGC
  have htwiceR : ((2 * t : ℕ) : ℝ) ≤ ((S.image label).card : ℝ) := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    have hratio : 0 ≤ (G : ℝ) / (C : ℝ) := by positivity
    have hmid : 2 * (t : ℝ) ≤
        3 * (G : ℝ) / (C : ℝ) - 2 := by
      ring_nf at htcast hratio2 ⊢
      linarith
    exact hmid.trans himageR
  have htwice : 2 * t ≤ (S.image label).card := by exact_mod_cast htwiceR
  obtain ⟨U, hUS, hinjU, hUcard⟩ :=
    Finset.exists_subset_injOn_card_eq_image S label
  let T := U.filter fun n => t ≤ label n
  have hlarge : t ≤ T.card := by
    apply card_rank_ge_of_twice_le_card U label hinjU t
    rwa [hUcard]
  refine ⟨T, (Finset.filter_subset _ _).trans hUS,
    hinjU.mono (fun n hn => (Finset.mem_filter.mp hn).1), hlarge, ?_⟩
  intro n hn
  exact (Finset.mem_filter.mp hn).2

/- Consolidated from F061.RoughPrimeSum. -/

open scoped BigOperators

/-- The elementary telescoping bound `1/(m+1)^2 ≤ 1/m - 1/(m+1)`. -/
theorem one_div_succ_sq_le_telescope (m : ℕ) (hm : 0 < m) :
    (1 : ℝ) / ((m + 1 : ℕ) : ℝ) ^ 2 ≤
      1 / (m : ℝ) - 1 / ((m + 1 : ℕ) : ℝ) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsR : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  have hid : (1 : ℝ) / (m : ℝ) - 1 / ((m + 1 : ℕ) : ℝ) =
      1 / ((m : ℝ) * ((m + 1 : ℕ) : ℝ)) := by
    field_simp
    norm_num only [Nat.cast_add, Nat.cast_one]
    ring
  rw [hid]
  apply one_div_le_one_div_of_le
  · positivity
  · have hle : (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ m
    have hmul := mul_le_mul_of_nonneg_right hle hsR.le
    simpa [pow_two] using hmul

/-- A finite initial segment of the reciprocal-square tail above `Y` is at
most `1/Y`. -/
theorem sum_range_one_div_add_sq_le (Y N : ℕ) (hY : 0 < Y) :
    (∑ i ∈ Finset.range N, (1 : ℝ) / ((Y + i + 1 : ℕ) : ℝ) ^ 2) ≤
      1 / (Y : ℝ) := by
  let f : ℕ → ℝ := fun i => 1 / ((Y + i : ℕ) : ℝ)
  calc
    (∑ i ∈ Finset.range N, (1 : ℝ) / ((Y + i + 1 : ℕ) : ℝ) ^ 2) ≤
        ∑ i ∈ Finset.range N, (f i - f (i + 1)) := by
      apply Finset.sum_le_sum
      intro i hi
      simpa [f, Nat.add_assoc] using one_div_succ_sq_le_telescope (Y + i) (by omega)
    _ = f 0 - f N := Finset.sum_range_sub' f N
    _ ≤ 1 / (Y : ℝ) := by
      dsimp [f]
      have hnonneg : (0 : ℝ) ≤ 1 / ((Y + N : ℕ) : ℝ) := by positivity
      linarith

/-- The reciprocal-square sum over any finite set of distinct integers in
`(Y,G]` is at most `1/Y`. -/
theorem finset_sum_one_div_sq_le
    (S : Finset ℕ) (Y G : ℕ) (hY : 0 < Y)
    (hlow : ∀ d ∈ S, Y < d) (hupp : ∀ d ∈ S, d ≤ G) :
    (∑ d ∈ S, (1 : ℝ) / (d : ℝ) ^ 2) ≤ 1 / (Y : ℝ) := by
  let shift : ℕ → ℕ := fun d => d - Y - 1
  let g : ℕ → ℝ := fun k => 1 / ((Y + k + 1 : ℕ) : ℝ) ^ 2
  have hinj : Set.InjOn shift (S : Set ℕ) := by
    intro d hd e he hde
    dsimp [shift] at hde
    have hdY := hlow d hd
    have heY := hlow e he
    omega
  have himage : S.image shift ⊆ Finset.range G := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨d, hd, rfl⟩
    apply Finset.mem_range.mpr
    dsimp [shift]
    have hdG := hupp d hd
    have hdY := hlow d hd
    omega
  calc
    (∑ d ∈ S, (1 : ℝ) / (d : ℝ) ^ 2) = ∑ d ∈ S, g (shift d) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdY := hlow d hd
      simp only [g, shift]
      congr 3
      omega
    _ = ∑ k ∈ S.image shift, g k := (Finset.sum_image hinj).symm
    _ ≤ ∑ k ∈ Finset.range G, g k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg himage
      intro k hk hkn
      positivity
    _ ≤ 1 / (Y : ℝ) := by
      exact sum_range_one_div_add_sq_le Y G hY

/-- The prime-fiber capacity sum in F-023 is `O(G^2/Y+G)` with explicit
constants. -/
theorem interval_prime_fiber_square_sum_cast_le
    (Y G : ℕ) (hY : 0 < Y) :
    (∑ p ∈ (G + 1).primesBelow \ (Y + 1).primesBelow,
        (((G / p + 1) ^ 2 : ℕ) : ℝ)) ≤
      2 * (G : ℝ) ^ 2 / (Y : ℝ) + 2 * ((G + 1 : ℕ) : ℝ) := by
  let P := (G + 1).primesBelow \ (Y + 1).primesBelow
  have hpLower : ∀ p ∈ P, Y < p := by
    intro p hp
    have hpG := Finset.mem_sdiff.mp hp
    have hpprime := (Nat.mem_primesBelow.mp hpG.1).2
    by_contra hnot
    have hpY : p < Y + 1 := by omega
    exact hpG.2 (Nat.mem_primesBelow.mpr ⟨hpY, hpprime⟩)
  have hpUpper : ∀ p ∈ P, p ≤ G := by
    intro p hp
    have := (Nat.mem_primesBelow.mp (Finset.mem_sdiff.mp hp).1).1
    omega
  have hrecip : (∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2) ≤ 1 / (Y : ℝ) :=
    finset_sum_one_div_sq_le P Y G hY hpLower hpUpper
  have hterm : ∀ p ∈ P,
      (((G / p + 1) ^ 2 : ℕ) : ℝ) ≤
        2 * (G : ℝ) ^ 2 * ((1 : ℝ) / (p : ℝ) ^ 2) + 2 := by
    intro p hp
    have hpprime := (Nat.mem_primesBelow.mp (Finset.mem_sdiff.mp hp).1).2
    have hpR : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
    have hq : ((G / p : ℕ) : ℝ) ≤ (G : ℝ) / (p : ℝ) := Nat.cast_div_le
    have hq0 : (0 : ℝ) ≤ (G / p : ℕ) := by positivity
    have hratio0 : (0 : ℝ) ≤ (G : ℝ) / (p : ℝ) := by positivity
    have hsq : (((G / p : ℕ) : ℝ)) ^ 2 ≤ ((G : ℝ) / (p : ℝ)) ^ 2 :=
      (sq_le_sq₀ hq0 hratio0).2 hq
    norm_num only [Nat.cast_pow, Nat.cast_add, Nat.cast_one]
    have hbasic : ((((G / p : ℕ) : ℝ)) + 1) ^ 2 ≤
        2 * (((G / p : ℕ) : ℝ)) ^ 2 + 2 := by
      nlinarith [sq_nonneg ((((G / p : ℕ) : ℝ)) - 1)]
    calc
      ((((G / p : ℕ) : ℝ)) + 1) ^ 2 ≤
          2 * (((G / p : ℕ) : ℝ)) ^ 2 + 2 := hbasic
      _ ≤ 2 * ((G : ℝ) / (p : ℝ)) ^ 2 + 2 := by nlinarith
      _ = 2 * (G : ℝ) ^ 2 * ((1 : ℝ) / (p : ℝ) ^ 2) + 2 := by
        field_simp
  have hPsubset : P ⊆ Finset.range (G + 1) := by
    intro p hp
    exact Finset.mem_range.mpr
      (Nat.mem_primesBelow.mp (Finset.mem_sdiff.mp hp).1).1
  have hcardNat : P.card ≤ G + 1 := by
    simpa using Finset.card_le_card hPsubset
  have hcard : (P.card : ℝ) ≤ ((G + 1 : ℕ) : ℝ) := by
    exact_mod_cast hcardNat
  calc
    (∑ p ∈ (G + 1).primesBelow \ (Y + 1).primesBelow,
        (((G / p + 1) ^ 2 : ℕ) : ℝ)) =
        ∑ p ∈ P, (((G / p + 1) ^ 2 : ℕ) : ℝ) := rfl
    _ ≤ ∑ p ∈ P,
        (2 * (G : ℝ) ^ 2 * ((1 : ℝ) / (p : ℝ) ^ 2) + 2) := by
      apply Finset.sum_le_sum
      exact hterm
    _ = 2 * (G : ℝ) ^ 2 *
          (∑ p ∈ P, ((1 : ℝ) / (p : ℝ) ^ 2)) + 2 * (P.card : ℝ) := by
      rw [Finset.sum_add_distrib]
      simp [Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ 2 * (G : ℝ) ^ 2 * (1 / (Y : ℝ)) + 2 * ((G + 1 : ℕ) : ℝ) := by
      have hG0 : 0 ≤ 2 * (G : ℝ) ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hrecip hG0]
    _ = 2 * (G : ℝ) ^ 2 / (Y : ℝ) + 2 * ((G + 1 : ℕ) : ℝ) := by ring

/-- Explicit real bound for the number of ordered noncoprime pairs among rough
points in an interval. -/
theorem noncoprimeOrderedPairs_cast_le_rough_interval
    (S : Finset ℕ) (L G Y : ℕ) (hY : 0 < Y)
    (hinterval : ∀ n ∈ S, L ≤ n ∧ n ≤ L + G)
    (hrough : ∀ n ∈ S, ∀ p, Nat.Prime p → p ∣ n → Y < p) :
    ((noncoprimeOrderedPairs S).card : ℝ) ≤
      2 * (G : ℝ) ^ 2 / (Y : ℝ) + 2 * ((G + 1 : ℕ) : ℝ) := by
  have hnat := noncoprimeOrderedPairs_card_le_interval_prime_sum
    S L G Y hinterval hrough
  have hcast : ((noncoprimeOrderedPairs S).card : ℝ) ≤
      (∑ p ∈ (G + 1).primesBelow \ (Y + 1).primesBelow,
        (((G / p + 1) ^ 2 : ℕ) : ℝ)) := by
    exact_mod_cast hnat
  exact hcast.trans (interval_prime_fiber_square_sum_cast_le Y G hY)

/- Consolidated from F061.ProgressionCoprimePairs. -/

open scoped BigOperators

/-- A finite set in an interval whose pairwise distances are multiples of `d`
has at most `G / d + 1` elements. -/
theorem spaced_interval_card_le
    (S : Finset ℕ) (L G d : ℕ) (hd : 0 < d)
    (hinterval : ∀ n ∈ S, L ≤ n ∧ n ≤ L + G)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, d ∣ Nat.dist x y) :
    S.card ≤ G / d + 1 := by
  let f : ℕ → ℕ := fun n => (n - L) / d
  have hinj : Set.InjOn f (S : Set ℕ) := by
    intro x hx y hy heq
    have hxL := (hinterval x hx).1
    have hyL := (hinterval y hy).1
    rcases le_total x y with hxy | hyx
    · have hddiv : d ∣ y - x := by
        simpa [Nat.dist_eq_sub_of_le hxy] using hsep x hx y hy
      have hxlow : d * ((x - L) / d) ≤ x - L := Nat.mul_div_le _ _
      have hyup : y - L < d * ((y - L) / d + 1) := Nat.lt_mul_div_succ _ hd
      have hdiffshift : (y - L) - (x - L) = y - x := by omega
      have hdiff : y - x < d := by
        dsimp [f] at heq
        rw [← heq, Nat.mul_add] at hyup
        simp only [mul_one] at hyup
        rw [← hdiffshift]
        omega
      have hz : y - x = 0 := Nat.eq_zero_of_dvd_of_lt hddiv hdiff
      omega
    · apply Eq.symm
      apply Nat.le_antisymm hyx
      have hddiv : d ∣ x - y := by
        have hdxy := hsep x hx y hy
        rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hyx] at hdxy
        exact hdxy
      have hylow : d * ((y - L) / d) ≤ y - L := Nat.mul_div_le _ _
      have hxup : x - L < d * ((x - L) / d + 1) := Nat.lt_mul_div_succ _ hd
      have hdiffshift : (x - L) - (y - L) = x - y := by omega
      have hdiff : x - y < d := by
        dsimp [f] at heq
        rw [heq, Nat.mul_add] at hxup
        simp only [mul_one] at hxup
        rw [← hdiffshift]
        omega
      have hz : x - y = 0 := Nat.eq_zero_of_dvd_of_lt hddiv hdiff
      omega
  have himage : S.image f ⊆ Finset.range (G / d + 1) := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨n, hn, rfl⟩
    have hnI := hinterval n hn
    apply Finset.mem_range.mpr
    dsimp [f]
    have hsub : n - L ≤ G := by omega
    have := (Nat.div_le_div_right hsub : (n - L) / d ≤ G / d)
    omega
  calc
    S.card = (S.image f).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (Finset.range (G / d + 1)).card := Finset.card_le_card himage
    _ = G / d + 1 := Finset.card_range _

/-- In one prime fiber of a progression `n ≡ 1 (mod Q)`, the points are
`Qp`-spaced. -/
theorem progression_primeFiber_card_le
    (S : Finset ℕ) (L G Q p : ℕ) (hQ : 0 < Q) (hp : Nat.Prime p)
    (hinterval : ∀ n ∈ S, L ≤ n ∧ n ≤ L + G)
    (hcong : ∀ n ∈ S, Nat.ModEq Q n 1)
    (hpQ : ¬p ∣ Q) :
    (multiplesIn S p).card ≤ G / (Q * p) + 1 := by
  let M := multiplesIn S p
  have hcop : Nat.Coprime Q p :=
    (hp.coprime_iff_not_dvd.mpr hpQ).symm
  apply spaced_interval_card_le M L G (Q * p) (Nat.mul_pos hQ hp.pos)
  · intro n hn
    exact hinterval n (Finset.mem_filter.mp hn).1
  · intro x hx y hy
    have hxS : x ∈ S := (Finset.mem_filter.mp hx).1
    have hyS : y ∈ S := (Finset.mem_filter.mp hy).1
    have hpx : p ∣ x := (Finset.mem_filter.mp hx).2
    have hpy : p ∣ y := (Finset.mem_filter.mp hy).2
    have hQdist : Q ∣ Nat.dist x y := by
      rcases le_total x y with hxy | hyx
      · rw [Nat.dist_eq_sub_of_le hxy]
        apply (Nat.modEq_iff_dvd' hxy).mp
        exact (hcong x hxS).trans (hcong y hyS).symm
      · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hyx]
        apply (Nat.modEq_iff_dvd' hyx).mp
        exact (hcong y hyS).trans (hcong x hxS).symm
    have hpdist : p ∣ Nat.dist x y := by
      rcases le_total x y with hxy | hyx
      · rw [Nat.dist_eq_sub_of_le hxy]
        exact Nat.dvd_sub hpy hpx
      · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hyx]
        exact Nat.dvd_sub hpx hpy
    exact hcop.mul_dvd_of_dvd_of_dvd hQdist hpdist

/-- Prime-fiber union bound for points in `n ≡ 1 (mod Q)`, when every prime
at most `Y` divides `Q`. -/
theorem progression_noncoprimePairs_card_le_prime_sum
    (S : Finset ℕ) (L G Q Y : ℕ) (hQ : 0 < Q)
    (hinterval : ∀ n ∈ S, L ≤ n ∧ n ≤ L + G)
    (hcong : ∀ n ∈ S, Nat.ModEq Q n 1)
    (hsmall : ∀ p, Nat.Prime p → p ≤ Y → p ∣ Q) :
    (noncoprimeOrderedPairs S).card ≤
      ∑ p ∈ (G + 1).primesBelow \ (Y + 1).primesBelow,
        (G / (Q * p) + 1) ^ 2 := by
  apply noncoprimeOrderedPairs_card_le_primeFiber_sum S Y G
    (fun p => G / (Q * p) + 1)
  · intro n hn p hp hpn
    by_contra hnot
    have hpY : p ≤ Y := by omega
    have hpQ : p ∣ Q := hsmall p hp hpY
    have hp1 : p ∣ 1 := ((hcong n hn).dvd_iff hpQ).mp hpn
    exact hp.ne_one (Nat.dvd_one.mp hp1)
  · intro x hx y hy
    have hxI := hinterval x hx
    have hyI := hinterval y hy
    rcases le_total x y with hxy | hyx
    · rw [Nat.dist_eq_sub_of_le hxy]
      omega
    · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hyx]
      omega
  · intro p hpP
    have hp : Nat.Prime p :=
      (Nat.mem_primesBelow.mp (Finset.mem_sdiff.mp hpP).1).2
    by_cases hM : (multiplesIn S p).Nonempty
    · obtain ⟨n, hnM⟩ := hM
      have hnS : n ∈ S := (Finset.mem_filter.mp hnM).1
      have hpn : p ∣ n := (Finset.mem_filter.mp hnM).2
      have hpnotQ : ¬p ∣ Q := by
        intro hpQ
        have hp1 : p ∣ 1 := ((hcong n hnS).dvd_iff hpQ).mp hpn
        exact hp.ne_one (Nat.dvd_one.mp hp1)
      exact progression_primeFiber_card_le S L G Q p hQ hp hinterval hcong hpnotQ
    · rw [Finset.not_nonempty_iff_eq_empty.mp hM]
      simp

/-- The reciprocal-square estimate with a numerator `H` independent of the
upper prime cutoff `G`. -/
theorem prime_fiber_square_sum_num_cast_le
    (H Y G : ℕ) (hY : 0 < Y) :
    (∑ p ∈ (G + 1).primesBelow \ (Y + 1).primesBelow,
        (((H / p + 1) ^ 2 : ℕ) : ℝ)) ≤
      2 * (H : ℝ) ^ 2 / (Y : ℝ) + 2 * ((G + 1 : ℕ) : ℝ) := by
  let P := (G + 1).primesBelow \ (Y + 1).primesBelow
  have hpLower : ∀ p ∈ P, Y < p := by
    intro p hp
    have hpG := Finset.mem_sdiff.mp hp
    have hpprime := (Nat.mem_primesBelow.mp hpG.1).2
    by_contra hnot
    have hpY : p < Y + 1 := by omega
    exact hpG.2 (Nat.mem_primesBelow.mpr ⟨hpY, hpprime⟩)
  have hpUpper : ∀ p ∈ P, p ≤ G := by
    intro p hp
    have := (Nat.mem_primesBelow.mp (Finset.mem_sdiff.mp hp).1).1
    omega
  have hrecip : (∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2) ≤ 1 / (Y : ℝ) :=
    finset_sum_one_div_sq_le P Y G hY hpLower hpUpper
  have hterm : ∀ p ∈ P,
      (((H / p + 1) ^ 2 : ℕ) : ℝ) ≤
        2 * (H : ℝ) ^ 2 * ((1 : ℝ) / (p : ℝ) ^ 2) + 2 := by
    intro p hp
    have hpprime := (Nat.mem_primesBelow.mp (Finset.mem_sdiff.mp hp).1).2
    have hpR : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
    have hq : ((H / p : ℕ) : ℝ) ≤ (H : ℝ) / (p : ℝ) := Nat.cast_div_le
    have hq0 : (0 : ℝ) ≤ (H / p : ℕ) := by positivity
    have hratio0 : (0 : ℝ) ≤ (H : ℝ) / (p : ℝ) := by positivity
    have hsq : (((H / p : ℕ) : ℝ)) ^ 2 ≤ ((H : ℝ) / (p : ℝ)) ^ 2 :=
      (sq_le_sq₀ hq0 hratio0).2 hq
    norm_num only [Nat.cast_pow, Nat.cast_add, Nat.cast_one]
    have hbasic : ((((H / p : ℕ) : ℝ)) + 1) ^ 2 ≤
        2 * (((H / p : ℕ) : ℝ)) ^ 2 + 2 := by
      nlinarith [sq_nonneg ((((H / p : ℕ) : ℝ)) - 1)]
    calc
      ((((H / p : ℕ) : ℝ)) + 1) ^ 2 ≤
          2 * (((H / p : ℕ) : ℝ)) ^ 2 + 2 := hbasic
      _ ≤ 2 * ((H : ℝ) / (p : ℝ)) ^ 2 + 2 := by nlinarith
      _ = 2 * (H : ℝ) ^ 2 * ((1 : ℝ) / (p : ℝ) ^ 2) + 2 := by
        field_simp
  have hPsubset : P ⊆ Finset.range (G + 1) := by
    intro p hp
    exact Finset.mem_range.mpr
      (Nat.mem_primesBelow.mp (Finset.mem_sdiff.mp hp).1).1
  have hcardNat : P.card ≤ G + 1 := by
    simpa using Finset.card_le_card hPsubset
  have hcard : (P.card : ℝ) ≤ ((G + 1 : ℕ) : ℝ) := by
    exact_mod_cast hcardNat
  calc
    (∑ p ∈ (G + 1).primesBelow \ (Y + 1).primesBelow,
        (((H / p + 1) ^ 2 : ℕ) : ℝ)) =
        ∑ p ∈ P, (((H / p + 1) ^ 2 : ℕ) : ℝ) := rfl
    _ ≤ ∑ p ∈ P,
        (2 * (H : ℝ) ^ 2 * ((1 : ℝ) / (p : ℝ) ^ 2) + 2) := by
      apply Finset.sum_le_sum
      exact hterm
    _ = 2 * (H : ℝ) ^ 2 *
          (∑ p ∈ P, ((1 : ℝ) / (p : ℝ) ^ 2)) + 2 * (P.card : ℝ) := by
      rw [Finset.sum_add_distrib]
      simp [Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ 2 * (H : ℝ) ^ 2 * (1 / (Y : ℝ)) +
          2 * ((G + 1 : ℕ) : ℝ) := by
      have hH0 : 0 ≤ 2 * (H : ℝ) ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hrecip hH0]
    _ = 2 * (H : ℝ) ^ 2 / (Y : ℝ) +
          2 * ((G + 1 : ℕ) : ℝ) := by ring

/-- Explicit progression version: ordered noncoprime pairs have quadratic
coefficient at most `2/(Q²Y)`, plus a linear endpoint term. -/
theorem noncoprimeOrderedPairs_cast_le_progression
    (S : Finset ℕ) (L G Q Y : ℕ) (hQ : 0 < Q) (hY : 0 < Y)
    (hinterval : ∀ n ∈ S, L ≤ n ∧ n ≤ L + G)
    (hcong : ∀ n ∈ S, Nat.ModEq Q n 1)
    (hsmall : ∀ p, Nat.Prime p → p ≤ Y → p ∣ Q) :
    ((noncoprimeOrderedPairs S).card : ℝ) ≤
      2 * (G : ℝ) ^ 2 / ((Q : ℝ) ^ 2 * (Y : ℝ)) +
        2 * ((G + 1 : ℕ) : ℝ) := by
  have hnat := progression_noncoprimePairs_card_le_prime_sum
    S L G Q Y hQ hinterval hcong hsmall
  have hcast : ((noncoprimeOrderedPairs S).card : ℝ) ≤
      (∑ p ∈ (G + 1).primesBelow \ (Y + 1).primesBelow,
        ((((G / Q) / p + 1) ^ 2 : ℕ) : ℝ)) := by
    rw [show (∑ p ∈ (G + 1).primesBelow \ (Y + 1).primesBelow,
        ((((G / Q) / p + 1) ^ 2 : ℕ) : ℝ)) =
      (∑ p ∈ (G + 1).primesBelow \ (Y + 1).primesBelow,
        (((G / (Q * p) + 1) ^ 2 : ℕ) : ℝ)) by
          apply Finset.sum_congr rfl
          intro p hp
          rw [Nat.div_div_eq_div_mul]]
    exact_mod_cast hnat
  have hsum := prime_fiber_square_sum_num_cast_le (G / Q) Y G hY
  have hdiv : ((G / Q : ℕ) : ℝ) ≤ (G : ℝ) / (Q : ℝ) := Nat.cast_div_le
  have hdiv0 : (0 : ℝ) ≤ (G / Q : ℕ) := by positivity
  have hratio0 : (0 : ℝ) ≤ (G : ℝ) / (Q : ℝ) := by positivity
  have hsq : ((G / Q : ℕ) : ℝ) ^ 2 ≤ ((G : ℝ) / (Q : ℝ)) ^ 2 :=
    (sq_le_sq₀ hdiv0 hratio0).2 hdiv
  calc
    ((noncoprimeOrderedPairs S).card : ℝ) ≤
        (∑ p ∈ (G + 1).primesBelow \ (Y + 1).primesBelow,
          ((((G / Q) / p + 1) ^ 2 : ℕ) : ℝ)) := hcast
    _ ≤ 2 * ((G / Q : ℕ) : ℝ) ^ 2 / (Y : ℝ) +
          2 * ((G + 1 : ℕ) : ℝ) := hsum
    _ ≤ 2 * ((G : ℝ) / (Q : ℝ)) ^ 2 / (Y : ℝ) +
          2 * ((G + 1 : ℕ) : ℝ) := by
      have hY0 : (0 : ℝ) ≤ (Y : ℝ) := by positivity
      have hnum : 2 * ((G / Q : ℕ) : ℝ) ^ 2 ≤
          2 * ((G : ℝ) / (Q : ℝ)) ^ 2 := by nlinarith
      have hquot := div_le_div_of_nonneg_right hnum hY0
      linarith
    _ = 2 * (G : ℝ) ^ 2 / ((Q : ℝ) ^ 2 * (Y : ℝ)) +
          2 * ((G + 1 : ℕ) : ℝ) := by
      field_simp <;> ring

/- Consolidated from F061.CoprimePairSupply. -/

open scoped BigOperators

/-- Ordered pairs of distinct coprime elements. -/
def coprimeOrderedPairs (S : Finset ℕ) : Finset (ℕ × ℕ) :=
  S.offDiag.filter fun z => Nat.Coprime z.1 z.2

lemma noncoprimeOrderedPairs_eq_offDiag_filter (S : Finset ℕ) :
    noncoprimeOrderedPairs S =
      S.offDiag.filter fun z => ¬Nat.Coprime z.1 z.2 := by
  ext z
  simp only [noncoprimeOrderedPairs, Finset.mem_filter,
    Finset.mem_product, Finset.mem_offDiag]
  tauto

/-- Good and bad ordered pairs partition the off-diagonal. -/
theorem coprime_add_noncoprime_card (S : Finset ℕ) :
    (coprimeOrderedPairs S).card + (noncoprimeOrderedPairs S).card =
      S.card * (S.card - 1) := by
  rw [noncoprimeOrderedPairs_eq_offDiag_filter]
  have h := Finset.card_filter_add_card_filter_not
    (s := S.offDiag) (fun z : ℕ × ℕ => Nat.Coprime z.1 z.2)
  rw [Finset.offDiag_card] at h
  simpa [coprimeOrderedPairs, Nat.mul_sub_left_distrib] using h

/-- If `S` has at least `dG` points and `dG≥2`, then at least
`d²G²/2-B` ordered pairs are coprime whenever at most `B` are bad. -/
theorem coprimeOrderedPairs_cast_lower_of_card
    (S : Finset ℕ) (G : ℕ) (d B : ℝ)
    (hd : 0 ≤ d)
    (hcard : d * (G : ℝ) ≤ (S.card : ℝ))
    (hlarge : 2 ≤ d * (G : ℝ))
    (hbad : ((noncoprimeOrderedPairs S).card : ℝ) ≤ B) :
    d ^ 2 * (G : ℝ) ^ 2 / 2 - B ≤
      ((coprimeOrderedPairs S).card : ℝ) := by
  have hm2 : 2 ≤ S.card := by exact_mod_cast hlarge.trans hcard
  have hpart := coprime_add_noncoprime_card S
  have hpartR : ((coprimeOrderedPairs S).card : ℝ) +
      ((noncoprimeOrderedPairs S).card : ℝ) =
      (S.card : ℝ) * ((S.card : ℝ) - 1) := by
    have hcast := congrArg (fun n : ℕ => (n : ℝ)) hpart
    norm_num only [Nat.cast_add, Nat.cast_mul,
      Nat.cast_sub (show 1 ≤ S.card by omega), Nat.cast_one] at hcast
    exact hcast
  have hm : d * (G : ℝ) ≤ (S.card : ℝ) := hcard
  have hdG : 0 ≤ d * (G : ℝ) := by positivity
  have hm0 : 0 ≤ (S.card : ℝ) := by positivity
  have hquad : d ^ 2 * (G : ℝ) ^ 2 / 2 ≤
      (S.card : ℝ) * ((S.card : ℝ) - 1) := by
    have hsquare : (d * (G : ℝ)) ^ 2 ≤ (S.card : ℝ) ^ 2 :=
      (sq_le_sq₀ hdG hm0).2 hm
    nlinarith
  linarith

/-- Explicit affine-progression corollary: a linearly large set has a
quadratic supply of coprime ordered pairs, up to the `Q,Y` union-bound error. -/
theorem progression_coprimeOrderedPairs_cast_lower
    (S : Finset ℕ) (L G Q Y : ℕ) (d : ℝ)
    (hQ : 0 < Q) (hY : 0 < Y)
    (hinterval : ∀ n ∈ S, L ≤ n ∧ n ≤ L + G)
    (hcong : ∀ n ∈ S, Nat.ModEq Q n 1)
    (hsmall : ∀ p, Nat.Prime p → p ≤ Y → p ∣ Q)
    (hd : 0 ≤ d) (hcard : d * (G : ℝ) ≤ (S.card : ℝ))
    (hlarge : 2 ≤ d * (G : ℝ)) :
    d ^ 2 * (G : ℝ) ^ 2 / 2 -
        (2 * (G : ℝ) ^ 2 / ((Q : ℝ) ^ 2 * (Y : ℝ)) +
          2 * ((G + 1 : ℕ) : ℝ)) ≤
      ((coprimeOrderedPairs S).card : ℝ) := by
  apply coprimeOrderedPairs_cast_lower_of_card S G d _ hd hcard hlarge
  exact noncoprimeOrderedPairs_cast_le_progression
    S L G Q Y hQ hY hinterval hcong hsmall

/- Consolidated from F061.QuantitativeCoprimePairs. -/

/-- A convenient integral form of the progression coprime-pair estimate.  The
loose constants isolate all endpoint losses: once `G ≥ 256 C²` and
`Q²Y ≥ 64 C²`, any `G/C`-point progression set has enough coprime ordered
pairs to pay for `G²` with multiplier `16 C²`. -/
theorem progression_many_coprime_pairs
    (S : Finset ℕ) (L G Q Y C : ℕ)
    (hQ : 0 < Q) (hY : 0 < Y) (hC : 0 < C)
    (hinterval : ∀ n ∈ S, L ≤ n ∧ n ≤ L + G)
    (hcong : ∀ n ∈ S, Nat.ModEq Q n 1)
    (hsmall : ∀ p, Nat.Prime p → p ≤ Y → p ∣ Q)
    (hcard : G / C ≤ S.card)
    (hG : 256 * C ^ 2 ≤ G)
    (hCY : 64 * C ^ 2 ≤ Q ^ 2 * Y) :
    G ^ 2 ≤ 16 * C ^ 2 * (coprimeOrderedPairs S).card := by
  let q := G / C
  let d : ℝ := 1 / (2 * (C : ℝ))
  have hC1 : 1 ≤ C := hC
  have hCG : C ≤ G := by
    calc
      C ≤ 256 * C ^ 2 := by nlinarith
      _ ≤ G := hG
  have hq1 : 1 ≤ q := by
    dsimp [q]
    exact (Nat.le_div_iff_mul_le hC).2 (by simpa using hCG)
  have hGlt : G < C * (q + 1) := by
    simpa [q] using Nat.lt_mul_div_succ G hC
  have hGle2Cq : G ≤ 2 * C * q := by
    have hstep : C * (q + 1) ≤ C * (2 * q) :=
      Nat.mul_le_mul_left C (by omega)
    have := (Nat.le_of_lt hGlt).trans hstep
    nlinarith
  have hCposR : (0 : ℝ) < C := by exact_mod_cast hC
  have hqbound : d * (G : ℝ) ≤ (q : ℝ) := by
    have hcast : (G : ℝ) ≤ ((2 * C * q : ℕ) : ℝ) := by exact_mod_cast hGle2Cq
    norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hcast
    dsimp [d]
    rw [show (1 / (2 * (C : ℝ))) * (G : ℝ) =
      (G : ℝ) / (2 * (C : ℝ)) by ring]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * C)).2
    nlinarith
  have hcardR : (q : ℝ) ≤ (S.card : ℝ) := by
    exact_mod_cast (show q ≤ S.card by simpa [q] using hcard)
  have hdcard : d * (G : ℝ) ≤ (S.card : ℝ) := hqbound.trans hcardR
  have h4C : 4 * C ≤ G := by
    have : 4 * C ≤ 256 * C ^ 2 := by nlinarith
    exact this.trans hG
  have hdlarge : 2 ≤ d * (G : ℝ) := by
    have h4CR : (4 * C : ℕ) ≤ G := h4C
    have hcast : (4 : ℝ) * C ≤ G := by exact_mod_cast h4CR
    dsimp [d]
    rw [show (1 / (2 * (C : ℝ))) * (G : ℝ) =
      (G : ℝ) / (2 * (C : ℝ)) by ring]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * C)).2
    nlinarith
  have hpair := progression_coprimeOrderedPairs_cast_lower
    S L G Q Y d hQ hY hinterval hcong hsmall
    (by dsimp [d]; positivity) hdcard hdlarge
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hYR : (0 : ℝ) < Y := by exact_mod_cast hY
  have hCYR : (64 * C ^ 2 : ℕ) ≤ Q ^ 2 * Y := hCY
  have hCYcast : (64 : ℝ) * (C : ℝ) ^ 2 ≤
      (Q : ℝ) ^ 2 * (Y : ℝ) := by exact_mod_cast hCYR
  have hquadcoeff : (2 : ℝ) / ((Q : ℝ) ^ 2 * (Y : ℝ)) ≤
      1 / (32 * (C : ℝ) ^ 2) := by
    calc
      (2 : ℝ) / ((Q : ℝ) ^ 2 * (Y : ℝ)) ≤
          2 / (64 * (C : ℝ) ^ 2) :=
        div_le_div_of_nonneg_left (by positivity)
          (by positivity) hCYcast
      _ = 1 / (32 * (C : ℝ) ^ 2) := by field_simp <;> ring
  have hquad : 2 * (G : ℝ) ^ 2 /
      ((Q : ℝ) ^ 2 * (Y : ℝ)) ≤
      (G : ℝ) ^ 2 / (32 * (C : ℝ) ^ 2) := by
    have hm := mul_le_mul_of_nonneg_right hquadcoeff
      (sq_nonneg (G : ℝ))
    ring_nf at hm ⊢
    exact hm
  have hGcast : (256 : ℝ) * (C : ℝ) ^ 2 ≤ (G : ℝ) := by
    exact_mod_cast hG
  have hGpos : (0 : ℝ) < G := lt_of_lt_of_le (by positivity) hGcast
  have hend : 2 * ((G + 1 : ℕ) : ℝ) ≤
      (G : ℝ) ^ 2 / (64 * (C : ℝ) ^ 2) := by
    have hsucc : (((G + 1 : ℕ) : ℝ)) ≤ 2 * (G : ℝ) := by
      norm_num only [Nat.cast_add, Nat.cast_one]
      have : (1 : ℝ) ≤ G := by exact_mod_cast (show 1 ≤ G by omega)
      linarith
    have hscaled := mul_le_mul_of_nonneg_right hGcast
      (show (0 : ℝ) ≤ G by positivity)
    have hfour : 4 * (G : ℝ) ≤
        (G : ℝ) ^ 2 / (64 * (C : ℝ) ^ 2) := by
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 64 * C ^ 2)).2
      nlinarith
    linarith
  have hmain : d ^ 2 * (G : ℝ) ^ 2 / 2 =
      (G : ℝ) ^ 2 / (8 * (C : ℝ) ^ 2) := by
    dsimp [d]
    field_simp <;> ring
  have hlower : (G : ℝ) ^ 2 / (16 * (C : ℝ) ^ 2) ≤
      ((coprimeOrderedPairs S).card : ℝ) := by
    rw [hmain] at hpair
    ring_nf at hpair hquad hend ⊢
    linarith
  have hcross : (G : ℝ) ^ 2 ≤
      (16 * (C : ℝ) ^ 2) * ((coprimeOrderedPairs S).card : ℝ) := by
    have h := (div_le_iff₀
      (by positivity : (0 : ℝ) < 16 * C ^ 2)).mp hlower
    simpa [mul_comm] using h
  exact_mod_cast hcross

/- Consolidated from F061.AffineGapWitnesses. -/

open scoped BigOperators

namespace Erdos489

/-- A long covered interval contains many distinctly and highly ranked divisor
witnesses in the fixed affine progression. -/
theorem exists_affine_gap_high_rank_witnesses
    (p : ℕ → Prop) [DecidablePred p] (hp : Set.Infinite {n | p n})
    (hp2 : ∀ n, p n → 2 ≤ n)
    (R Q L G C : ℕ) (ρ : ℝ)
    (hQ : 1 < Q) (hC : 0 < C) (hGC : 2 * C ≤ G)
    (hρ0 : 0 ≤ ρ)
    (hρ : ρ ≤ sieveDensity ((List.range R).map (Nat.nth p)))
    (hdensity : (4 : ℝ) / (C : ℝ) ≤ ρ / (2 * (Q : ℝ)))
    (hperiod : 5 * (Q *
      (coprimePart ((List.range R).map (Nat.nth p)) Q).prod) ≤ G)
    (hcovered : ∀ n, L < n → n < L + G → ∃ a, p a ∧ a ∣ n)
    (htail : ∀ T : Finset ℕ, (∀ r ∈ T, R ≤ r) →
      (∑ r ∈ T, ((Nat.nth p r : ℝ)⁻¹)) ≤ 1 / (C : ℝ)) :
    ∃ T : Finset ℕ,
      (∀ n ∈ T, L < n ∧ n < L + G) ∧
      (∀ n ∈ T, Nat.ModEq Q n 1) ∧
      Set.InjOn (divisorWitnessRank p) (T : Set ℕ) ∧
      G / C ≤ T.card ∧
      (∀ n ∈ T, G / C ≤ divisorWitnessRank p n) ∧
      (∀ n ∈ T, R ≤ divisorWitnessRank p n) ∧
      (∀ n ∈ T, Nat.nth p (divisorWitnessRank p n) ∣ n) := by
  let l := (List.range R).map (Nat.nth p)
  let closed := (Finset.Icc L (L + G)).filter
    (affineCandidates (coprimePart l Q) Q)
  let S := closed.filter fun n => L < n ∧ n < L + G
  let label := divisorWitnessRank p
  let a := Nat.nth p
  have hl : ∀ m ∈ l, 2 ≤ m := by
    intro m hm
    rcases List.mem_map.mp hm with ⟨r, hr, rfl⟩
    exact hp2 _ (Nat.nth_mem_of_infinite hp r)
  have hclosed := affineCandidates_coprimePart_linear_supply
    l Q L G hQ hl ρ hρ0 (by simpa [l] using hρ)
    (by simpa [l] using hperiod)
  have hclosedInterval : ∀ n ∈ closed, L ≤ n ∧ n ≤ L + G := by
    intro n hn
    exact Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
  have hparammul := mul_le_mul_of_nonneg_right hdensity
    (show (0 : ℝ) ≤ G by positivity)
  have hfour : 4 * (G : ℝ) / (C : ℝ) ≤
      ρ * (G : ℝ) / (2 * (Q : ℝ)) := by
    calc
      4 * (G : ℝ) / (C : ℝ) =
          ((4 : ℝ) / (C : ℝ)) * (G : ℝ) := by ring
      _ ≤ (ρ / (2 * (Q : ℝ))) * (G : ℝ) := hparammul
      _ = ρ * (G : ℝ) / (2 * (Q : ℝ)) := by ring
  have hclosedDense : 4 * (G : ℝ) / (C : ℝ) ≤ (closed.card : ℝ) :=
    hfour.trans (by simpa [closed] using hclosed)
  have hSDense : 4 * (G : ℝ) / (C : ℝ) - 2 ≤ (S.card : ℝ) := by
    exact (interval_interior_card_cast_lower closed L (L + G)
      hclosedInterval _ hclosedDense)
  have hSsub : S ⊆ closed := Finset.filter_subset _ _
  have hSinterval : ∀ n ∈ S, L ≤ n ∧ n ≤ L + G := by
    intro n hn
    exact hclosedInterval n (hSsub hn)
  have hSint : ∀ n ∈ S, L < n ∧ n < L + G := by
    intro n hn
    exact (Finset.mem_filter.mp hn).2
  have hScov : ∀ n ∈ S, ∃ m, p m ∧ m ∣ n := by
    intro n hn
    exact hcovered n (hSint n hn).1 (hSint n hn).2
  have hSdiv : ∀ n ∈ S, a (label n) ∣ n := by
    intro n hn
    exact nth_divisorWitnessRank_dvd p n (hScov n hn)
  have hSavoid : ∀ n ∈ S, ∀ m ∈ l, ¬m ∣ n := by
    intro n hn
    have hnclosed := hSsub hn
    have hnaff := (Finset.mem_filter.mp hnclosed).2
    exact affineCandidates_coprimePart_avoid_all l Q n hnaff
  have hSrankR : ∀ n ∈ S, R ≤ label n := by
    intro n hn
    exact le_divisorWitnessRank_of_avoid_prefix p n R (hScov n hn)
      (hSavoid n hn)
  have ha : ∀ r, 0 < a r := by
    intro r
    dsimp [a]
    exact lt_of_lt_of_le (by omega : 0 < 2)
      (hp2 _ (Nat.nth_mem_of_infinite hp r))
  have hmass : (∑ r ∈ S.image label, (a r : ℝ)⁻¹) ≤
      1 / (C : ℝ) := by
    apply htail (S.image label)
    intro r hr
    rcases Finset.mem_image.mp hr with ⟨n, hn, rfl⟩
    exact hSrankR n hn
  obtain ⟨T, hTS, hinj, hcard, hhigh⟩ :=
    exists_high_rank_divisor_representatives_sub_two
      S L G C a label hC hGC ha hSinterval hSdiv hSDense hmass
  refine ⟨T, ?_, ?_, hinj, hcard, hhigh, ?_, ?_⟩
  · intro n hn
    exact hSint n (hTS hn)
  · intro n hn
    have hnclosed := hSsub (hTS hn)
    exact (Finset.mem_filter.mp hnclosed).2.1
  · intro n hn
    exact hSrankR n (hTS hn)
  · intro n hn
    exact hSdiv n (hTS hn)

/-- Adding the rough-prime numerical hypotheses turns the witnesses above into
a full quadratic coprime-pair payment for the gap. -/
theorem exists_affine_gap_coprime_pair_payment
    (p : ℕ → Prop) [DecidablePred p] (hp : Set.Infinite {n | p n})
    (hp2 : ∀ n, p n → 2 ≤ n)
    (R Q L G C Y : ℕ) (ρ : ℝ)
    (hQ : 1 < Q) (hY : 0 < Y) (hC : 0 < C)
    (hρ0 : 0 ≤ ρ)
    (hρ : ρ ≤ sieveDensity ((List.range R).map (Nat.nth p)))
    (hdensity : (4 : ℝ) / (C : ℝ) ≤ ρ / (2 * (Q : ℝ)))
    (hperiod : 5 * (Q *
      (coprimePart ((List.range R).map (Nat.nth p)) Q).prod) ≤ G)
    (hcovered : ∀ n, L < n → n < L + G → ∃ a, p a ∧ a ∣ n)
    (htail : ∀ T : Finset ℕ, (∀ r ∈ T, R ≤ r) →
      (∑ r ∈ T, ((Nat.nth p r : ℝ)⁻¹)) ≤ 1 / (C : ℝ))
    (hsmall : ∀ q, Nat.Prime q → q ≤ Y → q ∣ Q)
    (hG : 256 * C ^ 2 ≤ G) (hCY : 64 * C ^ 2 ≤ Q ^ 2 * Y) :
    ∃ T : Finset ℕ,
      (∀ n ∈ T, L < n ∧ n < L + G) ∧
      Set.InjOn (divisorWitnessRank p) (T : Set ℕ) ∧
      (∀ n ∈ T, G / C ≤ divisorWitnessRank p n) ∧
      (∀ n ∈ T, R ≤ divisorWitnessRank p n) ∧
      (∀ n ∈ T, Nat.nth p (divisorWitnessRank p n) ∣ n) ∧
      G ^ 2 ≤ 16 * C ^ 2 * (coprimeOrderedPairs T).card := by
  have hGC : 2 * C ≤ G := by
    have : 2 * C ≤ 256 * C ^ 2 := by nlinarith
    exact this.trans hG
  obtain ⟨T, hint, hcong, hinj, hcard, hhigh, hR, hdiv⟩ :=
    exists_affine_gap_high_rank_witnesses p hp hp2 R Q L G C ρ
      hQ hC hGC hρ0 hρ hdensity hperiod hcovered htail
  have hinterval : ∀ n ∈ T, L ≤ n ∧ n ≤ L + G := by
    intro n hn
    have := hint n hn
    omega
  have hpay := progression_many_coprime_pairs T L G Q Y C
    (by omega) hY hC hinterval hcong hsmall hcard hG hCY
  exact ⟨T, hint, hinj, hhigh, hR, hdiv, hpay⟩

/-- Strengthened packaging retaining the linear cardinality bound together
with the quadratic coprime-pair payment. -/
theorem exists_affine_gap_full_witness
    (p : ℕ → Prop) [DecidablePred p] (hp : Set.Infinite {n | p n})
    (hp2 : ∀ n, p n → 2 ≤ n)
    (R Q L G C Y : ℕ) (ρ : ℝ)
    (hQ : 1 < Q) (hY : 0 < Y) (hC : 0 < C)
    (hρ0 : 0 ≤ ρ)
    (hρ : ρ ≤ sieveDensity ((List.range R).map (Nat.nth p)))
    (hdensity : (4 : ℝ) / (C : ℝ) ≤ ρ / (2 * (Q : ℝ)))
    (hperiod : 5 * (Q *
      (coprimePart ((List.range R).map (Nat.nth p)) Q).prod) ≤ G)
    (hcovered : ∀ n, L < n → n < L + G → ∃ a, p a ∧ a ∣ n)
    (htail : ∀ T : Finset ℕ, (∀ r ∈ T, R ≤ r) →
      (∑ r ∈ T, ((Nat.nth p r : ℝ)⁻¹)) ≤ 1 / (C : ℝ))
    (hsmall : ∀ q, Nat.Prime q → q ≤ Y → q ∣ Q)
    (hG : 256 * C ^ 2 ≤ G) (hCY : 64 * C ^ 2 ≤ Q ^ 2 * Y) :
    ∃ T : Finset ℕ,
      (∀ n ∈ T, L < n ∧ n < L + G) ∧
      (∀ n ∈ T, Nat.ModEq Q n 1) ∧
      Set.InjOn (divisorWitnessRank p) (T : Set ℕ) ∧
      G / C ≤ T.card ∧
      (∀ n ∈ T, G / C ≤ divisorWitnessRank p n) ∧
      (∀ n ∈ T, R ≤ divisorWitnessRank p n) ∧
      (∀ n ∈ T, Nat.nth p (divisorWitnessRank p n) ∣ n) ∧
      G ^ 2 ≤ 16 * C ^ 2 * (coprimeOrderedPairs T).card := by
  have hGC : 2 * C ≤ G := by
    have : 2 * C ≤ 256 * C ^ 2 := by nlinarith
    exact this.trans hG
  obtain ⟨T, hint, hcong, hinj, hcard, hhigh, hR, hdiv⟩ :=
    exists_affine_gap_high_rank_witnesses p hp hp2 R Q L G C ρ
      hQ hC hGC hρ0 hρ hdensity hperiod hcovered htail
  have hinterval : ∀ n ∈ T, L ≤ n ∧ n ≤ L + G := by
    intro n hn
    have := hint n hn
    omega
  have hpay := progression_many_coprime_pairs T L G Q Y C
    (by omega) hY hC hinterval hcong hsmall hcard hG hCY
  exact ⟨T, hint, hcong, hinj, hcard, hhigh, hR, hdiv, hpay⟩

end Erdos489

/- Consolidated from F061.MaxGapBound. -/

/-- Distinct divisor ranks represented inside a gap are bounded by the
forbidden counting function at the right endpoint. -/
theorem divisor_rank_witness_card_le_count
    (p : ℕ → Prop) [DecidablePred p] (hp : Set.Infinite {n | p n})
    (T : Finset ℕ) (rank : ℕ → ℕ) (U : ℕ)
    (hinj : Set.InjOn rank (T : Set ℕ))
    (hpos : ∀ n ∈ T, 0 < n)
    (hupper : ∀ n ∈ T, n < U)
    (hdiv : ∀ n ∈ T, Nat.nth p (rank n) ∣ n) :
    T.card ≤ Nat.count p U := by
  have hrange : T.image rank ⊆ Finset.range (Nat.count p U) := by
    intro r hr
    rcases Finset.mem_image.mp hr with ⟨n, hn, rfl⟩
    have hmodle : Nat.nth p (rank n) ≤ n :=
      Nat.le_of_dvd (hpos n hn) (hdiv n hn)
    have hnthlt : Nat.nth p (rank n) < U := hmodle.trans_lt (hupper n hn)
    exact Finset.mem_range.mpr ((Nat.lt_nth_iff_count_lt hp).2 hnthlt)
  calc
    T.card = (T.image rank).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (Finset.range (Nat.count p U)).card := Finset.card_le_card hrange
    _ = Nat.count p U := Finset.card_range _

/-- A sufficiently strong linear upper bound on the forbidden count forces all
gaps beginning below `x` to have length at most `x`, once each long gap has
`gap/C` distinct divisor-rank witnesses. -/
theorem eventual_gap_le_prefix
    (p : ℕ → Prop) [DecidablePred p] (hp : Set.Infinite {n | p n})
    (bseq gap rank : ℕ → ℕ) (C H0 N : ℕ) (hC : 0 < C)
    (hgap : ∀ i, bseq (i + 1) = bseq i + gap i)
    (hcount : ∀ n, N ≤ n → 8 * C * Nat.count p n ≤ n)
    (hwitness : ∀ i, H0 ≤ gap i →
      ∃ T : Finset ℕ, Set.InjOn rank (T : Set ℕ) ∧
        gap i / C ≤ T.card ∧
        (∀ n ∈ T, bseq i < n ∧ n < bseq (i + 1)) ∧
        (∀ n ∈ T, Nat.nth p (rank n) ∣ n)) :
    ∀ x, max (max H0 N) (2 * C) ≤ x →
      ∀ i, bseq i < x → gap i ≤ x := by
  intro x hx i hbix
  by_contra hnot
  have hxg : x < gap i := by omega
  have hgH : H0 ≤ gap i := by omega
  obtain ⟨T, hinj, hcard, hint, hdiv⟩ := hwitness i hgH
  have hTcount : T.card ≤ Nat.count p (bseq (i + 1)) := by
    apply divisor_rank_witness_card_le_count p hp T rank
      (bseq (i + 1)) hinj
    · intro n hn
      have := (hint n hn).1
      omega
    · intro n hn
      exact (hint n hn).2
    · exact hdiv
  have hbnext : bseq (i + 1) ≤ 2 * gap i := by
    rw [hgap i]
    omega
  have hcountmono : Nat.count p (bseq (i + 1)) ≤
      Nat.count p (2 * gap i) := Nat.count_monotone p hbnext
  have hN : N ≤ 2 * gap i := by omega
  have hc := hcount (2 * gap i) hN
  have hq : gap i / C ≤ Nat.count p (2 * gap i) :=
    hcard.trans (hTcount.trans hcountmono)
  have hdivlt : gap i < C * (gap i / C + 1) := Nat.lt_mul_div_succ _ hC
  have hupper : gap i < C * (Nat.count p (2 * gap i) + 1) :=
    hdivlt.trans_le (Nat.mul_le_mul_left C (by omega))
  have hgC : 2 * C ≤ gap i := by omega
  nlinarith

/- Consolidated from F061.CountLinear. -/

open Filter
open scoped Topology

/-- A counting function which is little-o of `sqrt n` is eventually below any
fixed positive linear slope, in an exact natural cross-multiplied form. -/
theorem eventually_mul_count_le_of_isLittleO_sqrt
    (p : ℕ → Prop) [DecidablePred p]
    (h : (fun n : ℕ => (Nat.count p n : ℝ)) =o[atTop]
      (fun n : ℕ => Real.sqrt (n : ℝ)))
    (K : ℕ) (hK : 0 < K) :
    ∀ᶠ n : ℕ in atTop, K * Nat.count p n ≤ n := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hcpos : (0 : ℝ) < 1 / (2 * (K : ℝ)) := by positivity
  have hb := h.bound hcpos
  filter_upwards [hb, eventually_ge_atTop 1] with n hn hn1
  have hncount : (Nat.count p n : ℝ) ≤
      (1 / (2 * (K : ℝ))) * Real.sqrt (n : ℝ) := by
    simpa only [Real.norm_natCast, Real.norm_eq_abs,
      abs_of_nonneg (show (0 : ℝ) ≤ (Nat.count p n : ℝ) by positivity),
      abs_of_nonneg (Real.sqrt_nonneg _)] using hn
  have hsqrt : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      nlinarith
  have hmul := mul_le_mul_of_nonneg_left hncount hKR.le
  have hcast : ((K * Nat.count p n : ℕ) : ℝ) ≤ (n : ℝ) := by
    norm_num only [Nat.cast_mul]
    have hid : (K : ℝ) * (1 / (2 * (K : ℝ))) = 1 / 2 := by
      field_simp
    rw [← mul_assoc, hid] at hmul
    nlinarith
  exact_mod_cast hcast

/- Consolidated from F061.RankKernel. -/

open Filter
open scoped Topology BigOperators NNReal

noncomputable def rankDecay (n : ℕ) : ℝ :=
  1 / (((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1))

lemma summable_rankDecay : Summable rankDecay := by
  have h := (Real.summable_one_div_nat_add_rpow 1 (3 / 2 : ℝ)).2 (by norm_num)
  convert h using 1
  funext n
  rw [rankDecay, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
  congr 2
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
    Real.rpow_add (by positivity) 1 (1 / 2), Real.rpow_one,
    ← Real.sqrt_eq_rpow]

noncomputable def rankPairKernel (a : ℕ → ℕ) (z : ℕ × ℕ) : ℝ :=
  let x : ℝ := z.1 + 1
  let y : ℝ := z.2 + 1
  min x y / ((a z.1 : ℝ) * (a z.2 : ℝ))

/-- A global quadratic lower bound on an enumeration makes its rank-weighted
pair kernel summable. -/
theorem summable_rankPairKernel_of_sq_le (a : ℕ → ℕ)
    (ha : ∀ n, (n + 1) ^ 2 ≤ a n) :
    Summable (rankPairKernel a) := by
  have hprod : Summable (fun z : ℕ × ℕ => rankDecay z.1 * rankDecay z.2) := by
    exact summable_mul_of_summable_norm summable_rankDecay.norm summable_rankDecay.norm
  apply Summable.of_norm_bounded hprod
  intro z
  dsimp [rankPairKernel, rankDecay]
  rw [abs_of_nonneg (by positivity)]
  let x : ℝ := (z.1 : ℝ) + 1
  let y : ℝ := (z.2 : ℝ) + 1
  let A : ℝ := a z.1
  let B : ℝ := a z.2
  have hx : 0 < x := by dsimp [x]; positivity
  have hy : 0 < y := by dsimp [y]; positivity
  have hA : 0 < A := by
    dsimp [A]
    exact_mod_cast (lt_of_lt_of_le (by positivity : 0 < (z.1 + 1) ^ 2) (ha z.1))
  have hB : 0 < B := by
    dsimp [B]
    exact_mod_cast (lt_of_lt_of_le (by positivity : 0 < (z.2 + 1) ^ 2) (ha z.2))
  have hAi : x ^ 2 ≤ A := by dsimp [x, A]; exact_mod_cast ha z.1
  have hBj : y ^ 2 ≤ B := by dsimp [y, B]; exact_mod_cast ha z.2
  have hmin : min x y ≤ Real.sqrt (x * y) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    rw [pow_two]
    exact mul_le_mul (min_le_left _ _) (min_le_right _ _) (by positivity) (by positivity)
  rw [Real.sqrt_mul hx.le] at hmin
  have hsx : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx.le
  have hsy : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt hy.le
  have hmxy : min x y * (Real.sqrt x * Real.sqrt y) ≤ x * y := by
    have hsnon : 0 ≤ Real.sqrt x * Real.sqrt y :=
      mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)
    have hmul := mul_le_mul_of_nonneg_right hmin hsnon
    calc
      min x y * (Real.sqrt x * Real.sqrt y) ≤
          (Real.sqrt x * Real.sqrt y) * (Real.sqrt x * Real.sqrt y) := by simpa [mul_comm] using hmul
      _ = (Real.sqrt x) ^ 2 * (Real.sqrt y) ^ 2 := by ring
      _ = x * y := by rw [hsx, hsy]
  let den : ℝ := (x * Real.sqrt x) * (y * Real.sqrt y)
  have hdpos : 0 < den := by dsimp [den]; positivity
  have hcross : min x y * den ≤ A * B := by
    calc
      min x y * den = (min x y * (Real.sqrt x * Real.sqrt y)) * (x * y) := by
        dsimp [den]
        ring
      _ ≤ (x * y) * (x * y) :=
        mul_le_mul_of_nonneg_right hmxy (mul_nonneg hx.le hy.le)
      _ = (x ^ 2) * (y ^ 2) := by ring
      _ ≤ A * B := mul_le_mul hAi hBj (sq_nonneg _) hA.le
  have hquot : min x y / (A * B) ≤ (1 / (x * Real.sqrt x)) * (1 / (y * Real.sqrt y)) := by
    apply (div_le_iff₀ (mul_pos hA hB)).2
    calc
      min x y ≤ (A * B) / den := (le_div_iff₀ hdpos).2 hcross
      _ = (1 / (x * Real.sqrt x)) * (1 / (y * Real.sqrt y)) * (A * B) := by
        field_simp
        <;> ring
  simpa [x, y, A, B] using hquot

/- Consolidated from F061.FullCliqueCharging. -/

open scoped BigOperators

/-- Unweighted full-clique double counting.  If each object `i` has enough
labels to pay for `gap(i)^2`, and each label occurs at most `cap(z)` times,
then the total square mass is bounded by the sum of capacities. -/
theorem unweighted_pair_witness_double_count
    (I : Finset ℕ) (J : Finset (ℕ × ℕ)) (gap : ℕ → ℕ)
    (cap : ℕ × ℕ → ℕ) (R : ℕ → ℕ × ℕ → Prop) [DecidableRel R]
    (K : ℕ)
    (hw : ∀ i ∈ I, (gap i) ^ 2 ≤ K * (J.filter (R i)).card)
    (hcap : ∀ z ∈ J, (I.filter fun i => R i z).card ≤ cap z) :
    (∑ i ∈ I, (gap i) ^ 2) ≤ K * ∑ z ∈ J, cap z := by
  calc
    (∑ i ∈ I, (gap i) ^ 2) ≤
        ∑ i ∈ I, K * (J.filter (R i)).card :=
      Finset.sum_le_sum hw
    _ = K * ∑ i ∈ I, (J.filter (R i)).card := by
      rw [Finset.mul_sum]
    _ = K * ∑ i ∈ I, ∑ z ∈ J, if R i z then 1 else 0 := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.card_filter]
    _ = K * ∑ z ∈ J, ∑ i ∈ I, if R i z then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = K * ∑ z ∈ J, (I.filter fun i => R i z).card := by
      congr 1
      apply Finset.sum_congr rfl
      intro z hz
      rw [Finset.card_filter]
    _ ≤ K * ∑ z ∈ J, cap z := by
      apply Nat.mul_le_mul_left
      exact Finset.sum_le_sum hcap

/-- Actual-prefix capacity architecture.  A quadratic number of pair labels per
gap, together with a primitive-ray capacity

`aᵣaₛ cap(r,s) ≤ 4XC min(r+1,s+1) + 2aᵣaₛ`,

bounds the square-gap mass by a finite rank-kernel sum plus one endpoint term
per rank pair. -/
theorem full_clique_charge_le_rankKernel
    (I : Finset ℕ) (J : Finset (ℕ × ℕ)) (gap : ℕ → ℕ)
    (cap : ℕ × ℕ → ℕ) (R : ℕ → ℕ × ℕ → Prop) [DecidableRel R]
    (a : ℕ → ℕ) (K C X : ℕ)
    (hw : ∀ i ∈ I, (gap i) ^ 2 ≤ K * (J.filter (R i)).card)
    (hocc : ∀ z ∈ J, (I.filter fun i => R i z).card ≤ cap z)
    (ha : ∀ r, 0 < a r)
    (hcap : ∀ z ∈ J,
      a z.1 * a z.2 * cap z ≤
        4 * X * C * min (z.1 + 1) (z.2 + 1) +
          2 * (a z.1 * a z.2)) :
    ((∑ i ∈ I, (gap i) ^ 2 : ℕ) : ℝ) ≤
      (K : ℝ) *
        (4 * (X : ℝ) * (C : ℝ) *
            (∑ z ∈ J, rankPairKernel a z) + 2 * (J.card : ℝ)) := by
  have hdouble := unweighted_pair_witness_double_count
    I J gap cap R K hw hocc
  have hdoubleR : ((∑ i ∈ I, (gap i) ^ 2 : ℕ) : ℝ) ≤
      (K : ℝ) * (∑ z ∈ J, (cap z : ℝ)) := by
    exact_mod_cast hdouble
  have hterm : ∀ z ∈ J,
      (cap z : ℝ) ≤
        4 * (X : ℝ) * (C : ℝ) * rankPairKernel a z + 2 := by
    intro z hz
    have ha1 : (0 : ℝ) < a z.1 := by exact_mod_cast ha z.1
    have ha2 : (0 : ℝ) < a z.2 := by exact_mod_cast ha z.2
    have hab : (0 : ℝ) < (a z.1 : ℝ) * (a z.2 : ℝ) := mul_pos ha1 ha2
    have hc := hcap z hz
    have hcR : ((a z.1 * a z.2 * cap z : ℕ) : ℝ) ≤
        ((4 * X * C * min (z.1 + 1) (z.2 + 1) +
          2 * (a z.1 * a z.2) : ℕ) : ℝ) := by exact_mod_cast hc
    norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat,
      Nat.cast_min] at hcR
    dsimp [rankPairKernel]
    rw [show 4 * (X : ℝ) * (C : ℝ) *
        (min ((z.1 : ℝ) + 1) ((z.2 : ℝ) + 1) /
          ((a z.1 : ℝ) * (a z.2 : ℝ))) + 2 =
      (4 * (X : ℝ) * (C : ℝ) *
          min ((z.1 : ℝ) + 1) ((z.2 : ℝ) + 1) +
        2 * ((a z.1 : ℝ) * (a z.2 : ℝ))) /
          ((a z.1 : ℝ) * (a z.2 : ℝ)) by field_simp <;> ring]
    apply (le_div_iff₀ hab).mpr
    calc
      (cap z : ℝ) * ((a z.1 : ℝ) * (a z.2 : ℝ)) =
          (a z.1 : ℝ) * (a z.2 : ℝ) * (cap z : ℝ) := by ring
      _ ≤ 4 * (X : ℝ) * (C : ℝ) *
            min ((z.1 : ℝ) + 1) ((z.2 : ℝ) + 1) +
          2 * ((a z.1 : ℝ) * (a z.2 : ℝ)) := by
        simpa only [Nat.cast_add, Nat.cast_one] using hcR
  have hsum : (∑ z ∈ J, (cap z : ℝ)) ≤
      4 * (X : ℝ) * (C : ℝ) * (∑ z ∈ J, rankPairKernel a z) +
        2 * (J.card : ℝ) := by
    calc
      (∑ z ∈ J, (cap z : ℝ)) ≤
          ∑ z ∈ J, (4 * (X : ℝ) * (C : ℝ) *
            rankPairKernel a z + 2) := Finset.sum_le_sum hterm
      _ = 4 * (X : ℝ) * (C : ℝ) *
            (∑ z ∈ J, rankPairKernel a z) + 2 * (J.card : ℝ) := by
        rw [Finset.sum_add_distrib]
        simp [Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
        ring
  exact hdoubleR.trans (mul_le_mul_of_nonneg_left hsum (by positivity))

/- Consolidated from F061.PrimitiveRayPacking. -/

open scoped BigOperators

/-- Twice the signed area of the triangle spanned by two planar vectors. -/
def rayDet (x₁ y₁ x₂ y₂ : ℝ) : ℝ := x₁ * y₂ - y₁ * x₂

/-- A point on the top/right boundary of a rectangle, on the same ray as an
interior point. -/
structure RadialBoundary (X D x y : ℝ) where
  bx : ℝ
  yc : ℝ
  scale : ℝ
  bx_nonneg : 0 ≤ bx
  bx_le : bx ≤ X
  yc_nonneg : 0 ≤ yc
  yc_le : yc ≤ D
  on_edge : bx = X ∨ yc = D
  scale_pos : 0 < scale
  scale_le_one : scale ≤ 1
  x_eq : x = scale * bx
  y_eq : y = scale * yc

/-- Every positive point of a positive rectangle is a contraction of a point
on the top/right boundary along its ray from the origin. -/
theorem exists_radialBoundary
    (X D x y : ℝ) (hX : 0 < X) (hD : 0 < D)
    (hx : 0 < x) (hxX : x ≤ X) (hy : 0 < y) (hyD : y ≤ D) :
    Nonempty (RadialBoundary X D x y) := by
  by_cases hright : X * y ≤ D * x
  · let qy := X * y / x
    let t := x / X
    have hqy0 : 0 ≤ qy := by positivity
    have hqyD : qy ≤ D := by
      dsimp [qy]
      exact (div_le_iff₀ hx).2 (by nlinarith)
    have ht0 : 0 < t := by positivity
    have ht1 : t ≤ 1 := by
      dsimp [t]
      exact (div_le_one hX).2 hxX
    refine ⟨{
      bx := X
      yc := qy
      scale := t
      bx_nonneg := hX.le
      bx_le := le_rfl
      yc_nonneg := hqy0
      yc_le := hqyD
      on_edge := Or.inl rfl
      scale_pos := ht0
      scale_le_one := ht1
      x_eq := ?_
      y_eq := ?_ }⟩
    · dsimp [t]
      field_simp
    · dsimp [t, qy]
      field_simp
  · have htop : D * x < X * y := lt_of_not_ge hright
    let qx := D * x / y
    let t := y / D
    have hqx0 : 0 ≤ qx := by positivity
    have hqxX : qx ≤ X := by
      dsimp [qx]
      exact (div_le_iff₀ hy).2 (by nlinarith)
    have ht0 : 0 < t := by positivity
    have ht1 : t ≤ 1 := by
      dsimp [t]
      exact (div_le_one hD).2 hyD
    refine ⟨{
      bx := qx
      yc := D
      scale := t
      bx_nonneg := hqx0
      bx_le := hqxX
      yc_nonneg := hD.le
      yc_le := le_rfl
      on_edge := Or.inr rfl
      scale_pos := ht0
      scale_le_one := ht1
      x_eq := ?_
      y_eq := ?_ }⟩
    · dsimp [t, qx]
      field_simp
    · dsimp [t]
      field_simp

/-- A monotone coordinate along the top/right boundary, scaled so its range is
`[0,2XD]`. -/
noncomputable def boundaryPotential (X D x y : ℝ) : ℝ :=
  if x = X then X * y else 2 * X * D - D * x

/-- For two boundary points in counterclockwise order, their determinant is at
most the increase of the boundary potential. -/
theorem rayDet_le_boundaryPotential_sub
    (X D px py qx qy : ℝ) (hX : 0 < X) (hD : 0 < D)
    (hpx0 : 0 ≤ px) (hpxX : px ≤ X) (hpy0 : 0 ≤ py) (hpyD : py ≤ D)
    (hqx0 : 0 ≤ qx) (hqxX : qx ≤ X) (hqy0 : 0 ≤ qy) (hqyD : qy ≤ D)
    (hpedge : px = X ∨ py = D) (hqedge : qx = X ∨ qy = D)
    (horient : 0 ≤ rayDet px py qx qy) :
    rayDet px py qx qy ≤
      boundaryPotential X D qx qy - boundaryPotential X D px py := by
  by_cases hpx : px = X
  · by_cases hqx : qx = X
    · simp [boundaryPotential, rayDet, hpx, hqx]
      ring_nf
      exact le_rfl
    · have hqy : qy = D := hqedge.resolve_left hqx
      simp [boundaryPotential, rayDet, hpx, hqx, hqy]
      have hprod : 0 ≤ (X - qx) * (D - py) :=
        mul_nonneg (sub_nonneg.mpr hqxX) (sub_nonneg.mpr hpyD)
      nlinarith
  · have hpy : py = D := hpedge.resolve_left hpx
    by_cases hqx : qx = X
    · have hpxlt : px < X := lt_of_le_of_ne hpxX hpx
      have hmul1 : px * qy ≤ px * D :=
        mul_le_mul_of_nonneg_left hqyD hpx0
      have hmul2 : px * D < X * D := mul_lt_mul_of_pos_right hpxlt hD
      have : rayDet px py qx qy < 0 := by
        simp [rayDet, hpy, hqx]
        nlinarith
      linarith
    · have hqy : qy = D := hqedge.resolve_left hqx
      simp [boundaryPotential, rayDet, hpx, hqx, hpy, hqy]
      ring_nf
      exact le_rfl

/-- The boundary potential always lies in `[0,2XD]`. -/
theorem boundaryPotential_mem_Icc
    (X D x y : ℝ) (hX : 0 < X) (hD : 0 < D)
    (hx0 : 0 ≤ x) (hxX : x ≤ X) (hy0 : 0 ≤ y) (hyD : y ≤ D)
    (hedge : x = X ∨ y = D) :
    boundaryPotential X D x y ∈ Set.Icc (0 : ℝ) (2 * X * D) := by
  by_cases hx : x = X
  · simp [boundaryPotential, hx]
    constructor <;> nlinarith [mul_nonneg hX.le hy0, mul_le_mul_of_nonneg_left hyD hX.le]
  · have hyedge : y = D := hedge.resolve_left hx
    simp [boundaryPotential, hx, hyedge]
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left hxX hD.le]
    · nlinarith [mul_nonneg hD.le hx0]

/-- Radially projecting two angularly ordered rectangle points to the boundary
can only increase their determinant, which is then controlled by the boundary
potential. -/
theorem rayDet_le_potential_of_radialBoundary
    (X D px py qx qy : ℝ) (hX : 0 < X) (hD : 0 < D)
    (wp : RadialBoundary X D px py) (wq : RadialBoundary X D qx qy)
    (horient : 0 < rayDet px py qx qy) :
    rayDet px py qx qy ≤
      boundaryPotential X D wq.bx wq.yc - boundaryPotential X D wp.bx wp.yc := by
  rcases wp with ⟨pbx, pyc, pt, hpbx0, hpbxX, hpyc0, hpycD, hpedge,
    hpt0, hpt1, hpx, hpy⟩
  rcases wq with ⟨qbx, qyc, qt, hqbx0, hqbxX, hqyc0, hqycD, hqedge,
    hqt0, hqt1, hqx, hqy⟩
  have hscale :
      rayDet px py qx qy = pt * qt * rayDet pbx pyc qbx qyc := by
    rw [hpx, hpy, hqx, hqy]
    simp only [rayDet]
    ring
  have hprodpos : 0 < pt * qt := mul_pos hpt0 hqt0
  have hbdetpos : 0 < rayDet pbx pyc qbx qyc := by
    have hmulpos : 0 < pt * qt * rayDet pbx pyc qbx qyc := by
      rw [← hscale]
      exact horient
    by_contra hnot
    have hbnonpos : rayDet pbx pyc qbx qyc ≤ 0 := le_of_not_gt hnot
    have := mul_nonpos_of_nonneg_of_nonpos hprodpos.le hbnonpos
    linarith
  have hprodle : pt * qt ≤ 1 := by
    calc
      pt * qt ≤ 1 * qt := mul_le_mul_of_nonneg_right hpt1 hqt0.le
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hqt1 (by norm_num)
      _ = 1 := by ring
  have hinterior_le_boundary : rayDet px py qx qy ≤ rayDet pbx pyc qbx qyc := by
    rw [hscale]
    have := mul_le_mul_of_nonneg_right hprodle hbdetpos.le
    simpa using this
  exact hinterior_le_boundary.trans
    (rayDet_le_boundaryPotential_sub X D pbx pyc qbx qyc hX hD
      hpbx0 hpbxX hpyc0 hpycD hqbx0 hqbxX hqyc0 hqycD
      hpedge hqedge hbdetpos.le)

/-- Fan triangles with vertices in a positive rectangle have total doubled area
at most `2XD`, provided their rays occur in angular order. -/
theorem rectangle_fan_sum_le
    (N : ℕ) (X D : ℝ) (x y : ℕ → ℝ)
    (hX : 0 < X) (hD : 0 < D)
    (hx : ∀ i, 0 < x i) (hxX : ∀ i, x i ≤ X)
    (hy : ∀ i, 0 < y i) (hyD : ∀ i, y i ≤ D)
    (horient : ∀ i < N, 0 < rayDet (x i) (y i) (x (i + 1)) (y (i + 1))) :
    (∑ i ∈ Finset.range N, rayDet (x i) (y i) (x (i + 1)) (y (i + 1))) ≤
      2 * X * D := by
  classical
  let w : ∀ i : ℕ, RadialBoundary X D (x i) (y i) := fun i =>
    Classical.choice (exists_radialBoundary X D (x i) (y i) hX hD
      (hx i) (hxX i) (hy i) (hyD i))
  let p : ℕ → ℝ := fun i => boundaryPotential X D (w i).bx (w i).yc
  have hlocal : ∀ i < N,
      rayDet (x i) (y i) (x (i + 1)) (y (i + 1)) ≤ p (i + 1) - p i := by
    intro i hi
    simpa [p] using rayDet_le_potential_of_radialBoundary X D
      (x i) (y i) (x (i + 1)) (y (i + 1)) hX hD
      (w i) (w (i + 1)) (horient i hi)
  have htel : ∀ M : ℕ,
      (∑ i ∈ Finset.range M, (p (i + 1) - p i)) = p M - p 0 := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  calc
    (∑ i ∈ Finset.range N, rayDet (x i) (y i) (x (i + 1)) (y (i + 1))) ≤
        ∑ i ∈ Finset.range N, (p (i + 1) - p i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hlocal i (Finset.mem_range.mp hi)
    _ = p N - p 0 := htel N
    _ ≤ 2 * X * D := by
      have hp0 := boundaryPotential_mem_Icc X D (w 0).bx (w 0).yc hX hD
        (w 0).bx_nonneg (w 0).bx_le (w 0).yc_nonneg (w 0).yc_le (w 0).on_edge
      have hpN := boundaryPotential_mem_Icc X D (w N).bx (w N).yc hX hD
        (w N).bx_nonneg (w N).bx_le (w N).yc_nonneg (w N).yc_le (w N).on_edge
      have hp0' : 0 ≤ p 0 := by simpa [p] using hp0.1
      have hpN' : p N ≤ 2 * X * D := by simpa [p] using hpN.2
      linarith

/-- One-sided primitive-ray packing in its ordered integer form.  If `N+1`
positive lattice rays lie in `0 < a*r-b*s ≤ D`, with both covered coordinates
bounded by `X`, and are listed in strictly increasing slope order, then the
`N` angular sectors each have determinant at least `a*b`. -/
theorem ordered_positive_ray_count_bound
    (N a b X D : ℕ) (r s : ℕ → ℕ)
    (ha : 0 < a) (hb : 0 < b) (hX : 0 < X) (hD : 0 < D)
    (hr : ∀ i, 0 < r i) (hs : ∀ i, 0 < s i)
    (hbsX : ∀ i, b * s i ≤ X)
    (hside : ∀ i, b * s i < a * r i)
    (hstrip : ∀ i, a * r i ≤ b * s i + D)
    (horder : ∀ i < N, r i * s (i + 1) < r (i + 1) * s i) :
    a * b * N ≤ 2 * X * D := by
  let xr : ℕ → ℝ := fun i => (b * s i : ℕ)
  let yr : ℕ → ℝ := fun i => (a * r i : ℕ) - (b * s i : ℕ)
  have hxrpos : ∀ i, 0 < xr i := by
    intro i
    have hpos : 0 < b * s i := Nat.mul_pos hb (hs i)
    dsimp [xr]
    exact_mod_cast hpos
  have hxrX : ∀ i, xr i ≤ (X : ℝ) := by
    intro i
    dsimp [xr]
    exact_mod_cast hbsX i
  have hyrpos : ∀ i, 0 < yr i := by
    intro i
    have hsR : (b * s i : ℕ) < (a * r i : ℕ) := hside i
    have hsR' : ((b * s i : ℕ) : ℝ) < ((a * r i : ℕ) : ℝ) := by
      exact_mod_cast hsR
    dsimp [yr]
    linarith
  have hyrD : ∀ i, yr i ≤ (D : ℝ) := by
    intro i
    have hsR : ((a * r i : ℕ) : ℝ) ≤
        ((b * s i : ℕ) : ℝ) + (D : ℝ) := by
      exact_mod_cast hstrip i
    dsimp [yr]
    linarith
  have hdetid : ∀ i,
      rayDet (xr i) (yr i) (xr (i + 1)) (yr (i + 1)) =
        (a : ℝ) * (b : ℝ) *
          ((r (i + 1) : ℝ) * (s i : ℝ) - (r i : ℝ) * (s (i + 1) : ℝ)) := by
    intro i
    simp only [xr, yr, rayDet, Nat.cast_mul]
    ring
  have hdetpos : ∀ i < N,
      0 < rayDet (xr i) (yr i) (xr (i + 1)) (yr (i + 1)) := by
    intro i hi
    rw [hdetid i]
    have hord : (r i : ℝ) * (s (i + 1) : ℝ) <
        (r (i + 1) : ℝ) * (s i : ℝ) := by
      exact_mod_cast horder i hi
    positivity
  have hdetlower : ∀ i < N,
      ((a * b : ℕ) : ℝ) ≤ rayDet (xr i) (yr i) (xr (i + 1)) (yr (i + 1)) := by
    intro i hi
    rw [hdetid i, Nat.cast_mul]
    have hsucc : r i * s (i + 1) + 1 ≤ r (i + 1) * s i :=
      (Nat.succ_le_iff).2 (horder i hi)
    have hsuccR : ((r i * s (i + 1) : ℕ) : ℝ) + 1 ≤
        ((r (i + 1) * s i : ℕ) : ℝ) := by
      exact_mod_cast hsucc
    have hdelta : (1 : ℝ) ≤
        (r (i + 1) : ℝ) * (s i : ℝ) - (r i : ℝ) * (s (i + 1) : ℝ) := by
      norm_num only [Nat.cast_mul] at hsuccR
      linarith
    have hab0 : 0 ≤ (a : ℝ) * (b : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_left hdelta hab0
    simpa using this
  have hfan := rectangle_fan_sum_le N (X : ℝ) (D : ℝ) xr yr
    (by exact_mod_cast hX) (by exact_mod_cast hD)
    hxrpos hxrX hyrpos hyrD hdetpos
  have hreal : (N : ℝ) * ((a * b : ℕ) : ℝ) ≤ 2 * (X : ℝ) * (D : ℝ) := by
    calc
      (N : ℝ) * ((a * b : ℕ) : ℝ) =
          ∑ i ∈ Finset.range N, ((a * b : ℕ) : ℝ) := by simp
      _ ≤ ∑ i ∈ Finset.range N,
          rayDet (xr i) (yr i) (xr (i + 1)) (yr (i + 1)) := by
        apply Finset.sum_le_sum
        intro i hi
        exact hdetlower i (Finset.mem_range.mp hi)
      _ ≤ 2 * (X : ℝ) * (D : ℝ) := hfan
  have hnat : N * (a * b) ≤ 2 * X * D := by
    exact_mod_cast hreal
  simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hnat

/- Consolidated from F061.RayCapacity. -/

open scoped BigOperators

/-- A finite, pairwise nonproportional family of positive quotient vectors in
one diagonal strip obeys the same fan-area bound as an explicitly ordered
family. -/
theorem positive_ray_finset_count_bound
    (T : Finset (ℕ × ℕ)) (a b X D : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hX : 0 < X) (hD : 0 < D)
    (hr : ∀ z ∈ T, 0 < z.1) (hs : ∀ z ∈ T, 0 < z.2)
    (hbsX : ∀ z ∈ T, b * z.2 ≤ X)
    (hside : ∀ z ∈ T, b * z.2 < a * z.1)
    (hstrip : ∀ z ∈ T, a * z.1 ≤ b * z.2 + D)
    (hnonprop : ∀ z ∈ T, ∀ w ∈ T,
      z.1 * w.2 = w.1 * z.2 → z = w) :
    a * b * (T.card - 1) ≤ 2 * X * D := by
  by_cases hsmall : T.card ≤ 1
  · have hz : T.card - 1 = 0 := Nat.sub_eq_zero_of_le hsmall
    simp [hz]
  · have hcard : 1 < T.card := by omega
    have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
    let α := {z : ℕ × ℕ // z ∈ T}
    let key : α → ℚ := fun z => (z.1.1 : ℚ) / (z.1.2 : ℚ)
    have hkeyinj : Function.Injective key := by
      intro z w hkey
      apply Subtype.ext
      apply hnonprop z.1 z.2 w.1 w.2
      have hzs : (z.1.2 : ℚ) ≠ 0 := by
        exact_mod_cast (hs z.1 z.2).ne'
      have hws : (w.1.2 : ℚ) ≠ 0 := by
        exact_mod_cast (hs w.1 w.2).ne'
      have hcross : (z.1.1 : ℚ) * (w.1.2 : ℚ) =
          (w.1.1 : ℚ) * (z.1.2 : ℚ) :=
        (div_eq_div_iff hzs hws).mp hkey
      exact_mod_cast hcross
    let rel : α → α → Prop := fun z w => key z ≤ key w
    letI : IsTrans α rel := ⟨fun _ _ _ h₁ h₂ => h₁.trans h₂⟩
    letI : Std.Antisymm rel :=
      ⟨fun _ _ h₁ h₂ => hkeyinj (le_antisymm h₁ h₂)⟩
    letI : Std.Total rel := ⟨fun z w => le_total (key z) (key w)⟩
    let U : Finset α := Finset.univ
    let Ls : List α := U.sort rel
    obtain ⟨zv, hzv⟩ := hTne
    let z0 : α := ⟨zv, hzv⟩
    let z : ℕ → ℕ × ℕ := fun i => (Ls.getD i z0).1
    have hlen : Ls.length = T.card := by
      dsimp [Ls, U]
      rw [Finset.length_sort, Finset.card_univ, Fintype.card_coe]
    have hzmem : ∀ i, z i ∈ T := by
      intro i
      by_cases hi : i < Ls.length
      · have hzi : z i = Ls[i].1 := by
          dsimp [z]
          rw [List.getD_eq_getElem Ls z0 hi]
        rw [hzi]
        exact Ls[i].2
      · have hi' : Ls.length ≤ i := by omega
        simpa [z, List.getD_eq_default _ _ hi'] using z0.2
    have hzorder : ∀ i < T.card - 1,
        (z i).1 * (z (i + 1)).2 < (z (i + 1)).1 * (z i).2 := by
      intro i hi
      have hi0 : i < Ls.length := by omega
      have hi1 : i + 1 < Ls.length := by omega
      have hlekey : key Ls[i] ≤ key Ls[i + 1] := by
        have hpw := Finset.pairwise_sort U rel
        exact (List.pairwise_iff_getElem.mp hpw) i (i + 1) hi0 hi1 (by omega)
      have hneα : Ls[i] ≠ Ls[i + 1] := by
        intro heq
        have hiEq : i = i + 1 :=
          (Finset.sort_nodup U rel).getElem_inj_iff.mp heq
        omega
      have hnekey : key Ls[i] ≠ key Ls[i + 1] :=
        fun heq => hneα (hkeyinj heq)
      have hltkey : key Ls[i] < key Ls[i + 1] :=
        lt_of_le_of_ne hlekey hnekey
      have hden0 : (0 : ℚ) < (Ls[i].1.2 : ℕ) := by
        exact_mod_cast hs Ls[i].1 Ls[i].2
      have hden1 : (0 : ℚ) < (Ls[i + 1].1.2 : ℕ) := by
        exact_mod_cast hs Ls[i + 1].1 Ls[i + 1].2
      have hcrossQ : (Ls[i].1.1 : ℚ) * (Ls[i + 1].1.2 : ℕ) <
          (Ls[i + 1].1.1 : ℚ) * (Ls[i].1.2 : ℕ) := by
        exact (div_lt_div_iff₀ hden0 hden1).mp hltkey
      have hcrossN : Ls[i].1.1 * Ls[i + 1].1.2 <
          Ls[i + 1].1.1 * Ls[i].1.2 := by
        exact_mod_cast hcrossQ
      have hzi : z i = Ls[i].1 := by
        dsimp [z]
        rw [List.getD_eq_getElem Ls z0 hi0]
      have hzi1 : z (i + 1) = Ls[i + 1].1 := by
        dsimp [z]
        rw [List.getD_eq_getElem Ls z0 hi1]
      rw [hzi, hzi1]
      exact hcrossN
    apply ordered_positive_ray_count_bound (T.card - 1) a b X D
      (fun i => (z i).1) (fun i => (z i).2) ha hb hX hD
    · intro i
      exact hr (z i) (hzmem i)
    · intro i
      exact hs (z i) (hzmem i)
    · intro i
      exact hbsX (z i) (hzmem i)
    · intro i
      exact hside (z i) (hzmem i)
    · intro i
      exact hstrip (z i) (hzmem i)
    · exact hzorder

/-- Coprime covered vectors cannot represent the same quotient ray twice. -/
theorem quotient_pair_eq_of_proportional_of_covered_coprime
    (a b r s u v : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hprop : r * v = u * s)
    (hc₁ : Nat.Coprime (a * r) (b * s))
    (hc₂ : Nat.Coprime (a * u) (b * v)) :
    (r, s) = (u, v) := by
  have hcovered : (a * r) * (b * v) = (b * s) * (a * u) := by
    calc
      (a * r) * (b * v) = (a * b) * (r * v) := by ring
      _ = (a * b) * (u * s) := by rw [hprop]
      _ = (b * s) * (a * u) := by ring
  have heq := nat_pair_eq_of_proportional_of_coprime
    (a * r) (b * s) (a * u) (b * v) hcovered hc₁ hc₂
  apply Prod.ext
  · exact Nat.eq_of_mul_eq_mul_left ha heq.1
  · exact Nat.eq_of_mul_eq_mul_left hb heq.2

/-- One-sided capacity bound for a finite set of quotient pairs whose covered
vectors are primitive. -/
theorem primitive_covered_positive_ray_count_bound
    (T : Finset (ℕ × ℕ)) (a b X D : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hX : 0 < X) (hD : 0 < D)
    (hr : ∀ z ∈ T, 0 < z.1) (hs : ∀ z ∈ T, 0 < z.2)
    (hprimitive : ∀ z ∈ T, Nat.Coprime (a * z.1) (b * z.2))
    (hbsX : ∀ z ∈ T, b * z.2 ≤ X)
    (hside : ∀ z ∈ T, b * z.2 < a * z.1)
    (hstrip : ∀ z ∈ T, a * z.1 ≤ b * z.2 + D) :
    a * b * (T.card - 1) ≤ 2 * X * D := by
  apply positive_ray_finset_count_bound T a b X D ha hb hX hD
    hr hs hbsX hside hstrip
  intro z hz w hw hprop
  exact quotient_pair_eq_of_proportional_of_covered_coprime
    a b z.1 z.2 w.1 w.2 ha hb hprop (hprimitive z hz) (hprimitive w hw)

/-- The symmetric one-sided bound for the strip `0 < b*s-a*r ≤ D`. -/
theorem primitive_covered_negative_ray_count_bound
    (T : Finset (ℕ × ℕ)) (a b X D : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hX : 0 < X) (hD : 0 < D)
    (hr : ∀ z ∈ T, 0 < z.1) (hs : ∀ z ∈ T, 0 < z.2)
    (hprimitive : ∀ z ∈ T, Nat.Coprime (a * z.1) (b * z.2))
    (harX : ∀ z ∈ T, a * z.1 ≤ X)
    (hside : ∀ z ∈ T, a * z.1 < b * z.2)
    (hstrip : ∀ z ∈ T, b * z.2 ≤ a * z.1 + D) :
    a * b * (T.card - 1) ≤ 2 * X * D := by
  let swapPair : ℕ × ℕ → ℕ × ℕ := fun z => (z.2, z.1)
  let U := T.image swapPair
  have hcard : U.card = T.card := by
    apply Finset.card_image_of_injective
    intro z w h
    dsimp [swapPair] at h
    exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
  have hbound := primitive_covered_positive_ray_count_bound U b a X D
    hb ha hX hD
    (fun z hz => by
      rcases Finset.mem_image.mp hz with ⟨w, hw, rfl⟩
      exact hs w hw)
    (fun z hz => by
      rcases Finset.mem_image.mp hz with ⟨w, hw, rfl⟩
      exact hr w hw)
    (fun z hz => by
      rcases Finset.mem_image.mp hz with ⟨w, hw, rfl⟩
      exact (hprimitive w hw).symm)
    (fun z hz => by
      rcases Finset.mem_image.mp hz with ⟨w, hw, rfl⟩
      exact harX w hw)
    (fun z hz => by
      rcases Finset.mem_image.mp hz with ⟨w, hw, rfl⟩
      exact hside w hw)
    (fun z hz => by
      rcases Finset.mem_image.mp hz with ⟨w, hw, rfl⟩
      exact hstrip w hw)
  rw [hcard] at hbound
  simpa [Nat.mul_comm, Nat.mul_left_comm] using hbound

/-- Two-sided primitive-ray capacity.  Primitive covered vectors in
`0 < |a*r-b*s| ≤ D`, with both covered coordinates at most `X`, satisfy the
cross-multiplied count bound `ab·#T ≤ 4XD+2ab`. -/
theorem primitive_covered_two_sided_count_bound
    (T : Finset (ℕ × ℕ)) (a b X D : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hX : 0 < X) (hD : 0 < D)
    (hr : ∀ z ∈ T, 0 < z.1) (hs : ∀ z ∈ T, 0 < z.2)
    (hprimitive : ∀ z ∈ T, Nat.Coprime (a * z.1) (b * z.2))
    (harX : ∀ z ∈ T, a * z.1 ≤ X)
    (hbsX : ∀ z ∈ T, b * z.2 ≤ X)
    (hne : ∀ z ∈ T, a * z.1 ≠ b * z.2)
    (hdist : ∀ z ∈ T, Nat.dist (a * z.1) (b * z.2) ≤ D) :
    a * b * T.card ≤ 4 * X * D + 2 * (a * b) := by
  let Tp := T.filter fun z => b * z.2 < a * z.1
  let Tn := T.filter fun z => a * z.1 < b * z.2
  have hcover : T ⊆ Tp ∪ Tn := by
    intro z hz
    have hneq := hne z hz
    rcases lt_or_gt_of_ne hneq with hlt | hgt
    · exact Finset.mem_union_right Tp (Finset.mem_filter.mpr ⟨hz, hlt⟩)
    · exact Finset.mem_union_left Tn (Finset.mem_filter.mpr ⟨hz, hgt⟩)
  have hcardcover : T.card ≤ Tp.card + Tn.card := by
    calc
      T.card ≤ (Tp ∪ Tn).card := Finset.card_le_card hcover
      _ ≤ Tp.card + Tn.card := Finset.card_union_le Tp Tn
  have hp := primitive_covered_positive_ray_count_bound Tp a b X D
    ha hb hX hD
    (fun z hz => hr z (Finset.mem_filter.mp hz).1)
    (fun z hz => hs z (Finset.mem_filter.mp hz).1)
    (fun z hz => hprimitive z (Finset.mem_filter.mp hz).1)
    (fun z hz => hbsX z (Finset.mem_filter.mp hz).1)
    (fun z hz => (Finset.mem_filter.mp hz).2)
    (fun z hz => by
      have hzT := (Finset.mem_filter.mp hz).1
      have hdistz := hdist z hzT
      rw [Nat.dist_comm, Nat.dist_eq_sub_of_le
        (Nat.le_of_lt (Finset.mem_filter.mp hz).2)] at hdistz
      omega)
  have hn := primitive_covered_negative_ray_count_bound Tn a b X D
    ha hb hX hD
    (fun z hz => hr z (Finset.mem_filter.mp hz).1)
    (fun z hz => hs z (Finset.mem_filter.mp hz).1)
    (fun z hz => hprimitive z (Finset.mem_filter.mp hz).1)
    (fun z hz => harX z (Finset.mem_filter.mp hz).1)
    (fun z hz => (Finset.mem_filter.mp hz).2)
    (fun z hz => by
      have hzT := (Finset.mem_filter.mp hz).1
      have hdistz := hdist z hzT
      rw [Nat.dist_eq_sub_of_le
        (Nat.le_of_lt (Finset.mem_filter.mp hz).2)] at hdistz
      omega)
  have hp' : a * b * Tp.card ≤ 2 * X * D + a * b := by
    have hc : Tp.card ≤ (Tp.card - 1) + 1 := by omega
    have hm := Nat.mul_le_mul_left (a * b) hc
    calc
      a * b * Tp.card ≤ a * b * ((Tp.card - 1) + 1) := hm
      _ = a * b * (Tp.card - 1) + a * b := by ring
      _ ≤ 2 * X * D + a * b := Nat.add_le_add_right hp _
  have hn' : a * b * Tn.card ≤ 2 * X * D + a * b := by
    have hc : Tn.card ≤ (Tn.card - 1) + 1 := by omega
    have hm := Nat.mul_le_mul_left (a * b) hc
    calc
      a * b * Tn.card ≤ a * b * ((Tn.card - 1) + 1) := hm
      _ = a * b * (Tn.card - 1) + a * b := by ring
      _ ≤ 2 * X * D + a * b := Nat.add_le_add_right hn _
  have hmulcover := Nat.mul_le_mul_left (a * b) hcardcover
  calc
    a * b * T.card ≤ a * b * (Tp.card + Tn.card) := hmulcover
    _ = a * b * Tp.card + a * b * Tn.card := by ring
    _ ≤ (2 * X * D + a * b) + (2 * X * D + a * b) :=
      Nat.add_le_add hp' hn'
    _ = 4 * X * D + 2 * (a * b) := by ring

/- Consolidated from F061.OccurrenceRayCapacity. -/

/-- Primitive covered occurrences of one fixed modulus pair satisfy the
primitive-ray capacity bound, provided quotient pairs distinguish occurrences. -/
theorem fixed_modulus_occurrence_capacity
    (I : Finset ℕ) (u v : ℕ → ℕ) (a b X D : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hX : 0 < X) (hD : 0 < D)
    (hu : ∀ i ∈ I, 0 < u i) (hv : ∀ i ∈ I, 0 < v i)
    (hadu : ∀ i ∈ I, a ∣ u i) (hbdv : ∀ i ∈ I, b ∣ v i)
    (hprimitive : ∀ i ∈ I, Nat.Coprime (u i) (v i))
    (huX : ∀ i ∈ I, u i ≤ X) (hvX : ∀ i ∈ I, v i ≤ X)
    (hne : ∀ i ∈ I, u i ≠ v i)
    (hdist : ∀ i ∈ I, Nat.dist (u i) (v i) ≤ D)
    (hinj : Set.InjOn (fun i => (u i / a, v i / b)) (I : Set ℕ)) :
    a * b * I.card ≤ 4 * X * D + 2 * (a * b) := by
  let q : ℕ → ℕ × ℕ := fun i => (u i / a, v i / b)
  let T := I.image q
  have hcard : T.card = I.card := Finset.card_image_iff.mpr hinj
  have hbound := primitive_covered_two_sided_count_bound T a b X D
    ha hb hX hD
    (fun z hz => by
      rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
      dsimp [q]
      apply Nat.div_pos (Nat.le_of_dvd (hu i hi) (hadu i hi)) ha)
    (fun z hz => by
      rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
      dsimp [q]
      apply Nat.div_pos (Nat.le_of_dvd (hv i hi) (hbdv i hi)) hb)
    (fun z hz => by
      rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
      dsimp [q]
      simpa [Nat.mul_div_cancel' (hadu i hi),
        Nat.mul_div_cancel' (hbdv i hi)] using hprimitive i hi)
    (fun z hz => by
      rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
      dsimp [q]
      simpa [Nat.mul_div_cancel' (hadu i hi)] using huX i hi)
    (fun z hz => by
      rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
      dsimp [q]
      simpa [Nat.mul_div_cancel' (hbdv i hi)] using hvX i hi)
    (fun z hz => by
      rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
      dsimp [q]
      simpa [Nat.mul_div_cancel' (hadu i hi),
        Nat.mul_div_cancel' (hbdv i hi)] using hne i hi)
    (fun z hz => by
      rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
      dsimp [q]
      simpa [Nat.mul_div_cancel' (hadu i hi),
        Nat.mul_div_cancel' (hbdv i hi)] using hdist i hi)
  rwa [hcard] at hbound

/- Consolidated from F061.DisjointGapInjection. -/

/-- Choosing one point in each open gap of a strictly increasing sequence gives
an injective map of gap indices. -/
theorem injective_of_mem_successive_intervals
    (b u : ℕ → ℕ) (hb : StrictMono b)
    (hu : ∀ i, b i < u i ∧ u i < b (i + 1)) :
    Function.Injective u := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hijlt | hjilt
  · have hstep : b (i + 1) ≤ b j := hb.monotone (by omega)
    have := hu i
    have := hu j
    omega
  · have hstep : b (j + 1) ≤ b i := hb.monotone (by omega)
    have := hu i
    have := hu j
    omega

/-- Exact divisibility upgrades the preceding point injection to injection of
fixed-modulus quotient pairs. -/
theorem quotient_pair_injOn_of_successive_intervals
    (I : Finset ℕ) (bseq u v : ℕ → ℕ) (a b : ℕ)
    (hbseq : StrictMono bseq)
    (huGap : ∀ i ∈ I, bseq i < u i ∧ u i < bseq (i + 1))
    (hadu : ∀ i ∈ I, a ∣ u i) :
    Set.InjOn (fun i => (u i / a, v i / b)) (I : Set ℕ) := by
  intro i hi j hj hpairs
  have hq : u i / a = u j / a := congrArg Prod.fst hpairs
  have huEq : u i = u j := by
    calc
      u i = a * (u i / a) := (Nat.mul_div_cancel' (hadu i hi)).symm
      _ = a * (u j / a) := by rw [hq]
      _ = u j := Nat.mul_div_cancel' (hadu j hj)
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hmono : bseq (i + 1) ≤ bseq j := hbseq.monotone (by omega)
    have hiGap := huGap i hi
    have hjGap := huGap j hj
    omega
  · have hmono : bseq (j + 1) ≤ bseq i := hbseq.monotone (by omega)
    have hiGap := huGap i hi
    have hjGap := huGap j hj
    omega

/- Consolidated from F061.GlobalGapCharging. -/

open scoped BigOperators

noncomputable def rankPairPreimage
    (S : Finset ℕ) (rank : ℕ → ℕ) (z : ℕ × ℕ) : ℕ × ℕ := by
  classical
  let P := coprimeOrderedPairs S
  let f : ℕ × ℕ → ℕ × ℕ := fun w => (rank w.1, rank w.2)
  exact if h : z ∈ P.image f then Classical.choose (Finset.mem_image.mp h) else (0, 0)

theorem rankPairPreimage_spec
    (S : Finset ℕ) (rank : ℕ → ℕ) (z : ℕ × ℕ)
    (hz : z ∈ (coprimeOrderedPairs S).image
      (fun w => (rank w.1, rank w.2))) :
    rankPairPreimage S rank z ∈ coprimeOrderedPairs S ∧
      (rank (rankPairPreimage S rank z).1,
        rank (rankPairPreimage S rank z).2) = z := by
  classical
  unfold rankPairPreimage
  rw [dif_pos hz]
  exact Classical.choose_spec (Finset.mem_image.mp hz)

/-- Global actual-prefix charging architecture. Each gap pays its square with
coprime position pairs. Fixed rank pairs are then bounded by primitive-ray
capacity across disjoint successive gaps. -/
theorem global_gap_charge_le_rankKernel
    (I : Finset ℕ) (bseq gap : ℕ → ℕ) (T : ℕ → Finset ℕ)
    (rank a : ℕ → ℕ) (C X N : ℕ)
    (hC : 0 < C) (hX : 0 < X) (hb : StrictMono bseq)
    (hgap : ∀ i ∈ I, bseq (i + 1) = bseq i + gap i)
    (hint : ∀ i ∈ I, ∀ n ∈ T i,
      bseq i < n ∧ n < bseq (i + 1))
    (hrankinj : ∀ i ∈ I, Set.InjOn rank (T i : Set ℕ))
    (ha : ∀ r, 0 < a r)
    (hdiv : ∀ i ∈ I, ∀ n ∈ T i, a (rank n) ∣ n)
    (hcoordX : ∀ i ∈ I, ∀ n ∈ T i, n ≤ X)
    (hhigh : ∀ i ∈ I, ∀ n ∈ T i, gap i / C ≤ rank n)
    (hN : ∀ i ∈ I, N ≤ gap i / C)
    (hpay : ∀ i ∈ I,
      (gap i) ^ 2 ≤ 16 * C ^ 2 * (coprimeOrderedPairs (T i)).card) :
    ∃ J : Finset (ℕ × ℕ),
      ((∑ i ∈ I, (gap i) ^ 2 : ℕ) : ℝ) ≤
        ((16 * C ^ 2 : ℕ) : ℝ) *
          (4 * (X : ℝ) * (C : ℝ) *
              (∑ z ∈ J, rankPairKernel a z) + 2 * (J.card : ℝ)) ∧
      (∀ z ∈ J, N ≤ z.1 ∧ N ≤ z.2) ∧
      (∀ z ∈ J, a z.1 ≤ X ∧ a z.2 ≤ X) := by
  classical
  let pairRanks : ℕ → Finset (ℕ × ℕ) := fun i =>
    (coprimeOrderedPairs (T i)).image
      (fun w => (rank w.1, rank w.2))
  let J : Finset (ℕ × ℕ) := I.biUnion pairRanks
  let R : ℕ → ℕ × ℕ → Prop := fun i z => z ∈ pairRanks i
  let cap : ℕ × ℕ → ℕ := fun z => (I.filter fun i => R i z).card
  have hpairInj : ∀ i ∈ I,
      Set.InjOn (fun w : ℕ × ℕ => (rank w.1, rank w.2))
        (coprimeOrderedPairs (T i) : Set (ℕ × ℕ)) := by
    intro i hi w hw v hv heq
    have hwmem := Finset.mem_filter.mp hw
    have hvmem := Finset.mem_filter.mp hv
    have hwT := Finset.mem_offDiag.mp hwmem.1
    have hvT := Finset.mem_offDiag.mp hvmem.1
    apply Prod.ext
    · exact hrankinj i hi hwT.1 hvT.1 (congrArg Prod.fst heq)
    · exact hrankinj i hi hwT.2.1 hvT.2.1 (congrArg Prod.snd heq)
  have hpairCard : ∀ i ∈ I,
      (pairRanks i).card = (coprimeOrderedPairs (T i)).card := by
    intro i hi
    exact Finset.card_image_iff.mpr (hpairInj i hi)
  have hpairSub : ∀ i ∈ I, pairRanks i ⊆ J := by
    intro i hi z hz
    exact Finset.mem_biUnion.mpr ⟨i, hi, hz⟩
  have hw : ∀ i ∈ I,
      (gap i) ^ 2 ≤ 16 * C ^ 2 * (J.filter (R i)).card := by
    intro i hi
    have hfilter : J.filter (R i) = pairRanks i := by
      ext z
      simp only [Finset.mem_filter]
      constructor
      · exact fun hz => hz.2
      · intro hz
        exact ⟨hpairSub i hi hz, hz⟩
    rw [hfilter, hpairCard i hi]
    exact hpay i hi
  have hocc : ∀ z ∈ J,
      (I.filter fun i => R i z).card ≤ cap z := by
    intro z hz
    exact le_rfl
  have hcap : ∀ z ∈ J,
      a z.1 * a z.2 * cap z ≤
        4 * X * C * min (z.1 + 1) (z.2 + 1) +
          2 * (a z.1 * a z.2) := by
    intro z hz
    let Iz := I.filter fun i => R i z
    let w : ℕ → ℕ × ℕ := fun i => rankPairPreimage (T i) rank z
    let u : ℕ → ℕ := fun i => (w i).1
    let v : ℕ → ℕ := fun i => (w i).2
    have hiI : ∀ i ∈ Iz, i ∈ I := by
      intro i hi
      exact (Finset.mem_filter.mp hi).1
    have hiR : ∀ i ∈ Iz, R i z := by
      intro i hi
      exact (Finset.mem_filter.mp hi).2
    have hspec : ∀ i ∈ Iz,
        w i ∈ coprimeOrderedPairs (T i) ∧
          (rank (u i), rank (v i)) = z := by
      intro i hi
      exact rankPairPreimage_spec (T i) rank z (hiR i hi)
    have huT : ∀ i ∈ Iz, u i ∈ T i := by
      intro i hi
      exact (Finset.mem_offDiag.mp
        (Finset.mem_filter.mp (hspec i hi).1).1).1
    have hvT : ∀ i ∈ Iz, v i ∈ T i := by
      intro i hi
      exact (Finset.mem_offDiag.mp
        (Finset.mem_filter.mp (hspec i hi).1).1).2.1
    have hru : ∀ i ∈ Iz, rank (u i) = z.1 := by
      intro i hi
      exact congrArg Prod.fst (hspec i hi).2
    have hrv : ∀ i ∈ Iz, rank (v i) = z.2 := by
      intro i hi
      exact congrArg Prod.snd (hspec i hi).2
    have hdistGap : ∀ i ∈ Iz, Nat.dist (u i) (v i) ≤ gap i := by
      intro i hi
      have hi' := hiI i hi
      have huInt := hint i hi' (u i) (huT i hi)
      have hvInt := hint i hi' (v i) (hvT i hi)
      have hg := hgap i hi'
      rcases le_total (u i) (v i) with huv | hvu
      · rw [Nat.dist_eq_sub_of_le huv]
        omega
      · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hvu]
        omega
    have hgapD : ∀ i ∈ Iz,
        gap i ≤ C * min (z.1 + 1) (z.2 + 1) := by
      intro i hi
      have hi' := hiI i hi
      have hglt : gap i < C * (gap i / C + 1) := Nat.lt_mul_div_succ _ hC
      have hgu := hhigh i hi' (u i) (huT i hi)
      have hgv := hhigh i hi' (v i) (hvT i hi)
      rw [hru i hi] at hgu
      rw [hrv i hi] at hgv
      have hm : gap i / C + 1 ≤ min (z.1 + 1) (z.2 + 1) := by
        exact le_min (by omega) (by omega)
      exact (Nat.le_of_lt hglt).trans (Nat.mul_le_mul_left C hm)
    have haduIz : ∀ i ∈ Iz, a z.1 ∣ u i := by
      intro i hi
      have hd := hdiv i (hiI i hi) (u i) (huT i hi)
      simpa [hru i hi] using hd
    have hbdvIz : ∀ i ∈ Iz, a z.2 ∣ v i := by
      intro i hi
      have hd := hdiv i (hiI i hi) (v i) (hvT i hi)
      simpa [hrv i hi] using hd
    have hquotInj := quotient_pair_injOn_of_successive_intervals Iz
      bseq u v (a z.1) (a z.2) hb
      (fun i hi => hint i (hiI i hi) (u i) (huT i hi)) haduIz
    have hfixed := fixed_modulus_occurrence_capacity Iz u v
      (a z.1) (a z.2) X (C * min (z.1 + 1) (z.2 + 1))
      (ha z.1) (ha z.2) hX (Nat.mul_pos hC (by positivity))
      (fun i hi => lt_of_le_of_lt (Nat.zero_le _) (hint i (hiI i hi) (u i) (huT i hi)).1)
      (fun i hi => lt_of_le_of_lt (Nat.zero_le _) (hint i (hiI i hi) (v i) (hvT i hi)).1)
      haduIz hbdvIz
      (fun i hi => (Finset.mem_filter.mp (hspec i hi).1).2)
      (fun i hi => hcoordX i (hiI i hi) (u i) (huT i hi))
      (fun i hi => hcoordX i (hiI i hi) (v i) (hvT i hi))
      (fun i hi => (Finset.mem_offDiag.mp
        (Finset.mem_filter.mp (hspec i hi).1).1).2.2)
      (fun i hi => (hdistGap i hi).trans (hgapD i hi)) hquotInj
    have hfixed' : a z.1 * a z.2 * Iz.card ≤
        4 * X * C * min (z.1 + 1) (z.2 + 1) +
          2 * (a z.1 * a z.2) := by
      calc
        a z.1 * a z.2 * Iz.card ≤
            4 * X * (C * min (z.1 + 1) (z.2 + 1)) +
              2 * (a z.1 * a z.2) := hfixed
        _ = 4 * X * C * min (z.1 + 1) (z.2 + 1) +
              2 * (a z.1 * a z.2) := by ring
    simpa [cap, Iz] using hfixed'
  have hglobal := full_clique_charge_le_rankKernel I J gap cap R a
    (16 * C ^ 2) C X hw hocc ha hcap
  refine ⟨J, hglobal, ?_, ?_⟩
  · intro z hz
    rcases Finset.mem_biUnion.mp hz with ⟨i, hi, hzi⟩
    rcases Finset.mem_image.mp hzi with ⟨w, hw, rfl⟩
    have hwT := Finset.mem_offDiag.mp (Finset.mem_filter.mp hw).1
    exact ⟨(hN i hi).trans (hhigh i hi w.1 hwT.1),
      (hN i hi).trans (hhigh i hi w.2 hwT.2.1)⟩
  · intro z hz
    rcases Finset.mem_biUnion.mp hz with ⟨i, hi, hzi⟩
    rcases Finset.mem_image.mp hzi with ⟨w, hw, rfl⟩
    have hwT := Finset.mem_offDiag.mp (Finset.mem_filter.mp hw).1
    constructor
    · exact (Nat.le_of_dvd (by
        have := (hint i hi w.1 hwT.1).1
        omega) (hdiv i hi w.1 hwT.1)).trans (hcoordX i hi w.1 hwT.1)
    · exact (Nat.le_of_dvd (by
        have := (hint i hi w.2 hwT.2.1).1
        omega) (hdiv i hi w.2 hwT.2.1)).trans (hcoordX i hi w.2 hwT.2.1)

/- Consolidated from F061.PairSetCard. -/

/-- A finite pair set whose coordinates lie below `M` has at most `M²`
elements. -/
theorem pair_finset_card_le_sq
    (J : Finset (ℕ × ℕ)) (M : ℕ)
    (hJ : ∀ z ∈ J, z.1 < M ∧ z.2 < M) :
    J.card ≤ M ^ 2 := by
  have hsub : J ⊆ Finset.range M ×ˢ Finset.range M := by
    intro z hz
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (hJ z hz).1,
        Finset.mem_range.mpr (hJ z hz).2⟩
  calc
    J.card ≤ (Finset.range M ×ˢ Finset.range M).card :=
      Finset.card_le_card hsub
    _ = M ^ 2 := by simp [pow_two]

/-- Ranks of enumerated predicate elements not exceeding `X` lie below the
strict count through `X+1`. -/
theorem nth_rank_lt_count_succ_of_le
    (p : ℕ → Prop) [DecidablePred p] (hp : Set.Infinite {n | p n})
    (r X : ℕ) (hr : Nat.nth p r ≤ X) :
    r < Nat.count p (X + 1) := by
  have hcount := Nat.count_nth_succ_of_infinite hp r
  have hmono : Nat.count p (Nat.nth p r + 1) ≤ Nat.count p (X + 1) :=
    Nat.count_monotone p (by omega)
  rw [hcount] at hmono
  omega

/-- Hence a pair set whose enumerated moduli are at most `X` has at most the
square of the forbidden counting function through `X+1` elements. -/
theorem rank_pair_finset_card_le_count_sq
    (p : ℕ → Prop) [DecidablePred p] (hp : Set.Infinite {n | p n})
    (J : Finset (ℕ × ℕ)) (X : ℕ)
    (hJ : ∀ z ∈ J, Nat.nth p z.1 ≤ X ∧ Nat.nth p z.2 ≤ X) :
    J.card ≤ (Nat.count p (X + 1)) ^ 2 := by
  apply pair_finset_card_le_sq J (Nat.count p (X + 1))
  intro z hz
  exact ⟨nth_rank_lt_count_succ_of_le p hp z.1 X (hJ z hz).1,
    nth_rank_lt_count_succ_of_le p hp z.2 X (hJ z hz).2⟩

/- Consolidated from F061.SieveGaps. -/

/-- Positive integers avoiding every divisor satisfying `p`. -/
def divisorSifted (p : ℕ → Prop) (n : ℕ) : Prop :=
  0 < n ∧ ∀ a, p a → ¬a ∣ n

/-- No sifted integer lies strictly between consecutive members of the
increasing enumeration of an infinite sifted set. -/
theorem divisorSifted_consecutive_gap_covered
    (p : ℕ → Prop) [DecidablePred p]
    (hB : Set.Infinite {n | divisorSifted p n}) (i n : ℕ)
    (hleft : Nat.nth (divisorSifted p) i < n)
    (hright : n < Nat.nth (divisorSifted p) (i + 1)) :
    ∃ a, p a ∧ a ∣ n := by
  classical
  have hnpos : 0 < n :=
    lt_of_le_of_lt (Nat.zero_le _) hleft
  by_contra hnone
  push_neg at hnone
  have hnB : divisorSifted p n := ⟨hnpos, hnone⟩
  have hicount : i < Nat.count (divisorSifted p) n :=
    (Nat.lt_nth_iff_count_lt hB).2 hleft
  have hindex : i + 1 ≤ Nat.count (divisorSifted p) n := by omega
  have hmono : Nat.nth (divisorSifted p) (i + 1) ≤
      Nat.nth (divisorSifted p) (Nat.count (divisorSifted p) n) :=
    (Nat.nth_strictMono hB).monotone hindex
  have hnth : Nat.nth (divisorSifted p)
      (Nat.count (divisorSifted p) n) = n := Nat.nth_count hnB
  rw [hnth] at hmono
  exact (not_lt_of_ge hmono) hright

/-- The sifted enumeration is strictly increasing and all of its consecutive
open gaps are covered by forbidden divisors. -/
theorem divisorSifted_enumeration_structure
    (p : ℕ → Prop) [DecidablePred p]
    (hB : Set.Infinite {n | divisorSifted p n}) :
    StrictMono (Nat.nth (divisorSifted p)) ∧
      ∀ i n,
        Nat.nth (divisorSifted p) i < n →
        n < Nat.nth (divisorSifted p) (i + 1) →
        ∃ a, p a ∧ a ∣ n := by
  exact ⟨Nat.nth_strictMono hB,
    divisorSifted_consecutive_gap_covered p hB⟩

/- Consolidated from F061.ActualGapTailBound. -/

open scoped BigOperators

namespace Erdos489

noncomputable instance divisorSiftedDecidable (p : ℕ → Prop) :
    DecidablePred (divisorSifted p) := Classical.decPred _

noncomputable def divisorSiftedEnumeration (p : ℕ → Prop) : ℕ → ℕ :=
  Nat.nth (divisorSifted p)

noncomputable def divisorSiftedGap (p : ℕ → Prop) (i : ℕ) : ℕ :=
  divisorSiftedEnumeration p (i + 1) - divisorSiftedEnumeration p i

/-- Finite-prefix square-gap tails are bounded by a high-rank kernel tail plus
the square of the forbidden counting function. -/
theorem actual_long_gap_sum_bound
    (p : ℕ → Prop) [DecidablePred p] (hp : Set.Infinite {n | p n})
    (hp2 : ∀ n, p n → 2 ≤ n)
    (hB : Set.Infinite {n | divisorSifted p n})
    (ρ : ℝ) (Y Q C R H x : ℕ)
    (hQ : 1 < Q) (hY : 0 < Y) (hC : 0 < C) (hx : 0 < x)
    (hρ0 : 0 ≤ ρ)
    (hρ : ρ ≤ sieveDensity ((List.range R).map (Nat.nth p)))
    (hdensity : (4 : ℝ) / (C : ℝ) ≤ ρ / (2 * (Q : ℝ)))
    (htail : ∀ T : Finset ℕ, (∀ r ∈ T, R ≤ r) →
      (∑ r ∈ T, ((Nat.nth p r : ℝ)⁻¹)) ≤ 1 / (C : ℝ))
    (hsmall : ∀ q, Nat.Prime q → q ≤ Y → q ∣ Q)
    (hCY : 64 * C ^ 2 ≤ Q ^ 2 * Y)
    (hHperiod : 5 * (Q *
      (coprimePart ((List.range R).map (Nat.nth p)) Q).prod) ≤ H)
    (hHlarge : 256 * C ^ 2 ≤ H)
    (hmax : ∀ i, divisorSiftedEnumeration p i < x →
      divisorSiftedGap p i ≤ x) :
    ∃ J : Finset (ℕ × ℕ),
      ((∑ i ∈ (Finset.range (Nat.count (divisorSifted p) x)).filter
          (fun i => H ≤ divisorSiftedGap p i),
          (divisorSiftedGap p i) ^ 2 : ℕ) : ℝ) ≤
        ((16 * C ^ 2 : ℕ) : ℝ) *
          (8 * (x : ℝ) * (C : ℝ) *
              (∑ z ∈ J, rankPairKernel (Nat.nth p) z) +
            2 * (((Nat.count p (2 * x + 1)) ^ 2 : ℕ) : ℝ)) ∧
      (∀ z ∈ J, H / C ≤ z.1 ∧ H / C ≤ z.2) := by
  classical
  letI : DecidablePred (divisorSifted p) := Classical.decPred _
  let b := divisorSiftedEnumeration p
  let gap := divisorSiftedGap p
  let I := (Finset.range (Nat.count (divisorSifted p) x)).filter
    (fun i => H ≤ gap i)
  let rank := divisorWitnessRank p
  have hb : StrictMono b := Nat.nth_strictMono hB
  have hgapEq : ∀ i, b (i + 1) = b i + gap i := by
    intro i
    dsimp [b, gap, divisorSiftedGap, divisorSiftedEnumeration]
    exact (Nat.add_sub_of_le (hb.monotone (by omega))).symm
  have hiStart : ∀ i ∈ I, b i < x := by
    intro i hi
    have hirange := (Finset.mem_filter.mp hi).1
    exact Nat.nth_lt_of_lt_count (Finset.mem_range.mp hirange)
  have hiLong : ∀ i ∈ I, H ≤ gap i := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hex : ∀ i ∈ I, ∃ T : Finset ℕ,
      (∀ n ∈ T, b i < n ∧ n < b (i + 1)) ∧
      (∀ n ∈ T, Nat.ModEq Q n 1) ∧
      Set.InjOn rank (T : Set ℕ) ∧
      gap i / C ≤ T.card ∧
      (∀ n ∈ T, gap i / C ≤ rank n) ∧
      (∀ n ∈ T, R ≤ rank n) ∧
      (∀ n ∈ T, Nat.nth p (rank n) ∣ n) ∧
      gap i ^ 2 ≤ 16 * C ^ 2 * (coprimeOrderedPairs T).card := by
    intro i hi
    have hcovered : ∀ n, b i < n → n < b i + gap i →
        ∃ a, p a ∧ a ∣ n := by
      intro n hnL hnR
      apply divisorSifted_consecutive_gap_covered p hB i n hnL
      change n < b (i + 1)
      rw [hgapEq i]
      exact hnR
    have hperiod : 5 * (Q *
        (coprimePart ((List.range R).map (Nat.nth p)) Q).prod) ≤ gap i :=
      hHperiod.trans (hiLong i hi)
    have hlarge : 256 * C ^ 2 ≤ gap i := hHlarge.trans (hiLong i hi)
    have hfull := exists_affine_gap_full_witness p hp hp2
      R Q (b i) (gap i) C Y ρ hQ hY hC hρ0 hρ hdensity
      hperiod hcovered htail hsmall hlarge hCY
    simpa [rank, hgapEq i] using hfull
  let T : ℕ → Finset ℕ := fun i =>
    if hi : i ∈ I then Classical.choose (hex i hi) else ∅
  have hTspec : ∀ i ∈ I,
      (∀ n ∈ T i, b i < n ∧ n < b (i + 1)) ∧
      (∀ n ∈ T i, Nat.ModEq Q n 1) ∧
      Set.InjOn rank (T i : Set ℕ) ∧
      gap i / C ≤ (T i).card ∧
      (∀ n ∈ T i, gap i / C ≤ rank n) ∧
      (∀ n ∈ T i, R ≤ rank n) ∧
      (∀ n ∈ T i, Nat.nth p (rank n) ∣ n) ∧
      gap i ^ 2 ≤ 16 * C ^ 2 * (coprimeOrderedPairs (T i)).card := by
    intro i hi
    dsimp [T]
    rw [dif_pos hi]
    exact Classical.choose_spec (hex i hi)
  have ha : ∀ r, 0 < Nat.nth p r := by
    intro r
    exact lt_of_lt_of_le (by omega : 0 < 2)
      (hp2 _ (Nat.nth_mem_of_infinite hp r))
  have hcoord : ∀ i ∈ I, ∀ n ∈ T i, n ≤ 2 * x := by
    intro i hi n hn
    have hnint := (hTspec i hi).1 n hn
    have hstart := hiStart i hi
    have hgmax : gap i ≤ x := by
      apply hmax i
      simpa [b] using hstart
    rw [hgapEq i] at hnint
    omega
  have hN : ∀ i ∈ I, H / C ≤ gap i / C := by
    intro i hi
    exact Nat.div_le_div_right (hiLong i hi)
  obtain ⟨J, hbound, hJhigh, hJmod⟩ :=
    global_gap_charge_le_rankKernel I b gap T rank (Nat.nth p)
      C (2 * x) (H / C) hC (Nat.mul_pos (by omega) hx) hb
      (fun i hi => hgapEq i)
      (fun i hi => (hTspec i hi).1)
      (fun i hi => (hTspec i hi).2.2.1)
      ha
      (fun i hi => (hTspec i hi).2.2.2.2.2.2.1)
      hcoord
      (fun i hi => (hTspec i hi).2.2.2.2.1)
      hN
      (fun i hi => (hTspec i hi).2.2.2.2.2.2.2)
  have hJcard := rank_pair_finset_card_le_count_sq p hp J (2 * x) hJmod
  refine ⟨J, ?_, hJhigh⟩
  have hinside :
      4 * ((2 * x : ℕ) : ℝ) * (C : ℝ) *
          (∑ z ∈ J, rankPairKernel (Nat.nth p) z) + 2 * (J.card : ℝ) ≤
      8 * (x : ℝ) * (C : ℝ) *
          (∑ z ∈ J, rankPairKernel (Nat.nth p) z) +
        2 * (((Nat.count p (2 * x + 1)) ^ 2 : ℕ) : ℝ) := by
    have hk0 : 0 ≤ ∑ z ∈ J, rankPairKernel (Nat.nth p) z := by
      apply Finset.sum_nonneg
      intro z hz
      dsimp [rankPairKernel]
      positivity
    have hcardR : (J.card : ℝ) ≤
        (((Nat.count p (2 * x + 1)) ^ 2 : ℕ) : ℝ) := by exact_mod_cast hJcard
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    nlinarith
  have hK0 : (0 : ℝ) ≤ (16 * C ^ 2 : ℕ) := by positivity
  exact hbound.trans (mul_le_mul_of_nonneg_left hinside hK0)

end Erdos489

/- Consolidated from F061.EventualKernelTail. -/

open Filter
open scoped Topology BigOperators

/-- Eventual quadratic growth, rather than a global quadratic lower bound, is
enough for summability of the rank-pair kernel. -/
theorem summable_rankPairKernel_of_eventually_sq_le
    (a : ℕ → ℕ) (ha : ∀ n, 0 < a n)
    (hev : ∀ᶠ n : ℕ in atTop, (n + 1) ^ 2 ≤ a n) :
    Summable (rankPairKernel a) := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  let K := 1 + ∑ n ∈ Finset.range N, (n + 1) ^ 2
  have hK : 0 < K := by dsimp [K]; omega
  have hglobal : ∀ n, (n + 1) ^ 2 ≤ K * a n := by
    intro n
    by_cases hn : n < N
    · have hterm : (n + 1) ^ 2 ≤ ∑ m ∈ Finset.range N, (m + 1) ^ 2 :=
        Finset.single_le_sum
          (s := Finset.range N) (f := fun m => (m + 1) ^ 2)
          (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hn)
      have hleK : (n + 1) ^ 2 ≤ K := by dsimp [K]; omega
      have ha1 : 1 ≤ a n := ha n
      exact hleK.trans (by simpa using Nat.mul_le_mul_left K ha1)
    · have hnN : N ≤ n := by omega
      have hsq := hN n hnN
      have hmul : a n ≤ K * a n := by
        have := Nat.mul_le_mul_right (a n) (show 1 ≤ K by omega)
        simpa [Nat.mul_comm] using this
      exact hsq.trans hmul
  let A : ℕ → ℕ := fun n => K * a n
  have hsA : Summable (rankPairKernel A) :=
    summable_rankPairKernel_of_sq_le A hglobal
  have heq : ∀ z : ℕ × ℕ,
      rankPairKernel a z = (K : ℝ) ^ 2 * rankPairKernel A z := by
    intro z
    have ha1 : (0 : ℝ) < a z.1 := by exact_mod_cast ha z.1
    have ha2 : (0 : ℝ) < a z.2 := by exact_mod_cast ha z.2
    have hKR : (0 : ℝ) < K := by exact_mod_cast hK
    dsimp [rankPairKernel, A]
    norm_num only [Nat.cast_mul]
    field_simp
  apply (hsA.mul_left ((K : ℝ) ^ 2)).congr
  intro z
  exact (heq z).symm

/-- Uniform finite-set tails for the kernel under eventual quadratic growth. -/
theorem rankPairKernel_uniform_finset_tail_of_eventually
    (a : ℕ → ℕ) (ha : ∀ n, 0 < a n)
    (hev : ∀ᶠ n : ℕ in atTop, (n + 1) ^ 2 ≤ a n) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ t : Finset (ℕ × ℕ),
      (∀ z ∈ t, N ≤ z.1 ∧ N ≤ z.2) →
      ∑ z ∈ t, rankPairKernel a z < ε := by
  intro ε hε
  have hs := summable_rankPairKernel_of_eventually_sq_le a ha hev
  have hvanish := (summable_iff_vanishing.mp hs)
    (Metric.ball (0 : ℝ) ε) (Metric.ball_mem_nhds 0 hε)
  obtain ⟨core, hcore⟩ := hvanish
  let N : ℕ := ∑ z ∈ core, (z.1 + z.2 + 1)
  have hcoord : ∀ z ∈ core, z.1 < N ∧ z.2 < N := by
    intro z hz
    have hterm : z.1 + z.2 + 1 ≤ N := by
      dsimp [N]
      exact Finset.single_le_sum
        (s := core) (f := fun w : ℕ × ℕ => w.1 + w.2 + 1)
        (fun _ _ => Nat.zero_le _) hz
    omega
  refine ⟨N, ?_⟩
  intro t ht
  have hdisj : Disjoint t core := by
    rw [Finset.disjoint_left]
    intro z hzt hzc
    have := ht z hzt
    have := hcoord z hzc
    omega
  have hball := hcore t hdisj
  rw [Metric.mem_ball, Real.dist_eq] at hball
  have hnonneg : 0 ≤ ∑ z ∈ t, rankPairKernel a z := by
    apply Finset.sum_nonneg
    intro z hz
    dsimp [rankPairKernel]
    positivity
  have habs : |∑ z ∈ t, rankPairKernel a z| < ε := by simpa using hball
  exact (abs_lt.mp habs).2

/- Consolidated from F061.EndpointCountTail. -/

open Filter
open scoped Topology

/-- Square-root thinness makes the squared forbidden count at `2x+1`
negligible compared with `x`. -/
theorem tendsto_count_two_mul_add_one_sq_div
    (p : ℕ → Prop) [DecidablePred p]
    (hcount : (fun n : ℕ => (Nat.count p n : ℝ)) =o[atTop]
      (fun n : ℕ => Real.sqrt (n : ℝ))) :
    Tendsto (fun x : ℕ =>
      (Nat.count p (2 * x + 1) : ℝ) ^ 2 / (x : ℝ))
      atTop (𝓝 0) := by
  let g : ℕ → ℕ := fun x => 2 * x + 1
  have hgmono : StrictMono g := by
    intro x y hxy
    dsimp [g]
    omega
  have hg : Tendsto g atTop atTop := hgmono.tendsto_atTop
  have hr := (hcount.comp_tendsto hg).tendsto_div_nhds_zero
  have hinv : Tendsto (fun x : ℕ => ((x : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun x : ℕ => ((g x : ℕ) : ℝ) / (x : ℝ))
      atTop (𝓝 2) := by
    have hbase : Tendsto (fun x : ℕ => (2 : ℝ) + ((x : ℝ))⁻¹)
        atTop (𝓝 ((2 : ℝ) + 0)) := tendsto_const_nhds.add hinv
    have hbase' : Tendsto (fun x : ℕ => (2 : ℝ) + ((x : ℝ))⁻¹)
        atTop (𝓝 2) := by simpa using hbase
    refine hbase'.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with x hx
    dsimp [g]
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
    field_simp
  have hprod := (hr.pow 2).mul hratio
  have hzero : (0 : ℝ) ^ 2 * 2 = 0 := by norm_num
  rw [hzero] at hprod
  apply hprod.congr'
  filter_upwards [eventually_ge_atTop 1] with x hx
  dsimp [g]
  have hgpos : (0 : ℝ) < (2 * x + 1 : ℕ) := by positivity
  have hsqrt : (Real.sqrt ((2 * x + 1 : ℕ) : ℝ)) ^ 2 =
      ((2 * x + 1 : ℕ) : ℝ) := Real.sq_sqrt hgpos.le
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  field_simp [Real.sqrt_ne_zero'.mpr hgpos, hxpos.ne']
  nlinarith

/- Consolidated from F061.UniformGapTail. -/

open Filter
open scoped Topology BigOperators

namespace Erdos489

/-- The normalized square mass of sufficiently long actual sifted gaps is
uniformly small on all sufficiently large prefixes. -/
theorem uniform_long_gap_square_tail
    (p : ℕ → Prop) [DecidablePred p] (hp : Set.Infinite {n | p n})
    (hp2 : ∀ n, p n → 2 ≤ n)
    (hB : Set.Infinite {n | divisorSifted p n})
    (hs : Summable fun n => ((Nat.nth p n : ℝ)⁻¹))
    (hev : ∀ᶠ n : ℕ in atTop, (n + 1) ^ 2 ≤ Nat.nth p n)
    (hcount : (fun n : ℕ => (Nat.count p n : ℝ)) =o[atTop]
      (fun n : ℕ => Real.sqrt (n : ℝ))) :
    ∀ ε : ℝ, 0 < ε → ∃ H : ℕ, ∀ᶠ x : ℕ in atTop,
      (((∑ i ∈ (Finset.range (Nat.count (divisorSifted p) x)).filter
          (fun i => H ≤ divisorSiftedGap p i),
          (divisorSiftedGap p i) ^ 2 : ℕ) : ℝ) / (x : ℝ)) < ε := by
  intro ε hε
  have ha2 : ∀ n, 2 ≤ Nat.nth p n := by
    intro n
    exact hp2 _ (Nat.nth_mem_of_infinite hp n)
  obtain ⟨ρ, Y, Q, C, R, hρpos, hρ1, hY, hQ, hC, hsmall,
      hdensity, hCY, hRdensity, hRtail⟩ :=
    exists_sieve_parameter_bundle (Nat.nth p) ha2 hs
  let H0 := max
    (5 * (Q * (coprimePart ((List.range R).map (Nat.nth p)) Q).prod))
    (256 * C ^ 2)
  let b := divisorSiftedEnumeration p
  let gap := divisorSiftedGap p
  let rank := divisorWitnessRank p
  have hb : StrictMono b := Nat.nth_strictMono hB
  have hgapEq : ∀ i, b (i + 1) = b i + gap i := by
    intro i
    dsimp [b, gap, divisorSiftedGap, divisorSiftedEnumeration]
    exact (Nat.add_sub_of_le (hb.monotone (by omega))).symm
  have hwitness : ∀ i, H0 ≤ gap i →
      ∃ T : Finset ℕ, Set.InjOn rank (T : Set ℕ) ∧
        gap i / C ≤ T.card ∧
        (∀ n ∈ T, b i < n ∧ n < b (i + 1)) ∧
        (∀ n ∈ T, Nat.nth p (rank n) ∣ n) := by
    intro i hi
    have hperiod : 5 * (Q *
        (coprimePart ((List.range R).map (Nat.nth p)) Q).prod) ≤ gap i :=
      (le_max_left _ _).trans hi
    have hlarge : 256 * C ^ 2 ≤ gap i :=
      (le_max_right _ _).trans hi
    have hcovered : ∀ n, b i < n → n < b i + gap i →
        ∃ a, p a ∧ a ∣ n := by
      intro n hnL hnR
      apply divisorSifted_consecutive_gap_covered p hB i n hnL
      change n < b (i + 1)
      rw [hgapEq i]
      exact hnR
    obtain ⟨T, hint, hcong, hinj, hcard, hhigh, htailrank, hdiv, hpay⟩ :=
      exists_affine_gap_full_witness p hp hp2 R Q (b i) (gap i) C Y ρ
        hQ hY hC hρpos.le hRdensity hdensity hperiod hcovered hRtail
        hsmall hlarge hCY
    have hint' : ∀ n ∈ T, b i < n ∧ n < b (i + 1) := by
      intro n hn
      have hni := hint n hn
      rw [hgapEq i]
      exact hni
    exact ⟨T, hinj, hcard, hint', hdiv⟩
  have hcountLinEv := eventually_mul_count_le_of_isLittleO_sqrt
    p hcount (8 * C) (Nat.mul_pos (by omega) hC)
  obtain ⟨Ncount, hNcount⟩ := Filter.eventually_atTop.mp hcountLinEv
  let X0 := max (max H0 Ncount) (2 * C)
  have hmaxEventually : ∀ᶠ x : ℕ in atTop,
      ∀ i, b i < x → gap i ≤ x := by
    filter_upwards [eventually_ge_atTop X0] with x hx
    have hx' : max (max H0 Ncount) (2 * C) ≤ x := by
      simpa [X0] using hx
    exact eventual_gap_le_prefix p hp b gap rank C H0 Ncount hC
      hgapEq hNcount hwitness x hx'
  let K0 : ℝ := (16 * C ^ 2 : ℕ)
  have hK0 : 0 < K0 := by dsimp [K0]; positivity
  have hCR : (0 : ℝ) < C := by exact_mod_cast hC
  let δk := ε / (4 * K0 * (8 * (C : ℝ)))
  let δe := ε / (4 * K0 * 2)
  have hδk : 0 < δk := by dsimp [δk]; positivity
  have hδe : 0 < δe := by dsimp [δe]; positivity
  have haPos : ∀ n, 0 < Nat.nth p n := by
    intro n
    exact lt_of_lt_of_le (by omega : 0 < 2) (ha2 n)
  obtain ⟨Nk, hNk⟩ :=
    rankPairKernel_uniform_finset_tail_of_eventually
      (Nat.nth p) haPos hev δk hδk
  let H := max H0 (C * Nk)
  have hHperiod : 5 * (Q *
      (coprimePart ((List.range R).map (Nat.nth p)) Q).prod) ≤ H :=
    (le_max_left _ _).trans (le_max_left _ _)
  have hHlarge : 256 * C ^ 2 ≤ H :=
    (le_max_right _ _).trans (le_max_left _ _)
  have hNkHC : Nk ≤ H / C := by
    apply (Nat.le_div_iff_mul_le hC).2
    change Nk * C ≤ max H0 (C * Nk)
    rw [Nat.mul_comm]
    exact le_max_right H0 (C * Nk)
  have hendTend := tendsto_count_two_mul_add_one_sq_div p hcount
  have hendEv : ∀ᶠ x : ℕ in atTop,
      (Nat.count p (2 * x + 1) : ℝ) ^ 2 / (x : ℝ) < δe :=
    (tendsto_order.1 hendTend).2 δe hδe
  refine ⟨H, ?_⟩
  filter_upwards [hmaxEventually, hendEv, eventually_ge_atTop 1] with x hmaxx hendx hx
  have hxpos : 0 < x := by omega
  obtain ⟨J, hbound, hJhigh⟩ := actual_long_gap_sum_bound
    p hp hp2 hB ρ Y Q C R H x hQ hY hC hxpos hρpos.le
    hRdensity hdensity hRtail hsmall hCY hHperiod hHlarge
    (by simpa [b, gap] using hmaxx)
  have hkern : (∑ z ∈ J, rankPairKernel (Nat.nth p) z) < δk := by
    apply hNk J
    intro z hz
    have hzH := hJhigh z hz
    exact ⟨hNkHC.trans hzH.1, hNkHC.trans hzH.2⟩
  have hxR : (0 : ℝ) < x := by exact_mod_cast hxpos
  have hdivbound := div_le_div_of_nonneg_right hbound hxR.le
  have hnormalized :
      ((∑ i ∈ (Finset.range (Nat.count (divisorSifted p) x)).filter
          (fun i => H ≤ divisorSiftedGap p i),
          (divisorSiftedGap p i) ^ 2 : ℕ) : ℝ) / (x : ℝ) ≤
        K0 * (8 * (C : ℝ) *
            (∑ z ∈ J, rankPairKernel (Nat.nth p) z) +
          2 * ((Nat.count p (2 * x + 1) : ℝ) ^ 2 / (x : ℝ))) := by
    dsimp [K0]
    calc
      _ ≤ (((16 * C ^ 2 : ℕ) : ℝ) *
          (8 * (x : ℝ) * (C : ℝ) *
              (∑ z ∈ J, rankPairKernel (Nat.nth p) z) +
            2 * (((Nat.count p (2 * x + 1)) ^ 2 : ℕ) : ℝ))) / (x : ℝ) :=
        hdivbound
      _ = ((16 * C ^ 2 : ℕ) : ℝ) *
          (8 * (C : ℝ) *
              (∑ z ∈ J, rankPairKernel (Nat.nth p) z) +
            2 * ((Nat.count p (2 * x + 1) : ℝ) ^ 2 / (x : ℝ))) := by
        norm_num only [Nat.cast_pow]
        field_simp
  have hkMul := mul_lt_mul_of_pos_left hkern
    (mul_pos hK0 (by positivity : (0 : ℝ) < 8 * C))
  have heMul := mul_lt_mul_of_pos_left hendx
    (mul_pos hK0 (by norm_num : (0 : ℝ) < 2))
  have hidk : (K0 * (8 * (C : ℝ))) * δk = ε / 4 := by
    dsimp [δk]
    field_simp
  have hide : (K0 * 2) * δe = ε / 4 := by
    dsimp [δe]
    field_simp
  rw [hidk] at hkMul
  rw [hide] at heMul
  have hkern0 : 0 ≤ ∑ z ∈ J, rankPairKernel (Nat.nth p) z := by
    apply Finset.sum_nonneg
    intro z hz
    dsimp [rankPairKernel]
    positivity
  have hend0 : 0 ≤ (Nat.count p (2 * x + 1) : ℝ) ^ 2 / (x : ℝ) := by positivity
  ring_nf at hnormalized hkMul heMul ⊢
  linarith

end Erdos489

/- Consolidated from F061.TruncatedGapCost. -/

open scoped BigOperators

/-- A gap of exact length `d` starts at `n` for predicate `q`. -/
def gapPattern (q : ℕ → Prop) (d n : ℕ) : Prop :=
  q n ∧ q (n + d) ∧ ∀ k, 0 < k → k < d → ¬q (n + k)

/-- Local squared-gap cost, truncated to lengths below `H`. -/
noncomputable def truncatedGapCost (q : ℕ → Prop) (H n : ℕ) : ℕ := by
  classical
  exact ∑ d ∈ Finset.Ico 1 H, if gapPattern q d n then d ^ 2 else 0

/-- There is no predicate member strictly between consecutive terms of an
infinite predicate enumeration. -/
theorem nth_consecutive_no_mem
    (q : ℕ → Prop) [DecidablePred q] (hq : Set.Infinite {n | q n})
    (i n : ℕ) (hleft : Nat.nth q i < n)
    (hright : n < Nat.nth q (i + 1)) : ¬q n := by
  intro hn
  have hicount : i < Nat.count q n := (Nat.lt_nth_iff_count_lt hq).2 hleft
  have hidx : i + 1 ≤ Nat.count q n := by omega
  have hmono : Nat.nth q (i + 1) ≤ Nat.nth q (Nat.count q n) :=
    (Nat.nth_strictMono hq).monotone hidx
  have hnth : Nat.nth q (Nat.count q n) = n := Nat.nth_count hn
  rw [hnth] at hmono
  exact (not_lt_of_ge hmono) hright

/-- On an enumerated predicate point, the exact-gap word is equivalent to the
successive enumerated gap having that length. -/
theorem gapPattern_nth_iff_gap_eq
    (q : ℕ → Prop) [DecidablePred q] (hq : Set.Infinite {n | q n})
    (i d : ℕ) (hd : 0 < d) :
    gapPattern q d (Nat.nth q i) ↔
      Nat.nth q (i + 1) - Nat.nth q i = d := by
  have hbmono : StrictMono (Nat.nth q) := Nat.nth_strictMono hq
  have hbi : q (Nat.nth q i) := Nat.nth_mem_of_infinite hq i
  have hbi1 : q (Nat.nth q (i + 1)) := Nat.nth_mem_of_infinite hq (i + 1)
  constructor
  · rintro ⟨_, hend, hinterior⟩
    have hilt : Nat.nth q i < Nat.nth q i + d := by omega
    have hicount : i < Nat.count q (Nat.nth q i + d) :=
      (Nat.lt_nth_iff_count_lt hq).2 hilt
    have hidx : i + 1 ≤ Nat.count q (Nat.nth q i + d) := by omega
    have hnextle : Nat.nth q (i + 1) ≤ Nat.nth q i + d := by
      have hm : Nat.nth q (i + 1) ≤
          Nat.nth q (Nat.count q (Nat.nth q i + d)) :=
        hbmono.monotone hidx
      have hnth : Nat.nth q (Nat.count q (Nat.nth q i + d)) =
          Nat.nth q i + d := Nat.nth_count hend
      rwa [hnth] at hm
    have hnextge : Nat.nth q i + d ≤ Nat.nth q (i + 1) := by
      by_contra hnot
      have hstrict : Nat.nth q (i + 1) < Nat.nth q i + d := by omega
      let k := Nat.nth q (i + 1) - Nat.nth q i
      have hstep := hbmono (by omega : i < i + 1)
      have hkpos : 0 < k := Nat.sub_pos_of_lt hstep
      have hklt : k < d := by dsimp [k]; omega
      have hsum : Nat.nth q i + k = Nat.nth q (i + 1) := by
        dsimp [k]
        exact Nat.add_sub_of_le hstep.le
      exact hinterior k hkpos hklt (hsum ▸ hbi1)
    have heq : Nat.nth q (i + 1) = Nat.nth q i + d :=
      le_antisymm hnextle hnextge
    omega
  · intro hgap
    have hstep := hbmono (by omega : i < i + 1)
    have heq : Nat.nth q (i + 1) = Nat.nth q i + d := by omega
    refine ⟨hbi, ?_, ?_⟩
    · rw [← heq]
      exact hbi1
    · intro k hk0 hkd hkq
      apply nth_consecutive_no_mem q hq i (Nat.nth q i + k)
      · omega
      · rw [heq]
        omega
      · exact hkq

/-- The local truncated cost at the `i`-th predicate member is exactly the
square of its next gap when that gap is below `H`, and zero otherwise. -/
theorem truncatedGapCost_nth
    (q : ℕ → Prop) [DecidablePred q] (hq : Set.Infinite {n | q n})
    (H i : ℕ) :
    truncatedGapCost q H (Nat.nth q i) =
      if Nat.nth q (i + 1) - Nat.nth q i < H then
        (Nat.nth q (i + 1) - Nat.nth q i) ^ 2 else 0 := by
  classical
  let g := Nat.nth q (i + 1) - Nat.nth q i
  have hg : 0 < g := Nat.sub_pos_of_lt (Nat.nth_strictMono hq (by omega))
  by_cases hgH : g < H
  · rw [if_pos hgH]
    unfold truncatedGapCost
    have hgmem : g ∈ Finset.Ico 1 H := Finset.mem_Ico.mpr ⟨hg, hgH⟩
    rw [Finset.sum_eq_single g]
    · rw [if_pos]
      exact gapPattern_nth_iff_gap_eq q hq i g hg |>.2 rfl
    · intro d hdmem hdne
      rw [if_neg]
      intro hpat
      have heq := (gapPattern_nth_iff_gap_eq q hq i d
        (by exact (Finset.mem_Ico.mp hdmem).1)).1 hpat
      exact hdne heq.symm
    · exact fun h => (h hgmem).elim
  · rw [if_neg hgH]
    unfold truncatedGapCost
    apply Finset.sum_eq_zero
    intro d hdmem
    rw [if_neg]
    intro hpat
    have heq := (gapPattern_nth_iff_gap_eq q hq i d
      (Finset.mem_Ico.mp hdmem).1).1 hpat
    have hdH := (Finset.mem_Ico.mp hdmem).2
    omega

/-- A local cost vanishes away from predicate members. -/
theorem truncatedGapCost_eq_zero_of_not
    (q : ℕ → Prop) (H n : ℕ) (hn : ¬q n) :
    truncatedGapCost q H n = 0 := by
  classical
  unfold truncatedGapCost
  apply Finset.sum_eq_zero
  intro d hd
  rw [if_neg]
  exact fun h => hn h.1

/-- Exact-gap words inherit every period of the underlying predicate. -/
theorem gapPattern_periodic
    (q : ℕ → Prop) (P d : ℕ) (hq : Function.Periodic q P) :
    Function.Periodic (gapPattern q d) P := by
  intro n
  apply propext
  constructor
  · rintro ⟨hn, hend, hint⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa using hq n ▸ hn
    · have hp := hq (n + d)
      rw [show n + P + d = n + d + P by omega] at hend
      exact hp ▸ hend
    · intro k hk0 hkd
      have hp := hq (n + k)
      have hh := hint k hk0 hkd
      rw [show n + P + k = n + k + P by omega] at hh
      exact hp ▸ hh
  · rintro ⟨hn, hend, hint⟩
    refine ⟨?_, ?_, ?_⟩
    · exact hq n ▸ hn
    · have hp := hq (n + d)
      rw [show n + P + d = n + d + P by omega]
      exact hp.symm ▸ hend
    · intro k hk0 hkd
      have hp := hq (n + k)
      rw [show n + P + k = n + k + P by omega]
      exact hp.symm ▸ hint k hk0 hkd

/-- Truncated local gap cost inherits every period of the predicate. -/
theorem truncatedGapCost_periodic
    (q : ℕ → Prop) (H P : ℕ) (hq : Function.Periodic q P) :
    Function.Periodic (truncatedGapCost q H) P := by
  intro n
  unfold truncatedGapCost
  apply Finset.sum_congr rfl
  intro d hd
  have hp := gapPattern_periodic q P d hq n
  rw [hp]

/-- Agreement of two predicates throughout the inspected window forces equal
local truncated costs. -/
theorem truncatedGapCost_eq_of_window_agree
    (q r : ℕ → Prop) (H n : ℕ)
    (hagree : ∀ k, k ≤ H → (q (n + k) ↔ r (n + k))) :
    truncatedGapCost q H n = truncatedGapCost r H n := by
  classical
  unfold truncatedGapCost
  apply Finset.sum_congr rfl
  intro d hd
  have hdH := (Finset.mem_Ico.mp hd).2
  congr 1
  apply propext
  constructor
  · rintro ⟨hn, hend, hint⟩
    refine ⟨(by simpa using (hagree 0 (Nat.zero_le H)).mp hn),
      (hagree d hdH.le).mp hend, ?_⟩
    intro k hk0 hkd
    exact fun hk => hint k hk0 hkd ((hagree k (by omega)).mpr hk)
  · rintro ⟨hn, hend, hint⟩
    refine ⟨(by simpa using (hagree 0 (Nat.zero_le H)).mpr hn),
      (hagree d hdH.le).mpr hend, ?_⟩
    intro k hk0 hkd
    exact fun hk => hint k hk0 hkd ((hagree k (by omega)).mp hk)

/-- A crude uniform bound sufficient for approximation arguments. -/
theorem truncatedGapCost_le_cube (q : ℕ → Prop) (H n : ℕ) :
    truncatedGapCost q H n ≤ H ^ 3 := by
  classical
  unfold truncatedGapCost
  calc
    (∑ d ∈ Finset.Ico 1 H, if gapPattern q d n then d ^ 2 else 0) ≤
        ∑ d ∈ Finset.Ico 1 H, H ^ 2 := by
      apply Finset.sum_le_sum
      intro d hd
      split_ifs
      · exact Nat.pow_le_pow_left (Finset.mem_Ico.mp hd).2.le 2
      · exact Nat.zero_le _
    _ = (Finset.Ico 1 H).card * H ^ 2 := by simp
    _ ≤ H * H ^ 2 := by
      apply Nat.mul_le_mul_right
      simp
    _ = H ^ 3 := by ring

/-- Predicate members below `x` are exactly the image of enumeration indices
below the strict count at `x`. -/
theorem image_nth_range_count
    (q : ℕ → Prop) [DecidablePred q] (hq : Set.Infinite {n | q n}) (x : ℕ) :
    (Finset.range (Nat.count q x)).image (Nat.nth q) =
      (Finset.range x).filter q := by
  ext n
  constructor
  · intro hn
    rcases Finset.mem_image.mp hn with ⟨i, hi, rfl⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr
      (Nat.nth_lt_of_lt_count (Finset.mem_range.mp hi)),
      Nat.nth_mem_of_infinite hq i⟩
  · intro hn
    have hnr := Finset.mem_range.mp (Finset.mem_filter.mp hn).1
    have hnq := (Finset.mem_filter.mp hn).2
    apply Finset.mem_image.mpr
    refine ⟨Nat.count q n, Finset.mem_range.mpr ?_, Nat.nth_count hnq⟩
    exact Nat.count_strict_mono hnq hnr

/-- Summing local truncated costs over integer starts equals summing squared
short gaps over enumeration indices. -/
theorem sum_truncatedGapCost_eq_gap_sum
    (q : ℕ → Prop) [DecidablePred q] (hq : Set.Infinite {n | q n})
    (H x : ℕ) :
    ∑ n ∈ Finset.range x, truncatedGapCost q H n =
      ∑ i ∈ (Finset.range (Nat.count q x)).filter
        (fun i => Nat.nth q (i + 1) - Nat.nth q i < H),
        (Nat.nth q (i + 1) - Nat.nth q i) ^ 2 := by
  classical
  let S := Finset.range (Nat.count q x)
  let B := (Finset.range x).filter q
  have hfilter : (∑ n ∈ B, truncatedGapCost q H n) =
      ∑ n ∈ Finset.range x, truncatedGapCost q H n := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hnx hnB
    apply truncatedGapCost_eq_zero_of_not q H n
    intro hnq
    exact hnB (Finset.mem_filter.mpr ⟨hnx, hnq⟩)
  have himage : S.image (Nat.nth q) = B := by
    simpa [S, B] using image_nth_range_count q hq x
  rw [← hfilter, ← himage, Finset.sum_image]
  · rw [Finset.sum_filter]
    change (∑ i ∈ S, truncatedGapCost q H (Nat.nth q i)) =
      ∑ i ∈ S, if Nat.nth q (i + 1) - Nat.nth q i < H then
        (Nat.nth q (i + 1) - Nat.nth q i) ^ 2 else 0
    apply Finset.sum_congr rfl
    intro i hi
    rw [truncatedGapCost_nth q hq]
  · exact (Nat.nth_injective hq).injOn

/- Consolidated from F061.FiniteSieveApproximation. -/

open scoped BigOperators
namespace Erdos489

/-- Avoid the first `R` enumerated forbidden moduli. -/
def finiteDivisorSifted (p : ℕ → Prop) (R n : ℕ) : Prop :=
  ∀ a ∈ (List.range R).map (Nat.nth p), ¬a ∣ n

noncomputable instance finiteDivisorSiftedDecidable
    (p : ℕ → Prop) (R : ℕ) : DecidablePred (finiteDivisorSifted p R) :=
  Classical.decPred _

 theorem finiteDivisorSifted_periodic (p : ℕ → Prop) (R : ℕ) :
    Function.Periodic (finiteDivisorSifted p R)
      ((List.range R).map (Nat.nth p)).prod :=
  avoidList_periodic _

 theorem divisorSifted_imp_finite (p : ℕ → Prop) [DecidablePred p]
    (hp : Set.Infinite {n | p n}) (R n : ℕ) :
    divisorSifted p n → finiteDivisorSifted p R n := by
  intro hn a ha
  rcases List.mem_map.mp ha with ⟨r, hr, rfl⟩
  exact hn.2 _ (Nat.nth_mem_of_infinite hp r)

 theorem finiteDivisorSifted_pos
    (p : ℕ → Prop) [DecidablePred p] (hp : Set.Infinite {n | p n})
    (hp2 : ∀ n, p n → 2 ≤ n) (R n : ℕ) (hR : 0 < R)
    (hn : finiteDivisorSifted p R n) : 0 < n := by
  by_contra hn0
  have heq : n = 0 := by omega
  have hmem : Nat.nth p 0 ∈ (List.range R).map (Nat.nth p) :=
    List.mem_map.mpr ⟨0, List.mem_range.mpr hR, rfl⟩
  apply hn (Nat.nth p 0) hmem
  rw [heq]
  exact dvd_zero _

/-- Prefix/full disagreement points below `M`. -/
noncomputable def sieveMismatch (p : ℕ → Prop) (R M : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range M).filter fun n =>
    finiteDivisorSifted p R n ∧ ¬divisorSifted p n

 theorem sieveMismatch_card_cast_le
    (p : ℕ → Prop) [DecidablePred p] (hp : Set.Infinite {n | p n})
    (hp2 : ∀ n, p n → 2 ≤ n)
    (R M : ℕ) (hR : 0 < R) (ε : ℝ)
    (htail : ∀ T : Finset ℕ, (∀ r ∈ T, R ≤ r) →
      (∑ r ∈ T, ((Nat.nth p r : ℝ)⁻¹)) ≤ ε) :
    ((sieveMismatch p R M).card : ℝ) ≤
      (M : ℝ) * ε + (Nat.count p M : ℝ) := by
  classical
  let S := sieveMismatch p R M
  let rank := divisorWitnessRank p
  let a := Nat.nth p
  have hinterval : ∀ n ∈ S, 0 ≤ n ∧ n ≤ 0 + M := by
    intro n hn
    have hh : n ∈ sieveMismatch p R M := by simpa [S] using hn
    have hnr := Finset.mem_range.mp (Finset.mem_filter.mp hh).1
    omega
  have hfinite : ∀ n ∈ S, finiteDivisorSifted p R n := by
    intro n hn
    have hh : n ∈ sieveMismatch p R M := by simpa [S] using hn
    exact (Finset.mem_filter.mp hh).2.1
  have hnotfull : ∀ n ∈ S, ¬divisorSifted p n := by
    intro n hn
    have hh : n ∈ sieveMismatch p R M := by simpa [S] using hn
    exact (Finset.mem_filter.mp hh).2.2
  have hpos : ∀ n ∈ S, 0 < n := by
    intro n hn
    exact finiteDivisorSifted_pos p hp hp2 R n hR (hfinite n hn)
  have hcov : ∀ n ∈ S, ∃ d, p d ∧ d ∣ n := by
    intro n hn
    have hnf := hnotfull n hn
    rw [divisorSifted] at hnf
    push_neg at hnf
    exact hnf (hpos n hn)
  have hdvd : ∀ n ∈ S, a (rank n) ∣ n := by
    intro n hn
    exact nth_divisorWitnessRank_dvd p n (hcov n hn)
  have hrank : ∀ n ∈ S, R ≤ rank n := by
    intro n hn
    apply le_divisorWitnessRank_of_avoid_prefix p n R (hcov n hn)
    exact hfinite n hn
  have hmass : (∑ r ∈ S.image rank, ((a r : ℝ)⁻¹)) ≤ ε := by
    apply htail
    intro r hr
    rcases Finset.mem_image.mp hr with ⟨n, hn, rfl⟩
    exact hrank n hn
  have ha : ∀ r, 0 < a r := by
    intro r
    dsimp [a]
    have hh := hp2 _ (Nat.nth_mem_of_infinite hp r)
    exact lt_of_lt_of_le (by omega : 0 < 2) hh
  have hcharge0 := interval_label_card_le_reciprocal_mass
    S 0 M a rank ha hinterval hdvd
  have hcharge : (S.card : ℝ) ≤
      (M : ℝ) * ε + ((S.image rank).card : ℝ) := by
    calc
      (S.card : ℝ) ≤ (M : ℝ) *
          (∑ r ∈ S.image rank, ((a r : ℝ)⁻¹)) + (S.image rank).card := hcharge0
      _ ≤ (M : ℝ) * ε + (S.image rank).card := by gcongr
  have himage : (S.image rank).card ≤ Nat.count p M := by
    have hsubset : S.image rank ⊆ Finset.range (Nat.count p M) := by
      intro r hr
      apply Finset.mem_range.mpr
      rcases Finset.mem_image.mp hr with ⟨n, hn, rfl⟩
      have hh : n ∈ sieveMismatch p R M := by simpa [S] using hn
      have hnM := Finset.mem_range.mp (Finset.mem_filter.mp hh).1
      have hale : a (rank n) ≤ n := Nat.le_of_dvd (hpos n hn) (hdvd n hn)
      exact (Nat.lt_nth_iff_count_lt hp).2 (lt_of_le_of_lt hale hnM)
    simpa using Finset.card_le_card hsubset
  dsimp [S] at hcharge ⊢
  calc
    ((sieveMismatch p R M).card : ℝ) ≤
        (M : ℝ) * ε + ((sieveMismatch p R M).image rank).card := by
      simpa using hcharge
    _ ≤ (M : ℝ) * ε + (Nat.count p M : ℝ) := by
      gcongr

/-- Starts below `x` whose length-`H` window contains a finite/full sieve
mismatch. -/
noncomputable def badGapStarts (p : ℕ → Prop) (R H x : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (H + 1)).biUnion fun k =>
    (Finset.range x).filter fun n => n + k ∈ sieveMismatch p R (x + H + 1)

 theorem badGapStarts_subset_range (p : ℕ → Prop) (R H x : ℕ) :
    badGapStarts p R H x ⊆ Finset.range x := by
  classical
  intro n hn
  rcases Finset.mem_biUnion.mp hn with ⟨k, hk, hnk⟩
  exact (Finset.mem_filter.mp hnk).1

 theorem badGapStarts_card_le (p : ℕ → Prop) (R H x : ℕ) :
    (badGapStarts p R H x).card ≤
      (H + 1) * (sieveMismatch p R (x + H + 1)).card := by
  classical
  unfold badGapStarts
  have hfiber : ∀ k ∈ Finset.range (H + 1),
      ((Finset.range x).filter fun n =>
        n + k ∈ sieveMismatch p R (x + H + 1)).card ≤
          (sieveMismatch p R (x + H + 1)).card := by
    intro k hk
    let T := (Finset.range x).filter fun n =>
      n + k ∈ sieveMismatch p R (x + H + 1)
    have himage : T.image (fun n => n + k) ⊆
        sieveMismatch p R (x + H + 1) := by
      intro m hm
      rcases Finset.mem_image.mp hm with ⟨n, hn, rfl⟩
      exact (Finset.mem_filter.mp hn).2
    calc
      ((Finset.range x).filter fun n =>
          n + k ∈ sieveMismatch p R (x + H + 1)).card = T.card := rfl
      _ = (T.image (fun n => n + k)).card :=
        (Finset.card_image_of_injective T (add_left_injective k)).symm
      _ ≤ (sieveMismatch p R (x + H + 1)).card :=
        Finset.card_le_card himage
  have h := Finset.card_biUnion_le_card_mul (Finset.range (H + 1))
    (fun k => (Finset.range x).filter fun n =>
      n + k ∈ sieveMismatch p R (x + H + 1))
    (sieveMismatch p R (x + H + 1)).card hfiber
  simpa using h

/-- Outside `badGapStarts`, full and finite sieves agree throughout the
window inspected by the truncated cost. -/
theorem sieve_window_agree_of_not_bad
    (p : ℕ → Prop) [DecidablePred p]
    (hp : Set.Infinite {n | p n}) (R H x n : ℕ)
    (hnx : n < x) (hgood : n ∉ badGapStarts p R H x) :
    ∀ k, k ≤ H →
      (divisorSifted p (n + k) ↔ finiteDivisorSifted p R (n + k)) := by
  classical
  intro k hk
  have hkRange : k ∈ Finset.range (H + 1) := Finset.mem_range.mpr (by omega)
  constructor
  · exact divisorSifted_imp_finite p hp R (n + k)
  · intro hfinite
    by_contra hfull
    have hm : n + k ∈ sieveMismatch p R (x + H + 1) := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_range.mpr (by omega), hfinite, hfull⟩
    apply hgood
    apply Finset.mem_biUnion.mpr
    exact ⟨k, hkRange, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hnx, hm⟩⟩

end Erdos489

/- Consolidated from F061.PeriodicAverage. -/

open Filter
open scoped Topology BigOperators

/-- Sum over an integral number of periods. -/
theorem sum_range_mul_periodic
    (f : ℕ → ℕ) (P : ℕ) (hf : Function.Periodic f P) (q : ℕ) :
    ∑ n ∈ Finset.range (q * P), f n =
      q * ∑ n ∈ Finset.range P, f n := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Nat.succ_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    simpa [Nat.add_comm, Nat.mul_comm] using (hf.nat_mul q n)

/-- Quotient/remainder decomposition of a periodic partial sum. -/
theorem sum_range_periodic_div_mod
    (f : ℕ → ℕ) (P x : ℕ) (hf : Function.Periodic f P) :
    ∑ n ∈ Finset.range x, f n =
      (x / P) * (∑ n ∈ Finset.range P, f n) +
        ∑ n ∈ Finset.range (x % P), f n := by
  by_cases hP : P = 0
  · subst P
    simp
  · have hx : x = (x / P) * P + x % P := by
      simpa [Nat.mul_comm, Nat.add_comm] using (Nat.mod_add_div x P).symm
    conv_lhs => rw [hx]
    rw [Finset.sum_range_add, sum_range_mul_periodic f P hf]
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    simpa [Nat.mul_comm, Nat.add_comm] using (hf.nat_mul (x / P) n)

/-- The real quotient `(x/P)/x` tends to `1/P`. -/
theorem tendsto_nat_div_cast_div (P : ℕ) (hP : 0 < P) :
    Tendsto (fun x : ℕ => ((x / P : ℕ) : ℝ) / (x : ℝ))
      atTop (𝓝 (1 / (P : ℝ))) := by
  have hm := tendsto_mod_div_atTop_nhds_zero_nat hP
  have hbase : Tendsto (fun x : ℕ =>
      (1 - (((x % P : ℕ) : ℝ) / (x : ℝ))) / (P : ℝ))
      atTop (𝓝 ((1 - 0) / (P : ℝ))) :=
    (tendsto_const_nhds.sub hm).div_const (P : ℝ)
  have hbase' : Tendsto (fun x : ℕ =>
      (1 - (((x % P : ℕ) : ℝ) / (x : ℝ))) / (P : ℝ))
      atTop (𝓝 (1 / (P : ℝ))) := by simpa using hbase
  apply hbase'.congr'
  filter_upwards [eventually_ge_atTop 1] with x hx
  have hPR : (0 : ℝ) < P := by exact_mod_cast hP
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hdecomp := Nat.mod_add_div x P
  have hdecompR : ((x % P : ℕ) : ℝ) +
      (P : ℝ) * ((x / P : ℕ) : ℝ) = (x : ℝ) := by exact_mod_cast hdecomp
  field_simp
  nlinarith

/-- Every nonnegative natural-valued periodic sequence has a Cesàro limit,
equal to its one-period mean. -/
theorem tendsto_periodic_nat_average
    (f : ℕ → ℕ) (P : ℕ) (hP : 0 < P)
    (hf : Function.Periodic f P) :
    Tendsto (fun x : ℕ =>
      ((∑ n ∈ Finset.range x, f n : ℕ) : ℝ) / (x : ℝ))
      atTop (𝓝 (((∑ n ∈ Finset.range P, f n : ℕ) : ℝ) / (P : ℝ))) := by
  let S : ℕ := ∑ n ∈ Finset.range P, f n
  let rem : ℕ → ℕ := fun x => ∑ n ∈ Finset.range (x % P), f n
  have hrem0 : ∀ x, 0 ≤ rem x := fun _ => Nat.zero_le _
  have hremS : ∀ x, rem x ≤ S := by
    intro x
    dsimp [rem, S]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.range_mono (Nat.mod_lt x hP).le
    · intro i hiP hir
      exact Nat.zero_le _
  have hremT : Tendsto (fun x : ℕ => (rem x : ℝ) / (x : ℝ))
      atTop (𝓝 0) := by
    apply tendsto_bdd_div_atTop_nhds_zero (b := (0 : ℝ)) (B := (S : ℝ))
    · exact Filter.Eventually.of_forall (fun x => by exact_mod_cast hrem0 x)
    · exact Filter.Eventually.of_forall (fun x => by exact_mod_cast hremS x)
    · exact tendsto_natCast_atTop_atTop
  have hq := (tendsto_nat_div_cast_div P hP).mul_const (S : ℝ)
  have hsum := hq.add hremT
  have hlim : (1 / (P : ℝ)) * (S : ℝ) + 0 = (S : ℝ) / (P : ℝ) := by ring
  rw [hlim] at hsum
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop 1] with x hx
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hdecomp := sum_range_periodic_div_mod f P x hf
  dsimp [S, rem] at hdecomp ⊢
  rw [hdecomp]
  norm_num only [Nat.cast_add, Nat.cast_mul]
  field_simp

/- Consolidated from F061.CountShift. -/

open Filter
open scoped Topology

/-- A square-root-little-o counting function remains negligible after any
fixed additive shift when divided by the original variable. -/
theorem tendsto_count_add_div
    (p : ℕ → Prop) [DecidablePred p]
    (h : (fun n : ℕ => (Nat.count p n : ℝ)) =o[atTop]
      (fun n : ℕ => Real.sqrt (n : ℝ)))
    (c : ℕ) :
    Tendsto (fun x : ℕ => (Nat.count p (x + c) : ℝ) / (x : ℝ))
      atTop (𝓝 0) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall fun x => by
      have hnonneg : (0 : ℝ) ≤ (Nat.count p (x + c) : ℝ) / (x : ℝ) := by positivity
      linarith
  · intro b hb
    obtain ⟨N, hN⟩ := exists_nat_gt (2 / b)
    have hNpos : 0 < N := by
      have htwo : (0 : ℝ) < 2 / b := by positivity
      exact_mod_cast (lt_trans htwo hN)
    obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp
      (eventually_mul_count_le_of_isLittleO_sqrt p h N hNpos)
    filter_upwards [eventually_ge_atTop (max N0 (max c 1))] with x hx
    have hxN0 : N0 ≤ x + c := le_trans (le_trans (le_max_left _ _) hx) (Nat.le_add_right x c)
    have hlin := hN0 (x + c) hxN0
    have hxc : x + c ≤ 2 * x := by
      have hcx : c ≤ x := le_trans (le_max_left c 1) (le_trans (le_max_right N0 _) hx)
      omega
    have hlinR : (N : ℝ) * (Nat.count p (x + c) : ℝ) ≤ 2 * (x : ℝ) := by
      exact_mod_cast hlin.trans hxc
    have hxpos : (0 : ℝ) < x := by
      have : 1 ≤ x := le_trans (le_max_right c 1) (le_trans (le_max_right N0 _) hx)
      exact_mod_cast this
    have hNreal : (0 : ℝ) < N := by exact_mod_cast hNpos
    have hNb : (2 : ℝ) < b * N := by
      have := hN
      rw [div_lt_iff₀ hb] at this
      nlinarith
    rw [div_lt_iff₀ hxpos]
    nlinarith

/- Consolidated from F061.UniformApproximation. -/

open Filter
open scoped Topology

/-- A sequence which is eventually uniformly approximable, to arbitrary
accuracy, by convergent sequences is itself convergent in `ℝ`. -/
theorem exists_tendsto_of_uniform_eventual_approx
    (f : ℕ → ℝ) (approx : ℕ → ℕ → ℝ)
    (hclose : ∀ ε : ℝ, 0 < ε → ∃ H : ℕ,
      ∀ᶠ x : ℕ in atTop, |f x - approx H x| < ε)
    (hconv : ∀ H : ℕ, ∃ L : ℝ, Tendsto (approx H) atTop (𝓝 L)) :
    ∃ L : ℝ, Tendsto f atTop (𝓝 L) := by
  have hcauchy : CauchySeq f := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨H, hH⟩ := hclose (ε / 4) (by positivity)
    obtain ⟨L, hL⟩ := hconv H
    have hLmetric := (Metric.tendsto_atTop.1 hL) (ε / 4) (by positivity)
    obtain ⟨Nclose, hNclose⟩ := Filter.eventually_atTop.mp hH
    obtain ⟨Nlim, hNlim⟩ := hLmetric
    refine ⟨max Nclose Nlim, ?_⟩
    intro m hm n hn
    have hmclose := hNclose m (le_trans (le_max_left _ _) hm)
    have hnclose := hNclose n (le_trans (le_max_left _ _) hn)
    have hmlim := hNlim m (le_trans (le_max_right _ _) hm)
    have hnlim := hNlim n (le_trans (le_max_right _ _) hn)
    rw [Real.dist_eq] at hmlim hnlim ⊢
    have htri1 : |f m - f n| ≤
        |f m - approx H m| + |approx H m - L| + |L - f n| := by
      simpa only [Real.dist_eq] using
        dist_triangle4 (f m) (approx H m) L (f n)
    have htri2 : |L - f n| ≤
        |L - approx H n| + |approx H n - f n| := by
      simpa only [Real.dist_eq] using dist_triangle L (approx H n) (f n)
    have hmclose' : |f m - approx H m| < ε / 4 := hmclose
    have hnclose' : |approx H n - f n| < ε / 4 := by
      simpa [abs_sub_comm] using hnclose
    have hnlim' : |L - approx H n| < ε / 4 := by
      simpa [abs_sub_comm] using hnlim
    nlinarith
  exact cauchySeq_tendsto_of_complete hcauchy

/- Consolidated from F061.TruncatedGapApproximation. -/

open Filter
open scoped Topology BigOperators

/-- If two bounded nonnegative costs agree off `B`, their total sums differ by
at most `#B` times the common bound. -/
theorem abs_cast_sum_sub_sum_le_card_mul
    (S B : Finset ℕ) (f g : ℕ → ℕ) (K : ℕ)
    (hBS : B ⊆ S)
    (hf : ∀ n ∈ B, f n ≤ K) (hg : ∀ n ∈ B, g n ≤ K)
    (heq : ∀ n ∈ S, n ∉ B → f n = g n) :
    |((∑ n ∈ S, f n : ℕ) : ℝ) - ((∑ n ∈ S, g n : ℕ) : ℝ)| ≤
      (B.card : ℝ) * (K : ℝ) := by
  have hoff : (∑ n ∈ S \ B, f n) = ∑ n ∈ S \ B, g n := by
    apply Finset.sum_congr rfl
    intro n hn
    exact heq n (Finset.mem_sdiff.mp hn).1 (Finset.mem_sdiff.mp hn).2
  have hfs := Finset.sum_sdiff hBS (f := f)
  have hgs := Finset.sum_sdiff hBS (f := g)
  have hfb : ∑ n ∈ B, f n ≤ B.card * K := by
    calc
      ∑ n ∈ B, f n ≤ ∑ _n ∈ B, K := Finset.sum_le_sum hf
      _ = B.card * K := by simp
  have hgb : ∑ n ∈ B, g n ≤ B.card * K := by
    calc
      ∑ n ∈ B, g n ≤ ∑ _n ∈ B, K := Finset.sum_le_sum hg
      _ = B.card * K := by simp
  have hfbR : ((∑ n ∈ B, f n : ℕ) : ℝ) ≤ (B.card : ℝ) * K := by exact_mod_cast hfb
  have hgbR : ((∑ n ∈ B, g n : ℕ) : ℝ) ≤ (B.card : ℝ) * K := by exact_mod_cast hgb
  have hfsR : ((∑ n ∈ S \ B, f n : ℕ) : ℝ) +
      ((∑ n ∈ B, f n : ℕ) : ℝ) = ((∑ n ∈ S, f n : ℕ) : ℝ) := by
    exact_mod_cast hfs
  have hgsR : ((∑ n ∈ S \ B, g n : ℕ) : ℝ) +
      ((∑ n ∈ B, g n : ℕ) : ℝ) = ((∑ n ∈ S, g n : ℕ) : ℝ) := by
    exact_mod_cast hgs
  have hoffR : ((∑ n ∈ S \ B, f n : ℕ) : ℝ) =
      ((∑ n ∈ S \ B, g n : ℕ) : ℝ) := by exact_mod_cast hoff
  have heqR : ((∑ n ∈ S, f n : ℕ) : ℝ) - ((∑ n ∈ S, g n : ℕ) : ℝ) =
      ((∑ n ∈ B, f n : ℕ) : ℝ) - ((∑ n ∈ B, g n : ℕ) : ℝ) := by
    linarith
  rw [heqR, abs_le]
  have hfn : (0 : ℝ) ≤ ((∑ n ∈ B, f n : ℕ) : ℝ) := by positivity
  have hgn : (0 : ℝ) ≤ ((∑ n ∈ B, g n : ℕ) : ℝ) := by positivity
  constructor <;> linarith

namespace Erdos489

noncomputable def fullTruncatedGapAverage
    (p : ℕ → Prop) (H x : ℕ) : ℝ :=
  ((∑ n ∈ Finset.range x, truncatedGapCost (divisorSifted p) H n : ℕ) : ℝ) /
    (x : ℝ)

noncomputable def finiteTruncatedGapAverage
    (p : ℕ → Prop) (R H x : ℕ) : ℝ :=
  ((∑ n ∈ Finset.range x, truncatedGapCost (finiteDivisorSifted p R) H n : ℕ) : ℝ) /
    (x : ℝ)

noncomputable def finiteTruncatedGapLimit
    (p : ℕ → Prop) (R H : ℕ) : ℝ :=
  let P := ((List.range R).map (Nat.nth p)).prod
  ((∑ n ∈ Finset.range P,
      truncatedGapCost (finiteDivisorSifted p R) H n : ℕ) : ℝ) / (P : ℝ)

 theorem finiteTruncatedGapAverage_tendsto
    (p : ℕ → Prop) [DecidablePred p]
    (hp : Set.Infinite {n | p n}) (hp2 : ∀ n, p n → 2 ≤ n)
    (R H : ℕ) :
    Tendsto (finiteTruncatedGapAverage p R H) atTop
      (𝓝 (finiteTruncatedGapLimit p R H)) := by
  let P := ((List.range R).map (Nat.nth p)).prod
  have hP : 0 < P := by
    apply List.prod_pos
    intro a ha
    rcases List.mem_map.mp ha with ⟨r, hr, rfl⟩
    have hh := hp2 _ (Nat.nth_mem_of_infinite hp r)
    exact lt_of_lt_of_le (by omega : 0 < 2) hh
  have hper := truncatedGapCost_periodic (finiteDivisorSifted p R) H P
    (finiteDivisorSifted_periodic p R)
  change Tendsto (fun x : ℕ =>
      ((∑ n ∈ Finset.range x,
        truncatedGapCost (finiteDivisorSifted p R) H n : ℕ) : ℝ) / (x : ℝ))
    atTop (𝓝 (((∑ n ∈ Finset.range P,
      truncatedGapCost (finiteDivisorSifted p R) H n : ℕ) : ℝ) / (P : ℝ)))
  simpa only [Nat.cast_sum] using
    tendsto_periodic_nat_average
      (truncatedGapCost (finiteDivisorSifted p R) H) P hP hper

 theorem full_finite_truncated_sum_difference
    (p : ℕ → Prop) [DecidablePred p]
    (hp : Set.Infinite {n | p n}) (R H x : ℕ) :
    |((∑ n ∈ Finset.range x,
        truncatedGapCost (divisorSifted p) H n : ℕ) : ℝ) -
      ((∑ n ∈ Finset.range x,
        truncatedGapCost (finiteDivisorSifted p R) H n : ℕ) : ℝ)| ≤
      ((badGapStarts p R H x).card : ℝ) * (H ^ 3 : ℕ) := by
  classical
  apply abs_cast_sum_sub_sum_le_card_mul
    (Finset.range x) (badGapStarts p R H x)
  · exact badGapStarts_subset_range p R H x
  · intro n hn
    exact truncatedGapCost_le_cube _ H n
  · intro n hn
    exact truncatedGapCost_le_cube _ H n
  · intro n hnx hgood
    apply truncatedGapCost_eq_of_window_agree
    exact sieve_window_agree_of_not_bad p hp R H x n
      (Finset.mem_range.mp hnx) hgood

/-- For every fixed gap cutoff, one finite periodic prefix eventually
approximates the full truncated-gap average arbitrarily well. -/
theorem exists_prefix_eventually_full_finite_close
    (p : ℕ → Prop) [DecidablePred p]
    (hp : Set.Infinite {n | p n}) (hp2 : ∀ n, p n → 2 ≤ n)
    (hcount : (fun n : ℕ => (Nat.count p n : ℝ)) =o[atTop]
      (fun n : ℕ => Real.sqrt (n : ℝ)))
    (hsum : Summable fun r : ℕ => ((Nat.nth p r : ℝ)⁻¹))
    (H : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ R, ∀ᶠ x : ℕ in atTop,
      |fullTruncatedGapAverage p H x - finiteTruncatedGapAverage p R H x| < ε := by
  classical
  by_cases hH : H = 0
  · subst H
    refine ⟨0, Filter.Eventually.of_forall ?_⟩
    intro x
    simp [fullTruncatedGapAverage, finiteTruncatedGapAverage,
      truncatedGapCost, hε]
  · have hHpos : 0 < H := Nat.pos_of_ne_zero hH
    let K : ℕ := (H + 1) * H ^ 3
    have hK : 0 < K := by dsimp [K]; positivity
    have hKR : (0 : ℝ) < K := by exact_mod_cast hK
    let δ : ℝ := ε / (4 * (K : ℝ))
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have htailEv := eventually_finset_tail_sum_le_of_summable
      (fun r : ℕ => ((Nat.nth p r : ℝ)⁻¹)) hsum
      (fun r => inv_nonneg.mpr (by positivity)) δ hδ
    obtain ⟨R, htail, hR⟩ :=
      Filter.Eventually.exists (htailEv.and (eventually_ge_atTop 1))
    have hRpos : 0 < R := by omega
    have hMlim : Tendsto
        (fun x : ℕ => (((x + (H + 1) : ℕ) : ℝ) / (x : ℝ)))
        atTop (𝓝 1) := by
      have ht := tendsto_add_mul_div_add_mul_atTop_nhds (𝕜 := ℝ)
        ((H + 1 : ℕ) : ℝ) 0 1 (d := 1) (by norm_num)
      simpa [Nat.cast_add, add_comm] using ht
    have hM2 : ∀ᶠ x : ℕ in atTop,
        (((x + (H + 1) : ℕ) : ℝ) / (x : ℝ)) < 2 :=
      (tendsto_order.1 hMlim).2 2 (by norm_num)
    have hClim := tendsto_count_add_div p hcount (H + 1)
    have hsmallPos : 0 < ε / (2 * (K : ℝ)) := by positivity
    have hCsmall : ∀ᶠ x : ℕ in atTop,
        (Nat.count p (x + (H + 1)) : ℝ) / (x : ℝ) <
          ε / (2 * (K : ℝ)) :=
      (tendsto_order.1 hClim).2 _ hsmallPos
    refine ⟨R, ?_⟩
    filter_upwards [hM2, hCsmall, eventually_ge_atTop 1] with x hxM hxC hx
    have hxR : (0 : ℝ) < x := by exact_mod_cast hx
    let M : ℕ := x + H + 1
    have hMeq : M = x + (H + 1) := by dsimp [M]; omega
    have hbad := badGapStarts_card_le p R H x
    have hmis := sieveMismatch_card_cast_le p hp hp2 R M hRpos δ htail
    have hnum0 := full_finite_truncated_sum_difference p hp R H x
    have hbadR : ((badGapStarts p R H x).card : ℝ) ≤
        ((H + 1) : ℝ) * ((sieveMismatch p R M).card : ℝ) := by
      exact_mod_cast (by simpa [M] using hbad)
    have hnum :
        |((∑ n ∈ Finset.range x,
            truncatedGapCost (divisorSifted p) H n : ℕ) : ℝ) -
          ((∑ n ∈ Finset.range x,
            truncatedGapCost (finiteDivisorSifted p R) H n : ℕ) : ℝ)| ≤
        (K : ℝ) * ((M : ℝ) * δ + (Nat.count p M : ℝ)) := by
      calc
        _ ≤ ((badGapStarts p R H x).card : ℝ) * (H ^ 3 : ℕ) := hnum0
        _ ≤ (((H + 1) : ℝ) * ((sieveMismatch p R M).card : ℝ)) *
              (H ^ 3 : ℕ) := by gcongr
        _ = (K : ℝ) * ((sieveMismatch p R M).card : ℝ) := by
          dsimp [K]
          norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow]
          ring
        _ ≤ (K : ℝ) * ((M : ℝ) * δ + (Nat.count p M : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hmis hKR.le
    change |(((∑ n ∈ Finset.range x,
        truncatedGapCost (divisorSifted p) H n : ℕ) : ℝ) / (x : ℝ)) -
      (((∑ n ∈ Finset.range x,
        truncatedGapCost (finiteDivisorSifted p R) H n : ℕ) : ℝ) / (x : ℝ))| < ε
    rw [← sub_div, abs_div, abs_of_pos hxR]
    calc
      _ ≤ ((K : ℝ) * ((M : ℝ) * δ + (Nat.count p M : ℝ))) / (x : ℝ) :=
        div_le_div_of_nonneg_right hnum hxR.le
      _ = (K : ℝ) *
          ((((M : ℝ) / (x : ℝ)) * δ) +
            ((Nat.count p M : ℝ) / (x : ℝ))) := by field_simp
      _ < ε := by
        have hxM' : (M : ℝ) / (x : ℝ) < 2 := by simpa [hMeq] using hxM
        have hxC' : (Nat.count p M : ℝ) / (x : ℝ) <
            ε / (2 * (K : ℝ)) := by simpa [hMeq] using hxC
        have hpart1 : (K : ℝ) * (((M : ℝ) / (x : ℝ)) * δ) < ε / 2 := by
          have hm := mul_lt_mul_of_pos_right hxM' hδ
          dsimp [δ] at hm ⊢
          have hfour : (0 : ℝ) < 4 * K := by positivity
          calc
            (K : ℝ) * ((M : ℝ) / (x : ℝ) * (ε / (4 * K))) <
                (K : ℝ) * (2 * (ε / (4 * K))) :=
              mul_lt_mul_of_pos_left hm hKR
            _ = ε / 2 := by field_simp; ring
        have hpart2 : (K : ℝ) * ((Nat.count p M : ℝ) / (x : ℝ)) < ε / 2 := by
          calc
            _ < (K : ℝ) * (ε / (2 * (K : ℝ))) :=
              mul_lt_mul_of_pos_left hxC' hKR
            _ = ε / 2 := by field_simp
        nlinarith

/-- Consequently, the normalized squared-gap contribution from gaps below
any fixed cutoff has a finite limit. -/
theorem exists_fullTruncatedGapAverage_limit
    (p : ℕ → Prop) [DecidablePred p]
    (hp : Set.Infinite {n | p n}) (hp2 : ∀ n, p n → 2 ≤ n)
    (hcount : (fun n : ℕ => (Nat.count p n : ℝ)) =o[atTop]
      (fun n : ℕ => Real.sqrt (n : ℝ)))
    (hsum : Summable fun r : ℕ => ((Nat.nth p r : ℝ)⁻¹))
    (H : ℕ) :
    ∃ L : ℝ, Tendsto (fullTruncatedGapAverage p H) atTop (𝓝 L) := by
  apply exists_tendsto_of_uniform_eventual_approx
    (fullTruncatedGapAverage p H)
    (fun R => finiteTruncatedGapAverage p R H)
  · intro ε hε
    exact exists_prefix_eventually_full_finite_close
      p hp hp2 hcount hsum H ε hε
  · intro R
    exact ⟨finiteTruncatedGapLimit p R H,
      finiteTruncatedGapAverage_tendsto p hp hp2 R H⟩

end Erdos489

/- Consolidated from F061.FullGapConvergence. -/

open Filter
open scoped Topology BigOperators

namespace Erdos489

/-- The normalized full squared-gap sum for the infinite divisor sieve. -/
noncomputable def fullGapAverage (p : ℕ → Prop) (x : ℕ) : ℝ :=
  ((∑ i ∈ Finset.range (Nat.count (divisorSifted p) x),
      (divisorSiftedGap p i) ^ 2 : ℕ) : ℝ) / (x : ℝ)

/-- Exact decomposition into short-gap local cost and the long-gap tail. -/
theorem fullGapAverage_eq_truncated_add_tail
    (p : ℕ → Prop) [DecidablePred p]
    (hB : Set.Infinite {n | divisorSifted p n}) (H x : ℕ) :
    fullGapAverage p x = fullTruncatedGapAverage p H x +
      (((∑ i ∈ (Finset.range (Nat.count (divisorSifted p) x)).filter
          (fun i => H ≤ divisorSiftedGap p i),
          (divisorSiftedGap p i) ^ 2 : ℕ) : ℝ) / (x : ℝ)) := by
  classical
  have hshort := sum_truncatedGapCost_eq_gap_sum
    (divisorSifted p) hB H x
  have hpart := Finset.sum_filter_add_sum_filter_not
    (Finset.range (Nat.count (divisorSifted p) x))
    (fun i => divisorSiftedGap p i < H)
    (fun i => (divisorSiftedGap p i) ^ 2)
  simp only [not_lt] at hpart
  have htotal :
      (∑ i ∈ Finset.range (Nat.count (divisorSifted p) x),
        (divisorSiftedGap p i) ^ 2) =
      (∑ n ∈ Finset.range x,
        truncatedGapCost (divisorSifted p) H n) +
      (∑ i ∈ (Finset.range (Nat.count (divisorSifted p) x)).filter
        (fun i => H ≤ divisorSiftedGap p i),
        (divisorSiftedGap p i) ^ 2) := by
    have hs : (∑ n ∈ Finset.range x,
        truncatedGapCost (divisorSifted p) H n) =
      ∑ i ∈ (Finset.range (Nat.count (divisorSifted p) x)).filter
        (fun i => divisorSiftedGap p i < H),
        (divisorSiftedGap p i) ^ 2 := by
      rw [hshort]
      rfl
    omega
  unfold fullGapAverage fullTruncatedGapAverage
  rw [htotal]
  norm_num only [Nat.cast_add]
  ring

/-- The normalized full squared-gap sum converges for every infinite forbidden
predicate satisfying the established thinness consequences. -/
theorem exists_fullGapAverage_limit
    (p : ℕ → Prop) [DecidablePred p]
    (hp : Set.Infinite {n | p n})
    (hp2 : ∀ n, p n → 2 ≤ n)
    (hB : Set.Infinite {n | divisorSifted p n})
    (hs : Summable fun n => ((Nat.nth p n : ℝ)⁻¹))
    (hev : ∀ᶠ n : ℕ in atTop, (n + 1) ^ 2 ≤ Nat.nth p n)
    (hcount : (fun n : ℕ => (Nat.count p n : ℝ)) =o[atTop]
      (fun n : ℕ => Real.sqrt (n : ℝ))) :
    ∃ L : ℝ, Tendsto (fullGapAverage p) atTop (𝓝 L) := by
  apply exists_tendsto_of_uniform_eventual_approx
    (fullGapAverage p) (fun H => fullTruncatedGapAverage p H)
  · intro ε hε
    obtain ⟨H, htail⟩ := uniform_long_gap_square_tail
      p hp hp2 hB hs hev hcount ε hε
    refine ⟨H, ?_⟩
    filter_upwards [htail] with x hx
    rw [fullGapAverage_eq_truncated_add_tail p hB H x,
      add_sub_cancel_left]
    rw [abs_of_nonneg (by positivity)]
    exact hx
  · intro H
    exact exists_fullTruncatedGapAverage_limit p hp hp2 hcount hs H

end Erdos489

/- Consolidated from F061.Thinness. -/

open Filter
open scoped Topology BigOperators

/-- A sequence which eventually dominates the squares has summable reciprocals. -/
theorem summable_inv_of_eventually_sq_le (a : ℕ → ℕ)
    (h : ∀ᶠ n in atTop, (n + 1) ^ 2 ≤ a n) :
    Summable (fun n : ℕ => ((a n : ℝ)⁻¹)) := by
  have hs : Summable (fun n : ℕ => ((((n + 1 : ℕ) : ℝ) ^ 2)⁻¹)) := by
    have hζ : Summable (fun n : ℕ => (((n : ℝ) ^ 2)⁻¹)) :=
      Real.summable_nat_pow_inv.mpr (by omega)
    simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      hζ.comp_injective Nat.succ_injective
  apply Summable.of_norm_bounded_eventually_nat hs
  filter_upwards [h] with n hn
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
  have ha : 0 < (a n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by positivity : 0 < (n + 1) ^ 2) hn)
  have hb : 0 < (((n + 1 : ℕ) : ℝ) ^ 2) := by positivity
  rw [inv_le_inv₀ ha hb]
  exact_mod_cast hn

/-- Little-o square-root growth of a predicate's counting function forces the
reciprocals of its increasing enumeration to be summable. -/
theorem summable_inv_nth_of_count_isLittleO_sqrt (p : ℕ → Prop) [DecidablePred p]
    (hp : Set.Infinite {n | p n})
    (hcount : (fun x : ℕ => (Nat.count p x : ℝ)) =o[atTop]
      (fun x : ℕ => Real.sqrt (x : ℝ))) :
    Summable (fun n : ℕ => ((Nat.nth p n : ℝ)⁻¹)) := by
  apply summable_inv_of_eventually_sq_le
  have ht : Tendsto (Nat.nth p) atTop atTop :=
    (Nat.nth_injective hp).nat_tendsto_atTop
  have hb := hcount.bound (by norm_num : (0 : ℝ) < 1 / 2)
  have hbc : ∀ᶠ n in atTop,
      ‖(Nat.count p (Nat.nth p n) : ℝ)‖ ≤
        (1 / 2 : ℝ) * ‖Real.sqrt (Nat.nth p n : ℝ)‖ := ht.eventually hb
  filter_upwards [hbc, eventually_ge_atTop 1] with n hn hnpos
  rw [Nat.count_nth_of_infinite hp n] at hn
  have hnreal : (n : ℝ) ≤ (1 / 2 : ℝ) * Real.sqrt (Nat.nth p n : ℝ) := by
    simpa only [Real.norm_natCast, Real.norm_eq_abs,
      abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) by positivity),
      abs_of_nonneg (Real.sqrt_nonneg _)] using hn
  have hsqrt : (2 : ℝ) * n ≤ Real.sqrt (Nat.nth p n : ℝ) := by
    linarith
  have hsquare : ((2 : ℝ) * n) ^ 2 ≤ (Nat.nth p n : ℝ) := by
    calc
      ((2 : ℝ) * n) ^ 2 ≤ (Real.sqrt (Nat.nth p n : ℝ)) ^ 2 :=
        (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).2 hsqrt
      _ = (Nat.nth p n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have hcast : ((((n + 1) ^ 2 : ℕ) : ℝ)) ≤ (Nat.nth p n : ℝ) := by
    have hncast : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
    norm_num at hsquare ⊢
    nlinarith
  exact_mod_cast hcast

/-- For a predicate false at zero, strict counting through `x+1` is the
inclusive `[1,x]` filtered cardinality used in Erdős 489. -/
lemma count_succ_eq_card_filter_Icc (p : ℕ → Prop) [DecidablePred p]
    (hp0 : ¬p 0) (x : ℕ) :
    Nat.count p (x + 1) = ((Finset.Icc 1 x).filter p).card := by
  rw [Nat.count_eq_card_filter_range]
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨hnx, hpn⟩
    refine ⟨⟨?_, by omega⟩, hpn⟩
    by_contra hn1
    have : n = 0 := by omega
    exact hp0 (this ▸ hpn)
  · rintro ⟨⟨_, hnx⟩, hpn⟩
    exact ⟨by omega, hpn⟩

/-- The exact inclusive counting hypothesis in Erdős 489 implies summability
of the reciprocal series of the forbidden set (when zero is absent). -/
theorem summable_inv_nth_of_Icc_count_isLittleO_sqrt (p : ℕ → Prop)
    [DecidablePred p] (hp0 : ¬p 0) (hp : Set.Infinite {n | p n})
    (hcount : (fun x : ℕ => ((((Finset.Icc 1 x).filter p).card : ℝ)))
      =o[atTop] (fun x : ℕ => Real.sqrt (x : ℝ))) :
    Summable (fun n : ℕ => ((Nat.nth p n : ℝ)⁻¹)) := by
  apply summable_inv_of_eventually_sq_le
  have ht : Tendsto (Nat.nth p) atTop atTop :=
    (Nat.nth_injective hp).nat_tendsto_atTop
  have hb := hcount.bound (by norm_num : (0 : ℝ) < 1 / 2)
  have hbc := ht.eventually hb
  filter_upwards [hbc] with n hn
  have hcard : ((Finset.Icc 1 (Nat.nth p n)).filter p).card = n + 1 := by
    rw [← count_succ_eq_card_filter_Icc p hp0]
    exact Nat.count_nth_succ_of_infinite hp n
  rw [hcard] at hn
  have hnreal : ((n + 1 : ℕ) : ℝ) ≤
      (1 / 2 : ℝ) * Real.sqrt (Nat.nth p n : ℝ) := by
    simpa only [Real.norm_natCast, Real.norm_eq_abs,
      abs_of_nonneg (show (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) by positivity),
      abs_of_nonneg (Real.sqrt_nonneg _)] using hn
  have hsqrt : (((n + 1 : ℕ) : ℝ)) ≤ Real.sqrt (Nat.nth p n : ℝ) := by
    have : (0 : ℝ) ≤ Real.sqrt (Nat.nth p n : ℝ) := Real.sqrt_nonneg _
    linarith
  have hsquare : ((((n + 1) ^ 2 : ℕ) : ℝ)) ≤ (Nat.nth p n : ℝ) := by
    calc
      ((((n + 1) ^ 2 : ℕ) : ℝ)) = (((n + 1 : ℕ) : ℝ)) ^ 2 := by norm_num
      _ ≤ (Real.sqrt (Nat.nth p n : ℝ)) ^ 2 :=
        (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).2 hsqrt
      _ = (Nat.nth p n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  exact_mod_cast hsquare

/-- Quantitative form: the square of the enumeration index divided by the
corresponding forbidden integer tends to zero. -/
theorem tendsto_sq_index_div_nth_zero_of_Icc_count_isLittleO_sqrt
    (p : ℕ → Prop) [DecidablePred p] (hp0 : ¬p 0)
    (hp : Set.Infinite {n | p n})
    (hcount : (fun x : ℕ => ((((Finset.Icc 1 x).filter p).card : ℝ)))
      =o[atTop] (fun x : ℕ => Real.sqrt (x : ℝ))) :
    Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ 2) / (Nat.nth p n : ℝ))
      atTop (𝓝 0) := by
  have ht : Tendsto (Nat.nth p) atTop atTop :=
    (Nat.nth_injective hp).nat_tendsto_atTop
  have ho := hcount.comp_tendsto ht
  have traw := ho.tendsto_div_nhds_zero
  have hratio : Tendsto
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / Real.sqrt (Nat.nth p n : ℝ))
      atTop (𝓝 0) := by
    apply traw.congr'
    filter_upwards with n
    simp only [Function.comp_apply]
    rw [show ((Finset.Icc 1 (Nat.nth p n)).filter p).card = n + 1 by
      rw [← count_succ_eq_card_filter_Icc p hp0]
      exact Nat.count_nth_succ_of_infinite hp n]
  have hsquared := hratio.pow 2
  convert hsquared using 1
  · funext n
    have hpos : 0 < (Nat.nth p n : ℝ) := by
      exact_mod_cast (Nat.pos_of_ne_zero (fun hz => hp0 (hz ▸ Nat.nth_mem_of_infinite hp n)))
    rw [div_pow, Real.sq_sqrt hpos.le]
  · norm_num

/- Consolidated from F061.ProblemDefinitions. -/

namespace Erdos489

open Classical Filter
open scoped Topology BigOperators

/-- Positive natural numbers divisible by no member of `A`. -/
def sievedSet (A : Set ℕ) : Set ℕ :=
  {n : ℕ | 0 < n ∧ ∀ a ∈ A, ¬ a ∣ n}

/-- The sum of squared successive gaps whose left endpoint is below `x`. -/
noncomputable def gapSumSq (A : Set ℕ) (x : ℕ) : ℝ :=
  let B := sievedSet A
  let b := Nat.nth (· ∈ B)
  ∑ i ∈ Finset.range (Nat.count (· ∈ B) x),
    ((b (i + 1) : ℝ) - (b i : ℝ)) ^ 2

end Erdos489

/- Consolidated from F061.OriginalBridge. -/

open Classical Filter
open scoped Topology BigOperators

namespace Erdos489

/-- Remove the irrelevant forbidden integers `0` and `1`. -/
def restrictedForbidden (A : Set ℕ) (n : ℕ) : Prop := n ∈ A ∧ 2 ≤ n

noncomputable instance restrictedForbiddenDecidable (A : Set ℕ) :
    DecidablePred (restrictedForbidden A) := Classical.decPred _

 theorem restricted_count_le_original_Icc (A : Set ℕ) (x : ℕ) :
    Nat.count (restrictedForbidden A) x ≤
      ((Finset.Icc 1 x).filter (· ∈ A)).card := by
  rw [Nat.count_eq_card_filter_range]
  apply Finset.card_le_card
  intro n hn
  have hnr := Finset.mem_range.mp (Finset.mem_filter.mp hn).1
  have hnp := (Finset.mem_filter.mp hn).2
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_Icc.mpr ⟨le_trans (by omega : 1 ≤ 2) hnp.2, hnr.le⟩, hnp.1⟩

 theorem restricted_count_isLittleO
    (A : Set ℕ)
    (hA : (fun x : ℕ => (((Finset.Icc 1 x).filter (· ∈ A)).card : ℝ))
      =o[atTop] (fun x : ℕ => Real.sqrt (x : ℝ))) :
    (fun x : ℕ => (Nat.count (restrictedForbidden A) x : ℝ))
      =o[atTop] (fun x : ℕ => Real.sqrt (x : ℝ)) := by
  apply Asymptotics.IsLittleO.of_bound
  intro c hc
  have hb := hA.bound hc
  filter_upwards [hb] with x hx
  have hleR : (Nat.count (restrictedForbidden A) x : ℝ) ≤
      (((Finset.Icc 1 x).filter (· ∈ A)).card : ℝ) := by
    exact_mod_cast restricted_count_le_original_Icc A x
  have hx' : (((Finset.Icc 1 x).filter (· ∈ A)).card : ℝ) ≤
      c * Real.sqrt (x : ℝ) := by
    simpa only [Real.norm_natCast, Real.norm_eq_abs,
      abs_of_nonneg (show (0 : ℝ) ≤
        (((Finset.Icc 1 x).filter (· ∈ A)).card : ℝ) by positivity),
      abs_of_nonneg (Real.sqrt_nonneg _)] using hx
  simpa only [Real.norm_natCast, Real.norm_eq_abs,
    abs_of_nonneg (show (0 : ℝ) ≤ (Nat.count (restrictedForbidden A) x : ℝ) by positivity),
    abs_of_nonneg (Real.sqrt_nonneg _)] using hleR.trans hx'

 theorem eventually_sq_le_nth_of_count_isLittleO_sqrt
    (p : ℕ → Prop) [DecidablePred p] (hp : Set.Infinite {n | p n})
    (hcount : (fun x : ℕ => (Nat.count p x : ℝ)) =o[atTop]
      (fun x : ℕ => Real.sqrt (x : ℝ))) :
    ∀ᶠ n : ℕ in atTop, (n + 1) ^ 2 ≤ Nat.nth p n := by
  have ht : Tendsto (Nat.nth p) atTop atTop :=
    (Nat.nth_injective hp).nat_tendsto_atTop
  have hb := hcount.bound (by norm_num : (0 : ℝ) < 1 / 2)
  have hbc : ∀ᶠ n in atTop,
      ‖(Nat.count p (Nat.nth p n) : ℝ)‖ ≤
        (1 / 2 : ℝ) * ‖Real.sqrt (Nat.nth p n : ℝ)‖ := ht.eventually hb
  filter_upwards [hbc, eventually_ge_atTop 1] with n hn hnpos
  rw [Nat.count_nth_of_infinite hp n] at hn
  have hnreal : (n : ℝ) ≤ (1 / 2 : ℝ) * Real.sqrt (Nat.nth p n : ℝ) := by
    simpa only [Real.norm_natCast, Real.norm_eq_abs,
      abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) by positivity),
      abs_of_nonneg (Real.sqrt_nonneg _)] using hn
  have hsquare : ((2 : ℝ) * n) ^ 2 ≤ (Nat.nth p n : ℝ) := by
    have hsqrt : (2 : ℝ) * n ≤ Real.sqrt (Nat.nth p n : ℝ) := by linarith
    calc
      ((2 : ℝ) * n) ^ 2 ≤ (Real.sqrt (Nat.nth p n : ℝ)) ^ 2 :=
        (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).2 hsqrt
      _ = (Nat.nth p n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have hcast : ((((n + 1) ^ 2 : ℕ) : ℝ)) ≤ (Nat.nth p n : ℝ) := by
    have hncast : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
    norm_num at hsquare ⊢
    nlinarith
  exact_mod_cast hcast

 theorem restrictedForbidden_infinite (A : Set ℕ) (hA : A.Infinite) :
    Set.Infinite {n | restrictedForbidden A n} := by
  by_contra hnot
  rw [Set.not_infinite] at hnot
  have hsub : A ⊆ {n | restrictedForbidden A n} ∪ Set.Iio 2 := by
    intro n hn
    by_cases hn2 : 2 ≤ n
    · exact Set.mem_union_left _ ⟨hn, hn2⟩
    · apply Set.mem_union_right
      show n < 2
      omega
  exact hA ((hnot.union (Set.finite_Iio 2)).subset hsub)

 theorem one_not_mem_of_sievedSet_infinite
    (A : Set ℕ) (hB : (sievedSet A).Infinite) : 1 ∉ A := by
  intro h1
  rcases hB.nonempty with ⟨n, hn⟩
  exact hn.2 1 h1 (one_dvd n)

 theorem divisorSifted_restricted_iff
    (A : Set ℕ) (hB : (sievedSet A).Infinite) (n : ℕ) :
    divisorSifted (restrictedForbidden A) n ↔ n ∈ sievedSet A := by
  have h1 := one_not_mem_of_sievedSet_infinite A hB
  constructor
  · intro hn
    refine ⟨hn.1, ?_⟩
    intro a haA hadvd
    by_cases ha0 : a = 0
    · subst a
      have hn0 : n = 0 := by simpa using hadvd
      exact (Nat.ne_of_gt hn.1) hn0
    by_cases ha1 : a = 1
    · exact h1 (ha1 ▸ haA)
    · apply hn.2 a ⟨haA, by omega⟩ hadvd
  · intro hn
    refine ⟨hn.1, ?_⟩
    intro a ha hadvd
    exact hn.2 a ha.1 hadvd

 theorem fullGapAverage_restricted_eq
    (A : Set ℕ) (hB : (sievedSet A).Infinite) (x : ℕ) :
    fullGapAverage (restrictedForbidden A) x = gapSumSq A x / (x : ℝ) := by
  classical
  have hpred : divisorSifted (restrictedForbidden A) =
      fun n => n ∈ sievedSet A := by
    funext n
    exact propext (divisorSifted_restricted_iff A hB n)
  unfold fullGapAverage gapSumSq divisorSiftedGap divisorSiftedEnumeration
  simp only [hpred]
  norm_num only [Nat.cast_sum, Nat.cast_pow]
  congr 2
  funext i
  have hBin : Set.Infinite {n | n ∈ sievedSet A} := by simpa using hB
  have hmono : StrictMono (Nat.nth (fun n => n ∈ sievedSet A)) :=
    Nat.nth_strictMono hBin
  rw [Nat.cast_sub (hmono.monotone (by omega : i ≤ i + 1))]

 theorem exists_original_limit_of_infinite_forbidden
    (A : Set ℕ) (hAinf : A.Infinite)
    (hthin : (fun x : ℕ => (((Finset.Icc 1 x).filter (· ∈ A)).card : ℝ))
      =o[atTop] (fun x : ℕ => Real.sqrt (x : ℝ)))
    (hB : (sievedSet A).Infinite) :
    ∃ L : ℝ, Tendsto (fun x : ℕ => gapSumSq A x / (x : ℝ))
      atTop (𝓝 L) := by
  let p := restrictedForbidden A
  have hp : Set.Infinite {n | p n} := restrictedForbidden_infinite A hAinf
  have hp2 : ∀ n, p n → 2 ≤ n := fun _ hn => hn.2
  have hcount : (fun x : ℕ => (Nat.count p x : ℝ)) =o[atTop]
      (fun x : ℕ => Real.sqrt (x : ℝ)) := restricted_count_isLittleO A hthin
  have hs : Summable fun n => ((Nat.nth p n : ℝ)⁻¹) :=
    summable_inv_nth_of_count_isLittleO_sqrt p hp hcount
  have hev : ∀ᶠ n : ℕ in atTop, (n + 1) ^ 2 ≤ Nat.nth p n :=
    eventually_sq_le_nth_of_count_isLittleO_sqrt p hp hcount
  have hBp : Set.Infinite {n | divisorSifted p n} := by
    have heq : {n | divisorSifted p n} = sievedSet A := by
      ext n
      exact divisorSifted_restricted_iff A hB n
    rw [heq]
    exact hB
  obtain ⟨L, hL⟩ := exists_fullGapAverage_limit p hp hp2 hBp hs hev hcount
  refine ⟨L, hL.congr' ?_⟩
  exact Filter.Eventually.of_forall fun x => fullGapAverage_restricted_eq A hB x
end Erdos489

/- Consolidated from F061.FiniteForbiddenConvergence. -/

open Classical Filter
open scoped Topology BigOperators

/-- A sequence whose one-step shift is positive-periodic has a Cesàro limit. -/
theorem exists_tendsto_average_of_shift_periodic
    (f : ℕ → ℕ) (P : ℕ) (hP : 0 < P)
    (hf : Function.Periodic (fun n => f (n + 1)) P) :
    ∃ L : ℝ, Tendsto (fun x : ℕ =>
      ((∑ n ∈ Finset.range x, f n : ℕ) : ℝ) / (x : ℝ))
      atTop (𝓝 L) := by
  let L : ℝ := ((∑ n ∈ Finset.range P, f (n + 1) : ℕ) : ℝ) / (P : ℝ)
  have hv : Tendsto (fun x : ℕ =>
      ((∑ n ∈ Finset.range x, f (n + 1) : ℕ) : ℝ) / (x : ℝ))
      atTop (𝓝 L) := by
    exact tendsto_periodic_nat_average (fun n => f (n + 1)) P hP hf
  have hratio : Tendsto (fun x : ℕ => (x : ℝ) / ((x : ℝ) + 1))
      atTop (𝓝 1) := tendsto_natCast_div_add_atTop 1
  have hconst : Tendsto (fun x : ℕ => (f 0 : ℝ) / ((x : ℝ) + 1))
      atTop (𝓝 0) := by
    have ht := (tendsto_add_atTop_iff_nat 1).2
      (tendsto_const_div_atTop_nhds_zero_nat (f 0 : ℝ))
    simpa [Nat.cast_add] using ht
  have hcomb : Tendsto (fun x : ℕ =>
      (((∑ n ∈ Finset.range x, f (n + 1) : ℕ) : ℝ) / (x : ℝ)) *
        ((x : ℝ) / ((x : ℝ) + 1)) + (f 0 : ℝ) / ((x : ℝ) + 1))
      atTop (𝓝 L) := by
    simpa using (hv.mul hratio).add hconst
  have hsucc : Tendsto (fun x : ℕ =>
      ((∑ n ∈ Finset.range (x + 1), f n : ℕ) : ℝ) / ((x + 1 : ℕ) : ℝ))
      atTop (𝓝 L) := by
    apply hcomb.congr'
    filter_upwards [eventually_ge_atTop 1] with x hx
    rw [Finset.sum_range_succ']
    norm_num only [Nat.cast_add, Nat.cast_sum, Nat.cast_one]
    field_simp
  exact ⟨L, (tendsto_add_atTop_iff_nat 1).1 (by simpa [Nat.add_comm] using hsucc)⟩

/-- A forward period bounds every enumerated gap by one period. -/
theorem nth_gap_le_of_forward_period
    (q : ℕ → Prop) [DecidablePred q] (hq : Set.Infinite {n | q n})
    (P : ℕ) (hP : 0 < P) (hforward : ∀ n, q n → q (n + P)) (i : ℕ) :
    Nat.nth q (i + 1) - Nat.nth q i ≤ P := by
  have hmem := Nat.nth_mem_of_infinite hq i
  have hend := hforward _ hmem
  have hlt : Nat.nth q i < Nat.nth q i + P := by omega
  have hicount : i < Nat.count q (Nat.nth q i + P) :=
    (Nat.lt_nth_iff_count_lt hq).2 hlt
  have hidx : i + 1 ≤ Nat.count q (Nat.nth q i + P) := by omega
  have hmono : Nat.nth q (i + 1) ≤
      Nat.nth q (Nat.count q (Nat.nth q i + P)) :=
    (Nat.nth_strictMono hq).monotone hidx
  rw [Nat.nth_count hend] at hmono
  exact Nat.sub_le_iff_le_add'.2 hmono

namespace Erdos489

/-- A finite forbidden set gives a convergent normalized full gap sum. -/
theorem exists_original_limit_of_finite_forbidden
    (A : Set ℕ) (hAfin : A.Finite) (hB : (sievedSet A).Infinite) :
    ∃ L : ℝ, Tendsto (fun x : ℕ => gapSumSq A x / (x : ℝ))
      atTop (𝓝 L) := by
  let p := restrictedForbidden A
  let s : Finset ℕ := hAfin.toFinset.filter fun a => 2 ≤ a
  let avoid : ℕ → Prop := fun n => ∀ a ∈ s, ¬a ∣ n
  let P : ℕ := s.prod id
  have hpiff : ∀ a, p a ↔ a ∈ s := by
    intro a
    simp [p, s, restrictedForbidden, hAfin.mem_toFinset]
  have hqiff : ∀ n, 0 < n → (divisorSifted p n ↔ avoid n) := by
    intro n hn
    simp only [divisorSifted, hn, true_and, avoid]
    constructor
    · intro h a ha
      exact h a ((hpiff a).2 ha)
    · intro h a ha
      exact h a ((hpiff a).1 ha)
  have hP : 0 < P := by
    dsimp [P]
    apply Finset.prod_pos
    intro a ha
    have ha2 : 2 ≤ a := ((hpiff a).2 ha).2
    exact lt_of_lt_of_le (by omega : 0 < 2) ha2
  have havoid : Function.Periodic avoid P := by
    intro n
    apply propext
    constructor
    · intro hn a ha han
      apply hn a ha
      have hap : a ∣ P := by
        dsimp [P]
        exact Finset.dvd_prod_of_mem id ha
      exact (Nat.dvd_add_iff_left hap).1 han
    · intro hn a ha han
      apply hn a ha
      have hap : a ∣ P := by
        dsimp [P]
        exact Finset.dvd_prod_of_mem id ha
      exact (Nat.dvd_add_iff_left hap).2 han
  have hforward : ∀ n, divisorSifted p n → divisorSifted p (n + P) := by
    intro n hn
    have hnpos : 0 < n := hn.1
    apply (hqiff (n + P) (by omega)).2
    have hav := (hqiff n hnpos).1 hn
    exact havoid n ▸ hav
  have hBp : Set.Infinite {n | divisorSifted p n} := by
    have heq : {n | divisorSifted p n} = sievedSet A := by
      ext n
      exact divisorSifted_restricted_iff A hB n
    rw [heq]
    exact hB
  let H := P + 1
  have hgap : ∀ i, divisorSiftedGap p i < H := by
    intro i
    have hle := nth_gap_le_of_forward_period (divisorSifted p) hBp P hP hforward i
    simpa [divisorSiftedGap, divisorSiftedEnumeration, H] using (show
      Nat.nth (divisorSifted p) (i + 1) - Nat.nth (divisorSifted p) i < P + 1 by omega)
  have hshiftper : Function.Periodic
      (fun n => truncatedGapCost (divisorSifted p) H (n + 1)) P := by
    have heq : ∀ n, truncatedGapCost (divisorSifted p) H (n + 1) =
        truncatedGapCost avoid H (n + 1) := by
      intro n
      apply truncatedGapCost_eq_of_window_agree
      intro k hk
      exact hqiff (n + 1 + k) (by omega)
    intro n
    change truncatedGapCost (divisorSifted p) H (n + P + 1) =
      truncatedGapCost (divisorSifted p) H (n + 1)
    rw [heq (n + P), heq n]
    have ht := truncatedGapCost_periodic avoid H P havoid (n + 1)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht
  obtain ⟨L, hlocal⟩ := exists_tendsto_average_of_shift_periodic
    (truncatedGapCost (divisorSifted p) H) P hP hshiftper
  have heqavg : fullGapAverage p = fullTruncatedGapAverage p H := by
    funext x
    rw [fullGapAverage_eq_truncated_add_tail p hBp H x]
    have hempty : (Finset.range (Nat.count (divisorSifted p) x)).filter
        (fun i => H ≤ divisorSiftedGap p i) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro i hi
      exact (not_le_of_gt (hgap i)) (Finset.mem_filter.mp hi).2
    rw [hempty]
    simp
  have hfull : Tendsto (fullGapAverage p) atTop (𝓝 L) := by
    rw [heqavg]
    exact hlocal
  refine ⟨L, hfull.congr' ?_⟩
  exact Filter.Eventually.of_forall fun x => fullGapAverage_restricted_eq A hB x

end Erdos489

/- Consolidated from F061.Erdos489. -/

/-!
A faithful positive-answer formalization of Erdős Problem 489.

The original display presupposes that the sifted set can be enumerated as an
infinite increasing sequence. This is represented by the explicit hypothesis
`(sievedSet A).Infinite`.
-/

namespace Erdos489

open Classical Filter
open scoped Topology BigOperators

/-- A positive answer to Erdős Problem 489. -/
theorem erdos489_statement :
    ∀ A : Set ℕ,
      (fun x : ℕ => (((Finset.Icc 1 x).filter (· ∈ A)).card : ℝ))
          =o[atTop] (fun x : ℕ => Real.sqrt (x : ℝ)) →
      (sievedSet A).Infinite →
      ∃ L : ℝ,
        Tendsto (fun x : ℕ => gapSumSq A x / (x : ℝ)) atTop (𝓝 L) := by
  intro A hthin hB
  by_cases hAinf : A.Infinite
  · exact exists_original_limit_of_infinite_forbidden A hAinf hthin hB
  · rw [Set.not_infinite] at hAinf
    exact exists_original_limit_of_finite_forbidden A hAinf hB

end Erdos489

namespace Submissions.Erdos489GapLimitFull.ExternalProof

open Filter
open scoped Topology

abbrev sievedSet (A : Set ℕ) : Set ℕ :=
  Erdos489.sievedSet A

noncomputable abbrev GapSumSq (A : Set ℕ) (x : ℕ) : ℝ :=
  Erdos489.gapSumSq A x

theorem proof :
    ∀ (A : Set ℕ),
      (fun x : ℕ => (((Finset.Icc 1 x).filter (· ∈ A)).card : ℝ)) =o[atTop]
        (fun x : ℕ => (x : ℝ).sqrt) →
      (sievedSet A).Infinite →
      ∃ L : ℝ, Tendsto (fun x : ℕ => GapSumSq A x / (x : ℝ)) atTop (𝓝 L) := by
  exact Erdos489.erdos489_statement

end Submissions.Erdos489GapLimitFull.ExternalProof
