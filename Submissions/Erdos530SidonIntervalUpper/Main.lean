import Mathlib.Combinatorics.Additive.Energy
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Topology.Instances.Nat
import Mathlib.Tactic.FieldSimp

namespace Submissions.Erdos530SidonIntervalUpper.Main

open scoped Combinatorics.Additive

/-- The exact Sidon predicate used by the canonical problem. -/
def IsSidon (S : Finset ℝ) : Prop :=
  ∀ ⦃a b c d : ℝ⦄,
    a ∈ S → b ∈ S → c ∈ S → d ∈ S →
      a + b = c + d →
        (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- Sidon sets have at most one representation of each nonzero difference. -/
theorem sidon_cross_energy_le (S T : Finset ℝ) (hS : IsSidon S) :
    E[S, T] ≤ S.card * T.card + T.card ^ 2 := by
  classical
  let Q : Finset ((ℝ × ℝ) × (ℝ × ℝ)) :=
    ((S ×ˢ S) ×ˢ (T ×ˢ T)).filter fun q => q.1.1 + q.2.1 = q.1.2 + q.2.2
  let f : ((ℝ × ℝ) × (ℝ × ℝ)) → (ℝ × ℝ) ⊕ (ℝ × ℝ) :=
    fun q => if q.1.1 = q.1.2 then Sum.inl (q.1.1, q.2.1) else Sum.inr q.2
  have hf : Set.MapsTo f Q ((S ×ˢ T).disjSum (T ×ˢ T)) := by
    intro q hq
    rcases Finset.mem_filter.mp hq with ⟨hm, _⟩
    rcases Finset.mem_product.mp hm with ⟨hss, htt⟩
    rcases Finset.mem_product.mp hss with ⟨ha, _⟩
    rcases Finset.mem_product.mp htt with ⟨hb, hb'⟩
    by_cases h : q.1.1 = q.1.2
    · simp only [f, if_pos h, Finset.mem_coe, Finset.inl_mem_disjSum, Finset.mem_product]
      exact ⟨ha, hb⟩
    · simp [f, h, hb, hb']
  have hi : (Q : Set ((ℝ × ℝ) × (ℝ × ℝ))).InjOn f := by
    rintro ⟨⟨a, a'⟩, ⟨b, b'⟩⟩ hp ⟨⟨c, c'⟩, ⟨d, d'⟩⟩ hq heq
    simp only [Q, Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp hq
    rcases hp with ⟨⟨⟨ha, ha'⟩, ⟨hb, hb'⟩⟩, hab⟩
    rcases hq with ⟨⟨⟨hc, hc'⟩, ⟨hd, hd'⟩⟩, hcd⟩
    by_cases haa : a = a'
    · by_cases hcc : c = c'
      · have hpair : a = c ∧ b = d := by simpa [f, haa, hcc] using heq
        have hac' : a' = c' := by linarith [hpair.1]
        have hbd' : b' = d' := by linarith [hpair.1, hpair.2]
        exact Prod.ext (Prod.ext hpair.1 hac') (Prod.ext hpair.2 hbd')
      · simp [f, haa, hcc] at heq
    · by_cases hcc : c = c'
      · simp [f, haa, hcc] at heq
      · have hpair : b = d ∧ b' = d' := by simpa [f, haa, hcc] using heq
        have hsum : a + c' = c + a' := by linarith [hpair.1, hpair.2]
        rcases hS ha hc' hc ha' hsum with h | h
        · exact Prod.ext (Prod.ext h.1 h.2.symm) (Prod.ext hpair.1 hpair.2)
        · exact (haa h.1).elim
  have h := Finset.card_le_card_of_injOn f hf hi
  simpa [Q, Finset.addEnergy, Finset.card_product, pow_two] using h

/-- The interval of `N` nonnegative integers, embedded in the canonical real domain. -/
noncomputable def interval (N : ℕ) : Finset ℝ := by
  classical
  exact (Finset.range N).image fun n : ℕ => (n : ℝ)

@[simp] theorem card_interval (N : ℕ) : (interval N).card = N := by
  classical
  rw [interval, Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]

theorem add_mem_interval {N H : ℕ} {a b : ℝ}
    (ha : a ∈ interval N) (hb : b ∈ interval H) :
    a + b ∈ interval (N + H) := by
  classical
  rcases Finset.mem_image.mp ha with ⟨n, hn, rfl⟩
  rcases Finset.mem_image.mp hb with ⟨h, hh, rfl⟩
  apply Finset.mem_image.mpr
  refine ⟨n + h, Finset.mem_range.mpr ?_, by simp⟩
  exact Nat.add_lt_add (Finset.mem_range.mp hn) (Finset.mem_range.mp hh)

/-- A finite inequality whose epsilon-form has leading constant one. -/
theorem sidon_interval_energy_bound (N H : ℕ) (S : Finset ℝ)
    (hSN : S ⊆ interval N) (hS : IsSidon S) :
    S.card ^ 2 * H ^ 2 ≤ (N + H) * (S.card * H + H ^ 2) := by
  classical
  have hfilter :
      ((S ×ˢ interval H).filter fun xy => xy.1 + xy.2 ∈ interval (N + H)) =
        S ×ˢ interval H := by
    apply Finset.filter_eq_self.mpr
    intro xy hxy
    exact add_mem_interval (hSN (Finset.mem_product.mp hxy).1)
      (Finset.mem_product.mp hxy).2
  have h := Finset.card_sq_le_card_mul_addEnergy S (interval H) (interval (N + H))
  rw [hfilter, Finset.card_product, card_interval, card_interval, mul_pow] at h
  exact h.trans (Nat.mul_le_mul_left (N + H)
    (by simpa using sidon_cross_energy_le S (interval H) hS))

open Filter

theorem eventual_sqrt_bound (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ k : ℝ, 0 ≤ k →
      (∀ H : ℕ, 0 < H →
        k ^ 2 * (H : ℝ) ^ 2 ≤ ((N : ℝ) + H) * (k * H + (H : ℝ) ^ 2)) →
      k ≤ (1 + ε) * Real.sqrt N := by
  let δ : ℝ := ε / 2
  have hd : 0 < δ := by dsimp [δ]; positivity
  let C : ℝ := (1 + 2 * δ) / δ
  have hC : 0 < C := by dsimp [C]; positivity
  refine Filter.eventually_atTop.2 ⟨⌈max (1 / δ) ((C / δ) ^ 2)⌉₊, ?_⟩
  intro N hN k hk henergy
  have hlarge : max (1 / δ) ((C / δ) ^ 2) ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have hN1 : 1 / δ ≤ (N : ℝ) := (le_max_left _ _).trans hlarge
  have hN2 : (C / δ) ^ 2 ≤ (N : ℝ) := (le_max_right _ _).trans hlarge
  have hdn : 1 ≤ δ * N := by
    have := (div_le_iff₀ hd).mp hN1
    nlinarith
  let H : ℕ := ⌈δ * (N : ℝ)⌉₊
  have hHlo : δ * N ≤ (H : ℝ) := Nat.le_ceil _
  have hHhi : (H : ℝ) ≤ 2 * δ * N := by
    have := Nat.ceil_lt_add_one (show 0 ≤ δ * (N : ℝ) by positivity)
    change (⌈δ * (N : ℝ)⌉₊ : ℝ) ≤ 2 * δ * N
    nlinarith
  have hH : 0 < (H : ℝ) := by linarith
  have hHnat : 0 < H := by exact_mod_cast hH
  have hratio : (N : ℝ) + H ≤ C * H := by
    dsimp [C]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hd).2
    nlinarith
  have hraw := henergy H hHnat
  have hcancel : k ^ 2 * (H : ℝ) ≤ ((N : ℝ) + H) * (k + H) := by
    apply (mul_le_mul_iff_left₀ hH).mp
    nlinarith only [hraw]
  have hquad : k ^ 2 ≤ ((N : ℝ) + H) + C * k := by
    apply (mul_le_mul_iff_left₀ hH).mp
    calc
      k ^ 2 * (H : ℝ) ≤ ((N : ℝ) + H) * (k + H) := hcancel
      _ = ((N : ℝ) + H) * k + ((N : ℝ) + H) * H := by ring
      _ ≤ (C * H) * k + ((N : ℝ) + H) * H :=
        by nlinarith only [mul_le_mul_of_nonneg_right hratio hk]
      _ = (((N : ℝ) + H) + C * k) * H := by ring
  have hs : Real.sqrt (N : ℝ) ^ 2 = N := Real.sq_sqrt (Nat.cast_nonneg _)
  have hs0 := Real.sqrt_nonneg (N : ℝ)
  let t : ℝ := (1 + δ) * Real.sqrt N
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hts : t ^ 2 = (1 + δ) ^ 2 * N := by
    dsimp [t]
    rw [mul_pow, hs]
  have hquad' : k ^ 2 ≤ t ^ 2 + C * k := by
    nlinarith [mul_nonneg (sq_nonneg δ) (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hbound : k ≤ t + C := by
    by_contra! hbad
    have hp : 0 < (k - (t + C)) * (k + t) :=
      mul_pos (by linarith) (by linarith)
    nlinarith [mul_nonneg hC.le ht]
  have hCr : C / δ ≤ Real.sqrt N := Real.le_sqrt_of_sq_le hN2
  have hCr' : C ≤ δ * Real.sqrt N := by
    have := (div_le_iff₀ hd).mp hCr
    nlinarith
  dsimp [t, δ] at hbound hCr' ⊢
  nlinarith

theorem proof :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∃ A : Finset ℝ, A.card = N ∧
        ∀ S : Finset ℝ, S ⊆ A → IsSidon S →
          (S.card : ℝ) ≤ (1 + ε) * Real.sqrt N := by
  intro ε hε
  filter_upwards [eventual_sqrt_bound ε hε] with N hN
  refine ⟨interval N, card_interval N, ?_⟩
  intro S hsub hS
  apply hN (S.card : ℝ) (Nat.cast_nonneg _)
  intro H hH
  exact_mod_cast sidon_interval_energy_bound N H S hsub hS

end Submissions.Erdos530SidonIntervalUpper.Main
