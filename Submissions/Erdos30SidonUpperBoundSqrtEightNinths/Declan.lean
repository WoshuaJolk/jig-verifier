import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Algebra.BigOperators.Intervals

set_option Elab.async false



/-
Finite-support Sidon convolution energy estimate, following Hou--Zhao,
Vector-valued smoothing for finite Sidon sets, arXiv:2607.01169v2, Lemma2.1.
The proof below directly injects off-diagonal convolution triples into kernel
pairs; no summability or modular embedding assumptions are required.
-/
namespace SidonConvolutionEnergy

/-- Every nonzero ordered difference in A has a unique representation. -/
def IsSidon (A : Finset ℤ) : Prop :=
  Set.InjOn (fun p : ℤ × ℤ => p.1 - p.2) (A.offDiag : Set (ℤ × ℤ))

/-- The difference definition is exactly the usual uniqueness of unordered
two-term sums; it imposes no stronger hidden Sidon hypothesis. -/
theorem isSidon_iff_unique_sums (A : Finset ℤ) :
    IsSidon A ↔
      ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
        a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  constructor
  · intro h a ha b hb c hc d hd he
    by_cases hac : a = c
    · exact Or.inl ⟨hac, by omega⟩
    · have hdb : d ≠ b := by omega
      have hp : (a, c) ∈ A.offDiag := Finset.mem_offDiag.mpr ⟨ha, hc, hac⟩
      have hq : (d, b) ∈ A.offDiag := Finset.mem_offDiag.mpr ⟨hd, hb, hdb⟩
      have hh : (a, c) = (d, b) := h hp hq (by dsimp; omega)
      have h1 := congrArg Prod.fst hh
      have h2 := congrArg Prod.snd hh
      exact Or.inr ⟨h1, h2.symm⟩
  · intro h p hp q hq he
    obtain ⟨ha, hb, hab⟩ := Finset.mem_offDiag.mp hp
    obtain ⟨hc, hd, hcd⟩ := Finset.mem_offDiag.mp hq
    have hs : p.1 + q.2 = q.1 + p.2 := by
      change p.1 - p.2 = q.1 - q.2 at he
      omega
    rcases h p.1 ha q.2 hd q.1 hc p.2 hb hs with hh | hh
    · exact Prod.ext hh.1 hh.2.symm
    · exact (hab hh.1).elim

/-- A weighted injection may ignore source terms of weight zero. -/
theorem sum_le_of_inj_nonzero {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : Finset β) (f : α → ℝ) (g : β → ℝ) (i : α → β)
    (hmaps : ∀ x ∈ s, f x ≠ 0 → i x ∈ t)
    (hinj : Set.InjOn i (s.filter (fun x => f x ≠ 0) : Set α))
    (hweight : ∀ x ∈ s, f x = g (i x))
    (hgnonneg : ∀ y ∈ t, 0 ≤ g y) :
    ∑ x ∈ s, f x ≤ ∑ y ∈ t, g y := by
  classical
  let S := s.filter (fun x => f x ≠ 0)
  calc
    ∑ x ∈ s, f x = ∑ x ∈ S, f x := (Finset.sum_filter_ne_zero s).symm
    _ = ∑ x ∈ S, g (i x) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact hweight x (Finset.mem_filter.mp hx).1
    _ = ∑ y ∈ S.image i, g y := (Finset.sum_image hinj).symm
    _ ≤ ∑ y ∈ t, g y := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro y hy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
        exact hmaps x (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2
      · exact fun y hy _ => hgnonneg y hy

/-- A translated square sum over an arbitrary finite output domain is bounded
by the full finite kernel square sum. -/
theorem translated_square_sum_le (J B : Finset ℤ) (K : ℤ → ℝ)
    (hsupport : ∀ s, s ∉ B → K s = 0) (a : ℤ) :
    ∑ n ∈ J, K (n - a) ^ 2 ≤ ∑ s ∈ B, K s ^ 2 := by
  apply sum_le_of_inj_nonzero J B (fun n => K (n - a) ^ 2)
    (fun s => K s ^ 2) (fun n => n - a)
  · intro n hn hne
    by_contra hnot
    rw [hsupport _ hnot, zero_pow (by omega)] at hne
    exact hne rfl
  · intro x hx y hy he
    change x - a = y - a at he
    omega
  · intro x hx
    rfl
  · intro y hy
    positivity

/-- The Sidon property injects every off-diagonal convolution contribution
into a different ordered off-diagonal pair of kernel positions. -/
theorem off_diagonal_energy_le (A J B : Finset ℤ) (K : ℤ → ℝ)
    (hA : IsSidon A) (hK : ∀ s, 0 ≤ K s)
    (hsupport : ∀ s, s ∉ B → K s = 0) :
    ∑ p ∈ A.offDiag, ∑ n ∈ J, K (n - p.1) * K (n - p.2) ≤
      ∑ p ∈ B.offDiag, K p.1 * K p.2 := by
  rw [← Finset.sum_product A.offDiag J
    (fun p => K (p.2 - p.1.1) * K (p.2 - p.1.2))]
  apply sum_le_of_inj_nonzero (A.offDiag ×ˢ J) B.offDiag
    (fun p => K (p.2 - p.1.1) * K (p.2 - p.1.2))
    (fun p => K p.1 * K p.2)
    (fun p => (p.2 - p.1.1, p.2 - p.1.2))
  · rintro ⟨⟨a, b⟩, n⟩ hp hne
    have hab := Finset.mem_offDiag.mp (Finset.mem_product.mp hp).1
    have habne : a ≠ b := hab.2.2
    apply Finset.mem_offDiag.mpr
    refine ⟨?_, ?_, ?_⟩
    · by_contra hnot
      simp [hsupport _ hnot] at hne
    · by_contra hnot
      simp [hsupport _ hnot] at hne
    · dsimp
      omega
  · rintro ⟨⟨a, b⟩, n⟩ hp ⟨⟨c, d⟩, m⟩ hq he
    have hpA := (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
    have hqA := (Finset.mem_product.mp (Finset.mem_filter.mp hq).1).1
    have he1 : n - a = m - c := congrArg Prod.fst he
    have he2 : n - b = m - d := congrArg Prod.snd he
    have hab : (a, b) = (c, d) := hA hpA hqA (by dsimp; omega)
    cases hab
    have hnm : n = m := by omega
    subst m
    rfl
  · intro p hp
    rfl
  · intro p hp
    exact mul_nonneg (hK _) (hK _)

/-- Exact diagonal/off-diagonal expansion of the convolution square. -/
theorem energy_split (A J : Finset ℤ) (K : ℤ → ℝ) :
    (∑ n ∈ J, (∑ a ∈ A, K (n - a)) ^ 2) =
      (∑ a ∈ A, ∑ n ∈ J, K (n - a) ^ 2) +
      ∑ p ∈ A.offDiag, ∑ n ∈ J, K (n - p.1) * K (n - p.2) := by
  calc
    _ = ∑ n ∈ J, ∑ p ∈ A ×ˢ A, K (n - p.1) * K (n - p.2) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [pow_two, Finset.sum_mul_sum, Finset.sum_product]
    _ = ∑ p ∈ A ×ˢ A, ∑ n ∈ J, K (n - p.1) * K (n - p.2) := by
      rw [Finset.sum_comm]
    _ = _ := by
      rw [← Finset.diag_union_offDiag, Finset.sum_union (Finset.disjoint_diag_offDiag A),
        Finset.sum_diag]
      simp only [pow_two]

/-- The off-diagonal mass of a kernel pair is its total squared mass minus
its diagonal square mass. -/
theorem kernel_pair_split (B : Finset ℤ) (K : ℤ → ℝ) :
    (∑ s ∈ B, K s) ^ 2 =
      (∑ s ∈ B, K s ^ 2) + ∑ p ∈ B.offDiag, K p.1 * K p.2 := by
  rw [pow_two, Finset.sum_mul_sum,
    ← Finset.sum_product B B (fun p => K p.1 * K p.2),
    ← Finset.diag_union_offDiag, Finset.sum_union (Finset.disjoint_diag_offDiag B),
    Finset.sum_diag]
  simp only [pow_two]

/-- Generic finite-support energy bound, including arbitrary finite output
truncations and empty Sidon sets. -/
theorem convolution_energy_le (A J B : Finset ℤ) (K : ℤ → ℝ)
    (hA : IsSidon A) (hK : ∀ s, 0 ≤ K s)
    (hsupport : ∀ s, s ∉ B → K s = 0) :
    (∑ n ∈ J, (∑ a ∈ A, K (n - a)) ^ 2) ≤
      (∑ s ∈ B, K s) ^ 2 + ((A.card : ℝ) - 1) * ∑ s ∈ B, K s ^ 2 := by
  rw [energy_split]
  have hdiag : (∑ a ∈ A, ∑ n ∈ J, K (n - a) ^ 2) ≤
      (A.card : ℝ) * ∑ s ∈ B, K s ^ 2 := by
    calc
      _ ≤ ∑ _a ∈ A, ∑ s ∈ B, K s ^ 2 :=
        Finset.sum_le_sum fun a ha => translated_square_sum_le J B K hsupport a
      _ = _ := by simp [nsmul_eq_mul]
  have hoff := off_diagonal_energy_le A J B K hA hK hsupport
  have hsplit := kernel_pair_split B K
  nlinarith

/-- Hou--Zhao's unit-mass scalar energy estimate (their Eq.5 before mixing). -/
theorem probability_kernel_energy_le (A J B : Finset ℤ) (K : ℤ → ℝ)
    (hA : IsSidon A) (hK : ∀ s, 0 ≤ K s)
    (hsupport : ∀ s, s ∉ B → K s = 0) (hmass : ∑ s ∈ B, K s = 1) :
    (∑ n ∈ J, (∑ a ∈ A, K (n - a)) ^ 2) ≤
      1 + ((A.card : ℝ) - 1) * ∑ s ∈ B, K s ^ 2 := by
  simpa [hmass] using convolution_energy_le A J B K hA hK hsupport

/-- Averaging preserves the sharp diagonal correction; no individual kernel
needs its own boundary covering inequality. -/
theorem weighted_probability_kernel_energy_le {R : Type*} [Fintype R]
    (A J B : Finset ℤ) (K : R → ℤ → ℝ) (lam : R → ℝ)
    (hA : IsSidon A) (hK : ∀ r s, 0 ≤ K r s)
    (hsupport : ∀ r s, s ∉ B → K r s = 0)
    (hmass : ∀ r, ∑ s ∈ B, K r s = 1)
    (hlam : ∀ r, 0 ≤ lam r) (hlammass : ∑ r, lam r = 1) :
    (∑ r, lam r * ∑ n ∈ J, (∑ a ∈ A, K r (n - a)) ^ 2) ≤
      1 + ((A.card : ℝ) - 1) * ∑ r, lam r * ∑ s ∈ B, K r s ^ 2 := by
  calc
    _ ≤ ∑ r, lam r *
        (1 + ((A.card : ℝ) - 1) * ∑ s ∈ B, K r s ^ 2) := by
      apply Finset.sum_le_sum
      intro r hr
      exact mul_le_mul_of_nonneg_left
        (probability_kernel_energy_le A J B (K r) hA (hK r)
          (hsupport r) (hmass r)) (hlam r)
    _ = _ := by
      simp_rw [mul_add, mul_one]
      rw [Finset.sum_add_distrib, hlammass]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring

#print axioms probability_kernel_energy_le
#print axioms weighted_probability_kernel_energy_le
end SidonConvolutionEnergy


/-
The finite Hilbert-space step of Hou--Zhao, arXiv:2607.01169v2, Lemma2.1.
All analytic objects are finite sums. Concrete boundary interpolation and
kernel block-mass identities are supplied separately.
-/
namespace SidonFiniteSmoothing
open SidonConvolutionEnergy

/-- Weighted Cauchy--Schwarz on a finite direct sum, allowing signed weights Q
but requiring nonnegative mixing coefficients. -/
theorem weighted_cauchy_schwarz {R : Type*} [Fintype R]
    (J : Finset ℤ) (lam : R → ℝ) (Q u : R → ℤ → ℝ)
    (hlam : ∀ r, 0 ≤ lam r) :
    (∑ r, lam r * ∑ n ∈ J, Q r n * u r n) ^ 2 ≤
      (∑ r, lam r * ∑ n ∈ J, Q r n ^ 2) *
      (∑ r, lam r * ∑ n ∈ J, u r n ^ 2) := by
  classical
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ ×ˢ J)
    (fun p : R × ℤ => Real.sqrt (lam p.1) * Q p.1 p.2)
    (fun p : R × ℤ => Real.sqrt (lam p.1) * u p.1 p.2)
  have hp (r : R) (n : ℤ) :
      (Real.sqrt (lam r) * Q r n) * (Real.sqrt (lam r) * u r n) =
      lam r * (Q r n * u r n) := by
    rw [mul_mul_mul_comm, Real.mul_self_sqrt (hlam r)]
  have hs (r : R) : Real.sqrt (lam r) ^ 2 = lam r := Real.sq_sqrt (hlam r)
  simp only [Finset.sum_product] at hcs
  simp_rw [hp, mul_pow, hs, ← Finset.mul_sum] at hcs
  exact hcs

/-- Summing the pointwise cover over A gives the weighted convolution pairing. -/
theorem cardinal_le_pairing {R : Type*} [Fintype R]
    (A J : Finset ℤ) (lam : R → ℝ) (Q K : R → ℤ → ℝ)
    (hcover : ∀ x ∈ A,
      1 ≤ ∑ r, lam r * ∑ n ∈ J, Q r n * K r (n - x)) :
    (A.card : ℝ) ≤
      ∑ r, lam r * ∑ n ∈ J, Q r n * (∑ x ∈ A, K r (n - x)) := by
  calc
    (A.card : ℝ) = ∑ _x ∈ A, (1 : ℝ) := by simp
    _ ≤ ∑ x ∈ A, ∑ r, lam r * ∑ n ∈ J, Q r n * K r (n - x) :=
      Finset.sum_le_sum fun x hx => hcover x hx
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r hr
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mul_sum]

/-- The exact finite smoothing inequality. Interval placement of A and the
boundary construction are needed only to establish the explicit cover/norm
hypotheses; this statement does not conceal either of those obligations. -/
theorem finite_smoothing_bound {R : Type*} [Fintype R]
    (A J B : Finset ℤ) (K Q : R → ℤ → ℝ) (lam : R → ℝ)
    (N a b H : ℝ)
    (hA : IsSidon A) (hK : ∀ r s, 0 ≤ K r s)
    (hsupport : ∀ r s, s ∉ B → K r s = 0)
    (hmass : ∀ r, ∑ s ∈ B, K r s = 1)
    (hlam : ∀ r, 0 ≤ lam r) (hlammass : ∑ r, lam r = 1)
    (hcover : ∀ x ∈ A,
      1 ≤ ∑ r, lam r * ∑ n ∈ J, Q r n * K r (n - x))
    (hQnorm : (∑ r, lam r * ∑ n ∈ J, Q r n ^ 2) = N + b * H - 1)
    (hKnorm : (∑ r, lam r * ∑ s ∈ B, K r s ^ 2) = a / H) :
    (A.card : ℝ) ^ 2 ≤
      (N + b * H - 1) * (1 + a * ((A.card : ℝ) - 1) / H) := by
  let u : R → ℤ → ℝ := fun r n => ∑ x ∈ A, K r (n - x)
  have hpair := cardinal_le_pairing A J lam Q K hcover
  have hcard : 0 ≤ (A.card : ℝ) := by positivity
  have hsquare : (A.card : ℝ) ^ 2 ≤
      (∑ r, lam r * ∑ n ∈ J, Q r n * u r n) ^ 2 := by
    have hp : 0 ≤
        ((∑ r, lam r * ∑ n ∈ J, Q r n * u r n) - (A.card : ℝ)) *
        ((∑ r, lam r * ∑ n ∈ J, Q r n * u r n) + (A.card : ℝ)) := by
      apply mul_nonneg <;> dsimp [u] <;> linarith
    nlinarith
  have hcs := weighted_cauchy_schwarz J lam Q u hlam
  have henergy := weighted_probability_kernel_energy_le A J B K lam
    hA hK hsupport hmass hlam hlammass
  rw [hKnorm] at henergy
  have hnormpos : 0 ≤ ∑ r, lam r * ∑ n ∈ J, Q r n ^ 2 := by
    apply Finset.sum_nonneg
    intro r hr
    exact mul_nonneg (hlam r) (Finset.sum_nonneg fun n hn => sq_nonneg _)
  calc
    (A.card : ℝ) ^ 2 ≤
        (∑ r, lam r * ∑ n ∈ J, Q r n ^ 2) *
        (∑ r, lam r * ∑ n ∈ J, u r n ^ 2) := hsquare.trans hcs
    _ ≤ (∑ r, lam r * ∑ n ∈ J, Q r n ^ 2) *
        (1 + ((A.card : ℝ) - 1) * (a / H)) :=
      mul_le_mul_of_nonneg_left henergy hnormpos
    _ = _ := by rw [hQnorm]; ring

#print axioms finite_smoothing_bound
end SidonFiniteSmoothing


namespace SidonFiniteSmoothing

/-- Exact finite support reindexing for the convolution pairing. Q may be
signed; no inequality or positivity assumption is used. -/
theorem sum_shift_support (J B : Finset ℤ) (K Q : ℤ → ℝ) (x : ℤ)
    (hsupport : ∀ s, s ∉ B → K s = 0)
    (htranslate : ∀ s ∈ B, x + s ∈ J) :
    (∑ n ∈ J, Q n * K (n - x)) = ∑ s ∈ B, Q (x + s) * K s := by
  classical
  apply Finset.sum_bij_ne_zero (fun n _ _ => n - x)
  · intro n hn hne
    by_contra hnot
    rw [hsupport _ hnot, mul_zero] at hne
    exact hne rfl
  · intro n hn hne m hm hme he
    omega
  · intro s hs hne
    refine ⟨x + s, htranslate s hs, ?_, ?_⟩
    · simpa using hne
    · omega
  · intro n hn hne
    have he : x + (n - x) = n := by omega
    rw [he]

/-- Nat-indexed boundary sums identify exactly with their integer intervals. -/
theorem sum_int_Ico_nat (M : ℕ) (f : ℤ → ℝ) :
    (∑ z ∈ Finset.Ico (0 : ℤ) (M : ℤ), f z) =
      ∑ n ∈ Finset.range M, f (n : ℤ) := by
  classical
  symm
  apply Finset.sum_bij (fun (n : ℕ) _ => (n : ℤ))
  · intro n hn
    simp only [Finset.mem_range] at hn
    simp only [Finset.mem_Ico]
    omega
  · intro n hn m hm he
    omega
  · intro z hz
    simp only [Finset.mem_Ico] at hz
    refine ⟨z.toNat, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · omega
  · intro n hn
    rfl

#print axioms sum_shift_support
#print axioms sum_int_Ico_nat
end SidonFiniteSmoothing


namespace SidonBoundary

open scoped BigOperators
set_option linter.unusedSimpArgs false

theorem sum_range_blocks (m h : ℕ) (f : ℕ → ℝ) :
    ∑ s ∈ Finset.range (m*h), f s =
      ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range h, f (i*h+j) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, Finset.sum_range_succ, ih]

theorem div_block (q h t : ℕ) (hh : 0 < h) (ht : t < h) : (q*h+t)/h = q := by
  rw [Nat.add_comm, Nat.add_mul_div_right t q hh, Nat.div_eq_of_lt ht]
  simp

theorem div_shifted_block (q i h t j : ℕ) (hh : 0 < h) :
    (q*h+t+(i*h+j))/h = q+i+(t+j)/h := by
  have heq : q*h+t+(i*h+j) = (t+j)+(q+i)*h := by ring
  rw [heq, Nat.add_mul_div_right _ _ hh]
  omega

theorem block_weight_sum (h t a : ℕ) (hh : 0 < h) (ht : t < h) (w : ℕ → ℝ) :
    (∑ j ∈ Finset.range h, w (a+(t+j)/h)) =
      ((h:ℝ)-t)*w a + (t:ℝ)*w (a+1) := by
  have hleft : ∑ j ∈ Finset.range (h-t), w (a+(t+j)/h) = (h-t:ℕ)*w a := by
    calc
      _ = ∑ _j ∈ Finset.range (h-t), w a := by
        apply Finset.sum_congr rfl
        intro j hj
        have hj' := Finset.mem_range.mp hj
        rw [Nat.div_eq_of_lt (by omega : t+j<h), Nat.add_zero]
      _ = _ := by simp
  have hright : ∑ j ∈ Finset.range t, w (a+(t+(h-t+j))/h) = (t:ℝ)*w (a+1) := by
    calc
      _ = ∑ _j ∈ Finset.range t, w (a+1) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hj' := Finset.mem_range.mp hj
        have heq : t+(h-t+j) = h+j := by omega
        rw [heq, Nat.add_div_left j hh, Nat.div_eq_of_lt (by omega : j<h)]
      _ = _ := by simp
  calc
    _ = (∑ j ∈ Finset.range (h-t), w (a+(t+j)/h)) +
        ∑ j ∈ Finset.range t, w (a+(t+(h-t+j))/h) := by
      simpa only [Nat.sub_add_cancel ht.le] using
        Finset.sum_range_add (fun j => w (a+(t+j)/h)) (h-t) t
    _ = _ := by rw [hleft, hright, Nat.cast_sub ht.le]

theorem interpolation (m h q t : ℕ) (hh : 0 < h) (ht : t < h) (p w : ℕ → ℝ) :
    (∑ s ∈ Finset.range (m*h), (p (s/h) / h) * w ((q*h+t+s)/h)) =
      (1-(t:ℝ)/h) * (∑ i ∈ Finset.range m, p i*w (q+i)) +
      ((t:ℝ)/h) * (∑ i ∈ Finset.range m, p i*w (q+i+1)) := by
  rw [sum_range_blocks]
  have hR : (h:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hh)
  calc
    _ = ∑ i ∈ Finset.range m,
        (p i / h) * (((h:ℝ)-t)*w (q+i) + (t:ℝ)*w (q+i+1)) := by
      apply Finset.sum_congr rfl
      intro i hi
      calc
        _ = ∑ j ∈ Finset.range h, (p i / h) * w (q+i+(t+j)/h) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [div_block i h j hh (Finset.mem_range.mp hj), div_shifted_block q i h t j hh]
        _ = _ := by rw [← Finset.mul_sum, block_weight_sum h t (q+i) hh ht w]
    _ = _ := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      field_simp

#print axioms interpolation


variable {R : Type*} [Fintype R]

theorem weighted_interpolation (m h q t : ℕ) (hh : 0 < h) (ht : t < h)
    (lam : R → ℝ) (p w : R → ℕ → ℝ) :
    (∑ r, lam r * ∑ s ∈ Finset.range (m*h), (p r (s/h) / h) * w r ((q*h+t+s)/h)) =
      (1-(t:ℝ)/h) * (∑ r, lam r * ∑ i ∈ Finset.range m, p r i*w r (q+i)) +
      ((t:ℝ)/h) * (∑ r, lam r * ∑ i ∈ Finset.range m, p r i*w r (q+i+1)) := by
  simp_rw [interpolation m h q t hh ht]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro r hr <;> ring

theorem interpolated_cover (m h M x : ℕ) (hh : 0 < h) (hx : x < M*h)
    (lam : R → ℝ) (p w : R → ℕ → ℝ)
    (hc : ∀ q ≤ M, 1 ≤ ∑ r, lam r * ∑ i ∈ Finset.range m, p r i*w r (q+i)) :
    1 ≤ ∑ r, lam r * ∑ s ∈ Finset.range (m*h), (p r (s/h) / h)*w r ((x+s)/h) := by
  let q := x/h
  let t := x%h
  have ht : t < h := Nat.mod_lt _ hh
  have hq : q < M := (Nat.div_lt_iff_lt_mul hh).mpr hx
  have hxt : q*h+t = x := by simpa [q, t, Nat.mul_comm] using Nat.div_add_mod x h
  rw [← hxt, weighted_interpolation m h q t hh ht]
  have hhR : (0:ℝ) < h := by exact_mod_cast hh
  have htR : (t:ℝ) < h := by exact_mod_cast ht
  have hz : 0 ≤ (t:ℝ)/h := by positivity
  have ho : 0 ≤ 1-(t:ℝ)/h := by apply sub_nonneg.mpr; exact (div_le_one hhR).mpr htR.le
  have h1 := mul_le_mul_of_nonneg_left (hc q hq.le) ho
  have h2 := mul_le_mul_of_nonneg_left (hc (q+1) hq) hz
  simp only [Nat.add_right_comm q 1] at h2
  linarith

/-- Reflected boundary weights on positions 0,...,T−1. T≥2D keeps the two
D-point boundary regions disjoint. Values outside this interval are irrelevant. -/
def boundary (T D h : ℕ) (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n < D then w (n/h) else if T-1-n < D then w ((T-1-n)/h) else 1

theorem boundary_reflect (T D h n : ℕ) (hT : 2*D ≤ T) (hn : n < T) (w : ℕ → ℝ) :
    boundary T D h w (T-1-n) = boundary T D h w n := by
  have hinv : T-1-(T-1-n) = n := by omega
  have hd : ¬ (n<D ∧ T-1-n<D) := by omega
  unfold boundary
  rw [hinv]
  split_ifs <;> aesop

theorem boundary_square (T D h n : ℕ) (hT : 2*D ≤ T) (hn : n < T) (w : ℕ → ℝ) :
    (boundary T D h w n)^2 = 1 +
      (if n<D then (w (n/h))^2-1 else 0) +
      (if T-1-n<D then (w ((T-1-n)/h))^2-1 else 0) := by
  have hd : ¬ (n<D ∧ T-1-n<D) := by omega
  unfold boundary
  split_ifs <;> simp_all

theorem truncate_sum (T D : ℕ) (hD : D ≤ T) (f : ℕ → ℝ) :
    (∑ n ∈ Finset.range T, if n<D then f n else 0) = ∑ n ∈ Finset.range D, f n := by
  calc
    _ = (∑ n ∈ Finset.range D, if n<D then f n else 0) +
        ∑ n ∈ Finset.range (T-D), if D+n<D then f (D+n) else 0 := by
      simpa only [Nat.add_sub_of_le hD] using
        Finset.sum_range_add (fun n => if n<D then f n else 0) D (T-D)
    _ = _ := by
      have hs : (∑ n ∈ Finset.range (T-D), if D+n<D then f (D+n) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro n hn
        exact if_neg (by omega)
      rw [hs, add_zero]
      apply Finset.sum_congr rfl
      intro n hn
      exact if_pos (Finset.mem_range.mp hn)

theorem block_sum (M h : ℕ) (hh : 0 < h) (f : ℕ → ℝ) :
    (∑ n ∈ Finset.range (M*h), f (n/h)) = (h:ℝ)*∑ j ∈ Finset.range M, f j := by
  rw [sum_range_blocks, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    _ = ∑ _j ∈ Finset.range h, f i := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [div_block i h j hh (Finset.mem_range.mp hj)]
    _ = _ := by simp

theorem boundary_norm (T M h : ℕ) (hh : 0 < h) (hT : 2*(M*h) ≤ T) (w : ℕ → ℝ) :
    (∑ n ∈ Finset.range T, (boundary T (M*h) h w n)^2) =
      (T:ℝ) + 2*((h:ℝ)*∑ j ∈ Finset.range M, (w j)^2 - M*h) := by
  have hD : M*h ≤ T := by omega
  have hpoint : ∀ n ∈ Finset.range T, (boundary T (M*h) h w n)^2 =
      1 + (if n<M*h then (w (n/h))^2-1 else 0) +
      (if T-1-n<M*h then (w ((T-1-n)/h))^2-1 else 0) := by
    intro n hn
    exact boundary_square T (M*h) h n hT (Finset.mem_range.mp hn) w
  rw [Finset.sum_congr rfl hpoint]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [Finset.sum_range_reflect (fun n => if n<M*h then (w (n/h))^2-1 else 0),
    truncate_sum T (M*h) hD, Finset.sum_sub_distrib, block_sum M h hh (fun j => (w j)^2)]
  simp
  ring

#print axioms interpolated_cover
#print axioms boundary_norm


theorem boundary_left (N H M h x s : ℕ) (_hH : 0 < H) (hh : 0 < h)
    (hN : 2*(M*h) ≤ N) (hx : x < M*h) (hs : s < H)
    (w : ℕ → ℝ) (hw : ∀ j, M ≤ j → w j = 1) :
    boundary (N+H-1) (M*h) h w (x+s) = w ((x+s)/h) := by
  have hfar : M*h ≤ N+H-1-1-(x+s) := by omega
  unfold boundary
  rw [if_neg (by omega : ¬ N+H-1-1-(x+s)<M*h)]
  split_ifs with hx'
  · rfl
  · symm
    apply hw
    exact (Nat.le_div_iff_mul_le hh).mpr (by omega)

theorem boundary_middle (N H D h x s : ℕ) (_hH : 0 < H)
    (hx : D ≤ x) (hx' : x < N-D) (hs : s < H) (w : ℕ → ℝ) :
    boundary (N+H-1) D h w (x+s) = 1 := by
  unfold boundary
  rw [if_neg (by omega : ¬ x+s<D), if_neg (by omega : ¬ N+H-1-1-(x+s)<D)]

theorem kernel_mass (m h : ℕ) (hh : 0 < h) (p : ℕ → ℝ)
    (hp : ∑ i ∈ Finset.range m, p i = 1) :
    (∑ s ∈ Finset.range (m*h), p (s/h)/h) = 1 := by
  rw [block_sum m h hh (fun i => p i / h), ← Finset.sum_div, hp]
  have hR : (h:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hh)
  field_simp

theorem kernel_reflect (m h s : ℕ) (hh : 0 < h) (hs : s < m*h) (p : ℕ → ℝ)
    (hp : ∀ i < m, p (m-1-i) = p i) :
    p ((m*h-1-s)/h) / h = p (s/h) / h := by
  have hdiv : (m*h-1-s)/h = m-1-s/h := by
    have heq : m*h-1-s = h*m-(s+1) := by rw [Nat.sub_sub, Nat.mul_comm m h, Nat.add_comm 1 s]
    rw [heq, Nat.mul_sub_div s h m (by simpa [Nat.mul_comm] using hs)]
    omega
  rw [hdiv, hp (s/h) ((Nat.div_lt_iff_lt_mul hh).mpr hs)]

theorem boundary_window_reflect (N H D h x s : ℕ) (hH : 0 < H)
    (hN : 2*D ≤ N) (hx : x < N) (hs : s < H) (w : ℕ → ℝ) :
    boundary (N+H-1) D h w (x+(H-1-s)) =
      boundary (N+H-1) D h w (N-1-x+s) := by
  have hi : N+H-1-1-(x+(H-1-s)) = N-1-x+s := by omega
  have hr := boundary_reflect (N+H-1) D h (x+(H-1-s)) (by omega) (by omega) w
  rw [hi] at hr
  exact hr.symm

theorem convolution_reflect (N m h M x : ℕ) (hm : 0 < m) (hh : 0 < h)
    (hN : 2*(M*h) ≤ N) (hx : x < N) (p w : ℕ → ℝ)
    (hp : ∀ i < m, p (m-1-i) = p i) :
    (∑ s ∈ Finset.range (m*h), (p (s/h)/h)*boundary (N+m*h-1) (M*h) h w (x+s)) =
      ∑ s ∈ Finset.range (m*h), (p (s/h)/h)*boundary (N+m*h-1) (M*h) h w (N-1-x+s) := by
  have hH : 0 < m*h := Nat.mul_pos hm hh
  calc
    _ = ∑ s ∈ Finset.range (m*h), (p ((m*h-1-s)/h)/h)*
        boundary (N+m*h-1) (M*h) h w (x+(m*h-1-s)) := by
      exact (Finset.sum_range_reflect _ (m*h)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s hs
      have hs' := Finset.mem_range.mp hs
      rw [kernel_reflect m h s hh hs' p hp,
        boundary_window_reflect N (m*h) (M*h) h x s hH hN hx hs' w]

theorem actual_boundary_cover (N m h M x : ℕ) (hm : 0 < m) (hh : 0 < h)
    (hN : 2*(M*h) ≤ N) (hx : x < N) (lam : R → ℝ) (p w : R → ℕ → ℝ)
    (hlam : ∑ r, lam r = 1) (hmass : ∀ r, ∑ i ∈ Finset.range m, p r i = 1)
    (hsym : ∀ r i, i < m → p r (m-1-i) = p r i)
    (hw : ∀ r j, M ≤ j → w r j = 1)
    (hc : ∀ q ≤ M, 1 ≤ ∑ r, lam r * ∑ i ∈ Finset.range m, p r i*w r (q+i)) :
    1 ≤ ∑ r, lam r * ∑ s ∈ Finset.range (m*h),
      (p r (s/h)/h)*boundary (N+m*h-1) (M*h) h (w r) (x+s) := by
  have hH : 0 < m*h := Nat.mul_pos hm hh
  have hleft : ∀ y < M*h, 1 ≤ ∑ r, lam r * ∑ s ∈ Finset.range (m*h),
      (p r (s/h)/h)*boundary (N+m*h-1) (M*h) h (w r) (y+s) := by
    intro y hy
    have heq : (∑ r, lam r * ∑ s ∈ Finset.range (m*h),
        (p r (s/h)/h)*boundary (N+m*h-1) (M*h) h (w r) (y+s)) =
        ∑ r, lam r * ∑ s ∈ Finset.range (m*h), (p r (s/h)/h)*w r ((y+s)/h) := by
      apply Finset.sum_congr rfl
      intro r hr
      congr 1
      apply Finset.sum_congr rfl
      intro s hs
      rw [boundary_left N (m*h) M h y s hH hh hN hy (Finset.mem_range.mp hs) (w r) (hw r)]
    rw [heq]
    exact interpolated_cover m h M y hh hy lam p w hc
  by_cases hxl : x < M*h
  · exact hleft x hxl
  by_cases hxr : N-M*h ≤ x
  · have hy : N-1-x < M*h := by omega
    have heq : (∑ r, lam r * ∑ s ∈ Finset.range (m*h),
        (p r (s/h)/h)*boundary (N+m*h-1) (M*h) h (w r) (x+s)) =
        ∑ r, lam r * ∑ s ∈ Finset.range (m*h),
        (p r (s/h)/h)*boundary (N+m*h-1) (M*h) h (w r) (N-1-x+s) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [convolution_reflect N m h M x hm hh hN hx (p r) (w r) (hsym r)]
    rw [heq]
    exact hleft _ hy
  · have hone : ∀ r, (∑ s ∈ Finset.range (m*h),
        (p r (s/h)/h)*boundary (N+m*h-1) (M*h) h (w r) (x+s)) = 1 := by
      intro r
      calc
        _ = ∑ s ∈ Finset.range (m*h), p r (s/h)/h := by
          apply Finset.sum_congr rfl
          intro s hs
          rw [boundary_middle N (m*h) (M*h) h x s hH (by omega) (by omega)
            (Finset.mem_range.mp hs) (w r), mul_one]
        _ = 1 := kernel_mass m h hh (p r) (hmass r)
    simp_rw [hone, mul_one]
    rw [hlam]

#print axioms actual_boundary_cover


theorem weighted_boundary_norm (T M h : ℕ) (hh : 0 < h) (hT : 2*(M*h) ≤ T)
    (lam : R → ℝ) (w : R → ℕ → ℝ) (hlam : ∑ r, lam r = 1) :
    (∑ r, lam r * ∑ n ∈ Finset.range T, (boundary T (M*h) h (w r) n)^2) =
      (T:ℝ) + 2*((h:ℝ)*(∑ r, lam r * ∑ j ∈ Finset.range M, (w r j)^2) - M*h) := by
  simp_rw [boundary_norm T M h hh hT]
  have heq : ∀ r, lam r * ((T:ℝ)+2*((h:ℝ)*(∑ j ∈ Finset.range M, (w r j)^2)-M*h)) =
      (T:ℝ)*lam r + (2*(h:ℝ))*(lam r*∑ j ∈ Finset.range M, (w r j)^2) -
        (2*(M:ℝ)*h)*lam r := by intro r; ring
  simp_rw [heq, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hlam]
  ring

theorem weighted_boundary_norm_sidon (N m h L : ℕ) (hm : 0 < m) (hh : 0 < h)
    (hN : 2*(L*m*h) ≤ N) (lam : R → ℝ) (w : R → ℕ → ℝ)
    (hlam : ∑ r, lam r = 1) :
    (∑ r, lam r * ∑ n ∈ Finset.range (N+m*h-1),
      (boundary (N+m*h-1) (L*m*h) h (w r) n)^2) =
      (N:ℝ) + (1+2*((∑ r, lam r * ∑ j ∈ Finset.range (L*m), (w r j)^2)/(m:ℝ)-L)) *
        ((m:ℝ)*h)-1 := by
  have hH : 0 < m*h := Nat.mul_pos hm hh
  rw [weighted_boundary_norm (N+m*h-1) (L*m) h hh (by omega) lam w hlam]
  rw [Nat.cast_sub (by omega : 1 ≤ N+m*h), Nat.cast_add, Nat.cast_mul, Nat.cast_one,
    Nat.cast_mul]
  have hmR : (m:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  field_simp
  ring

#print axioms weighted_boundary_norm_sidon

end SidonBoundary


namespace SidonConcrete
open SidonConvolutionEnergy SidonFiniteSmoothing SidonBoundary

variable {R : Type*} [Fintype R]

noncomputable def blockKernel (m h : ℕ) (p : ℕ → ℝ) (s : ℤ) : ℝ :=
  if 0 ≤ s ∧ s < (m*h : ℕ) then p (s.toNat/h)/(h:ℝ) else 0

def blockWeight (N m h L : ℕ) (w : ℕ → ℝ) (z : ℤ) : ℝ :=
  boundary (N+m*h-1) (L*m*h) h w z.toNat

def aValue (m : ℕ) (lam : R → ℝ) (p : R → ℕ → ℝ) : ℝ :=
  (m:ℝ) * ∑ r, lam r * ∑ i ∈ Finset.range m, p r i ^ 2

noncomputable def bValue (m L : ℕ) (lam : R → ℝ) (w : R → ℕ → ℝ) : ℝ :=
  1 + 2 * ((∑ r, lam r * ∑ j ∈ Finset.range (L*m), w r j ^ 2)/(m:ℝ) - L)

theorem blockKernel_nat (m h s : ℕ) (p : ℕ → ℝ) (hs : s < m*h) :
    blockKernel m h p (s:ℤ) = p (s/h)/(h:ℝ) := by
  unfold blockKernel
  rw [if_pos (by omega)]
  simp

theorem blockKernel_support (m h : ℕ) (p : ℕ → ℝ) :
    ∀ s, s ∉ Finset.Ico (0:ℤ) (m*h:ℕ) → blockKernel m h p s = 0 := by
  intro s hs
  exact if_neg (by simpa only [Finset.mem_Ico] using hs)

theorem blockKernel_nonneg (m h : ℕ) (hh : 0 < h) (p : ℕ → ℝ)
    (hp : ∀ i < m, 0 ≤ p i) : ∀ s, 0 ≤ blockKernel m h p s := by
  intro s
  unfold blockKernel
  split_ifs with hs
  · apply div_nonneg
    · apply hp
      apply (Nat.div_lt_iff_lt_mul hh).mpr
      omega
    · positivity
  · rfl

theorem blockKernel_mass (m h : ℕ) (hh : 0 < h) (p : ℕ → ℝ)
    (hp : ∑ i ∈ Finset.range m, p i = 1) :
    (∑ s ∈ Finset.Ico (0:ℤ) (m*h:ℕ), blockKernel m h p s) = 1 := by
  rw [sum_int_Ico_nat]
  calc
    _ = ∑ s ∈ Finset.range (m*h), p (s/h)/(h:ℝ) := by
      apply Finset.sum_congr rfl
      intro s hs
      exact blockKernel_nat m h s p (Finset.mem_range.mp hs)
    _ = 1 := kernel_mass m h hh p hp

theorem blockKernel_square_mass (m h : ℕ) (hh : 0 < h) (p : ℕ → ℝ) :
    (∑ s ∈ Finset.Ico (0:ℤ) (m*h:ℕ), blockKernel m h p s ^ 2) =
      (∑ i ∈ Finset.range m, p i ^ 2)/(h:ℝ) := by
  rw [sum_int_Ico_nat]
  have hhR : (h:ℝ) ≠ 0 := by positivity
  calc
    _ = ∑ s ∈ Finset.range (m*h), (p (s/h)/(h:ℝ)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [blockKernel_nat m h s p (Finset.mem_range.mp hs)]
    _ = _ := by
      rw [block_sum m h hh (fun i => (p i/(h:ℝ)) ^ 2)]
      simp_rw [div_pow]
      rw [← Finset.sum_div]
      field_simp

theorem weighted_kernel_square_mass (m h : ℕ) (hm : 0 < m) (hh : 0 < h)
    (lam : R → ℝ) (p : R → ℕ → ℝ) :
    (∑ r, lam r * ∑ s ∈ Finset.Ico (0:ℤ) (m*h:ℕ), blockKernel m h (p r) s ^ 2) =
      aValue m lam p / ((m:ℝ)*h) := by
  simp_rw [blockKernel_square_mass m h hh, ← mul_div_assoc]
  rw [← Finset.sum_div]
  unfold aValue
  have hmR : (m:ℝ) ≠ 0 := by positivity
  have hhR : (h:ℝ) ≠ 0 := by positivity
  field_simp


end SidonConcrete

/-! The preceding unchanged foundation is copied from the verified round-two
UpperBoundDeclanV2.lean, stopping before its symmetric certificate pairing.
The following extension uses separate boundary weights and no kernel symmetry. -/
namespace SidonAsymmetric
open SidonConvolutionEnergy SidonFiniteSmoothing

set_option maxHeartbeats 0

def reverse (m : ℕ) (p : ℕ → ℝ) (i : ℕ) : ℝ := p (m-1-i)

def boundary (T D h : ℕ) (wLeft wRight : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n < D then wLeft (n/h)
  else if T-1-n < D then wRight ((T-1-n)/h) else 1

theorem boundary_reflect_swap (T D h n : ℕ) (hT : 2*D ≤ T) (hn : n < T)
    (wLeft wRight : ℕ → ℝ) :
    boundary T D h wLeft wRight (T-1-n) = boundary T D h wRight wLeft n := by
  have hinv : T-1-(T-1-n) = n := by omega
  have hd : ¬ (n<D ∧ T-1-n<D) := by omega
  unfold boundary
  rw [hinv]
  split_ifs <;> aesop

theorem boundary_square (T D h n : ℕ) (hT : 2*D ≤ T) (hn : n < T)
    (wLeft wRight : ℕ → ℝ) :
    (boundary T D h wLeft wRight n)^2 = 1 +
      (if n<D then (wLeft (n/h))^2-1 else 0) +
      (if T-1-n<D then (wRight ((T-1-n)/h))^2-1 else 0) := by
  have hd : ¬ (n<D ∧ T-1-n<D) := by omega
  unfold boundary
  split_ifs <;> simp_all

theorem boundary_norm (T M h : ℕ) (hh : 0 < h) (hT : 2*(M*h) ≤ T)
    (wLeft wRight : ℕ → ℝ) :
    (∑ n ∈ Finset.range T, (boundary T (M*h) h wLeft wRight n)^2) =
      (T:ℝ) + (h:ℝ)*(∑ j ∈ Finset.range M, (wLeft j)^2) +
        (h:ℝ)*(∑ j ∈ Finset.range M, (wRight j)^2) - 2*(M:ℝ)*h := by
  have hD : M*h ≤ T := by omega
  have hpoint : ∀ n ∈ Finset.range T, (boundary T (M*h) h wLeft wRight n)^2 =
      1 + (if n<M*h then (wLeft (n/h))^2-1 else 0) +
      (if T-1-n<M*h then (wRight ((T-1-n)/h))^2-1 else 0) := by
    intro n hn
    exact boundary_square T (M*h) h n hT (Finset.mem_range.mp hn) wLeft wRight
  rw [Finset.sum_congr rfl hpoint]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one]
  rw [Finset.sum_range_reflect (fun n => if n<M*h then (wRight (n/h))^2-1 else 0),
    SidonBoundary.truncate_sum T (M*h) hD,
    SidonBoundary.truncate_sum T (M*h) hD,
    Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    SidonBoundary.block_sum M h hh (fun j => (wLeft j)^2),
    SidonBoundary.block_sum M h hh (fun j => (wRight j)^2)]
  simp
  ring

theorem boundary_left (N H M h x s : ℕ) (_hH : 0 < H) (hh : 0 < h)
    (hN : 2*(M*h) ≤ N) (hx : x < M*h) (hs : s < H)
    (wLeft wRight : ℕ → ℝ) (hw : ∀ j, M ≤ j → wLeft j = 1) :
    boundary (N+H-1) (M*h) h wLeft wRight (x+s) = wLeft ((x+s)/h) := by
  have hfar : M*h ≤ N+H-1-1-(x+s) := by omega
  unfold boundary
  rw [if_neg (by omega : ¬ N+H-1-1-(x+s)<M*h)]
  split_ifs with hx'
  · rfl
  · symm
    apply hw
    exact (Nat.le_div_iff_mul_le hh).mpr (by omega)

theorem boundary_middle (N H D h x s : ℕ) (_hH : 0 < H)
    (hx : D ≤ x) (hx' : x < N-D) (hs : s < H) (wLeft wRight : ℕ → ℝ) :
    boundary (N+H-1) D h wLeft wRight (x+s) = 1 := by
  unfold boundary
  rw [if_neg (by omega : ¬ x+s<D),
    if_neg (by omega : ¬ N+H-1-1-(x+s)<D)]

theorem kernel_reverse (m h s : ℕ) (hh : 0 < h) (hs : s < m*h) (p : ℕ → ℝ) :
    p ((m*h-1-s)/h) / h = reverse m p (s/h) / h := by
  have hdiv : (m*h-1-s)/h = m-1-s/h := by
    have heq : m*h-1-s = h*m-(s+1) := by
      rw [Nat.sub_sub, Nat.mul_comm m h, Nat.add_comm 1 s]
    rw [heq, Nat.mul_sub_div s h m (by simpa [Nat.mul_comm] using hs)]
    omega
  rw [hdiv]
  rfl

theorem boundary_window_reflect (N H D h x s : ℕ) (hH : 0 < H)
    (hN : 2*D ≤ N) (hx : x < N) (hs : s < H) (wLeft wRight : ℕ → ℝ) :
    boundary (N+H-1) D h wLeft wRight (x+(H-1-s)) =
      boundary (N+H-1) D h wRight wLeft (N-1-x+s) := by
  have hi : N+H-1-1-(x+(H-1-s)) = N-1-x+s := by omega
  have hr := boundary_reflect_swap (N+H-1) D h (x+(H-1-s))
    (by omega) (by omega) wRight wLeft
  rw [hi] at hr
  exact hr.symm

theorem convolution_reflect (N m h M x : ℕ) (hm : 0 < m) (hh : 0 < h)
    (hN : 2*(M*h) ≤ N) (hx : x < N) (p wLeft wRight : ℕ → ℝ) :
    (∑ s ∈ Finset.range (m*h), (p (s/h)/h)*
      boundary (N+m*h-1) (M*h) h wLeft wRight (x+s)) =
    ∑ s ∈ Finset.range (m*h), (reverse m p (s/h)/h)*
      boundary (N+m*h-1) (M*h) h wRight wLeft (N-1-x+s) := by
  have hH : 0 < m*h := Nat.mul_pos hm hh
  calc
    _ = ∑ s ∈ Finset.range (m*h), (p ((m*h-1-s)/h)/h)*
        boundary (N+m*h-1) (M*h) h wLeft wRight (x+(m*h-1-s)) := by
      exact (Finset.sum_range_reflect _ (m*h)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s hs
      have hs' := Finset.mem_range.mp hs
      rw [kernel_reverse m h s hh hs' p,
        boundary_window_reflect N (m*h) (M*h) h x s hH hN hx hs' wLeft wRight]

theorem interpolated_cover (m h M x : ℕ) (hh : 0 < h) (hx : x < M*h)
    (p w : ℕ → ℝ)
    (hc : ∀ q ≤ M, 1 ≤ ∑ i ∈ Finset.range m, p i*w (q+i)) :
    1 ≤ ∑ s ∈ Finset.range (m*h), (p (s/h)/h)*w ((x+s)/h) := by
  have hh' := SidonBoundary.interpolated_cover m h M x hh hx
    (fun _ : Unit => (1:ℝ)) (fun _ => p) (fun _ => w)
    (by intro q hq; simpa using hc q hq)
  simpa using hh'

theorem actual_left_cover (N m h M x : ℕ) (hm : 0 < m) (hh : 0 < h)
    (hN : 2*(M*h) ≤ N) (hx : x < M*h) (p wLeft wRight : ℕ → ℝ)
    (hw : ∀ j, M ≤ j → wLeft j = 1)
    (hc : ∀ q ≤ M, 1 ≤ ∑ i ∈ Finset.range m, p i*wLeft (q+i)) :
    1 ≤ ∑ s ∈ Finset.range (m*h), (p (s/h)/h)*
      boundary (N+m*h-1) (M*h) h wLeft wRight (x+s) := by
  have hH : 0 < m*h := Nat.mul_pos hm hh
  have heq : (∑ s ∈ Finset.range (m*h), (p (s/h)/h)*
      boundary (N+m*h-1) (M*h) h wLeft wRight (x+s)) =
      ∑ s ∈ Finset.range (m*h), (p (s/h)/h)*wLeft ((x+s)/h) := by
    apply Finset.sum_congr rfl
    intro s hs
    rw [boundary_left N (m*h) M h x s hH hh hN hx
      (Finset.mem_range.mp hs) wLeft wRight hw]
  rw [heq]
  exact interpolated_cover m h M x hh hx p wLeft hc

theorem actual_boundary_cover (N m h M x : ℕ) (hm : 0 < m) (hh : 0 < h)
    (hN : 2*(M*h) ≤ N) (hx : x < N) (p wLeft wRight : ℕ → ℝ)
    (hmass : ∑ i ∈ Finset.range m, p i = 1)
    (hwLeft : ∀ j, M ≤ j → wLeft j = 1)
    (hwRight : ∀ j, M ≤ j → wRight j = 1)
    (hcLeft : ∀ q ≤ M, 1 ≤ ∑ i ∈ Finset.range m, p i*wLeft (q+i))
    (hcRight : ∀ q ≤ M, 1 ≤ ∑ i ∈ Finset.range m, reverse m p i*wRight (q+i)) :
    1 ≤ ∑ s ∈ Finset.range (m*h), (p (s/h)/h)*
      boundary (N+m*h-1) (M*h) h wLeft wRight (x+s) := by
  have hH : 0 < m*h := Nat.mul_pos hm hh
  by_cases hxl : x < M*h
  · exact actual_left_cover N m h M x hm hh hN hxl p wLeft wRight hwLeft hcLeft
  by_cases hxr : N-M*h ≤ x
  · have hy : N-1-x < M*h := by omega
    rw [convolution_reflect N m h M x hm hh hN hx p wLeft wRight]
    exact actual_left_cover N m h M (N-1-x) hm hh hN hy
      (reverse m p) wRight wLeft hwRight hcRight
  · have he : (∑ s ∈ Finset.range (m*h), (p (s/h)/h)*
        boundary (N+m*h-1) (M*h) h wLeft wRight (x+s)) = 1 := by
      calc
        _ = ∑ s ∈ Finset.range (m*h), p (s/h)/h := by
          apply Finset.sum_congr rfl
          intro s hs
          rw [boundary_middle N (m*h) (M*h) h x s hH (by omega) (by omega)
            (Finset.mem_range.mp hs) wLeft wRight, mul_one]
        _ = 1 := SidonBoundary.kernel_mass m h hh p hmass
    rw [he]

#print axioms boundary_norm
#print axioms convolution_reflect
#print axioms actual_boundary_cover

def aValue (m : ℕ) (p : ℕ → ℝ) : ℝ :=
  (m:ℝ) * ∑ i ∈ Finset.range m, p i ^ 2

noncomputable def bValue (m L : ℕ) (wLeft wRight : ℕ → ℝ) : ℝ :=
  1 + ((∑ j ∈ Finset.range (L*m), wLeft j ^ 2) +
    (∑ j ∈ Finset.range (L*m), wRight j ^ 2))/(m:ℝ) - 2*L

def blockWeight (N m h L : ℕ) (wLeft wRight : ℕ → ℝ) (z : ℤ) : ℝ :=
  boundary (N+m*h-1) (L*m*h) h wLeft wRight z.toNat

theorem boundary_norm_sidon (N m h L : ℕ) (hm : 0 < m) (hh : 0 < h)
    (hN : 2*(L*m*h) ≤ N) (wLeft wRight : ℕ → ℝ) :
    (∑ n ∈ Finset.range (N+m*h-1),
      (boundary (N+m*h-1) (L*m*h) h wLeft wRight n)^2) =
      (N:ℝ) + bValue m L wLeft wRight*((m:ℝ)*h)-1 := by
  have hH : 0 < m*h := Nat.mul_pos hm hh
  rw [boundary_norm (N+m*h-1) (L*m) h hh (by omega) wLeft wRight]
  rw [Nat.cast_sub (by omega : 1 ≤ N+m*h), Nat.cast_add, Nat.cast_mul,
    Nat.cast_one, Nat.cast_mul]
  have hmR : (m:ℝ) ≠ 0 := by positivity
  unfold bValue
  field_simp
  ring

/-- Actual finite support reindexing, with distinct left and right weights. -/
theorem block_pairing (N m h L : ℕ) (hm : 0 < m) (hh : 0 < h)
    (p wLeft wRight : ℕ → ℝ) (x : ℤ) (hx : x ∈ Finset.Ico (0:ℤ) (N:ℤ)) :
    (∑ n ∈ Finset.Ico (0:ℤ) (N+m*h-1:ℕ),
      blockWeight N m h L wLeft wRight n * SidonConcrete.blockKernel m h p (n-x)) =
    ∑ s ∈ Finset.range (m*h), (p (s/h)/(h:ℝ)) *
      boundary (N+m*h-1) (L*m*h) h wLeft wRight (x.toNat+s) := by
  have hx0 := (Finset.mem_Ico.mp hx).1
  have hxN := (Finset.mem_Ico.mp hx).2
  have hH : 0 < m*h := Nat.mul_pos hm hh
  rw [sum_shift_support _ (Finset.Ico (0:ℤ) (m*h:ℕ)) _ _ x
    (SidonConcrete.blockKernel_support m h p)]
  · rw [sum_int_Ico_nat]
    apply Finset.sum_congr rfl
    intro s hs
    rw [SidonConcrete.blockKernel_nat m h s p (Finset.mem_range.mp hs)]
    unfold blockWeight
    have he : (x + (s:ℤ)).toNat = x.toNat + s := by omega
    rw [he, mul_comm]
  · intro s hs
    have hs0 := (Finset.mem_Ico.mp hs).1
    have hsH := (Finset.mem_Ico.mp hs).2
    apply Finset.mem_Ico.mpr
    constructor <;> omega

theorem block_cover (N m h L : ℕ) (hm : 0 < m) (hh : 0 < h)
    (hN : 2*(L*m*h) ≤ N) (p wLeft wRight : ℕ → ℝ)
    (hmass : ∑ i ∈ Finset.range m, p i = 1)
    (hwLeft : ∀ j, L*m ≤ j → wLeft j = 1)
    (hwRight : ∀ j, L*m ≤ j → wRight j = 1)
    (hcLeft : ∀ q ≤ L*m, 1 ≤ ∑ i ∈ Finset.range m, p i*wLeft (q+i))
    (hcRight : ∀ q ≤ L*m, 1 ≤ ∑ i ∈ Finset.range m, reverse m p i*wRight (q+i)) :
    ∀ x ∈ Finset.Ico (0:ℤ) (N:ℤ),
      1 ≤ ∑ n ∈ Finset.Ico (0:ℤ) (N+m*h-1:ℕ),
        blockWeight N m h L wLeft wRight n * SidonConcrete.blockKernel m h p (n-x) := by
  intro x hx
  rw [block_pairing N m h L hm hh p wLeft wRight x hx]
  exact actual_boundary_cover N m h (L*m) x.toNat hm hh hN
    (by have hx' := Finset.mem_Ico.mp hx; omega)
    p wLeft wRight hmass hwLeft hwRight hcLeft hcRight

theorem block_weight_norm (N m h L : ℕ) (hm : 0 < m) (hh : 0 < h)
    (hN : 2*(L*m*h) ≤ N) (wLeft wRight : ℕ → ℝ) :
    (∑ n ∈ Finset.Ico (0:ℤ) (N+m*h-1:ℕ),
      blockWeight N m h L wLeft wRight n ^ 2) =
      (N:ℝ) + bValue m L wLeft wRight * ((m:ℝ)*h) - 1 := by
  rw [sum_int_Ico_nat]
  simp only [blockWeight, Int.toNat_natCast]
  exact boundary_norm_sidon N m h L hm hh hN wLeft wRight

/-- Complete interval Sidon inequality from a single asymmetric kernel and two
independent boundary covers. There is no symmetry assumption on p. -/
theorem finite_bound_from_certificate (N m h L : ℕ) (hm : 0 < m) (hh : 0 < h)
    (hN : 2*(L*m*h) ≤ N) (p wLeft wRight : ℕ → ℝ)
    (hp_nonneg : ∀ i, i < m → 0 ≤ p i)
    (hmass : ∑ i ∈ Finset.range m, p i = 1)
    (hwLeft : ∀ j, L*m ≤ j → wLeft j = 1)
    (hwRight : ∀ j, L*m ≤ j → wRight j = 1)
    (hcLeft : ∀ q ≤ L*m, 1 ≤ ∑ i ∈ Finset.range m, p i*wLeft (q+i))
    (hcRight : ∀ q ≤ L*m, 1 ≤ ∑ i ∈ Finset.range m, reverse m p i*wRight (q+i))
    (A : Finset ℤ) (hA : IsSidon A)
    (hAN : A ⊆ Finset.Ico (0:ℤ) (N:ℤ)) :
    (A.card : ℝ) ^ 2 ≤
      ((N:ℝ) + bValue m L wLeft wRight * ((m:ℝ)*h) - 1) *
      (1 + aValue m p * ((A.card : ℝ)-1) / ((m:ℝ)*h)) := by
  apply finite_smoothing_bound A
    (Finset.Ico (0:ℤ) (N+m*h-1:ℕ)) (Finset.Ico (0:ℤ) (m*h:ℕ))
    (fun _ : Unit => SidonConcrete.blockKernel m h p)
    (fun _ : Unit => blockWeight N m h L wLeft wRight)
    (fun _ : Unit => 1) (N:ℝ) (aValue m p) (bValue m L wLeft wRight) ((m:ℝ)*h) hA
  · exact fun _ => SidonConcrete.blockKernel_nonneg m h hh p hp_nonneg
  · exact fun _ => SidonConcrete.blockKernel_support m h p
  · exact fun _ => SidonConcrete.blockKernel_mass m h hh p hmass
  · intro _; norm_num
  · simp
  · intro x hx
    simpa using block_cover N m h L hm hh hN p wLeft wRight
      hmass hwLeft hwRight hcLeft hcRight x (hAN hx)
  · simpa using block_weight_norm N m h L hm hh hN wLeft wRight
  · have he := SidonConcrete.weighted_kernel_square_mass m h hm hh
      (fun _ : Unit => (1:ℝ)) (fun _ : Unit => p)
    simpa [aValue, SidonConcrete.aValue] using he

noncomputable def rightBValue (m L : ℕ) (wRight : ℕ → ℝ) : ℝ :=
  1 + (∑ j ∈ Finset.range (L*m), wRight j ^ 2)/(m:ℝ) - L

theorem bValue_left_one (m L : ℕ) (hm : 0 < m) (wRight : ℕ → ℝ) :
    bValue m L (fun _ => 1) wRight = rightBValue m L wRight := by
  unfold bValue rightBValue
  simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    Nat.cast_mul]
  have hmR : (m:ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- Convenient one-sided specialization: left weights identically one. -/
theorem finite_bound_left_one (N m h L : ℕ) (hm : 0 < m) (hh : 0 < h)
    (hN : 2*(L*m*h) ≤ N) (p wRight : ℕ → ℝ)
    (hp_nonneg : ∀ i, i < m → 0 ≤ p i)
    (hmass : ∑ i ∈ Finset.range m, p i = 1)
    (hwRight : ∀ j, L*m ≤ j → wRight j = 1)
    (hcRight : ∀ q ≤ L*m, 1 ≤ ∑ i ∈ Finset.range m, p (m-1-i)*wRight (q+i))
    (A : Finset ℤ) (hA : IsSidon A)
    (hAN : A ⊆ Finset.Ico (0:ℤ) (N:ℤ)) :
    (A.card : ℝ) ^ 2 ≤
      ((N:ℝ) + rightBValue m L wRight * ((m:ℝ)*h) - 1) *
      (1 + aValue m p * ((A.card : ℝ)-1) / ((m:ℝ)*h)) := by
  have he := finite_bound_from_certificate N m h L hm hh hN p (fun _ => 1) wRight
    hp_nonneg hmass (by intro j hj; rfl) hwRight
    (by intro q hq; simpa [hmass]) (by simpa only [reverse] using hcRight) A hA hAN
  rw [bValue_left_one m L hm wRight] at he
  exact he

#print axioms block_pairing
#print axioms block_cover
#print axioms block_weight_norm
#print axioms finite_bound_from_certificate
#print axioms finite_bound_left_one

end SidonAsymmetric



/-!
Finite renewal identities for the asymmetric triangular Sidon kernel.
This file is independent of the Sidon property and uses only finite sums.
-/
namespace SidonRenewal

noncomputable def weightedWindow (m : ℕ) (u : ℤ → ℝ) (n : ℤ) : ℝ :=
  ∑ i ∈ Finset.range m, ((m : ℝ) - (i : ℝ)) * u (n - (i : ℤ))

/-- Exact telescoping identity behind the renewal convolution. -/
theorem weightedWindow_step (m : ℕ) (u : ℤ → ℝ) (n : ℤ) :
    weightedWindow m u n = weightedWindow m u (n-1) + (m : ℝ) * u n -
      ∑ i ∈ Finset.range m, u (n - ((i+1 : ℕ) : ℤ)) := by
  have hp (i : ℕ) :
      ((m : ℝ) - ((i+1 : ℕ) : ℝ)) * u (n - ((i+1 : ℕ) : ℤ)) =
      ((m : ℝ) - (i : ℝ)) * u ((n-1) - (i : ℤ)) -
        u (n - ((i+1 : ℕ) : ℤ)) := by
    have hi : n - ((i+1 : ℕ) : ℤ) = (n-1) - (i : ℤ) := by omega
    rw [hi]
    push_cast
    ring
  calc
    weightedWindow m u n =
        ∑ i ∈ Finset.range (m+1), ((m : ℝ) - (i : ℝ)) * u (n - (i : ℤ)) := by
      rw [Finset.sum_range_succ]
      simp [weightedWindow]
    _ = (m : ℝ) * u n +
        ∑ i ∈ Finset.range m, ((m : ℝ) - ((i+1 : ℕ) : ℝ)) * u (n - ((i+1 : ℕ) : ℤ)) := by
      rw [Finset.sum_range_succ']
      simp [add_comm]
    _ = (m : ℝ) * u n +
        (weightedWindow m u (n-1) - ∑ i ∈ Finset.range m, u (n - ((i+1 : ℕ) : ℤ))) := by
      simp_rw [hp, Finset.sum_sub_distrib]
      rfl
    _ = _ := by ring

/-- All negative source coordinates vanish, so the first weighted window is
just its zeroth source atom. -/
theorem weightedWindow_zero (m : ℕ) (u : ℤ → ℝ)
    (hneg : ∀ n : ℤ, n < 0 → u n = 0) :
    weightedWindow m u 0 = (m : ℝ) * u 0 := by
  by_cases hm : m = 0
  · simp [weightedWindow, hm]
  · unfold weightedWindow
    rw [Finset.sum_eq_single 0]
    · simp
    · intro i hi hne
      have hi0 : 0 < i := Nat.pos_of_ne_zero hne
      have hn : (0 : ℤ) - (i : ℤ) < 0 := by omega
      rw [hneg _ hn, mul_zero]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr (Nat.pos_of_ne_zero hm))).elim

/-- The renewal recurrence conserves the triangular weighted window. -/
theorem weightedWindow_invariant (m : ℕ) (u : ℤ → ℝ)
    (hrec : ∀ n : ℕ, 0 < n →
      (m : ℝ) * u (n : ℤ) = ∑ i ∈ Finset.range m, u ((n : ℤ) - ((i+1 : ℕ) : ℤ)))
    (n : ℕ) : weightedWindow m u (n : ℤ) = weightedWindow m u 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hs := weightedWindow_step m u ((n+1 : ℕ) : ℤ)
    have hr := hrec (n+1) (by omega)
    have hn : ((n+1 : ℕ) : ℤ) - 1 = (n : ℤ) := by omega
    rw [hn, hr] at hs
    linarith

/-- The asymmetric triangular probability kernel as a finite list. -/
noncomputable def triangle (m i : ℕ) : ℝ :=
  2 * ((m : ℝ) - (i : ℝ)) / ((m : ℝ) * ((m : ℝ) + 1))

/-- Exact causal convolution identity for the actual triangular coefficients.
No generating-function or convergence premise is required. -/
theorem triangle_renewal_convolution (m : ℕ) (hm : 0 < m) (u : ℤ → ℝ)
    (hneg : ∀ n : ℤ, n < 0 → u n = 0)
    (hzero : u 0 = ((m : ℝ) + 1) / 2)
    (hrec : ∀ n : ℕ, 0 < n →
      (m : ℝ) * u (n : ℤ) = ∑ i ∈ Finset.range m, u ((n : ℤ) - ((i+1 : ℕ) : ℤ)))
    (n : ℕ) :
    (∑ i ∈ Finset.range m, triangle m i * u ((n : ℤ) - (i : ℤ))) = 1 := by
  have hw := weightedWindow_invariant m u hrec n
  rw [weightedWindow_zero m u hneg, hzero] at hw
  have hmR : (m : ℝ) ≠ 0 := by positivity
  have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
  calc
    _ = 2 / ((m : ℝ) * ((m : ℝ) + 1)) * weightedWindow m u (n : ℤ) := by
      rw [weightedWindow, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      unfold triangle
      ring
    _ = 1 := by rw [hw]; field_simp



private theorem range_sum_linear (m : ℕ) :
    (∑ i ∈ Finset.range m, (i : ℝ)) = (m : ℝ) * ((m : ℝ)-1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

private theorem range_sum_square (m : ℕ) :
    (∑ i ∈ Finset.range m, (i : ℝ)^2) =
      (m : ℝ) * ((m : ℝ)-1) * (2*(m : ℝ)-1) / 6 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

theorem triangle_nonneg (m i : ℕ) (hi : i < m) : 0 ≤ triangle m i := by
  apply div_nonneg
  · apply mul_nonneg (by norm_num)
    have hiR : (i : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Nat.le_of_lt hi)
    linarith
  · positivity

theorem triangle_mass (m : ℕ) (hm : 0 < m) :
    (∑ i ∈ Finset.range m, triangle m i) = 1 := by
  have hmR : (m : ℝ) ≠ 0 := by positivity
  have hm1 : (m : ℝ)+1 ≠ 0 := by positivity
  calc
    _ = (2 / ((m : ℝ)*((m : ℝ)+1))) *
        ∑ i ∈ Finset.range m, ((m : ℝ)-(i : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      unfold triangle
      ring
    _ = 1 := by
      rw [Finset.sum_sub_distrib, range_sum_linear]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp
      ring

theorem triangle_first_moment (m : ℕ) (hm : 0 < m) :
    (∑ i ∈ Finset.range m, (i : ℝ) * triangle m i) = ((m : ℝ)-1)/3 := by
  have hmR : (m : ℝ) ≠ 0 := by positivity
  have hm1 : (m : ℝ)+1 ≠ 0 := by positivity
  calc
    _ = (2 / ((m : ℝ)*((m : ℝ)+1))) *
        ∑ i ∈ Finset.range m, ((m : ℝ)*(i : ℝ) - (i : ℝ)^2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      unfold triangle
      ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, range_sum_linear, range_sum_square]
      field_simp
      ring

theorem triangle_square_mass (m : ℕ) (hm : 0 < m) :
    (∑ i ∈ Finset.range m, triangle m i ^ 2) =
      2*(2*(m : ℝ)+1)/(3*(m : ℝ)*((m : ℝ)+1)) := by
  have hmR : (m : ℝ) ≠ 0 := by positivity
  have hm1 : (m : ℝ)+1 ≠ 0 := by positivity
  calc
    _ = (4 / (((m : ℝ)*((m : ℝ)+1))^2)) *
        ∑ i ∈ Finset.range m, ((m : ℝ)^2 - 2*(m : ℝ)*(i : ℝ) + (i : ℝ)^2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      unfold triangle
      field_simp
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        range_sum_linear, range_sum_square]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp
      ring

/-- Canonical rational recurrence, viewed in the reals for the final theorem. -/
noncomputable def renewalNat (m : ℕ) : ℕ → ℝ
  | 0 => ((m : ℝ) + 1) / 2
  | n+1 => (∑ i ∈ Finset.range m,
      if i ≤ n then renewalNat m (n-i) else 0) / (m : ℝ)
termination_by n => n

/-- Extension of the canonical renewal source by zero on negative integers. -/
noncomputable def renewal (m : ℕ) (n : ℤ) : ℝ :=
  if n < 0 then 0 else renewalNat m n.toNat

theorem renewal_negative (m : ℕ) (n : ℤ) (hn : n < 0) : renewal m n = 0 := by
  simp [renewal, hn]

theorem renewal_nat (m n : ℕ) : renewal m (n : ℤ) = renewalNat m n := by
  simp [renewal]

theorem renewal_zero (m : ℕ) : renewal m 0 = ((m : ℝ) + 1) / 2 := by
  simp [renewal, renewalNat]

theorem renewal_nonneg (m : ℕ) : ∀ n : ℤ, 0 ≤ renewal m n := by
  have hNat : ∀ n : ℕ, 0 ≤ renewalNat m n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      cases n with
      | zero => simp [renewalNat]; positivity
      | succ n =>
        rw [renewalNat]
        apply div_nonneg _ (by positivity)
        apply Finset.sum_nonneg
        intro i hi
        split_ifs with hle
        · exact ih (n-i) (by omega)
        · exact le_rfl
  intro n
  unfold renewal
  split_ifs <;> first | exact le_rfl | exact hNat _

/-- The canonical source discharges the recurrence premise used by all
parametric renewal and boundary lemmas. -/
theorem renewal_recurrence (m : ℕ) (hm : 0 < m) (n : ℕ) (hn : 0 < n) :
    (m : ℝ) * renewal m (n : ℤ) =
      ∑ i ∈ Finset.range m, renewal m ((n : ℤ) - ((i+1 : ℕ) : ℤ)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [renewal_nat, renewalNat]
  have hmR : (m : ℝ) ≠ 0 := by positivity
  rw [mul_div_cancel₀ _ hmR]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hle : i ≤ n
  · rw [if_pos hle]
    have he : ((n+1 : ℕ) : ℤ) - ((i+1 : ℕ) : ℤ) = ((n-i : ℕ) : ℤ) := by omega
    rw [he, renewal_nat]
  · rw [if_neg hle]
    symm
    apply renewal_negative
    omega

/-- Finite existence package for downstream proofs. -/
theorem exists_renewal (m : ℕ) (hm : 0 < m) :
    ∃ u : ℤ → ℝ,
      (∀ n : ℤ, n < 0 → u n = 0) ∧
      u 0 = ((m : ℝ) + 1) / 2 ∧
      (∀ n : ℤ, 0 ≤ u n) ∧
      (∀ n : ℕ, 0 < n → (m : ℝ) * u (n : ℤ) =
        ∑ i ∈ Finset.range m, u ((n : ℤ) - ((i+1 : ℕ) : ℤ))) := by
  exact ⟨renewal m, renewal_negative m, renewal_zero m, renewal_nonneg m,
    renewal_recurrence m hm⟩


/-- Right-boundary profile of a finite kernel and a causal renewal source. -/
noncomputable def reverseProfile (m : ℕ) (p : ℕ → ℝ) (u : ℤ → ℝ) (n : ℤ) : ℝ :=
  ∑ i ∈ Finset.range m, p (m-1-i) * u (n-(i : ℤ))

private theorem reflected_correlation (m : ℕ) (p : ℕ → ℝ) (u : ℤ → ℝ) (q : ℤ) :
    (∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
      p (m-1-i) * p (m-1-j) * u (q+(i : ℤ)-(j : ℤ))) =
    ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
      p i * p j * u (q+(i : ℤ)-(j : ℤ)) := by
  rw [← Finset.sum_product (Finset.range m) (Finset.range m)
    (fun a : ℕ × ℕ => p (m-1-a.1) * p (m-1-a.2) * u (q+(a.1 : ℤ)-(a.2 : ℤ))),
    ← Finset.sum_product (Finset.range m) (Finset.range m)
    (fun a : ℕ × ℕ => p a.1 * p a.2 * u (q+(a.1 : ℤ)-(a.2 : ℤ)))]
  apply Finset.sum_bij (fun (a : ℕ × ℕ) _ => (m-1-a.2, m-1-a.1))
  · intro a ha
    obtain ⟨ha1, ha2⟩ := Finset.mem_product.mp ha
    simp only [Finset.mem_range] at ha1 ha2
    apply Finset.mem_product.mpr
    constructor <;> apply Finset.mem_range.mpr <;> omega
  · intro a ha b hb he
    obtain ⟨ha1, ha2⟩ := Finset.mem_product.mp ha
    obtain ⟨hb1, hb2⟩ := Finset.mem_product.mp hb
    simp only [Finset.mem_range] at ha1 ha2 hb1 hb2
    have he1 := congrArg Prod.fst he
    have he2 := congrArg Prod.snd he
    apply Prod.ext <;> dsimp at * <;> omega
  · intro b hb
    obtain ⟨hb1, hb2⟩ := Finset.mem_product.mp hb
    simp only [Finset.mem_range] at hb1 hb2
    refine ⟨(m-1-b.2, m-1-b.1), ?_, ?_⟩
    · apply Finset.mem_product.mpr
      constructor <;> apply Finset.mem_range.mpr <;> omega
    · apply Prod.ext <;> dsimp <;> omega
  · intro a ha
    obtain ⟨ha1, ha2⟩ := Finset.mem_product.mp ha
    simp only [Finset.mem_range] at ha1 ha2
    have he : q + ((m-1-a.2 : ℕ) : ℤ) - ((m-1-a.1 : ℕ) : ℤ) =
        q + (a.1 : ℤ) - (a.2 : ℤ) := by omega
    dsimp
    rw [he]
    ring

/-- Causal inversion gives an exact reversed-kernel boundary cover.
This identity needs no positivity, convergence, or asymptotic assumptions. -/
theorem reverseProfile_cover (m : ℕ) (p : ℕ → ℝ) (u : ℤ → ℝ)
    (hmass : ∑ i ∈ Finset.range m, p i = 1)
    (hflat : ∀ n : ℕ, (∑ i ∈ Finset.range m, p i * u ((n : ℤ)-(i : ℤ))) = 1)
    (q : ℕ) :
    (∑ i ∈ Finset.range m, p (m-1-i) * reverseProfile m p u ((q : ℤ)+(i : ℤ))) = 1 := by
  have hinner (i : ℕ) :
      (∑ j ∈ Finset.range m, p j * u ((q : ℤ)+(i : ℤ)-(j : ℤ))) = 1 := by
    simpa only [Nat.cast_add] using hflat (q+i)
  unfold reverseProfile
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [reflected_correlation]
  simp_rw [mul_assoc, ← Finset.mul_sum, hinner, mul_one]
  exact hmass

theorem triangle_reverse_cover (m : ℕ) (hm : 0 < m) (u : ℤ → ℝ)
    (hneg : ∀ n : ℤ, n < 0 → u n = 0)
    (hzero : u 0 = ((m : ℝ)+1)/2)
    (hrec : ∀ n : ℕ, 0 < n → (m : ℝ)*u (n : ℤ) =
      ∑ i ∈ Finset.range m, u ((n : ℤ)-((i+1 : ℕ) : ℤ))) (q : ℕ) :
    (∑ i ∈ Finset.range m, triangle m (m-1-i) *
      reverseProfile m (triangle m) u ((q : ℤ)+(i : ℤ))) = 1 := by
  exact reverseProfile_cover m (triangle m) u (triangle_mass m hm)
    (triangle_renewal_convolution m hm u hneg hzero hrec) q

theorem reverseProfile_nonneg (m : ℕ) (p : ℕ → ℝ) (u : ℤ → ℝ)
    (hp : ∀ i < m, 0 ≤ p i) (hu : ∀ n, 0 ≤ u n) (n : ℤ) :
    0 ≤ reverseProfile m p u n := by
  apply Finset.sum_nonneg
  intro i hi
  have hi' := Finset.mem_range.mp hi
  exact mul_nonneg (hp (m-1-i) (by omega)) (hu _)

end SidonRenewal
#print axioms SidonRenewal.weightedWindow_step
#print axioms SidonRenewal.triangle_renewal_convolution

#print axioms SidonRenewal.exists_renewal

#print axioms SidonRenewal.triangle_first_moment
#print axioms SidonRenewal.triangle_square_mass

#print axioms SidonRenewal.triangle_reverse_cover



namespace SidonRenewal

/-- Every source satisfying the finite causal recurrence is nonnegative. -/
theorem source_nonneg (m : ℕ) (hm : 0 < m) (u : ℤ → ℝ)
    (hneg : ∀ n : ℤ, n < 0 → u n = 0)
    (hzero : u 0 = ((m : ℝ)+1)/2)
    (hrec : ∀ n : ℕ, 0 < n → (m : ℝ)*u (n : ℤ) =
      ∑ i ∈ Finset.range m, u ((n : ℤ)-((i+1 : ℕ) : ℤ))) :
    ∀ n : ℤ, 0 ≤ u n := by
  have hmR : 0 < (m : ℝ) := by positivity
  have hNat : ∀ n : ℕ, 0 ≤ u (n : ℤ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : n = 0
      · subst n
        rw [Nat.cast_zero, hzero]
        positivity
      · have hr := hrec n (Nat.pos_of_ne_zero hn)
        have hs : 0 ≤ ∑ i ∈ Finset.range m, u ((n : ℤ)-((i+1 : ℕ) : ℤ)) := by
          apply Finset.sum_nonneg
          intro i hi
          by_cases hni : (n : ℤ)-((i+1 : ℕ) : ℤ) < 0
          · rw [hneg _ hni]
          · have he : (n : ℤ)-((i+1 : ℕ) : ℤ) = ((n-1-i : ℕ) : ℤ) := by omega
            rw [he]
            exact ih (n-1-i) (by omega)
        nlinarith
  intro n
  by_cases hn : n < 0
  · rw [hneg n hn]
  · have he : n = (n.toNat : ℤ) := by omega
    rw [he]
    exact hNat _

/-- Before the full window is populated, averaging is a prefix sum. -/
theorem causal_window_prefix (m n : ℕ) (hn : n ≤ m) (u : ℤ → ℝ)
    (hneg : ∀ n : ℤ, n < 0 → u n = 0) :
    (∑ i ∈ Finset.range m, u ((n : ℤ)-((i+1 : ℕ) : ℤ))) =
      ∑ s ∈ Finset.range n, u (s : ℤ) := by
  calc
    _ = ∑ i ∈ Finset.range n, u ((n : ℤ)-((i+1 : ℕ) : ℤ)) := by
      symm
      apply Finset.sum_subset (Finset.range_mono hn)
      intro i hi hnot
      apply hneg
      have hin : n ≤ i := by simpa using hnot
      omega
    _ = ∑ i ∈ Finset.range n, u ((n-1-i : ℕ) : ℤ) := by
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      have hi' := Finset.mem_range.mp hi
      omega
    _ = _ := Finset.sum_range_reflect (fun i => u (i : ℤ)) n

private theorem initial_sum_linear (p : ℕ) (m : ℝ) :
    (∑ i ∈ Finset.range p, ((1 : ℝ)/2 + ((i : ℝ)+1)/m)) =
      (p : ℝ)/2 + (p : ℝ)*((p : ℝ)+1)/(2*m) := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- A simple linear barrier on the first m nonzero source values. -/
theorem first_window_linear_bound (m : ℕ) (hm : 0 < m) (u : ℤ → ℝ)
    (hneg : ∀ n : ℤ, n < 0 → u n = 0)
    (hzero : u 0 = ((m : ℝ)+1)/2)
    (hrec : ∀ n : ℕ, 0 < n → (m : ℝ)*u (n : ℤ) =
      ∑ i ∈ Finset.range m, u ((n : ℤ)-((i+1 : ℕ) : ℤ))) :
    ∀ n : ℕ, 0 < n → n ≤ m → u (n : ℤ) ≤ 1/2 + (n : ℝ)/(m : ℝ) := by
  have hmR : 0 < (m : ℝ) := by positivity
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn hnm
    obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    have hr := hrec (p+1) (by omega)
    rw [causal_window_prefix m (p+1) hnm u hneg, Finset.sum_range_succ'] at hr
    have hs : (∑ i ∈ Finset.range p, u ((i+1 : ℕ) : ℤ)) ≤
        (p : ℝ)/2 + (p : ℝ)*((p : ℝ)+1)/(2*(m : ℝ)) := by
      rw [← initial_sum_linear]
      apply Finset.sum_le_sum
      intro i hi
      have hi' := Finset.mem_range.mp hi
      simpa only [Nat.cast_add, Nat.cast_one] using ih (i+1) (by omega) (by omega) (by omega)
    rw [Nat.cast_zero, hzero] at hr
    have hpR : (p : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : p ≤ m)
    have hprod := mul_le_mul_of_nonneg_right hpR (by positivity : 0 ≤ (p : ℝ)+1)
    have hsMul := mul_le_mul_of_nonneg_left hs (le_of_lt hmR)
    have hcancel : (m : ℝ) * ((p : ℝ)*((p : ℝ)+1)/(2*(m : ℝ))) =
        (p : ℝ)*((p : ℝ)+1)/2 := by field_simp
    have hcancel2 : ((p+1 : ℕ) : ℝ)/(m : ℝ) * (m : ℝ) = ((p+1 : ℕ) : ℝ) :=
      div_mul_cancel₀ _ (ne_of_gt hmR)
    rw [mul_add, hcancel] at hsMul
    have hrMul := congrArg (fun x : ℝ => (m : ℝ)*x) hr
    push_cast at hsMul hrMul hcancel2 ⊢
    have hstep : (m : ℝ) * ((m : ℝ) * u ((p : ℤ)+1)) ≤
        (m : ℝ) * ((m : ℝ)/2 + ((p : ℝ)+1)) := by nlinarith
    have hstep' := (mul_le_mul_iff_right₀ hmR).mp hstep
    apply (mul_le_mul_iff_right₀ hmR).mp
    nlinarith

/-- Uniform initial error, with no exponential estimate needed. -/
theorem first_window_abs_bound (m : ℕ) (hm : 0 < m) (u : ℤ → ℝ)
    (hneg : ∀ n : ℤ, n < 0 → u n = 0)
    (hzero : u 0 = ((m : ℝ)+1)/2)
    (hrec : ∀ n : ℕ, 0 < n → (m : ℝ)*u (n : ℤ) =
      ∑ i ∈ Finset.range m, u ((n : ℤ)-((i+1 : ℕ) : ℤ)))
    (n : ℕ) (hn : 0 < n) (hnm : n ≤ m) :
    |u (n : ℤ)-1| ≤ 1/2 := by
  have hmR : 0 < (m : ℝ) := by positivity
  have hu := source_nonneg m hm u hneg hzero hrec
  have hr := hrec n hn
  rw [causal_window_prefix m n hnm u hneg] at hr
  have hs : u 0 ≤ ∑ s ∈ Finset.range n, u (s : ℤ) := by
    simpa only [Nat.cast_zero] using
      (Finset.single_le_sum (f := fun s : ℕ => u (s : ℤ))
        (fun s hs => hu (s : ℤ)) (Finset.mem_range.mpr hn))
  rw [hzero] at hs
  have hlo : 1/2 ≤ u (n : ℤ) := by nlinarith
  have hhi := first_window_linear_bound m hm u hneg hzero hrec n hn hnm
  have hdiv : (n : ℝ)/(m : ℝ) ≤ 1 := by
    apply (div_le_one hmR).mpr
    exact_mod_cast hnm
  apply abs_le.mpr
  constructor <;> linarith

end SidonRenewal
#print axioms SidonRenewal.first_window_abs_bound



/-!
Uniform renewal convergence from the invariant triangular weighted mean.
The one-step estimate uses only finite sums, avoiding transition matrices.
-/
namespace SidonRenewal
open Finset

/-- Any probability weights with cap 2/m force the unweighted mean within
half of the original error from their invariant mean. -/
theorem capped_invariant_average (m : ℕ) (hm : 0 < m)
    (P v : ℕ → ℝ) (next E : ℝ)
    (hmass : (∑ i ∈ range m, P i) = 1)
    (hcap : ∀ i < m, (m:ℝ)*P i ≤ 2)
    (hmean : (∑ i ∈ range m, P i*v i) = 1)
    (hnext : (m:ℝ)*next = ∑ i ∈ range m, v i)
    (hbound : ∀ i < m, |v i-1| ≤ E) :
    |next-1| ≤ E/2 := by
  have hmR : (0:ℝ) < m := by positivity
  have hlo : 0 ≤ ∑ i ∈ range m, (2-(m:ℝ)*P i)*(E+v i-1) := by
    apply sum_nonneg
    intro i hi
    apply mul_nonneg (sub_nonneg.mpr (hcap i (mem_range.mp hi)))
    have h := (abs_le.mp (hbound i (mem_range.mp hi))).1
    linarith
  have hhi : 0 ≤ ∑ i ∈ range m, (2-(m:ℝ)*P i)*(E-v i+1) := by
    apply sum_nonneg
    intro i hi
    apply mul_nonneg (sub_nonneg.mpr (hcap i (mem_range.mp hi)))
    have h := (abs_le.mp (hbound i (mem_range.mp hi))).2
    linarith
  have htermLo (i : ℕ) : (2-(m:ℝ)*P i)*(E+v i-1) =
      (2*E-2)+2*v i-((m:ℝ)*(E-1))*P i-(m:ℝ)*(P i*v i) := by ring
  have htermHi (i : ℕ) : (2-(m:ℝ)*P i)*(E-v i+1) =
      (2*E+2)-2*v i-((m:ℝ)*(E+1))*P i+(m:ℝ)*(P i*v i) := by ring
  simp only [htermLo, sum_sub_distrib, sum_add_distrib, ← mul_sum] at hlo
  simp only [htermHi, sum_sub_distrib, sum_add_distrib, ← mul_sum] at hhi
  simp only [sum_const, card_range, nsmul_eq_mul, hmass, hmean] at hlo hhi
  rw [← hnext] at hlo hhi
  apply abs_le.mpr
  constructor
  · refine le_of_mul_le_mul_left (a := (m:ℝ)) ?_ hmR
    nlinarith only [hlo]
  · refine le_of_mul_le_mul_left (a := (m:ℝ)) ?_ hmR
    nlinarith only [hhi]

/-- The triangular invariant weights have the required uniform cap. -/
theorem triangle_cap (m : ℕ) (hm : 0 < m) (i : ℕ) :
    (m:ℝ)*triangle m i ≤ 2 := by
  have hmR : (m:ℝ) ≠ 0 := by positivity
  have hm1 : (0:ℝ) < (m:ℝ)+1 := by positivity
  have he : (m:ℝ)*triangle m i = 2*((m:ℝ)-(i:ℝ))/((m:ℝ)+1) := by
    unfold triangle
    field_simp
  rw [he]
  apply (div_le_iff₀ hm1).mpr
  nlinarith [Nat.cast_nonneg (α := ℝ) i]

/-- Starting from one bounded window, every subsequent value has half that
error. Values already produced remain within the original bound during the
induction, so no transition-coefficient calculation is required. -/
theorem future_error_half (m : ℕ) (hm : 0 < m) (u : ℤ → ℝ)
    (P : ℕ → ℝ)
    (hmass : (∑ i ∈ range m, P i) = 1)
    (hcap : ∀ i < m, (m:ℝ)*P i ≤ 2)
    (hinvariant : ∀ n : ℕ, (∑ i ∈ range m, P i*u ((n:ℤ)-(i:ℤ))) = 1)
    (hrec : ∀ n : ℕ, 0 < n →
      (m:ℝ)*u (n:ℤ) = ∑ i ∈ range m, u ((n:ℤ)-((i+1:ℕ):ℤ)))
    (S : ℕ) (hS : m ≤ S) (E : ℝ) (hE : 0 ≤ E)
    (hwindow : ∀ k : ℕ, S-m < k → k ≤ S → |u (k:ℤ)-1| ≤ E) :
    ∀ n : ℕ, S < n → |u (n:ℤ)-1| ≤ E/2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    have hn0 : 0 < n := by omega
    apply capped_invariant_average m hm P
      (fun i => u ((n:ℤ)-((i+1:ℕ):ℤ))) (u (n:ℤ)) E hmass hcap
    · have hv := hinvariant (n-1)
      convert hv using 1
      apply sum_congr rfl
      intro i hi
      congr 1
      congr 1
      omega
    · exact hrec n hn0
    · intro i hi
      let k : ℕ := n-(i+1)
      have hk : k < n := by dsimp [k]; omega
      have hklo : S-m < k := by dsimp [k]; omega
      have he : (n:ℤ)-((i+1:ℕ):ℤ) = (k:ℤ) := by dsimp [k]; omega
      rw [he]
      by_cases hkS : k ≤ S
      · exact hwindow k hklo hkS
      · exact (ih k hk (by omega)).trans (by linarith)

/-- Iterate the m-step contraction. This is stronger than the 2m-step delay
needed for the final Sidon application. -/
theorem geometric_tail_of_first_window (m : ℕ) (hm : 0 < m)
    (u : ℤ → ℝ) (P : ℕ → ℝ)
    (hmass : (∑ i ∈ range m, P i) = 1)
    (hcap : ∀ i < m, (m:ℝ)*P i ≤ 2)
    (hinvariant : ∀ n : ℕ, (∑ i ∈ range m, P i*u ((n:ℤ)-(i:ℤ))) = 1)
    (hrec : ∀ n : ℕ, 0 < n →
      (m:ℝ)*u (n:ℤ) = ∑ i ∈ range m, u ((n:ℤ)-((i+1:ℕ):ℤ)))
    (hfirst : ∀ n : ℕ, 0 < n → n ≤ m → |u (n:ℤ)-1| ≤ (1:ℝ)/2) :
    ∀ j n : ℕ, j*m < n → |u (n:ℤ)-1| ≤ ((1:ℝ)/2)*((1:ℝ)/2)^j := by
  intro j
  induction j with
  | zero =>
    intro n hn
    simp only [zero_mul] at hn
    simp only [pow_zero, mul_one]
    by_cases hnm : n ≤ m
    · exact hfirst n hn hnm
    · have hf := future_error_half m hm u P hmass hcap hinvariant hrec
        m le_rfl ((1:ℝ)/2) (by norm_num)
        (by intro k hk hkm; exact hfirst k (by simpa using hk) hkm) n (by omega)
      linarith
  | succ j ih =>
    intro n hn
    have hS : m ≤ (j+1)*m := by nlinarith
    have hf := future_error_half m hm u P hmass hcap hinvariant hrec
      ((j+1)*m) hS (((1:ℝ)/2)*((1:ℝ)/2)^j) (by positivity)
      (by
        intro k hk _
        apply ih k
        have hs : (j+1)*m-m = j*m := by simp [Nat.add_mul]
        simpa only [hs] using hk)
      n (by simpa only [Nat.succ_eq_add_one] using hn)
    rw [pow_succ]
    nlinarith only [hf]

/-- Uniform tail bound from the renewal recurrence and a verified initial
window. The remaining initial-window hypothesis is supplied separately. -/
theorem renewal_tail_of_initial (m : ℕ) (hm : 0 < m) (u : ℤ → ℝ)
    (hneg : ∀ n : ℤ, n < 0 → u n = 0)
    (hzero : u 0 = ((m:ℝ)+1)/2)
    (hrec : ∀ n : ℕ, 0 < n →
      (m:ℝ)*u (n:ℤ) = ∑ i ∈ range m, u ((n:ℤ)-((i+1:ℕ):ℤ)))
    (hfirst : ∀ n : ℕ, 0 < n → n ≤ m → |u (n:ℤ)-1| ≤ (1:ℝ)/2)
    (j n : ℕ) (hn : (2*j+1)*m ≤ n) :
    |u (n:ℤ)-1| ≤ ((1:ℝ)/2)/((2:ℝ)^j) := by
  have h := geometric_tail_of_first_window m hm u (triangle m)
    (triangle_mass m hm) (fun i _ => triangle_cap m hm i)
    (triangle_renewal_convolution m hm u hneg hzero hrec) hrec hfirst j n
    (by nlinarith)
  simpa only [div_pow, one_pow, one_div, div_eq_mul_inv, one_mul, inv_pow] using h

/-- A uniform geometric tail estimate for the canonical causal renewal source.
The proof uses only the source equations, with no extra positivity or initial
window hypothesis. -/
theorem uniform_renewal_tail (m : ℕ) (hm : 0 < m) (u : ℤ → ℝ)
    (hneg : ∀ n : ℤ, n < 0 → u n = 0)
    (hzero : u 0 = ((m:ℝ)+1)/2)
    (hrec : ∀ n : ℕ, 0 < n →
      (m:ℝ)*u (n:ℤ) = ∑ i ∈ range m, u ((n:ℤ)-((i+1:ℕ):ℤ)))
    (j n : ℕ) (hn : (2*j+1)*m ≤ n) :
    |u (n:ℤ)-1| ≤ ((1:ℝ)/2)/((2:ℝ)^j) := by
  exact renewal_tail_of_initial m hm u hneg hzero hrec
    (first_window_abs_bound m hm u hneg hzero hrec) j n hn

#print axioms capped_invariant_average
#print axioms future_error_half
#print axioms geometric_tail_of_first_window
#print axioms renewal_tail_of_initial
#print axioms uniform_renewal_tail
end SidonRenewal



namespace SidonRenewalNorm

set_option maxHeartbeats 0
set_option autoImplicit false
noncomputable section
open Finset

def reverseKernel (m : ℕ) (p : ℕ → ℝ) (i : ℕ) : ℝ := p (m-1-i)

def finiteConv (m : ℕ) (p : ℕ → ℝ) (u : ℤ → ℝ) (n : ℤ) : ℝ :=
  ∑ i ∈ range m, p i * u (n-(i:ℤ))

def truncate (M : ℕ) (u : ℤ → ℝ) (n : ℤ) : ℝ :=
  if 0 ≤ n ∧ n < (M:ℤ) then u n else 0

theorem shifted_pair_energy (m M i j : ℕ) (hi : i < m) (hj : j < m)
    (v : ℤ → ℝ) (hv : ∀ n : ℤ, ¬ (0 ≤ n ∧ n < (M:ℤ)) → v n = 0) :
    (∑ n ∈ Ico (0:ℤ) ((M:ℤ)+(m:ℤ)-1), v (n-i)*v (n-j)) =
    ∑ n ∈ Ico (0:ℤ) ((M:ℤ)+(m:ℤ)-1),
      v (n-((m-1-i:ℕ):ℤ))*v (n-((m-1-j:ℕ):ℤ)) := by
  have hmi : ((m-1-i:ℕ):ℤ) = (m:ℤ)-1-i := by omega
  have hmj : ((m-1-j:ℕ):ℤ) = (m:ℤ)-1-j := by omega
  have hsupp : ∀ n, v n ≠ 0 → 0 ≤ n ∧ n < (M:ℤ) := by
    intro n hn
    by_contra h
    exact hn (hv n h)
  apply Finset.sum_bij_ne_zero (fun n _ _ => n+(m:ℤ)-1-i-j)
  · intro n hn hne
    have hv1 : v (n-i) ≠ 0 := by intro h; simp [h] at hne
    have hv2 : v (n-j) ≠ 0 := by intro h; simp [h] at hne
    have h1 := hsupp _ hv1
    have h2 := hsupp _ hv2
    apply mem_Ico.mpr
    constructor <;> omega
  · intro n hn hne z hz hze he
    omega
  · intro z hz hne
    have hv1 : v (z-((m-1-i:ℕ):ℤ)) ≠ 0 := by intro h; simp [h] at hne
    have hv2 : v (z-((m-1-j:ℕ):ℤ)) ≠ 0 := by intro h; simp [h] at hne
    have h1 := hsupp _ hv1
    have h2 := hsupp _ hv2
    refine ⟨z-(m:ℤ)+1+i+j, ?_, ?_, ?_⟩
    · apply mem_Ico.mpr
      constructor <;> omega
    · have e1 : z-(m:ℤ)+1+i+j-(i:ℤ) = z-((m-1-j:ℕ):ℤ) := by omega
      have e2 : z-(m:ℤ)+1+i+j-(j:ℤ) = z-((m-1-i:ℕ):ℤ) := by omega
      rw [e1,e2,mul_comm]
      exact hne
    · omega
  · intro n hn hne
    have e1 : n+(m:ℤ)-1-i-j-((m-1-i:ℕ):ℤ) = n-j := by omega
    have e2 : n+(m:ℤ)-1-i-j-((m-1-j:ℕ):ℤ) = n-i := by omega
    rw [e1,e2,mul_comm]

theorem convolution_square_expand (m : ℕ) (p : ℕ → ℝ) (v : ℤ → ℝ)
    (J : Finset ℤ) :
    (∑ n ∈ J, (finiteConv m p v n)^2) =
      ∑ i ∈ range m, ∑ j ∈ range m, p i*p j * ∑ n ∈ J, v (n-i)*v (n-j) := by
  unfold finiteConv
  simp_rw [pow_two, sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  apply sum_congr rfl
  intro n hn
  ring

/-- Reversing one real kernel preserves the full energy of a finite convolution. -/
theorem convolution_energy_reflect (m M : ℕ) (p : ℕ → ℝ) (v : ℤ → ℝ)
    (hv : ∀ n : ℤ, ¬ (0 ≤ n ∧ n < (M:ℤ)) → v n = 0) :
    (∑ n ∈ Ico (0:ℤ) ((M:ℤ)+(m:ℤ)-1), (finiteConv m p v n)^2) =
    ∑ n ∈ Ico (0:ℤ) ((M:ℤ)+(m:ℤ)-1),
      (finiteConv m (reverseKernel m p) v n)^2 := by
  rw [convolution_square_expand, convolution_square_expand]
  rw [← sum_range_reflect (fun i => ∑ j ∈ range m,
    reverseKernel m p i*reverseKernel m p j*
      ∑ n ∈ Ico (0:ℤ) ((M:ℤ)+(m:ℤ)-1), v (n-i)*v (n-j)) m]
  apply sum_congr rfl
  intro i hi
  rw [← sum_range_reflect (fun j => reverseKernel m p (m-1-i)*reverseKernel m p j*
    ∑ n ∈ Ico (0:ℤ) ((M:ℤ)+(m:ℤ)-1), v (n-((m-1-i:ℕ):ℤ))*v (n-j)) m]
  apply sum_congr rfl
  intro j hj
  have hi' := mem_range.mp hi
  have hj' := mem_range.mp hj
  have ei : m-1-(m-1-i)=i := by omega
  have ej : m-1-(m-1-j)=j := by omega
  simp only [reverseKernel, ei,ej]
  rw [shifted_pair_energy m M i j hi' hj' v hv]

#print axioms convolution_energy_reflect

theorem sum_int_Ico_nat (M : ℕ) (f : ℤ → ℝ) :
    (∑ z ∈ Ico (0:ℤ) (M:ℤ), f z) = ∑ n ∈ range M, f (n:ℤ) := by
  symm
  apply Finset.sum_bij (fun (n : ℕ) _ => (n:ℤ))
  · intro n hn
    simp only [mem_range] at hn
    simp only [mem_Ico]
    omega
  · intro n hn z hz he
    omega
  · intro z hz
    simp only [mem_Ico] at hz
    refine ⟨z.toNat, ?_, ?_⟩
    · simp only [mem_range]
      omega
    · omega
  · intro n hn
    rfl

theorem convolution_energy_reflect_nat (m M : ℕ) (hm : 0 < m)
    (p : ℕ → ℝ) (v : ℤ → ℝ)
    (hv : ∀ n : ℤ, ¬ (0 ≤ n ∧ n < (M:ℤ)) → v n = 0) :
    (∑ n ∈ range (M+m-1), (finiteConv m p v n)^2) =
    ∑ n ∈ range (M+m-1), (finiteConv m (reverseKernel m p) v n)^2 := by
  have he := convolution_energy_reflect m M p v hv
  have hc : ((M+m-1:ℕ):ℤ) = (M:ℤ)+(m:ℤ)-1 := by omega
  rw [← hc, sum_int_Ico_nat, sum_int_Ico_nat] at he
  exact he

theorem truncated_conv_agrees (m M : ℕ) (p : ℕ → ℝ) (u : ℤ → ℝ)
    (hneg : ∀ n : ℤ, n < 0 → u n = 0) (n : ℕ) (hn : n < M) :
    finiteConv m p (truncate M u) n = finiteConv m p u n := by
  unfold finiteConv
  apply sum_congr rfl
  intro i hi
  congr 1
  unfold truncate
  split_ifs with hs
  · rfl
  · have hn' : (n:ℤ)-(i:ℤ) < 0 := by omega
    rw [hneg _ hn']

/-- Exact finite tail identity. The tail output index M+r equals M-1+ell
under ell=r+1, so the range r<m-1 contains exactly the usual m-1 tail terms. -/
theorem finite_tail_identity (m M : ℕ) (hm : 0 < m)
    (p : ℕ → ℝ) (u : ℤ → ℝ)
    (hneg : ∀ n : ℤ, n < 0 → u n = 0)
    (hconv : ∀ n : ℕ, finiteConv m p u n = 1) :
    (∑ n ∈ range M, ((finiteConv m (reverseKernel m p) u n)^2-1)) =
    ∑ r ∈ range (m-1),
      ((finiteConv m p (truncate M u) ((M:ℤ)+r))^2 -
      (finiteConv m (reverseKernel m p) (truncate M u) ((M:ℤ)+r))^2) := by
  have he := convolution_energy_reflect_nat m M hm p (truncate M u)
    (by intro n hn; simp [truncate, hn])
  have hn : M+m-1=M+(m-1) := by omega
  rw [hn, sum_range_add, sum_range_add] at he
  have hleft : (∑ n ∈ range M, (finiteConv m p (truncate M u) n)^2) = (M:ℝ) := by
    calc
      _ = ∑ n ∈ range M, (1:ℝ) := by
        apply sum_congr rfl
        intro n hn
        rw [truncated_conv_agrees m M p u hneg n (mem_range.mp hn), hconv n]
        ring
      _ = _ := by simp
  have hright : (∑ n ∈ range M,
      (finiteConv m (reverseKernel m p) (truncate M u) n)^2) =
      ∑ n ∈ range M, (finiteConv m (reverseKernel m p) u n)^2 := by
    apply sum_congr rfl
    intro n hn
    rw [truncated_conv_agrees m M (reverseKernel m p) u hneg n (mem_range.mp hn)]
  rw [hleft, hright] at he
  simp only [Nat.cast_add] at he
  rw [sum_sub_distrib, sum_sub_distrib]
  simp only [sum_const, card_range, nsmul_eq_mul, mul_one]
  linarith

#print axioms finite_tail_identity

def tailMass (m : ℕ) (p : ℕ → ℝ) (r : ℕ) : ℝ := ∑ i ∈ Ico (r+1) m, p i

theorem prefix_sum (m : ℕ) (p : ℕ → ℝ) :
    (∑ r ∈ range m, ∑ i ∈ range r, p i) =
    ∑ i ∈ range m, ((m:ℝ)-1-i)*p i := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, sum_range_succ, ih]
    simp only [Nat.cast_add, Nat.cast_one]
    have he : (∑ i ∈ range m, ((m:ℝ)+1-1-i)*p i) =
        (∑ i ∈ range m, ((m:ℝ)-1-i)*p i) + ∑ i ∈ range m, p i := by
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro i hi
      ring
    rw [he]
    ring

theorem tailMass_reverse (m : ℕ) (hm : 0 < m) (p : ℕ → ℝ) (r : ℕ) :
    tailMass m (reverseKernel m p) r = ∑ i ∈ range (m-1-r), p i := by
  unfold tailMass reverseKernel
  rw [sum_Ico_reflect p (r+1) (m := m) (n := m-1) (by omega)]
  have he : m-1+1-m=0 := by omega
  have he2 : m-1+1-(r+1)=m-1-r := by omega
  rw [he,he2,Nat.Ico_zero_eq_range]

theorem tailMass_reference (m : ℕ) (hm : 0 < m) (p : ℕ → ℝ)
    (hmass : ∑ i ∈ range m, p i = 1) :
    (∑ r ∈ range (m-1), ((tailMass m p r)^2-(tailMass m (reverseKernel m p) r)^2)) =
    2*(∑ i ∈ range m, (i:ℝ)*p i)-((m:ℝ)-1) := by
  have hm1 : m-1+1=m := by omega
  have hc : ((m-1:ℕ):ℝ) = (m:ℝ)-1 := by rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
  have hrev : (∑ r ∈ range (m-1), (tailMass m (reverseKernel m p) r)^2) =
      ∑ r ∈ range (m-1), (∑ i ∈ range (r+1), p i)^2 := by
    simp_rw [tailMass_reverse m hm p]
    rw [← sum_range_reflect (fun r => (∑ i ∈ range (r+1), p i)^2) (m-1)]
    apply sum_congr rfl
    intro r hr
    have hr' := mem_range.mp hr
    have he : m-1-1-r+1=m-1-r := by omega
    rw [he]
  have hpre : (∑ r ∈ range (m-1), ∑ i ∈ range (r+1), p i) =
      (m:ℝ)-1-∑ i ∈ range m, (i:ℝ)*p i := by
    have he := prefix_sum m p
    have hz : (∑ r ∈ range m, ∑ i ∈ range r, p i) =
      ∑ r ∈ range (m-1), ∑ i ∈ range (r+1), p i := by
      conv_lhs => rw [← hm1, sum_range_succ']
      simp
    rw [hz] at he
    rw [he]
    calc
      _ = ((m:ℝ)-1)*(∑ i ∈ range m, p i) - ∑ i ∈ range m, (i:ℝ)*p i := by
        rw [mul_sum, ← sum_sub_distrib]
        apply sum_congr rfl
        intro i hi
        ring
      _ = _ := by rw [hmass]; ring
  rw [sum_sub_distrib, hrev, ← sum_sub_distrib]
  calc
    _ = ∑ r ∈ range (m-1), (1-2*(∑ i ∈ range (r+1), p i)) := by
      apply sum_congr rfl
      intro r hr
      have hr' := mem_range.mp hr
      have he := sum_range_add_sum_Ico p (show r+1 ≤ m by omega)
      change (∑ i ∈ range (r+1), p i)+tailMass m p r = ∑ i ∈ range m, p i at he
      rw [hmass] at he
      nlinarith
    _ = _ := by
      rw [sum_sub_distrib, ← mul_sum, hpre]
      simp only [sum_const, card_range, nsmul_eq_mul, mul_one]
      rw [hc]
      ring

#print axioms tailMass_reference

theorem square_approx (x t ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hx : |x-t| ≤ ε) : |x^2-t^2| ≤ 3*ε := by
  have hd := abs_le.mp hx
  have hs : (x-t)^2 ≤ ε^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hd.2) (by linarith : 0 ≤ ε+(x-t))]
  have hprod1 : t*(x-t) ≤ ε := by
    have h1 := mul_le_mul_of_nonneg_left hd.2 ht0
    have h2 := mul_le_mul_of_nonneg_right ht1 hε
    nlinarith
  have hprod2 : -(ε) ≤ t*(x-t) := by
    have h1 := mul_le_mul_of_nonneg_left hd.1 ht0
    have h2 := mul_le_mul_of_nonneg_right ht1 hε
    nlinarith
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (x-t), mul_nonneg hε (sub_nonneg.mpr hε1)]

theorem probability_approx {ι : Type*} (s : Finset ι) (p f : ι → ℝ) (ε : ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hf : ∀ i ∈ s, |f i-1| ≤ ε) :
    |(∑ i ∈ s, p i*f i)-(∑ i ∈ s, p i)| ≤ ε*(∑ i ∈ s, p i) := by
  calc
    _ = |∑ i ∈ s, p i*(f i-1)| := by
      congr 1
      rw [← sum_sub_distrib]
      apply sum_congr rfl
      intro i hi
      ring
    _ ≤ ∑ i ∈ s, |p i*(f i-1)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, p i*ε := by
      apply sum_le_sum
      intro i hi
      rw [abs_mul, abs_of_nonneg (hp i hi)]
      exact mul_le_mul_of_nonneg_left (hf i hi) (hp i hi)
    _ = _ := by rw [← sum_mul]; ring

theorem reverse_mass (m : ℕ) (p : ℕ → ℝ) :
    (∑ i ∈ range m, reverseKernel m p i) = ∑ i ∈ range m, p i := by
  exact sum_range_reflect p m

theorem reverse_nonneg (m : ℕ) (p : ℕ → ℝ)
    (hp : ∀ i ∈ range m, 0 ≤ p i) : ∀ i ∈ range m, 0 ≤ reverseKernel m p i := by
  intro i hi
  apply hp
  apply mem_range.mpr
  have hi' := mem_range.mp hi
  omega

theorem tailMass_bounds (m : ℕ) (p : ℕ → ℝ)
    (hp : ∀ i ∈ range m, 0 ≤ p i) (hmass : ∑ i ∈ range m, p i = 1) (r : ℕ) :
    0 ≤ tailMass m p r ∧ tailMass m p r ≤ 1 := by
  have hsub : Ico (r+1) m ⊆ range m := by intro i hi; exact mem_range.mpr (mem_Ico.mp hi).2
  constructor
  · exact sum_nonneg (fun i hi => hp i (hsub hi))
  · rw [← hmass]
    exact sum_le_sum_of_subset_of_nonneg hsub (by intro i hi hnot; exact hp i hi)

/-- The finite output tail is a weighted sum over the surviving source positions. -/
theorem truncated_tail_eq (m M : ℕ) (hM : m ≤ M) (p : ℕ → ℝ) (u : ℤ → ℝ)
    (r : ℕ) : finiteConv m p (truncate M u) ((M:ℤ)+r) =
    ∑ i ∈ Ico (r+1) m, p i*u ((M:ℤ)+r-i) := by
  unfold finiteConv
  calc
    _ = ∑ i ∈ Ico (r+1) m, p i*truncate M u ((M:ℤ)+r-i) := by
      symm
      apply sum_subset (by intro i hi; exact mem_range.mpr (mem_Ico.mp hi).2)
      intro i hi hnot
      have hi' := mem_range.mp hi
      have hir : i ≤ r := by simp only [mem_Ico] at hnot; omega
      simp only [truncate, if_neg (show ¬ (0 ≤ (M:ℤ)+r-i ∧ (M:ℤ)+r-i < M) by omega), mul_zero]
    _ = _ := by
      apply sum_congr rfl
      intro i hi
      have hi' := mem_Ico.mp hi
      simp only [truncate, if_pos (show 0 ≤ (M:ℤ)+r-i ∧ (M:ℤ)+r-i < M by omega)]

/-- Only source values in the finite interval [M-m+1,M) enter the output tail. -/
theorem truncated_tail_approx (m M : ℕ) (hM : m ≤ M) (p : ℕ → ℝ) (u : ℤ → ℝ)
    (hp : ∀ i ∈ range m, 0 ≤ p i) (hmass : ∑ i ∈ range m, p i = 1)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hu : ∀ n : ℤ, (M:ℤ)-(m:ℤ)+1 ≤ n → n < M → |u n-1| ≤ ε)
    (r : ℕ) : |finiteConv m p (truncate M u) ((M:ℤ)+r)-tailMass m p r| ≤ ε := by
  rw [truncated_tail_eq m M hM]
  have he := probability_approx (Ico (r+1) m) p (fun i => u ((M:ℤ)+r-i)) ε
    (by intro i hi; exact hp i (mem_range.mpr (mem_Ico.mp hi).2))
    (by intro i hi; have hi' := mem_Ico.mp hi; apply hu <;> omega)
  exact he.trans (by
    have hb := (tailMass_bounds m p hp hmass r).2
    change (∑ i ∈ Ico (r+1) m, p i) ≤ 1 at hb
    nlinarith)

#print axioms truncated_tail_approx

/-- A finite energy estimate using only a finite source tail interval. -/
theorem unpatched_norm_bound (m M : ℕ) (hm : 0 < m) (hM : m ≤ M)
    (p : ℕ → ℝ) (u : ℤ → ℝ)
    (hp : ∀ i ∈ range m, 0 ≤ p i) (hmass : ∑ i ∈ range m, p i = 1)
    (hneg : ∀ n : ℤ, n < 0 → u n = 0)
    (hconv : ∀ n : ℕ, finiteConv m p u n = 1)
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hu : ∀ n : ℤ, (M:ℤ)-(m:ℤ)+1 ≤ n → n < M → |u n-1| ≤ ε) :
    (∑ n ∈ range M, ((finiteConv m (reverseKernel m p) u n)^2-1)) ≤
    2*(∑ i ∈ range m, (i:ℝ)*p i)-((m:ℝ)-1)+6*(m:ℝ)*ε := by
  rw [finite_tail_identity m M hm p u hneg hconv]
  have hrp := reverse_nonneg m p hp
  have hrmass : ∑ i ∈ range m, reverseKernel m p i = 1 := by rw [reverse_mass, hmass]
  calc
    _ ≤ ∑ r ∈ range (m-1),
        (((tailMass m p r)^2-(tailMass m (reverseKernel m p) r)^2)+6*ε) := by
      apply sum_le_sum
      intro r hr
      have hpbound := tailMass_bounds m p hp hmass r
      have hrbound := tailMass_bounds m (reverseKernel m p) hrp hrmass r
      have h1 := abs_le.mp (square_approx _ _ ε hε hε1 hpbound.1 hpbound.2
        (truncated_tail_approx m M hM p u hp hmass ε hε hu r))
      have h2 := abs_le.mp (square_approx _ _ ε hε hε1 hrbound.1 hrbound.2
        (truncated_tail_approx m M hM (reverseKernel m p) u hrp hrmass ε hε hu r))
      linarith
    _ ≤ _ := by
      rw [sum_add_distrib, tailMass_reference m hm p hmass]
      simp only [sum_const, card_range, nsmul_eq_mul]
      have hle : ((m-1:ℕ):ℝ) ≤ (m:ℝ) := by exact_mod_cast Nat.sub_le m 1
      nlinarith

def patched (m M : ℕ) (W : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n < M then if M-m < n then max (W n) 1 else W n else 1

theorem patched_tail (m M : ℕ) (W : ℕ → ℝ) (n : ℕ) (hn : M ≤ n) :
    patched m M W n = 1 := by simp [patched, show ¬ n < M by omega]

theorem patched_ge (m M : ℕ) (W : ℕ → ℝ) (n : ℕ) (hn : n < M) :
    W n ≤ patched m M W n := by
  simp only [patched, if_pos hn]
  split_ifs
  · exact le_max_left _ _
  · exact le_refl _

theorem patched_ge_one (m M : ℕ) (W : ℕ → ℝ) (n : ℕ) (hn : M-m < n) :
    1 ≤ patched m M W n := by
  by_cases h : n < M
  · rw [patched, if_pos h, if_pos hn]
    exact le_max_right _ _
  · simp [patched, h]

/-- The patch is feasible for every nonnegative probability kernel. -/
theorem patched_cover (m M : ℕ) (hM : m ≤ M) (p W : ℕ → ℝ)
    (hp : ∀ i ∈ range m, 0 ≤ p i) (hmass : ∑ i ∈ range m, p i = 1)
    (hcover : ∀ q : ℕ, 1 ≤ ∑ i ∈ range m, p i*W (q+i)) (q : ℕ) :
    1 ≤ ∑ i ∈ range m, p i*patched m M W (q+i) := by
  by_cases hq : q ≤ M-m
  · refine (hcover q).trans ?_
    apply sum_le_sum
    intro i hi
    have hi' := mem_range.mp hi
    apply mul_le_mul_of_nonneg_left _ (hp i hi)
    exact patched_ge m M W (q+i) (by omega)
  · calc
      1 = ∑ i ∈ range m, p i*1 := by simpa using hmass.symm
      _ ≤ _ := by
        apply sum_le_sum
        intro i hi
        apply mul_le_mul_of_nonneg_left _ (hp i hi)
        exact patched_ge_one m M W (q+i) (by omega)

theorem max_square_cost (x ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hx : |x-1| ≤ ε) : (max x 1)^2 ≤ x^2+2*ε := by
  have hb := abs_le.mp hx
  by_cases h : x ≤ 1
  · rw [max_eq_right h]
    have hx0 : 0 ≤ x := by linarith
    nlinarith [sq_nonneg (x-1)]
  · rw [max_eq_left (by linarith)]
    linarith

/-- Raising the last m-1 weights to one costs at most 2(m-1)epsilon in norm. -/
theorem patched_norm_cost (m M : ℕ) (hm : 0 < m) (hM : m ≤ M) (W : ℕ → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hW : ∀ n : ℕ, M-m < n → n < M → |W n-1| ≤ ε) :
    (∑ n ∈ range M, ((patched m M W n)^2-1)) ≤
    (∑ n ∈ range M, ((W n)^2-1))+2*(m:ℝ)*ε := by
  have hsplit : M-m+1 ≤ M := by omega
  rw [← sum_range_add_sum_Ico (fun n => (patched m M W n)^2-1) hsplit,
    ← sum_range_add_sum_Ico (fun n => (W n)^2-1) hsplit]
  have hpre : (∑ n ∈ range (M-m+1), ((patched m M W n)^2-1)) =
      ∑ n ∈ range (M-m+1), ((W n)^2-1) := by
    apply sum_congr rfl
    intro n hn
    have hn' := mem_range.mp hn
    simp [patched, show n < M by omega, show ¬ M-m < n by omega]
  rw [hpre]
  have he : (∑ n ∈ Ico (M-m+1) M, ((patched m M W n)^2-1)) ≤
      (∑ n ∈ Ico (M-m+1) M, ((W n)^2-1)) +2*(m:ℝ)*ε := by
    calc
      _ ≤ ∑ n ∈ Ico (M-m+1) M, (((W n)^2-1)+2*ε) := by
        apply sum_le_sum
        intro n hn
        have hn' := mem_Ico.mp hn
        simp only [patched, if_pos hn'.2, if_pos (show M-m < n by omega)]
        have hb := max_square_cost (W n) ε hε hε1 (hW n (by omega) hn'.2)
        linarith
      _ ≤ _ := by
        rw [sum_add_distrib]
        simp only [sum_const, Nat.card_Ico, nsmul_eq_mul]
        have hcard : ((M-(M-m+1):ℕ):ℝ) ≤ (m:ℝ) := by exact_mod_cast (show M-(M-m+1) ≤ m by omega)
        nlinarith
  linarith

#print axioms patched_norm_cost

/-- Closeness of the last m-1 unpatched weights follows from a finite source interval. -/
theorem profile_tail_approx (m M : ℕ) (p : ℕ → ℝ) (u : ℤ → ℝ)
    (hp : ∀ i ∈ range m, 0 ≤ p i) (hmass : ∑ i ∈ range m, p i = 1)
    (ε : ℝ)
    (hu : ∀ n : ℤ, (M:ℤ)-2*(m:ℤ)+2 ≤ n → n < M → |u n-1| ≤ ε)
    (n : ℕ) (hn : M-m < n) (hnM : n < M) :
    |finiteConv m (reverseKernel m p) u n-1| ≤ ε := by
  have hm : 0 < m := by omega
  have hrp := reverse_nonneg m p hp
  have hrmass : ∑ i ∈ range m, reverseKernel m p i = 1 := by rw [reverse_mass, hmass]
  have he := probability_approx (range m) (reverseKernel m p) (fun i => u ((n:ℤ)-i)) ε hrp
    (by intro i hi; have hi' := mem_range.mp hi; apply hu <;> omega)
  rw [hrmass, mul_one] at he
  exact he

/-- The exact norm estimate needed by the triangular renewal certificates.
All tail assumptions concern a finite source interval; no limiting identity is assumed. -/
theorem patched_profile_bound (m M : ℕ) (hm : 0 < m) (hM : m ≤ M)
    (p : ℕ → ℝ) (u : ℤ → ℝ)
    (hp : ∀ i ∈ range m, 0 ≤ p i) (hmass : ∑ i ∈ range m, p i = 1)
    (hneg : ∀ n : ℤ, n < 0 → u n = 0)
    (hconv : ∀ n : ℕ, finiteConv m p u n = 1)
    (hmoment : ∑ i ∈ range m, (i:ℝ)*p i = ((m:ℝ)-1)/3)
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hu : ∀ n : ℤ, (M:ℤ)-2*(m:ℤ)+2 ≤ n → n < M → |u n-1| ≤ ε) :
    (∑ n ∈ range M,
      ((patched m M (fun n => finiteConv m (reverseKernel m p) u n) n)^2-1)) ≤
    -((m:ℝ)-1)/3+8*(m:ℝ)*ε := by
  have he := patched_norm_cost m M hm hM (fun n => finiteConv m (reverseKernel m p) u n)
    ε hε hε1 (profile_tail_approx m M p u hp hmass ε hu)
  have hu' : ∀ n : ℤ, (M:ℤ)-(m:ℤ)+1 ≤ n → n < M → |u n-1| ≤ ε := by
    intro n hn hnM
    apply hu n (by omega) hnM
  have hb := unpatched_norm_bound m M hm hM p u hp hmass hneg hconv ε hε hε1 hu'
  rw [hmoment] at hb
  linarith

/-- Normalized boundary coefficient. -/
theorem patched_b_bound (m M : ℕ) (hm : 0 < m) (hM : m ≤ M)
    (p : ℕ → ℝ) (u : ℤ → ℝ)
    (hp : ∀ i ∈ range m, 0 ≤ p i) (hmass : ∑ i ∈ range m, p i = 1)
    (hneg : ∀ n : ℤ, n < 0 → u n = 0)
    (hconv : ∀ n : ℕ, finiteConv m p u n = 1)
    (hmoment : ∑ i ∈ range m, (i:ℝ)*p i = ((m:ℝ)-1)/3)
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hu : ∀ n : ℤ, (M:ℤ)-2*(m:ℤ)+2 ≤ n → n < M → |u n-1| ≤ ε) :
    1+(∑ n ∈ range M,
      ((patched m M (fun n => finiteConv m (reverseKernel m p) u n) n)^2-1))/(m:ℝ) ≤
    (2*(m:ℝ)+1)/(3*(m:ℝ))+8*ε := by
  have hb := patched_profile_bound m M hm hM p u hp hmass hneg hconv hmoment ε hε hε1 hu
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have he := div_le_div_of_nonneg_right hb (le_of_lt hmR)
  have heq : 1+(-((m:ℝ)-1)/3+8*(m:ℝ)*ε)/(m:ℝ) =
      (2*(m:ℝ)+1)/(3*(m:ℝ))+8*ε := by field_simp; ring
  linarith

#print axioms patched_cover
#print axioms patched_profile_bound
#print axioms patched_b_bound

end
end SidonRenewalNorm



namespace SidonRenewalFinite
open SidonRenewal SidonConvolutionEnergy

/-- The actual interval Sidon bridge, with every boundary obligation explicit.
The final unconditional theorem below supplies these obligations by renewal. -/
theorem triangle_finite_from_profile (N m L : ℕ) (hm : 0 < m)
    (hsep : 2*(L*m) ≤ N) (w : ℕ → ℝ) (delta : ℝ) (hdelta : 0 ≤ delta)
    (htail : ∀ j, L*m ≤ j → w j = 1)
    (hcover : ∀ q ≤ L*m,
      1 ≤ ∑ i ∈ Finset.range m, triangle m (m-1-i)*w (q+i))
    (hnorm : (∑ j ∈ Finset.range (L*m), (w j^2-1)) ≤
      -((m : ℝ)-1)/3 + delta*(m : ℝ))
    (A : Finset ℤ) (hA : IsSidon A)
    (hAN : A ⊆ Finset.Ico (0 : ℤ) (N : ℤ)) (hk : 1 ≤ A.card) :
    (A.card : ℝ)^2 ≤
      ((N : ℝ)+(2*(m : ℝ)-2)/3+delta*(m : ℝ)) *
        (1+(4 : ℝ)/3*((A.card : ℝ)-1)/(m : ℝ)) := by
  have hmR : 0 < (m : ℝ) := by positivity
  have hmR0 : (m : ℝ) ≠ 0 := ne_of_gt hmR
  have hm1 : 1 ≤ (m : ℝ) := by exact_mod_cast hm
  have hkR : (1 : ℝ) ≤ A.card := by exact_mod_cast hk
  have hkm : 0 ≤ (A.card : ℝ)-1 := sub_nonneg.mpr hkR
  have he := SidonAsymmetric.finite_bound_left_one N m 1 L hm (by omega)
    (by simpa using hsep) (triangle m) w (triangle_nonneg m) (triangle_mass m hm)
    htail hcover A hA hAN
  simp only [Nat.cast_one, mul_one] at he
  let a : ℝ := SidonAsymmetric.aValue m (triangle m)
  let b : ℝ := SidonAsymmetric.rightBValue m L w
  change (A.card : ℝ)^2 ≤ ((N : ℝ)+b*(m : ℝ)-1)*
    (1+a*((A.card : ℝ)-1)/(m : ℝ)) at he
  have haEq : a = 2*(2*(m : ℝ)+1)/(3*((m : ℝ)+1)) := by
    dsimp [a, SidonAsymmetric.aValue]
    rw [triangle_square_mass m hm]
    field_simp
  have ha0 : 0 ≤ a := by rw [haEq]; positivity
  have ha : a ≤ (4 : ℝ)/3 := by
    rw [haEq]
    apply (div_le_iff₀ (by positivity : 0 < 3*((m : ℝ)+1))).mpr
    nlinarith
  have hnorm' : (∑ j ∈ Finset.range (L*m), w j^2) - (L : ℝ)*(m : ℝ) ≤
      -((m : ℝ)-1)/3 + delta*(m : ℝ) := by
    simpa only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one, Nat.cast_mul] using hnorm
  have hQeq : (N : ℝ)+b*(m : ℝ)-1 =
      (N : ℝ)+(m : ℝ)-1+(∑ j ∈ Finset.range (L*m), w j^2)-(L : ℝ)*(m : ℝ) := by
    dsimp [b, SidonAsymmetric.rightBValue]
    field_simp
    ring
  have hQ : (N : ℝ)+b*(m : ℝ)-1 ≤
      (N : ℝ)+(2*(m : ℝ)-2)/3+delta*(m : ℝ) := by
    rw [hQeq]
    linarith
  have hQ0 : 0 ≤ (N : ℝ)+(2*(m : ℝ)-2)/3+delta*(m : ℝ) := by
    have hn0 : 0 ≤ (N : ℝ) := by positivity
    have hdm := mul_nonneg hdelta hmR.le
    nlinarith
  have hE0 : 0 ≤ 1+a*((A.card : ℝ)-1)/(m : ℝ) := by positivity
  have hE : 1+a*((A.card : ℝ)-1)/(m : ℝ) ≤
      1+(4 : ℝ)/3*((A.card : ℝ)-1)/(m : ℝ) := by
    have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ha hkm) hmR.le
    linarith
  exact he.trans ((mul_le_mul_of_nonneg_right hQ hE0).trans
    (mul_le_mul_of_nonneg_left hE hQ0))

/-- The triangular renewal certificate, with its source and every analytic
obligation discharged. The only hypotheses concern an actual interval Sidon set
and the finite separation of the two boundary profiles. -/
theorem triangular_finite_bound (N m j : ℕ) (hm : 0 < m)
    (hsize : 2 * ((2*j+3)*m) ≤ N)
    (A : Finset ℤ) (hA : IsSidon A)
    (hAN : A ⊆ Finset.Ico (0 : ℤ) (N : ℤ)) (hk1 : 1 ≤ A.card) :
    (A.card : ℝ)^2 ≤
      ((N : ℝ)+(2*(m : ℝ)-2)/3+(4/(2 : ℝ)^j)*(m : ℝ)) *
        (1+(4 : ℝ)/3*((A.card : ℝ)-1)/(m : ℝ)) := by
  let M : ℕ := (2*j+3)*m
  let u : ℤ → ℝ := renewal m
  let W : ℕ → ℝ := fun n =>
    SidonRenewalNorm.finiteConv m
      (SidonRenewalNorm.reverseKernel m (triangle m)) u (n : ℤ)
  let w : ℕ → ℝ := SidonRenewalNorm.patched m M W
  let ε : ℝ := ((1 : ℝ)/2)/(2 : ℝ)^j
  have hM : m ≤ M := by dsimp [M]; nlinarith
  have hp : ∀ i ∈ Finset.range m, 0 ≤ triangle m i := by
    intro i hi
    exact triangle_nonneg m i (Finset.mem_range.mp hi)
  have hneg : ∀ n : ℤ, n < 0 → u n = 0 := renewal_negative m
  have hzero : u 0 = ((m : ℝ)+1)/2 := renewal_zero m
  have hrec : ∀ n : ℕ, 0 < n → (m : ℝ)*u (n : ℤ) =
      ∑ i ∈ Finset.range m, u ((n : ℤ)-((i+1 : ℕ) : ℤ)) :=
    renewal_recurrence m hm
  have hpow : 1 ≤ (2 : ℝ)^j := one_le_pow₀ (by norm_num)
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hε1 : ε ≤ 1 := by
    dsimp [ε]
    apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ)^j)).mpr
    linarith
  have hu : ∀ n : ℤ, (M : ℤ)-2*(m : ℤ)+2 ≤ n → n < M →
      |u n-1| ≤ ε := by
    intro n hn _
    have hMz : (M : ℤ)-2*(m : ℤ)+2 =
        (((2*j+1)*m : ℕ) : ℤ)+2 := by
      dsimp [M]
      ring
    rw [hMz] at hn
    have hn0 : 0 ≤ n := by omega
    have hnn : (2*j+1)*m ≤ n.toNat := by omega
    have ht := uniform_renewal_tail m hm u hneg hzero hrec j n.toNat hnn
    simpa only [Int.toNat_of_nonneg hn0] using ht
  have hconv : ∀ n : ℕ,
      SidonRenewalNorm.finiteConv m (triangle m) u n = 1 := by
    intro n
    exact triangle_renewal_convolution m hm u hneg hzero hrec n
  have hnorm0 := SidonRenewalNorm.patched_profile_bound m M hm hM
    (triangle m) u hp (triangle_mass m hm) hneg hconv
    (triangle_first_moment m hm) ε hε hε1 hu
  have hnorm : (∑ n ∈ Finset.range M, (w n^2-1)) ≤
      -((m : ℝ)-1)/3+(4/(2 : ℝ)^j)*(m : ℝ) := by
    change (∑ n ∈ Finset.range M, (w n^2-1)) ≤
      -((m : ℝ)-1)/3+8*(m : ℝ)*ε at hnorm0
    have heq : 8*(m : ℝ)*ε = (4/(2 : ℝ)^j)*(m : ℝ) := by
      dsimp [ε]
      ring
    rwa [heq] at hnorm0
  have hcover0 : ∀ q : ℕ,
      1 ≤ ∑ i ∈ Finset.range m,
        SidonRenewalNorm.reverseKernel m (triangle m) i * W (q+i) := by
    intro q
    have hc := triangle_reverse_cover m hm u hneg hzero hrec q
    apply le_of_eq
    symm
    simpa only [W, SidonRenewalNorm.finiteConv,
      SidonRenewalNorm.reverseKernel, reverseProfile, Nat.cast_add] using hc
  have hcover : ∀ q ≤ M,
      1 ≤ ∑ i ∈ Finset.range m, triangle m (m-1-i)*w (q+i) := by
    intro q _
    exact SidonRenewalNorm.patched_cover m M hM
      (SidonRenewalNorm.reverseKernel m (triangle m)) W
      (SidonRenewalNorm.reverse_nonneg m (triangle m) hp)
      (by rw [SidonRenewalNorm.reverse_mass]; exact triangle_mass m hm)
      hcover0 q
  exact triangle_finite_from_profile N m (2*j+3) hm hsize w
    (4/(2 : ℝ)^j) (by positivity)
    (SidonRenewalNorm.patched_tail m M W) hcover hnorm A hA hAN hk1

end SidonRenewalFinite
#print axioms SidonRenewalFinite.triangle_finite_from_profile
#print axioms SidonRenewalFinite.triangular_finite_bound



namespace SidonExactAlgebra

theorem nat_square_le_four_two_pow (n : ℕ) : (n:ℝ)^2 ≤ 4*(2:ℝ)^n := by
  by_cases hn : n ≤ 2
  · interval_cases n <;> norm_num
  · have hn3 : 3 ≤ n := by omega
    clear hn
    induction n, hn3 using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
      have hnR : (3:ℝ) ≤ n := by exact_mod_cast hn
      simp only [Nat.cast_add, Nat.cast_one, pow_succ]
      nlinarith [sq_nonneg ((n:ℝ)-2)]

theorem tail_delta_bound {x : ℝ} (hx : 0 < x) (j : ℕ) (hj : x ≤ j) :
    4/(2:ℝ)^j ≤ 16/x^2 := by
  have hp := nat_square_le_four_two_pow j
  have hs : x^2 ≤ (j:ℝ)^2 := by gcongr
  apply (div_le_div_iff₀ (by positivity : 0 < (2:ℝ)^j)
    (sq_pos_of_pos hx)).2
  nlinarith

theorem quadratic_twenty_two {t d q c k : ℝ}
    (ht : 64 ≤ t) (hd : 0 ≤ d) (hk : 0 ≤ k)
    (hq : q ≤ t^4+d*t^3+40*t^2) (hc : c ≤ d*t+2)
    (hfinite : k^2 ≤ q+c*k) : k ≤ t^2+d*t+22 := by
  have ht0 : 0 ≤ t := by linarith
  have hdt : 0 ≤ d*t := mul_nonneg hd ht0
  have hh : k^2 ≤ t^4+d*t^3+40*t^2+(d*t+2)*k := by
    have hc' := mul_le_mul_of_nonneg_right hc hk
    linarith
  by_contra hnot
  have hgt : t^2+d*t+22 < k := lt_of_not_ge hnot
  have hprod : 0 < (k-(t^2+d*t+22))*(k+(t^2+d*t+22)-(d*t+2)) := by
    apply mul_pos
    · linarith
    · nlinarith [sq_nonneg t]
  nlinarith [sq_nonneg t]

theorem triangular_numeric_bound {t m delta k : ℝ}
    (ht : 64 ≤ t) (hk : 0 ≤ k)
    (hmlo : Real.sqrt 2*t^3 ≤ m)
    (hmhi : m ≤ Real.sqrt 2*t^3+1)
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ 16/t)
    (hfinite : k^2 ≤ (t^4+(2*m-2)/3+delta*m) *
      (1+(4:ℝ)/3*(k-1)/m)) :
    k ≤ t^2+(2*Real.sqrt 2/3)*t+22 := by
  let d : ℝ := 2*Real.sqrt 2/3
  let q : ℝ := t^4+(2*m-2)/3+delta*m
  let c : ℝ := (4:ℝ)/3*q/m
  have ht0 : 0 < t := by linarith
  have ht1 : 1 ≤ t := by linarith
  have ht3 : 1 ≤ t^3 := one_le_pow₀ ht1
  have hs0 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs2 : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hs1 : 1 ≤ Real.sqrt 2 := by nlinarith
  have hs15 : Real.sqrt 2 ≤ 3/2 := by nlinarith
  have hm1 : 1 ≤ m := by
    have h := mul_le_mul hs1 ht3 (by norm_num : (0:ℝ) ≤ 1) hs0.le
    nlinarith
  have hm0 : 0 < m := by linarith
  have hd0 : 0 ≤ d := by dsimp [d]; positivity
  have hds : d*Real.sqrt 2=4/3 := by dsimp [d]; nlinarith
  have hdt : delta*t ≤ 16 := (le_div_iff₀ ht0).mp hdelta
  have hdeltaquarter : delta ≤ 1/4 := by
    have h := mul_le_mul_of_nonneg_left ht hdelta0
    nlinarith
  have hm15 : m ≤ (3/2)*t^3+1 := by
    have h := mul_le_mul_of_nonneg_right hs15 (pow_nonneg ht0.le 3)
    linarith
  have hdm : delta*m ≤ 40*t^2 := by
    have h := mul_le_mul_of_nonneg_right hdt hm0.le
    have h16 : (16:ℝ) ≤ 16*t^3 := by nlinarith
    have hmul : (delta*m)*t ≤ (40*t^2)*t := by nlinarith
    exact (mul_le_mul_iff_left₀ ht0).mp hmul
  have hq0 : 0 ≤ q := by
    dsimp [q]
    have hdeltam := mul_nonneg hdelta0 hm0.le
    nlinarith [pow_nonneg ht0.le 4]
  have hq : q ≤ t^4+d*t^3+40*t^2 := by
    have hboundary : (2*m-2)/3 ≤ d*t^3 := by dsimp [d]; nlinarith
    dsimp [q]
    linarith
  have hratio : (4:ℝ)/3*t^4/m ≤ d*t := by
    apply (div_le_iff₀ hm0).2
    have h := mul_le_mul_of_nonneg_left hmlo (mul_nonneg hd0 ht0.le)
    calc
      (4:ℝ)/3*t^4 = (d*t)*(Real.sqrt 2*t^3) := by rw [← hds]; ring
      _ ≤ (d*t)*m := h
  have hc : c ≤ d*t+2 := by
    have he : c = ((4:ℝ)/3*t^4/m)+(8:ℝ)/9-8/(9*m)+(4:ℝ)/3*delta := by
      dsimp [c,q]
      field_simp
      <;> ring
    rw [he]
    have hneg : 0 ≤ 8/(9*m) := by positivity
    nlinarith
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hrelax : k^2 ≤ q+c*k := by
    have he : q*(1+(4:ℝ)/3*(k-1)/m)=q+c*(k-1) := by
      dsimp [c]
      ring
    change k^2 ≤ q*(1+(4:ℝ)/3*(k-1)/m) at hfinite
    rw [he] at hfinite
    nlinarith
  exact quadratic_twenty_two ht hd0 hk hq hc hrelax

theorem parameter_choice (N : ℕ) (x : ℝ) (hx : 8 ≤ x)
    (hNx : x^8 = N) :
    ∃ m j : ℕ, 0 < m ∧ 2*((2*j+3)*m) ≤ N ∧
      Real.sqrt 2*(x^2)^3 ≤ m ∧ (m:ℝ) ≤ Real.sqrt 2*(x^2)^3+1 ∧
      0 ≤ 4/(2:ℝ)^j ∧ 4/(2:ℝ)^j ≤ 16/(x^2) := by
  let m : ℕ := ⌈Real.sqrt 2*x^6⌉₊
  let j : ℕ := ⌈x⌉₊
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hx6 : 16 ≤ x^6 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 8) hx 6
    norm_num at h
    linarith
  have hs0 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs2 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hs23 : Real.sqrt 2 ≤ 23/16 := by nlinarith
  have hmlo : Real.sqrt 2*x^6 ≤ m := Nat.le_ceil _
  have hmhi : (m:ℝ) ≤ Real.sqrt 2*x^6+1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hm0 : 0 < m := by
    have : 0 < (m:ℝ) := lt_of_lt_of_le (by positivity) hmlo
    exact_mod_cast this
  have hm15 : (m:ℝ) ≤ (3/2)*x^6 := by
    have h := mul_le_mul_of_nonneg_right hs23 (by positivity : 0 ≤ x^6)
    nlinarith
  have hjlo : x ≤ j := Nat.le_ceil _
  have hjhi : (j:ℝ) ≤ x+1 := (Nat.ceil_lt_add_one hx0.le).le
  have hsize : (2:ℝ)*((2*(j:ℝ)+3)*(m:ℝ)) ≤ x^8 := by
    calc
      _ ≤ 2*((2*x+5)*((3/2)*x^6)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply mul_le_mul _ hm15 (by positivity) (by linarith)
        linarith
      _ = (6*x+15)*x^6 := by ring
      _ ≤ x^2*x^6 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        nlinarith [mul_nonneg (by linarith : 0 ≤ x-8) (by linarith : 0 ≤ x+2)]
      _ = x^8 := by ring
  refine ⟨m,j,hm0,?_,?_,?_,by positivity,tail_delta_bound hx0 j hjlo⟩
  · rw [hNx] at hsize
    exact_mod_cast hsize
  · convert hmlo using 1 <;> ring
  · convert hmhi using 1 <;> ring

theorem eighth_root_data (N : ℕ) (hN : 2^24 ≤ N) :
    ∃ x : ℝ, 8 ≤ x ∧ x^8 = N ∧ x^4 = Real.sqrt N ∧
      x^2 = Real.sqrt (Real.sqrt N) := by
  let s := Real.sqrt (N:ℝ)
  let t := Real.sqrt s
  let x := Real.sqrt t
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hs2 : s^2 = N := Real.sq_sqrt (by positivity)
  have ht2 : t^2 = s := Real.sq_sqrt hs0
  have hx2 : x^2 = t := Real.sq_sqrt ht0
  have hNR : (16777216:ℝ) ≤ N := by exact_mod_cast hN
  have hslo : 4096 ≤ s := by nlinarith
  have htlo : 64 ≤ t := by nlinarith
  have hxlo : 8 ≤ x := by nlinarith
  have hx4 : x^4 = s := by calc
    x^4 = (x^2)^2 := by ring
    _ = s := by rw [hx2,ht2]
  refine ⟨x,hxlo,?_,hx4,hx2⟩
  calc
    x^8 = (x^4)^2 := by ring
    _ = (N:ℝ) := by rw [hx4,hs2]

theorem bound_of_finite_family (N : ℕ) (hN : 2^24 ≤ N) (k : ℝ)
    (hk : 0 ≤ k)
    (hfinite : ∀ m j : ℕ, 0 < m → 2*((2*j+3)*m) ≤ N → 1 ≤ k →
      k^2 ≤ ((N:ℝ)+(2*(m:ℝ)-2)/3+(4/(2:ℝ)^j)*(m:ℝ)) *
        (1+(4:ℝ)/3*(k-1)/(m:ℝ))) :
    k ≤ Real.sqrt N+Real.sqrt ((8:ℝ)/9)*Real.sqrt (Real.sqrt N)+22 := by
  by_cases hk1 : 1 ≤ k
  · obtain ⟨x,hx,hx8,hx4,hx2⟩ := eighth_root_data N hN
    obtain ⟨m,j,hm,hsize,hmlo,hmhi,hd0,hd⟩ := parameter_choice N x hx hx8
    have ht : 64 ≤ x^2 := by nlinarith
    have hf := hfinite m j hm hsize hk1
    have hx8' : (x^2)^4 = (N:ℝ) := by nlinarith only [hx8]
    rw [← hx8'] at hf
    have hb := triangular_numeric_bound ht hk hmlo hmhi hd0 hd hf
    have hs0 := Real.sqrt_nonneg ((8:ℝ)/9)
    have hs2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 8/9)
    have ht2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    have hrt0 := Real.sqrt_nonneg (2:ℝ)
    have hc : 2*Real.sqrt 2/3 = Real.sqrt ((8:ℝ)/9) := by nlinarith
    rw [hc,hx2,Real.sq_sqrt (Real.sqrt_nonneg (N:ℝ))] at hb
    exact hb
  · have ht : 0 ≤ Real.sqrt ((8:ℝ)/9)*Real.sqrt (Real.sqrt (N:ℝ)) := by positivity
    have hs : 0 ≤ Real.sqrt (N:ℝ) := Real.sqrt_nonneg _
    linarith

#print axioms triangular_numeric_bound
#print axioms parameter_choice
#print axioms bound_of_finite_family
end SidonExactAlgebra

namespace Submissions.Erdos30SidonUpperBoundSqrtEightNinths.Declan

/-- Standard unordered-sum uniqueness, including repeated summands. -/
def IsSidon (A : Finset ℤ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

abbrev statement : Prop :=
  ∀ N : ℕ, 2^24 ≤ N → ∀ A : Finset ℤ,
    A ⊆ Finset.Ico 0 (N : ℤ) → IsSidon A →
      (A.card : ℝ) ≤ Real.sqrt N +
        Real.sqrt ((8:ℝ)/9) * Real.sqrt (Real.sqrt N) + 22

theorem proof : statement := by
  intro N hN A hAN hA
  apply SidonExactAlgebra.bound_of_finite_family N hN (A.card:ℝ) (by positivity)
  intro m j hm hsize hk
  have hsidon : SidonConvolutionEnergy.IsSidon A :=
    (SidonConvolutionEnergy.isSidon_iff_unique_sums A).2 hA
  have hk1 : 1 ≤ A.card := by exact_mod_cast hk
  exact SidonRenewalFinite.triangular_finite_bound N m j hm hsize A hsidon hAN hk1

#print axioms proof

end Submissions.Erdos30SidonUpperBoundSqrtEightNinths.Declan
