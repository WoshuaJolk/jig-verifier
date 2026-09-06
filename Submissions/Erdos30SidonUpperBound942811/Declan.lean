import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Interval

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



namespace SidonAlgebraicTransfer

lemma quadratic_bound {u v d w k : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hd : 0 ≤ d) (hw : 0 ≤ w)
    (_hk : 0 ≤ k)
    (h : k ^ 2 ≤ u ^ 2 + v * u + w + (v + d) * k) :
    k ≤ u + v + d + w + 1 := by
  by_contra hc
  have hgt : u + v + d + w + 1 < k := lt_of_not_ge hc
  have hp : 0 < (k - (u + v + d + w + 1)) * (k + u + w + 1) :=
    mul_pos (by linarith) (by linarith)
  have hdu : 0 ≤ d * u := mul_nonneg hd hu
  have hwu : 0 ≤ w * u := mul_nonneg hw hu
  have hwv : 0 ≤ w * v := mul_nonneg hw hv
  have hdw : 0 ≤ d * w := mul_nonneg hd hw
  nlinarith [sq_nonneg w]

/-- Explicit algebraic inversion of the finite smoothing inequality.  Here
`x` is the fourth root of the interval length and `H` is any admissible
kernel length between `t*x^3` and `t*x^3+m`. -/
theorem finite_smoothing_bound {a b c t m x H k : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (_ht : 0 < t)
    (hm : 0 ≤ m) (hx : 1 ≤ x) (hH : 0 < H) (hk : 0 ≤ k)
    (hat : a = c * t) (hbt : b * t = c)
    (hlo : t * x ^ 3 ≤ H) (hhi : H ≤ t * x ^ 3 + m)
    (hfinite : k ^ 2 ≤ (x ^ 4 + b * H - 1) * (1 + a * (k - 1) / H))
    (hfactor : 0 ≤ x ^ 4 + b * H - 1) :
    k ≤ x ^ 2 + c * x + a * b + b * m + 1 := by
  have hx0 : 0 ≤ x := by linarith
  have hB : 0 ≤ x ^ 4 + b * H := by positivity
  have hD : 0 ≤ 1 + a * k / H := by positivity
  have hrelax : k ^ 2 ≤ (x ^ 4 + b * H) * (1 + a * k / H) := by
    calc
      k ^ 2 ≤ (x ^ 4 + b * H - 1) * (1 + a * (k - 1) / H) := hfinite
      _ ≤ (x ^ 4 + b * H - 1) * (1 + a * k / H) := by
        gcongr
        linarith
      _ ≤ (x ^ 4 + b * H) * (1 + a * k / H) := by gcongr; linarith
  have hratio : a * x ^ 4 / H ≤ c * x := by
    apply (div_le_iff₀ hH).2
    calc
      a * x ^ 4 = (c * x) * (t * x ^ 3) := by rw [hat]; ring
      _ ≤ (c * x) * H := mul_le_mul_of_nonneg_left hlo (mul_nonneg hc hx0)
  have hboundary : b * H ≤ c * x ^ 3 + b * m := by
    calc
      b * H ≤ b * (t * x ^ 3 + m) := mul_le_mul_of_nonneg_left hhi hb
      _ = c * x ^ 3 + b * m := by rw [mul_add, ← mul_assoc, hbt]
  have hrewrite :
      (x ^ 4 + b * H) * (1 + a * k / H) =
        x ^ 4 + b * H + (a * x ^ 4 / H + a * b) * k := by
    field_simp
  rw [hrewrite] at hrelax
  have hineq : k ^ 2 ≤ (x ^ 2) ^ 2 + (c * x) * x ^ 2 + b * m +
      (c * x + a * b) * k := by
    have hmulk := mul_le_mul_of_nonneg_right hratio hk
    nlinarith
  exact quadratic_bound (sq_nonneg x) (mul_nonneg hc hx0)
    (mul_nonneg ha hb) (mul_nonneg hb hm) hk hineq

#print axioms finite_smoothing_bound

/-- The admissible kernel length can be selected without rounding errors in
the leading coefficient. -/
theorem admissible_length {t x : ℝ} (m : ℕ) (hm : 0 < m)
    (ht : 0 < t) (hx : 0 < x) :
    ∃ h : ℕ, 0 < h ∧
      t * x ^ 3 ≤ (m : ℝ) * h ∧
      (m : ℝ) * h ≤ t * x ^ 3 + m := by
  let z : ℝ := t * x ^ 3 / m
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hz : 0 < z := by dsimp [z]; positivity
  refine ⟨⌈z⌉₊, ?_, ?_, ?_⟩
  · exact Nat.ceil_pos.mpr hz
  · have h := Nat.le_ceil z
    have h' := mul_le_mul_of_nonneg_left h hmR.le
    dsimp [z] at h'
    have he : (m : ℝ) * (t * x ^ 3 / m) = t * x ^ 3 := by field_simp
    rwa [he] at h'
  · have h : (⌈z⌉₊ : ℝ) ≤ z + 1 := by
      have hc := Nat.ceil_lt_add_one hz.le
      exact hc.le
    have h' := mul_le_mul_of_nonneg_left h hmR.le
    dsimp [z] at h'
    have he : (m : ℝ) * (t * x ^ 3 / m + 1) = t * x ^ 3 + m := by field_simp
    rwa [he] at h'

#print axioms admissible_length

lemma separation_condition {L t m x H : ℝ}
    (hL : 0 ≤ L) (hx : 1 ≤ x)
    (hxt : 4 * L * t ≤ x) (hxm : 4 * L * m ≤ x)
    (hH : H ≤ t * x ^ 3 + m) : 2 * L * H ≤ x ^ 4 := by
  have hx0 : 0 ≤ x := by linarith
  have hx3 : 1 ≤ x ^ 3 := one_le_pow₀ hx
  have hx4x : x ≤ x ^ 4 := by
    have := mul_le_mul_of_nonneg_left hx3 hx0
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hxt (pow_nonneg hx0 3)
  have hmulH := mul_le_mul_of_nonneg_left hH (by positivity : 0 ≤ 2 * L)
  nlinarith

/-- A finite smoothing inequality for each admissible multiple of `m` implies
an eventual bound with an explicit additive constant.  The hypothesis is the
finite combinatorial inequality, rather than an asymptotic assumption. -/
theorem eventual_bound (m L : ℕ) (hm : 0 < m)
    {a b c t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (ht : 0 < t) (hat : a = c * t) (hbt : b * t = c) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ k : ℝ, 0 ≤ k →
      (∀ h : ℕ, 0 < h → 2 * (L : ℝ) * ((m : ℝ) * h) ≤ N →
        k ^ 2 ≤ ((N : ℝ) + b * ((m : ℝ) * h) - 1) *
          (1 + a * (k - 1) / ((m : ℝ) * h))) →
      k ≤ Real.sqrt N + c * Real.sqrt (Real.sqrt N) + a * b + b * m + 1 := by
  let T : ℝ := max 1 (4 * (L : ℝ) * (t + m))
  have hT1 : 1 ≤ T := le_max_left _ _
  have hT0 : 0 ≤ T := by linarith
  refine ⟨⌈T ^ 4⌉₊, ?_⟩
  intro N hN k hk hf
  let x : ℝ := Real.sqrt (Real.sqrt N)
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hx2 : x ^ 2 = Real.sqrt N := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hx4 : x ^ 4 = N := by
    calc
      x ^ 4 = (x ^ 2) ^ 2 := by ring
      _ = (Real.sqrt N) ^ 2 := by rw [hx2]
      _ = N := Real.sq_sqrt (by positivity)
  have hTN : T ^ 4 ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have hTx : T ≤ x := (pow_le_pow_iff_left₀ hT0 hx0 (by decide : 4 ≠ 0)).mp
    (by rwa [hx4])
  have hx1 : 1 ≤ x := hT1.trans hTx
  have hTsum : 4 * (L : ℝ) * (t + m) ≤ x := (le_max_right _ _).trans hTx
  have hxt : 4 * (L : ℝ) * t ≤ x := by
    have : 0 ≤ 4 * (L : ℝ) * m := by positivity
    nlinarith
  have hxm : 4 * (L : ℝ) * m ≤ x := by
    have : 0 ≤ 4 * (L : ℝ) * t := by positivity
    nlinarith
  obtain ⟨h, hh, hlo, hhi⟩ := admissible_length m hm ht (by linarith : 0 < x)
  have hsep : 2 * (L : ℝ) * ((m : ℝ) * h) ≤ N := by
    rw [← hx4]
    exact separation_condition (by positivity) hx1 hxt hxm hhi
  have hH : (0 : ℝ) < (m : ℝ) * h := by positivity
  have hfactor : 0 ≤ x ^ 4 + b * ((m : ℝ) * h) - 1 := by
    have hpow : 1 ≤ x ^ 4 := one_le_pow₀ hx1
    have hpos : 0 ≤ b * ((m : ℝ) * h) := by positivity
    linarith
  have hfinite := hf h hh hsep
  rw [← hx4] at hfinite
  have hbound := finite_smoothing_bound ha hb hc ht (by positivity : (0 : ℝ) ≤ m)
    hx1 hH hk hat hbt hlo hhi hfinite hfactor
  simpa [hx2, x] using hbound

#print axioms eventual_bound

/-- The leading coefficient from any positive certificate can be replaced
by an explicitly certified rational upper bound on its square root. -/
theorem eventual_bound_of_coefficient (m L : ℕ) (hm : 0 < m)
    {a b γ : ℝ} (ha : 0 < a) (hb : 0 < b) (hγ : 0 < γ)
    (hab : a * b < γ ^ 2) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ k : ℝ, 0 ≤ k →
      (∀ h : ℕ, 0 < h → 2 * (L : ℝ) * ((m : ℝ) * h) ≤ N →
        k ^ 2 ≤ ((N : ℝ) + b * ((m : ℝ) * h) - 1) *
          (1 + a * (k - 1) / ((m : ℝ) * h))) →
      k ≤ Real.sqrt N + γ * Real.sqrt (Real.sqrt N) + a * b + b * m + 1 := by
  let c := Real.sqrt (a * b)
  let t := c / b
  have hc : 0 < c := Real.sqrt_pos.2 (mul_pos ha hb)
  have hcsq : c ^ 2 = a * b := Real.sq_sqrt (mul_pos ha hb).le
  have ht : 0 < t := div_pos hc hb
  have hat : a = c * t := by
    dsimp [t]
    field_simp
    nlinarith [hcsq]
  have hbt : b * t = c := by dsimp [t]; field_simp
  obtain ⟨N₀, hN₀⟩ := eventual_bound m L hm ha.le hb.le hc.le ht hat hbt
  refine ⟨N₀, ?_⟩
  intro N hN k hk hf
  have hbound := hN₀ N hN k hk hf
  have hcγ : c ≤ γ := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hcγ (Real.sqrt_nonneg (Real.sqrt N))
  linarith

#print axioms eventual_bound_of_coefficient

end SidonAlgebraicTransfer


namespace SidonAsymmetric

/-- The complete eventual upper bound from any positive one-sided asymmetric
certificate. The Sidon hypothesis uses standard unordered sums. -/
theorem eventual_bound_left_one (m L : ℕ) (hm : 0 < m)
    (p wRight : ℕ → ℝ) (γ : ℝ)
    (hp_nonneg : ∀ i, i < m → 0 ≤ p i)
    (hmass : ∑ i ∈ Finset.range m, p i = 1)
    (hwRight : ∀ j, L*m ≤ j → wRight j = 1)
    (hcRight : ∀ q ≤ L*m, 1 ≤ ∑ i ∈ Finset.range m, p (m-1-i)*wRight (q+i))
    (ha : 0 < aValue m p) (hb : 0 < rightBValue m L wRight)
    (hγ : 0 < γ) (hab : aValue m p * rightBValue m L wRight < γ^2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Finset ℤ, A ⊆ Finset.Ico 0 (N:ℤ) →
        (∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
          a+b=c+d → (a=c ∧ b=d) ∨ (a=d ∧ b=c)) →
      (A.card:ℝ) ≤ Real.sqrt N + γ*Real.sqrt (Real.sqrt N)+C := by
  let a := aValue m p
  let b := rightBValue m L wRight
  have ha' : 0 < a := ha
  have hb' : 0 < b := hb
  obtain ⟨N₀, hN₀⟩ := SidonAlgebraicTransfer.eventual_bound_of_coefficient m L hm
    ha' hb' hγ hab
  refine ⟨a*b+b*m+1, by positivity, N₀, ?_⟩
  intro N hN A hAN hAS
  have hA : SidonConvolutionEnergy.IsSidon A :=
    (SidonConvolutionEnergy.isSidon_iff_unique_sums A).mpr hAS
  suffices hbound : (A.card:ℝ) ≤ Real.sqrt N + γ*Real.sqrt (Real.sqrt N) +
      a*b+b*m+1 by simpa only [add_assoc] using hbound
  apply hN₀ N hN (A.card:ℝ) (by positivity)
  intro h hh hsep
  have hsepNat : 2*(L*m*h) ≤ N := by
    norm_num [← mul_assoc] at hsep ⊢
    exact_mod_cast hsep
  exact finite_bound_left_one N m h L hm hh hsepNat p wRight
    hp_nonneg hmass hwRight hcRight A hA hAN

#print axioms eventual_bound_left_one
end SidonAsymmetric



set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/- Exact asymmetric scalar certificate, generated from certificate.json.
SHA256: 3dd946a1e412401705b0b5ee469ca592171de855b7775631024495b9d234754a
All numerical propositions are checked by Lean's kernel via decide +kernel.
No admitted proof, external computation axiom, or custom axiom is used. -/
namespace SidonAsymmetricData
open Finset

def weightRowLLLLLLLLLL (j : ℕ) : ℕ := if j < 1 then 3906250000001 else 7827758789064
def weightRowLLLLLLLLLRR (j : ℕ) : ℕ := if j < 4 then 15716791385786 else 19684435102137
def weightRowLLLLLLLLLR (j : ℕ) : ℕ := if j < 3 then 11764585971834 else weightRowLLLLLLLLLRR j
def weightRowLLLLLLLLL (j : ℕ) : ℕ := if j < 2 then weightRowLLLLLLLLLL j else weightRowLLLLLLLLLR j
def weightRowLLLLLLLLRL (j : ℕ) : ℕ := if j < 6 then 23667577426755 else 27666278901078
def weightRowLLLLLLLLRRR (j : ℕ) : ℕ := if j < 9 then 35710602647969 else 39756347189563
def weightRowLLLLLLLLRR (j : ℕ) : ℕ := if j < 8 then 31680600303035 else weightRowLLLLLLLLRRR j
def weightRowLLLLLLLLR (j : ℕ) : ℕ := if j < 7 then weightRowLLLLLLLLRL j else weightRowLLLLLLLLRR j
def weightRowLLLLLLLL (j : ℕ) : ℕ := if j < 5 then weightRowLLLLLLLLL j else weightRowLLLLLLLLR j
def weightRowLLLLLLLRLL (j : ℕ) : ℕ := if j < 11 then 43817895420772 else 47895309074759
def weightRowLLLLLLLRLRR (j : ℕ) : ℕ := if j < 14 then 56097980790387 else 60223363527849
def weightRowLLLLLLLRLR (j : ℕ) : ℕ := if j < 13 then 51988650125832 else weightRowLLLLLLLRLRR j
def weightRowLLLLLLLRL (j : ℕ) : ℕ := if j < 12 then weightRowLLLLLLLRLL j else weightRowLLLLLLLRLR j
def weightRowLLLLLLLRRL (j : ℕ) : ℕ := if j < 16 then 64364861041630 else 68522536280073
def weightRowLLLLLLLRRRR (j : ℕ) : ℕ := if j < 19 then 76886672954751 else 81093261520981
def weightRowLLLLLLLRRR (j : ℕ) : ℕ := if j < 18 then 72696452437418 else weightRowLLLLLLLRRRR j
def weightRowLLLLLLLRR (j : ℕ) : ℕ := if j < 17 then weightRowLLLLLLLRRL j else weightRowLLLLLLLRRR j
def weightRowLLLLLLLR (j : ℕ) : ℕ := if j < 15 then weightRowLLLLLLLRL j else weightRowLLLLLLLRR j
def weightRowLLLLLLL (j : ℕ) : ℕ := if j < 10 then weightRowLLLLLLLL j else weightRowLLLLLLLR j
def weightRowLLLLLLRLLL (j : ℕ) : ℕ := if j < 21 then 85316282073797 else 89555798800648
def weightRowLLLLLLRLLRR (j : ℕ) : ℕ := if j < 24 then 98084578780884 else 102373971666746
def weightRowLLLLLLRLLR (j : ℕ) : ℕ := if j < 23 then 93811876139713 else weightRowLLLLLLRLLRR j
def weightRowLLLLLLRLL (j : ℕ) : ℕ := if j < 22 then weightRowLLLLLLRLLL j else weightRowLLLLLLRLLR j
def weightRowLLLLLLRLRL (j : ℕ) : ℕ := if j < 26 then 106680119993570 else 111003089212294
def weightRowLLLLLLRLRRR (j : ℕ) : ℕ := if j < 29 then 119699753408552 else 124073580570304
def weightRowLLLLLLRLRR (j : ℕ) : ℕ := if j < 28 then 115342945029530 else weightRowLLLLLLRLRRR j
def weightRowLLLLLLRLR (j : ℕ) : ℕ := if j < 27 then weightRowLLLLLLRLRL j else weightRowLLLLLLRLRR j
def weightRowLLLLLLRL (j : ℕ) : ℕ := if j < 25 then weightRowLLLLLLRLL j else weightRowLLLLLLRLR j
def weightRowLLLLLLRRLL (j : ℕ) : ℕ := if j < 31 then 128464492994406 else 132872557420166
def weightRowLLLLLLRRLRR (j : ℕ) : ℕ := if j < 34 then 141740410538399 else 146200334017065
def weightRowLLLLLLRRLR (j : ℕ) : ℕ := if j < 33 then 137297840847588 else weightRowLLLLLLRRLRR j
def weightRowLLLLLLRRL (j : ℕ) : ℕ := if j < 32 then weightRowLLLLLLRRLL j else weightRowLLLLLLRRLR j
def weightRowLLLLLLRRRL (j : ℕ) : ℕ := if j < 36 then 150677679071819 else 155172513755693
def weightRowLLLLLLRRRRR (j : ℕ) : ℕ := if j < 39 then 164214925553128 else 168762640106070
def weightRowLLLLLLRRRR (j : ℕ) : ℕ := if j < 38 then 159684906387551 else weightRowLLLLLLRRRRR j
def weightRowLLLLLLRRR (j : ℕ) : ℕ := if j < 37 then weightRowLLLLLLRRRL j else weightRowLLLLLLRRRR j
def weightRowLLLLLLRR (j : ℕ) : ℕ := if j < 35 then weightRowLLLLLLRRL j else weightRowLLLLLLRRR j
def weightRowLLLLLLR (j : ℕ) : ℕ := if j < 30 then weightRowLLLLLLRL j else weightRowLLLLLLRR j
def weightRowLLLLLL (j : ℕ) : ℕ := if j < 20 then weightRowLLLLLLL j else weightRowLLLLLLR j
def weightRowLLLLLRLLLL (j : ℕ) : ℕ := if j < 41 then 173328119168984 else 177911432134488
def weightRowLLLLLRLLLRR (j : ℕ) : ℕ := if j < 44 then 187131838700116 else 191769072445038
def weightRowLLLLLRLLLR (j : ℕ) : ℕ := if j < 43 then 182512648666263 else weightRowLLLLLRLLLRR j
def weightRowLLLLLRLLL (j : ℕ) : ℕ := if j < 42 then weightRowLLLLLRLLLL j else weightRowLLLLLRLLLR j
def weightRowLLLLLRLLRL (j : ℕ) : ℕ := if j < 46 then 196424420384277 else 201097953276403
def weightRowLLLLLRLLRRR (j : ℕ) : ℕ := if j < 49 then 210499858336687 else 215228373408315
def weightRowLLLLLRLLRR (j : ℕ) : ℕ := if j < 48 then 205789742156389 else weightRowLLLLLRLLRRR j
def weightRowLLLLLRLLR (j : ℕ) : ℕ := if j < 47 then weightRowLLLLLRLLRL j else weightRowLLLLLRLLRR j
def weightRowLLLLLRLL (j : ℕ) : ℕ := if j < 45 then weightRowLLLLLRLLL j else weightRowLLLLLRLLR j
def weightRowLLLLLRLRLL (j : ℕ) : ℕ := if j < 51 then 219975359241941 else 224740887988980
def weightRowLLLLLRLRLRR (j : ℕ) : ℕ := if j < 54 then 234327864239260 else 239149457458944
def weightRowLLLLLRLRLR (j : ℕ) : ℕ := if j < 53 then 229525032082687 else weightRowLLLLLRLRLRR j
def weightRowLLLLLRLRL (j : ℕ) : ℕ := if j < 52 then weightRowLLLLLRLRLL j else weightRowLLLLLRLRLR j
def weightRowLLLLLRLRRL (j : ℕ) : ℕ := if j < 56 then 243989885027143 else 248849220515531
def weightRowLLLLLRLRRRR (j : ℕ) : ℕ := if j < 59 then 258624910977635 else 263541414536141
def weightRowLLLLLRLRRR (j : ℕ) : ℕ := if j < 58 then 253727537783169 else weightRowLLLLLRLRRRR j
def weightRowLLLLLRLRR (j : ℕ) : ℕ := if j < 57 then weightRowLLLLLRLRRL j else weightRowLLLLLRLRRR j
def weightRowLLLLLRLR (j : ℕ) : ℕ := if j < 55 then weightRowLLLLLRLRL j else weightRowLLLLLRLRR j
def weightRowLLLLLRL (j : ℕ) : ℕ := if j < 50 then weightRowLLLLLRLL j else weightRowLLLLLRLR j
def weightRowLLLLLRRLLL (j : ℕ) : ℕ := if j < 61 then 268477123186673 else 273432111949121
def weightRowLLLLLRRLLRR (j : ℕ) : ℕ := if j < 64 then 283400231355705 else 288413513509438
def weightRowLLLLLRRLLR (j : ℕ) : ℕ := if j < 63 then 278406456136422 else weightRowLLLLLRRLLRR j
def weightRowLLLLLRRLL (j : ℕ) : ℕ := if j < 62 then weightRowLLLLLRRLLL j else weightRowLLLLLRRLLR j
def weightRowLLLLLRRLRL (j : ℕ) : ℕ := if j < 66 then 293446378796584 else 298498903713759
def weightRowLLLLLRRLRRR (j : ℕ) : ℕ := if j < 69 then 308663239919892 else 313775205700829
def weightRowLLLLLRRLRR (j : ℕ) : ℕ := if j < 68 then 303571165056391 else weightRowLLLLLRRLRRR j
def weightRowLLLLLRRLR (j : ℕ) : ℕ := if j < 67 then weightRowLLLLLRRLRL j else weightRowLLLLLRRLRR j
def weightRowLLLLLRRL (j : ℕ) : ℕ := if j < 65 then weightRowLLLLLRRLL j else weightRowLLLLLRRLR j
def weightRowLLLLLRRRLL (j : ℕ) : ℕ := if j < 71 then 318907140098098 else 324059121114106
def weightRowLLLLLRRRLRR (j : ℕ) : ℕ := if j < 74 then 334423536536645 else 339636128476242
def weightRowLLLLLRRRLR (j : ℕ) : ℕ := if j < 73 then 329231227055958 else weightRowLLLLLRRRLRR j
def weightRowLLLLLRRRL (j : ℕ) : ℕ := if j < 72 then weightRowLLLLLRRRLL j else weightRowLLLLLRRRLR j
def weightRowLLLLLRRRRL (j : ℕ) : ℕ := if j < 76 then 344869082103102 else 350122476955067
def weightRowLLLLLRRRRRR (j : ℕ) : ℕ := if j < 79 then 360690910040363 else 366006108907708
def weightRowLLLLLRRRRR (j : ℕ) : ℕ := if j < 78 then 355396392880673 else weightRowLLLLLRRRRRR j
def weightRowLLLLLRRRR (j : ℕ) : ℕ := if j < 77 then weightRowLLLLLRRRRL j else weightRowLLLLLRRRRR j
def weightRowLLLLLRRR (j : ℕ) : ℕ := if j < 75 then weightRowLLLLLRRRL j else weightRowLLLLLRRRR j
def weightRowLLLLLRR (j : ℕ) : ℕ := if j < 70 then weightRowLLLLLRRL j else weightRowLLLLLRRR j
def weightRowLLLLLR (j : ℕ) : ℕ := if j < 60 then weightRowLLLLLRL j else weightRowLLLLLRR j
def weightRowLLLLL (j : ℕ) : ℕ := if j < 40 then weightRowLLLLLL j else weightRowLLLLLR j
def weightRowLLLLRLLLLL (j : ℕ) : ℕ := if j < 81 then 371342070270629 else 376698875232624
def weightRowLLLLRLLLLRR (j : ℕ) : ℕ := if j < 84 then 387475341953118 else 392895167507623
def weightRowLLLLRLLLLR (j : ℕ) : ℕ := if j < 83 then 382076605214001 else weightRowLLLLRLLLLRR j
def weightRowLLLLRLLLL (j : ℕ) : ℕ := if j < 82 then weightRowLLLLRLLLLL j else weightRowLLLLRLLLLR j
def weightRowLLLLRLLLRL (j : ℕ) : ℕ := if j < 86 then 398336164255699 else 403798414897323
def weightRowLLLLRLLLRRR (j : ℕ) : ℕ := if j < 89 then 414787010277608 else 420313522036505
def weightRowLLLLRLLLRR (j : ℕ) : ℕ := if j < 88 then 409282002455516 else weightRowLLLLRLLLRRR j
def weightRowLLLLRLLLR (j : ℕ) : ℕ := if j < 87 then weightRowLLLLRLLLRL j else weightRowLLLLRLLLRR j
def weightRowLLLLRLLL (j : ℕ) : ℕ := if j < 85 then weightRowLLLLRLLLL j else weightRowLLLLRLLLR j
def weightRowLLLLRLLRLL (j : ℕ) : ℕ := if j < 91 then 425861621731960 else 431431393691850
def weightRowLLLLRLLRLRR (j : ℕ) : ℕ := if j < 94 then 442636293364761 else 448271591385717
def weightRowLLLLRLLRLR (j : ℕ) : ℕ := if j < 93 then 437022922573459 else weightRowLLLLRLLRLRR j
def weightRowLLLLRLLRL (j : ℕ) : ℕ := if j < 92 then weightRowLLLLRLLRLL j else weightRowLLLLRLLRLR j
def weightRowLLLLRLLRRL (j : ℕ) : ℕ := if j < 96 then 453928902289568 else 459608312064137
def weightRowLLLLRLLRRRR (j : ℕ) : ℕ := if j < 99 then 471033773857485 else 476779999536616
def weightRowLLLLRLLRRR (j : ℕ) : ℕ := if j < 98 then 465309907033137 else weightRowLLLLRLLRRRR j
def weightRowLLLLRLLRR (j : ℕ) : ℕ := if j < 97 then weightRowLLLLRLLRRL j else weightRowLLLLRLLRRR j
def weightRowLLLLRLLR (j : ℕ) : ℕ := if j < 95 then weightRowLLLLRLLRL j else weightRowLLLLRLLRR j
def weightRowLLLLRLL (j : ℕ) : ℕ := if j < 90 then weightRowLLLLRLLL j else weightRowLLLLRLLR j
def weightRowLLLLRLRLLL (j : ℕ) : ℕ := if j < 101 then 482548671409806 else 488339877157501
def weightRowLLLLRLRLLRR (j : ℕ) : ℕ := if j < 104 then 499990242712032 else 505849579597626
def weightRowLLLLRLRLLR (j : ℕ) : ℕ := if j < 103 then 494153704802647 else weightRowLLLLRLRLLRR j
def weightRowLLLLRLRLL (j : ℕ) : ℕ := if j < 102 then weightRowLLLLRLRLLL j else weightRowLLLLRLRLLR j
def weightRowLLLLRLRLRL (j : ℕ) : ℕ := if j < 106 then 511731804517929 else 517637006879328
def weightRowLLLLRLRLRRR (j : ℕ) : ℕ := if j < 109 then 529516703298534 else 535491377920794
def weightRowLLLLRLRLRR (j : ℕ) : ℕ := if j < 108 then 523565276437450 else weightRowLLLLRLRLRRR j
def weightRowLLLLRLRLR (j : ℕ) : ℕ := if j < 107 then weightRowLLLLRLRLRL j else weightRowLLLLRLRLRR j
def weightRowLLLLRLRL (j : ℕ) : ℕ := if j < 105 then weightRowLLLLRLRLL j else weightRowLLLLRLRLR j
def weightRowLLLLRLRRLL (j : ℕ) : ℕ := if j < 111 then 541489391115797 else 547510834049843
def weightRowLLLLRLRRLRR (j : ℕ) : ℕ := if j < 114 then 559624375582246 else 565716658299364
def weightRowLLLLRLRRLR (j : ℕ) : ℕ := if j < 113 then 553555798245350 else weightRowLLLLRLRRLRR j
def weightRowLLLLRLRRL (j : ℕ) : ℕ := if j < 112 then weightRowLLLLRLRRLL j else weightRowLLLLRLRRLR j
def weightRowLLLLRLRRRL (j : ℕ) : ℕ := if j < 116 then 571832738995846 else 577972710632548
def weightRowLLLLRLRRRRR (j : ℕ) : ℕ := if j < 119 then 590324700387103 else 596536906247990
def weightRowLLLLRLRRRR (j : ℕ) : ℕ := if j < 118 then 584136666533457 else weightRowLLLLRLRRRRR j
def weightRowLLLLRLRRR (j : ℕ) : ℕ := if j < 117 then weightRowLLLLRLRRRL j else weightRowLLLLRLRRRR j
def weightRowLLLLRLRR (j : ℕ) : ℕ := if j < 115 then weightRowLLLLRLRRL j else weightRowLLLLRLRRR j
def weightRowLLLLRLR (j : ℕ) : ℕ := if j < 110 then weightRowLLLLRLRL j else weightRowLLLLRLRR j
def weightRowLLLLRL (j : ℕ) : ℕ := if j < 100 then weightRowLLLLRLL j else weightRowLLLLRLR j
def weightRowLLLLRRLLLL (j : ℕ) : ℕ := if j < 121 then 602773378538021 else 609034212047936
def weightRowLLLLRRLLLRR (j : ℕ) : ℕ := if j < 124 then 621629343743196 else 627963833367193
def weightRowLLLLRRLLLR (j : ℕ) : ℕ := if j < 123 then 615319501938748 else weightRowLLLLRRLLLRR j
def weightRowLLLLRRLLL (j : ℕ) : ℕ := if j < 122 then weightRowLLLLRRLLLL j else weightRowLLLLRRLLLR j
def weightRowLLLLRRLLRL (j : ℕ) : ℕ := if j < 126 then 634323067091284 else 640707141572109
def weightRowLLLLRRLLRRR (j : ℕ) : ℕ := if j < 129 then 653550201319828 else 660009381793733
def weightRowLLLLRRLLRR (j : ℕ) : ℕ := if j < 128 then 647116153843875 else weightRowLLLLRRLLRRR j
def weightRowLLLLRRLLR (j : ℕ) : ℕ := if j < 127 then weightRowLLLLRRLLRL j else weightRowLLLLRRLLRR j
def weightRowLLLLRRLL (j : ℕ) : ℕ := if j < 125 then weightRowLLLLRRLLL j else weightRowLLLLRRLLR j
def weightRowLLLLRRLRLL (j : ℕ) : ℕ := if j < 131 then 666493793441365 else 673003534821995
def weightRowLLLLRRLRLRR (j : ℕ) : ℕ := if j < 134 then 686099402945831 else 692685728738588
def weightRowLLLLRRLRLR (j : ℕ) : ℕ := if j < 133 then 679538704879894 else weightRowLLLLRRLRLRR j
def weightRowLLLLRRLRL (j : ℕ) : ℕ := if j < 132 then weightRowLLLLRRLRLL j else weightRowLLLLRRLRLR j
def weightRowLLLLRRLRRL (j : ℕ) : ℕ := if j < 136 then 699297782366473 else 705935664328842
def weightRowLLLLRRLRRRR (j : ℕ) : ℕ := if j < 139 then 719289317218867 else 726005291114253
def weightRowLLLLRRLRRR (j : ℕ) : ℕ := if j < 138 then 712599475517626 else weightRowLLLLRRLRRRR j
def weightRowLLLLRRLRR (j : ℕ) : ℕ := if j < 137 then weightRowLLLLRRLRRL j else weightRowLLLLRRLRRR j
def weightRowLLLLRRLR (j : ℕ) : ℕ := if j < 135 then weightRowLLLLRRLRL j else weightRowLLLLRRLRR j
def weightRowLLLLRRL (j : ℕ) : ℕ := if j < 130 then weightRowLLLLRRLL j else weightRowLLLLRRLR j
def weightRowLLLLRRRLLL (j : ℕ) : ℕ := if j < 141 then 732747499282668 else 739516044201741
def weightRowLLLLRRRLLRR (j : ℕ) : ℕ := if j < 144 then 753132556205457 else 759980730253134
def weightRowLLLLRRRLLR (j : ℕ) : ℕ := if j < 143 then 746311028749404 else weightRowLLLLRRRLLRR j
def weightRowLLLLRRRLL (j : ℕ) : ℕ := if j < 142 then weightRowLLLLRRRLLL j else weightRowLLLLRRRLLR j
def weightRowLLLLRRRLRL (j : ℕ) : ℕ := if j < 146 then 766855654980686 else 773757434882954
def weightRowLLLLRRRLRRR (j : ℕ) : ℕ := if j < 149 then 787641980233524 else 794624956718811
def weightRowLLLLRRRLRR (j : ℕ) : ℕ := if j < 148 then 780686174862965 else weightRowLLLLRRRLRRR j
def weightRowLLLLRRRLR (j : ℕ) : ℕ := if j < 147 then weightRowLLLLRRRLRL j else weightRowLLLLRRRLRR j
def weightRowLLLLRRRL (j : ℕ) : ℕ := if j < 145 then weightRowLLLLRRRLL j else weightRowLLLLRRRLR j
def weightRowLLLLRRRRLL (j : ℕ) : ℕ := if j < 151 then 801635210455994 else 808672847996838
def weightRowLLLLRRRRLRR (j : ℕ) : ℕ := if j < 154 then 822830702779284 else 829951135212015
def weightRowLLLLRRRRLR (j : ℕ) : ℕ := if j < 153 then 815737976309325 else weightRowLLLLRRRRLRR j
def weightRowLLLLRRRRL (j : ℕ) : ℕ := if j < 152 then weightRowLLLLRRRRLL j else weightRowLLLLRRRRLR j
def weightRowLLLLRRRRRL (j : ℕ) : ℕ := if j < 156 then 837099381833937 else 844275551294226
def weightRowLLLLRRRRRRR (j : ℕ) : ℕ := if j < 159 then 858712095450322 else 865972689573175
def weightRowLLLLRRRRRR (j : ℕ) : ℕ := if j < 158 then 851479752666469 else weightRowLLLLRRRRRRR j
def weightRowLLLLRRRRR (j : ℕ) : ℕ := if j < 157 then weightRowLLLLRRRRRL j else weightRowLLLLRRRRRR j
def weightRowLLLLRRRR (j : ℕ) : ℕ := if j < 155 then weightRowLLLLRRRRL j else weightRowLLLLRRRRR j
def weightRowLLLLRRR (j : ℕ) : ℕ := if j < 150 then weightRowLLLLRRRL j else weightRowLLLLRRRR j
def weightRowLLLLRR (j : ℕ) : ℕ := if j < 140 then weightRowLLLLRRL j else weightRowLLLLRRR j
def weightRowLLLLR (j : ℕ) : ℕ := if j < 120 then weightRowLLLLRL j else weightRowLLLLRR j
def weightRowLLLL (j : ℕ) : ℕ := if j < 80 then weightRowLLLLL j else weightRowLLLLR j
def weightRowLLLRLLLLLL (j : ℕ) : ℕ := if j < 161 then 873261645391820 else 880579073694132
def weightRowLLLRLLLLLRR (j : ℕ) : ℕ := if j < 164 then 895299793066768 else 902703307883435
def weightRowLLLRLLLLLR (j : ℕ) : ℕ := if j < 163 then 887925085700750 else weightRowLLLRLLLLLRR j
def weightRowLLLRLLLLL (j : ℕ) : ℕ := if j < 162 then weightRowLLLRLLLLLL j else weightRowLLLRLLLLLR j
def weightRowLLLRLLLLRL (j : ℕ) : ℕ := if j < 166 then 910135742679855 else 917597210424698
def weightRowLLLRLLLLRRR (j : ℕ) : ℕ := if j < 169 then 932607698842482 else 940156947666085
def weightRowLLLRLLLLRR (j : ℕ) : ℕ := if j < 168 then 925087824527920 else weightRowLLLRLLLLRRR j
def weightRowLLLRLLLLR (j : ℕ) : ℕ := if j < 167 then weightRowLLLRLLLLRL j else weightRowLLLRLLLLRR j
def weightRowLLLRLLLL (j : ℕ) : ℕ := if j < 165 then weightRowLLLRLLLLL j else weightRowLLLRLLLLR j
def weightRowLLLRLLLRLL (j : ℕ) : ℕ := if j < 171 then 947735685742906 else 955344028265339
def weightRowLLLRLLLRLRR (j : ℕ) : ℕ := if j < 174 then 970649989668234 else 978347841190376
def weightRowLLLRLLLRLR (j : ℕ) : ℕ := if j < 173 then 962982090875751 else weightRowLLLRLLLRLRR j
def weightRowLLLRLLLRL (j : ℕ) : ℕ := if j < 172 then weightRowLLLRLLLRLL j else weightRowLLLRLLLRLR j
def weightRowLLLRLLLRRL (j : ℕ) : ℕ := if j < 176 then 986075762445026 else 993833870892076
def weightRowLLLRLLLRRRR (j : ℕ) : ℕ := if j < 179 then 1009441121498882 else 1017290500879737
def weightRowLLLRLLLRRR (j : ℕ) : ℕ := if j < 178 then 1001622284450249 else weightRowLLLRLLLRRRR j
def weightRowLLLRLLLRR (j : ℕ) : ℕ := if j < 177 then weightRowLLLRLLLRRL j else weightRowLLLRLLLRRR j
def weightRowLLLRLLLR (j : ℕ) : ℕ := if j < 175 then weightRowLLLRLLLRL j else weightRowLLLRLLLRR j
def weightRowLLLRLLL (j : ℕ) : ℕ := if j < 170 then weightRowLLLRLLLL j else weightRowLLLRLLLR j
def weightRowLLLRLLRLLL (j : ℕ) : ℕ := if j < 181 then 1025170541898799 else 1033081364328091
def weightRowLLLRLLRLLRR (j : ℕ) : ℕ := if j < 184 then 1048995834846589 else 1056999724826459
def weightRowLLLRLLRLLR (j : ℕ) : ℕ := if j < 183 then 1041023088407498 else weightRowLLLRLLRLLRR j
def weightRowLLLRLLRLL (j : ℕ) : ℕ := if j < 182 then weightRowLLLRLLRLLL j else weightRowLLLRLLRLLR j
def weightRowLLLRLLRLRL (j : ℕ) : ℕ := if j < 186 then 1065034880001562 else 1073101422501568
def weightRowLLLRLLRLRRR (j : ℕ) : ℕ := if j < 189 then 1089329160382173 else 1097490602414916
def weightRowLLLRLLRLRR (j : ℕ) : ℕ := if j < 188 then 1081199474933215 else weightRowLLLRLLRLRRR j
def weightRowLLLRLLRLR (j : ℕ) : ℕ := if j < 187 then weightRowLLLRLLRLRL j else weightRowLLLRLLRLRR j
def weightRowLLLRLLRL (j : ℕ) : ℕ := if j < 185 then weightRowLLLRLLRLL j else weightRowLLLRLLRLR j
def weightRowLLLRLLRRLL (j : ℕ) : ℕ := if j < 191 then 1105683925080599 else 1113909252912945
def weightRowLLLRLLRRLRR (j : ℕ) : ℕ := if j < 194 then 1130456424646715 else 1138778520055491
def weightRowLLLRLLRRLR (j : ℕ) : ℕ := if j < 193 then 1122166710932136 else weightRowLLLRLLRRLRR j
def weightRowLLLRLLRRL (j : ℕ) : ℕ := if j < 192 then weightRowLLLRLLRRLL j else weightRowLLLRLLRRLR j
def weightRowLLLRLLRRRL (j : ℕ) : ℕ := if j < 196 then 1147133123649458 else 1155520362413714
def weightRowLLLRLLRRRRR (j : ℕ) : ℕ := if j < 199 then 1172393255875601 else 1180879167031365
def weightRowLLLRLLRRRR (j : ℕ) : ℕ := if j < 198 then 1163940363829392 else weightRowLLLRLLRRRRR j
def weightRowLLLRLLRRR (j : ℕ) : ℕ := if j < 197 then weightRowLLLRLLRRRL j else weightRowLLLRLLRRRR j
def weightRowLLLRLLRR (j : ℕ) : ℕ := if j < 195 then weightRowLLLRLLRRL j else weightRowLLLRLLRRR j
def weightRowLLLRLLR (j : ℕ) : ℕ := if j < 190 then weightRowLLLRLLRL j else weightRowLLLRLLRR j
def weightRowLLLRLL (j : ℕ) : ℕ := if j < 180 then weightRowLLLRLLL j else weightRowLLLRLLR j
def weightRowLLLRLRLLLL (j : ℕ) : ℕ := if j < 201 then 1189398226277581 else 1197950563098978
def weightRowLLLRLRLLLRR (j : ℕ) : ℕ := if j < 204 then 1215155589937201 else 1223808541460393
def weightRowLLLRLRLLLR (j : ℕ) : ℕ := if j < 203 then 1206536307486083 else weightRowLLLRLRLLLRR j
def weightRowLLLRLRLLL (j : ℕ) : ℕ := if j < 202 then weightRowLLLRLRLLLL j else weightRowLLLRLRLLLR j
def weightRowLLLRLRLLRL (j : ℕ) : ℕ := if j < 206 then 1232495293575473 else 1241215978316002
def weightRowLLLRLRLLRRR (j : ℕ) : ℕ := if j < 209 then 1258759676388452 else 1267582956374345
def weightRowLLLRLRLLRR (j : ℕ) : ℕ := if j < 208 then 1249970728231299 else weightRowLLLRLRLLRRR j
def weightRowLLLRLRLLR (j : ℕ) : ℕ := if j < 207 then weightRowLLLRLRLLRL j else weightRowLLLRLRLLRR j
def weightRowLLLRLRLL (j : ℕ) : ℕ := if j < 205 then weightRowLLLRLRLLL j else weightRowLLLRLRLLR j
def weightRowLLLRLRLRLL (j : ℕ) : ℕ := if j < 211 then 1276440702297682 else 1285333048791032
def weightRowLLLRLRLRLRR (j : ℕ) : ℕ := if j < 214 then 1303222084649641 else 1312219045917804
def weightRowLLLRLRLRLR (j : ℕ) : ℕ := if j < 213 then 1294260131012872 else weightRowLLLRLRLRLRR j
def weightRowLLLRLRLRL (j : ℕ) : ℕ := if j < 212 then weightRowLLLRLRLRLL j else weightRowLLLRLRLRLR j
def weightRowLLLRLRLRRL (j : ℕ) : ℕ := if j < 216 then 1321251151565920 else 1330318538876725
def weightRowLLLRLRLRRRR (j : ℕ) : ℕ := if j < 219 then 1348559710300732 else 1357733771669094
def weightRowLLLRLRLRRR (j : ℕ) : ℕ := if j < 218 then 1339421345669212 else weightRowLLLRLRLRRRR j
def weightRowLLLRLRLRR (j : ℕ) : ℕ := if j < 217 then weightRowLLLRLRLRRL j else weightRowLLLRLRLRRR j
def weightRowLLLRLRLR (j : ℕ) : ℕ := if j < 215 then weightRowLLLRLRLRL j else weightRowLLLRLRLRR j
def weightRowLLLRLRL (j : ℕ) : ℕ := if j < 210 then weightRowLLLRLRLL j else weightRowLLLRLRLR j
def weightRowLLLRLRRLLL (j : ℕ) : ℕ := if j < 221 then 1366943669214677 else 1376189542922547
def weightRowLLLRLRRLLRR (j : ℕ) : ℕ := if j < 224 then 1394789781501637 else 1404144429085628
def weightRowLLLRLRRLLR (j : ℕ) : ℕ := if j < 223 then 1385471533324588 else weightRowLLLRLRRLLRR j
def weightRowLLLRLRRLL (j : ℕ) : ℕ := if j < 222 then weightRowLLLRLRRLLL j else weightRowLLLRLRRLLR j
def weightRowLLLRLRRLRL (j : ℕ) : ℕ := if j < 226 then 1413535618261743 else 1422963491770578
def weightRowLLLRLRRLRRR (j : ℕ) : ℕ := if j < 229 then 1441929865538863 else 1451468654076124
def weightRowLLLRLRRLRR (j : ℕ) : ℕ := if j < 228 then 1432428192910307 else weightRowLLLRLRRLRRR j
def weightRowLLLRLRRLR (j : ℕ) : ℕ := if j < 227 then weightRowLLLRLRRLRL j else weightRowLLLRLRRLRR j
def weightRowLLLRLRRL (j : ℕ) : ℕ := if j < 225 then weightRowLLLRLRRLL j else weightRowLLLRLRRLR j
def weightRowLLLRLRRRLL (j : ℕ) : ℕ := if j < 231 then 1461044703506109 else 1470658159379180
def weightRowLLLRLRRRLRR (j : ℕ) : ℕ := if j < 234 then 1489997875501029 else 1499724429702205
def weightRowLLLRLRRRLR (j : ℕ) : ℕ := if j < 233 then 1480309167814255 else weightRowLLLRLRRRLRR j
def weightRowLLLRLRRRL (j : ℕ) : ℕ := if j < 232 then weightRowLLLRLRRRLL j else weightRowLLLRLRRRLR j
def weightRowLLLRLRRRRL (j : ℕ) : ℕ := if j < 236 then 1509488978255729 else 1519291669577041
def weightRowLLLRLRRRRRR (j : ℕ) : ℕ := if j < 239 then 1539012077085784 else 1548930093011901
def weightRowLLLRLRRRRR (j : ℕ) : ℕ := if j < 238 then 1529132652661326 else weightRowLLLRLRRRRRR j
def weightRowLLLRLRRRR (j : ℕ) : ℕ := if j < 237 then weightRowLLLRLRRRRL j else weightRowLLLRLRRRRR j
def weightRowLLLRLRRR (j : ℕ) : ℕ := if j < 235 then weightRowLLLRLRRRL j else weightRowLLLRLRRRR j
def weightRowLLLRLRR (j : ℕ) : ℕ := if j < 230 then weightRowLLLRLRRL j else weightRowLLLRLRRR j
def weightRowLLLRLR (j : ℕ) : ℕ := if j < 220 then weightRowLLLRLRL j else weightRowLLLRLRR j
def weightRowLLLRL (j : ℕ) : ℕ := if j < 200 then weightRowLLLRLL j else weightRowLLLRLR j
def weightRowLLLRRLLLLL (j : ℕ) : ℕ := if j < 241 then 1558886851187728 else 1568882502950180
def weightRowLLLRRLLLLRR (j : ℕ) : ℕ := if j < 244 then 1588991095540718 else 1599104342007674
def weightRowLLLRRLLLLR (j : ℕ) : ℕ := if j < 243 then 1578917200227330 else weightRowLLLRRLLLLRR j
def weightRowLLLRRLLLL (j : ℕ) : ℕ := if j < 242 then weightRowLLLRRLLLLL j else weightRowLLLRRLLLLR j
def weightRowLLLRRLLLRL (j : ℕ) : ℕ := if j < 246 then 1609257093343641 else 1619449503864515
def weightRowLLLRRLLLRRR (j : ℕ) : ℕ := if j < 249 then 1639953922740895 else 1650266242751602
def weightRowLLLRRLLLRR (j : ℕ) : ℕ := if j < 248 then 1629681728488985 else weightRowLLLRRLLLRRR j
def weightRowLLLRRLLLR (j : ℕ) : ℕ := if j < 247 then weightRowLLLRRLLLRL j else weightRowLLLRRLLLRR j
def weightRowLLLRRLLL (j : ℕ) : ℕ := if j < 245 then weightRowLLLRRLLLL j else weightRowLLLRRLLLR j
def weightRowLLLRRLLRLL (j : ℕ) : ℕ := if j < 251 then 1660618845262351 else 1671011887626657
def weightRowLLLRRLLRLRR (j : ℕ) : ℕ := if j < 254 then 1691919924405717 else 1702435236610426
def weightRowLLLRRLLRLR (j : ℕ) : ℕ := if j < 253 then 1681445527812698 else weightRowLLLRRLLRLRR j
def weightRowLLLRRLLRL (j : ℕ) : ℕ := if j < 252 then weightRowLLLRRLLRLL j else weightRowLLLRRLLRLR j
def weightRowLLLRRLLRRL (j : ℕ) : ℕ := if j < 256 then 1712991624253436 else 719682997785676
def weightRowLLLRRLLRRRR (j : ℕ) : ℕ := if j < 259 then 725270607120454 else 728057740015566
def weightRowLLLRRLLRRR (j : ℕ) : ℕ := if j < 258 then 722479000706714 else weightRowLLLRRLLRRRR j
def weightRowLLLRRLLRR (j : ℕ) : ℕ := if j < 257 then weightRowLLLRRLLRRL j else weightRowLLLRRLLRRR j
def weightRowLLLRRLLR (j : ℕ) : ℕ := if j < 255 then weightRowLLLRRLLRL j else weightRowLLLRRLLRR j
def weightRowLLLRRLL (j : ℕ) : ℕ := if j < 250 then weightRowLLLRRLLL j else weightRowLLLRRLLR j
def weightRowLLLRRLRLLL (j : ℕ) : ℕ := if j < 261 then 730840321846151 else 733618274528745
def weightRowLLLRRLRLLRR (j : ℕ) : ℕ := if j < 264 then 739159977410152 else 741923568726977
def weightRowLLLRRLRLLR (j : ℕ) : ℕ := if j < 263 then 736391519439300 else weightRowLLLRRLRLLRR j
def weightRowLLLRRLRLL (j : ℕ) : ℕ := if j < 262 then weightRowLLLRRLRLLL j else weightRowLLLRRLRLLR j
def weightRowLLLRRLRLRL (j : ℕ) : ℕ := if j < 266 then 744682213125723 else 747435829789536
def weightRowLLLRRLRLRRR (j : ℕ) : ℕ := if j < 269 then 752927653862347 else 755665696845693
def weightRowLLLRRLRLRR (j : ℕ) : ℕ := if j < 268 then 750184337345664 else weightRowLLLRRLRLRRR j
def weightRowLLLRRLRLR (j : ℕ) : ℕ := if j < 267 then weightRowLLLRRLRLRL j else weightRowLLLRRLRLRR j
def weightRowLLLRRLRL (j : ℕ) : ℕ := if j < 265 then weightRowLLLRRLRLL j else weightRowLLLRRLRLR j
def weightRowLLLRRLRRLL (j : ℕ) : ℕ := if j < 271 then 758398383236534 else 761125629407271
def weightRowLLLRRLRRLRR (j : ℕ) : ℕ := if j < 274 then 766563463716819 else 769273881729629
def weightRowLLLRRLRRLR (j : ℕ) : ℕ := if j < 273 then 763847351158699 else weightRowLLLRRLRRLRR j
def weightRowLLLRRLRRL (j : ℕ) : ℕ := if j < 272 then weightRowLLLRRLRRLL j else weightRowLLLRRLRRLR j
def weightRowLLLRRLRRRL (j : ℕ) : ℕ := if j < 276 then 771978519263906 else 774677289801964
def weightRowLLLRRLRRRRR (j : ℕ) : ℕ := if j < 279 then 780056880876831 else 782737525426586
def weightRowLLLRRLRRRR (j : ℕ) : ℕ := if j < 278 then 777370106238403 else weightRowLLLRRLRRRRR j
def weightRowLLLRRLRRR (j : ℕ) : ℕ := if j < 277 then weightRowLLLRRLRRRL j else weightRowLLLRRLRRRR j
def weightRowLLLRRLRR (j : ℕ) : ℕ := if j < 275 then weightRowLLLRRLRRL j else weightRowLLLRRLRRR j
def weightRowLLLRRLR (j : ℕ) : ℕ := if j < 270 then weightRowLLLRRLRL j else weightRowLLLRRLRR j
def weightRowLLLRRL (j : ℕ) : ℕ := if j < 260 then weightRowLLLRRLL j else weightRowLLLRRLR j
def weightRowLLLRRRLLLL (j : ℕ) : ℕ := if j < 281 then 785411950999420 else 788080068106189
def weightRowLLLRRRLLLRR (j : ℕ) : ℕ := if j < 284 then 793397015940383 else 796045664654879
def weightRowLLLRRRLLLR (j : ℕ) : ℕ := if j < 283 then 790741786653504 else weightRowLLLRRRLLLRR j
def weightRowLLLRRRLLL (j : ℕ) : ℕ := if j < 282 then weightRowLLLRRRLLLL j else weightRowLLLRRRLLLR j
def weightRowLLLRRRLLRL (j : ℕ) : ℕ := if j < 286 then 798687640870685 else 801322852043733
def weightRowLLLRRRLLRRR (j : ℕ) : ℕ := if j < 289 then 806572605975913 else 809186960527195
def weightRowLLLRRRLLRR (j : ℕ) : ℕ := if j < 288 then 803951205008770 else weightRowLLLRRRLLRRR j
def weightRowLLLRRRLLR (j : ℕ) : ℕ := if j < 287 then weightRowLLLRRRLLRL j else weightRowLLLRRRLLRR j
def weightRowLLLRRRLL (j : ℕ) : ℕ := if j < 285 then weightRowLLLRRRLLL j else weightRowLLLRRRLLR j
def weightRowLLLRRRLRLL (j : ℕ) : ℕ := if j < 291 then 811794173613089 else 814394149549011
def weightRowLLLRRRLRLRR (j : ℕ) : ℕ := if j < 294 then 819572004036250 else 822149688011441
def weightRowLLLRRRLRLR (j : ℕ) : ℕ := if j < 293 then 816986792011812 else weightRowLLLRRRLRLRR j
def weightRowLLLRRRLRL (j : ℕ) : ℕ := if j < 292 then weightRowLLLRRRLRLL j else weightRowLLLRRRLRLR j
def weightRowLLLRRRLRRL (j : ℕ) : ℕ := if j < 296 then 824719745677293 else 827282078120931
def weightRowLLLRRRLRRRR (j : ℕ) : ℕ := if j < 299 then 832383168404488 else 834921725122215
def weightRowLLLRRRLRRR (j : ℕ) : ℕ := if j < 298 then 829836585773087 else weightRowLLLRRRLRRRR j
def weightRowLLLRRRLRR (j : ℕ) : ℕ := if j < 297 then weightRowLLLRRRLRRL j else weightRowLLLRRRLRRR j
def weightRowLLLRRRLR (j : ℕ) : ℕ := if j < 295 then weightRowLLLRRRLRL j else weightRowLLLRRRLRR j
def weightRowLLLRRRL (j : ℕ) : ℕ := if j < 290 then weightRowLLLRRRLL j else weightRowLLLRRRLR j
def weightRowLLLRRRRLLL (j : ℕ) : ℕ := if j < 301 then 837452154366052 else 839974353904805
def weightRowLLLRRRRLLRR (j : ℕ) : ℕ := if j < 304 then 844993651565262 else 847490541836390
def weightRowLLLRRRRLLR (j : ℕ) : ℕ := if j < 303 then 842488220832620 else weightRowLLLRRRRLLRR j
def weightRowLLLRRRRLL (j : ℕ) : ℕ := if j < 302 then weightRowLLLRRRRLLL j else weightRowLLLRRRRLLR j
def weightRowLLLRRRRLRL (j : ℕ) : ℕ := if j < 306 then 849978786693811 else 852458280495707
def weightRowLLLRRRRLRRR (j : ℕ) : ℕ := if j < 309 then 857390588894815 else 859843188726112
def weightRowLLLRRRRLRR (j : ℕ) : ℕ := if j < 308 then 854928916906855 else weightRowLLLRRRRLRRR j
def weightRowLLLRRRRLR (j : ℕ) : ℕ := if j < 307 then weightRowLLLRRRRLRL j else weightRowLLLRRRRLRR j
def weightRowLLLRRRRL (j : ℕ) : ℕ := if j < 305 then weightRowLLLRRRRLL j else weightRowLLLRRRRLR j
def weightRowLLLRRRRRLL (j : ℕ) : ℕ := if j < 311 then 862286607962389 else 864720737456543
def weightRowLLLRRRRRLRR (j : ℕ) : ℕ := if j < 314 then 869560687063038 else 871966285302413
def weightRowLLLRRRRRLR (j : ℕ) : ℕ := if j < 313 then 867145467348846 else weightRowLLLRRRRRLRR j
def weightRowLLLRRRRRL (j : ℕ) : ℕ := if j < 312 then weightRowLLLRRRRRLL j else weightRowLLLRRRRRLR j
def weightRowLLLRRRRRRL (j : ℕ) : ℕ := if j < 316 then 874362150045869 else 876748168543954
def weightRowLLLRRRRRRRR (j : ℕ) : ℕ := if j < 319 then 881490212140528 else 883846008062419
def weightRowLLLRRRRRRR (j : ℕ) : ℕ := if j < 318 then 879124227314881 else weightRowLLLRRRRRRRR j
def weightRowLLLRRRRRR (j : ℕ) : ℕ := if j < 317 then weightRowLLLRRRRRRL j else weightRowLLLRRRRRRR j
def weightRowLLLRRRRR (j : ℕ) : ℕ := if j < 315 then weightRowLLLRRRRRL j else weightRowLLLRRRRRR j
def weightRowLLLRRRR (j : ℕ) : ℕ := if j < 310 then weightRowLLLRRRRL j else weightRowLLLRRRRR j
def weightRowLLLRRR (j : ℕ) : ℕ := if j < 300 then weightRowLLLRRRL j else weightRowLLLRRRR j
def weightRowLLLRR (j : ℕ) : ℕ := if j < 280 then weightRowLLLRRL j else weightRowLLLRRR j
def weightRowLLLR (j : ℕ) : ℕ := if j < 240 then weightRowLLLRL j else weightRowLLLRR j
def weightRowLLL (j : ℕ) : ℕ := if j < 160 then weightRowLLLL j else weightRowLLLR j
def weightRowLLRLLLLLLL (j : ℕ) : ℕ := if j < 321 then 886191499377680 else 888526569634978
def weightRowLLRLLLLLLRR (j : ℕ) : ℕ := if j < 324 then 893164977403552 else 895468078233033
def weightRowLLRLLLLLLR (j : ℕ) : ℕ := if j < 323 then 890851101630440 else weightRowLLRLLLLLLRR j
def weightRowLLRLLLLLL (j : ℕ) : ℕ := if j < 322 then weightRowLLRLLLLLLL j else weightRowLLRLLLLLLR j
def weightRowLLRLLLLLRL (j : ℕ) : ℕ := if j < 326 then 897760284632694 else 900041476347272
def weightRowLLRLLLLLRRR (j : ℕ) : ℕ := if j < 329 then 904570330829628 else 906817749203744
def weightRowLLRLLLLLRR (j : ℕ) : ℕ := if j < 328 then 902311532348245 else weightRowLLRLLLLLRRR j
def weightRowLLRLLLLLR (j : ℕ) : ℕ := if j < 327 then weightRowLLRLLLLLRL j else weightRowLLRLLLLLRR j
def weightRowLLRLLLLL (j : ℕ) : ℕ := if j < 325 then weightRowLLRLLLLLL j else weightRowLLRLLLLLR j
def weightRowLLRLLLLRLL (j : ℕ) : ℕ := if j < 331 then 909053664096975 else 911277951345494
def weightRowLLRLLLLRLRR (j : ℕ) : ℕ := if j < 334 then 915691142276268 else 917879793641095
def weightRowLLRLLLLRLR (j : ℕ) : ℕ := if j < 333 then 913490485990972 else weightRowLLRLLLLRLRR j
def weightRowLLRLLLLRL (j : ℕ) : ℕ := if j < 332 then weightRowLLRLLLLRLL j else weightRowLLRLLLLRLR j
def weightRowLLRLLLLRRL (j : ℕ) : ℕ := if j < 336 then 920056312717660 else 922220571326293
def weightRowLLRLLLLRRRR (j : ℕ) : ℕ := if j < 339 then 926511790335254 else 928638490277134
def weightRowLLRLLLLRRR (j : ℕ) : ℕ := if j < 338 then 924372440471041 else weightRowLLRLLLLRRRR j
def weightRowLLRLLLLRR (j : ℕ) : ℕ := if j < 337 then weightRowLLRLLLLRRL j else weightRowLLRLLLLRRR j
def weightRowLLRLLLLR (j : ℕ) : ℕ := if j < 335 then weightRowLLRLLLLRL j else weightRowLLRLLLLRR j
def weightRowLLRLLLL (j : ℕ) : ℕ := if j < 330 then weightRowLLRLLLLL j else weightRowLLRLLLLR j
def weightRowLLRLLLRLLL (j : ℕ) : ℕ := if j < 341 then 930752408825274 else 932853413674172
def weightRowLLRLLLRLLRR (j : ℕ) : ℕ := if j < 344 then 937016148854644 else 939077610364015
def weightRowLLRLLLRLLR (j : ℕ) : ℕ := if j < 343 then 934941371679712 else weightRowLLRLLLRLLRR j
def weightRowLLRLLLRLL (j : ℕ) : ℕ := if j < 342 then weightRowLLRLLLRLLL j else weightRowLLRLLLRLLR j
def weightRowLLRLLLRLRL (j : ℕ) : ℕ := if j < 346 then 941125620520603 else 943160042780306
def weightRowLLRLLLRLRRR (j : ℕ) : ℕ := if j < 349 then 947187573120517 else 949180403786717
def weightRowLLRLLLRLRR (j : ℕ) : ℕ := if j < 348 then 945180739737526 else weightRowLLRLLLRLRRR j
def weightRowLLRLLLRLR (j : ℕ) : ℕ := if j < 347 then weightRowLLRLLLRLRL j else weightRowLLRLLLRLRR j
def weightRowLLRLLLRL (j : ℕ) : ℕ := if j < 345 then weightRowLLRLLLRLL j else weightRowLLRLLLRLR j
def weightRowLLRLLLRRLL (j : ℕ) : ℕ := if j < 351 then 951159091718053 else 953123496016226
def weightRowLLRLLLRRLRR (j : ℕ) : ℕ := if j < 354 then 957008885690290 else 958929584825670
def weightRowLLRLLLRRLR (j : ℕ) : ℕ := if j < 353 then 955073474897970 else weightRowLLRLLLRRLRR j
def weightRowLLRLLLRRL (j : ℕ) : ℕ := if j < 352 then weightRowLLRLLLRRLL j else weightRowLLRLLLRRLR j
def weightRowLLRLLLRRRL (j : ℕ) : ℕ := if j < 356 then 960835427837264 else 962726269354064
def weightRowLLRLLLRRRRR (j : ℕ) : ℕ := if j < 359 then 966462361869231 else 968307317560897
def weightRowLLRLLLRRRR (j : ℕ) : ℕ := if j < 358 then 964601963096033 else weightRowLLRLLLRRRRR j
def weightRowLLRLLLRRR (j : ℕ) : ℕ := if j < 357 then weightRowLLRLLLRRRL j else weightRowLLRLLLRRRR j
def weightRowLLRLLLRR (j : ℕ) : ℕ := if j < 355 then weightRowLLRLLLRRL j else weightRowLLRLLLRRR j
def weightRowLLRLLLR (j : ℕ) : ℕ := if j < 350 then weightRowLLRLLLRL j else weightRowLLRLLLRR j
def weightRowLLRLLL (j : ℕ) : ℕ := if j < 340 then weightRowLLRLLLL j else weightRowLLRLLLR j
def weightRowLLRLLRLLLL (j : ℕ) : ℕ := if j < 361 then 970136681134525 else 971950302624904
def weightRowLLRLLRLLLRR (j : ℕ) : ℕ := if j < 364 then 975529714821626 else 977295200909064
def weightRowLLRLLRLLLR (j : ℕ) : ℕ := if j < 363 then 973748031133134 else weightRowLLRLLRLLLRR j
def weightRowLLRLLRLLL (j : ℕ) : ℕ := if j < 362 then weightRowLLRLLRLLLL j else weightRowLLRLLRLLLR j
def weightRowLLRLLRLLRL (j : ℕ) : ℕ := if j < 366 then 979044335665355 else 980776964406545
def weightRowLLRLLRLLRRR (j : ℕ) : ℕ := if j < 369 then 984192080307836 else 985874253284643
def weightRowLLRLLRLLRR (j : ℕ) : ℕ := if j < 368 then 982492931489712 else weightRowLLRLLRLLRRR j
def weightRowLLRLLRLLR (j : ℕ) : ℕ := if j < 367 then weightRowLLRLLRLLRL j else weightRowLLRLLRLLRR j
def weightRowLLRLLRLL (j : ℕ) : ℕ := if j < 365 then weightRowLLRLLRLLL j else weightRowLLRLLRLLR j
def weightRowLLRLLRLRLL (j : ℕ) : ℕ := if j < 371 then 987539291869418 else 989187036531801
def weightRowLLRLLRLRLRR (j : ℕ) : ℕ := if j < 374 then 992430001038285 else 994024896876194
def weightRowLLRLLRLRLR (j : ℕ) : ℕ := if j < 373 then 990817326756551 else weightRowLLRLLRLRLRR j
def weightRowLLRLLRLRL (j : ℕ) : ℕ := if j < 372 then weightRowLLRLLRLRLL j else weightRowLLRLLRLRLR j
def weightRowLLRLLRLRRL (j : ℕ) : ℕ := if j < 376 then 995601850768730 else 997160698208264
def weightRowLLRLLRLRRRR (j : ℕ) : ℕ := if j < 379 then 1000223410635210 else 1001726941528555
def weightRowLLRLLRLRRR (j : ℕ) : ℕ := if j < 378 then 998701273675726 else weightRowLLRLLRLRRRR j
def weightRowLLRLLRLRR (j : ℕ) : ℕ := if j < 377 then weightRowLLRLLRLRRL j else weightRowLLRLLRLRRR j
def weightRowLLRLLRLR (j : ℕ) : ℕ := if j < 375 then weightRowLLRLLRLRL j else weightRowLLRLLRLRR j
def weightRowLLRLLRL (j : ℕ) : ℕ := if j < 370 then weightRowLLRLLRLL j else weightRowLLRLLRLR j
def weightRowLLRLLRRLLL (j : ℕ) : ℕ := if j < 381 then 1003211697769904 else 1004677509740227
def weightRowLLRLLRRLLRR (j : ℕ) : ℕ := if j < 384 then 1007551617192800 else 1008959568221507
def weightRowLLRLLRRLLR (j : ℕ) : ℕ := if j < 383 then 1006124206781825 else weightRowLLRLLRRLLRR j
def weightRowLLRLLRRLL (j : ℕ) : ℕ := if j < 382 then weightRowLLRLLRRLLL j else weightRowLLRLLRRLLR j
def weightRowLLRLLRRLRL (j : ℕ) : ℕ := if j < 386 then 1010347886060967 else 1011716395843260
def weightRowLLRLLRRLRRR (j : ℕ) : ℕ := if j < 389 then 1014393286426127 else 1015701312135292
def weightRowLLRLLRRLRR (j : ℕ) : ℕ := if j < 388 then 1013064921633893 else weightRowLLRLLRRLRRR j
def weightRowLLRLLRRLR (j : ℕ) : ℕ := if j < 387 then weightRowLLRLLRRLRL j else weightRowLLRLLRRLRR j
def weightRowLLRLLRRL (j : ℕ) : ℕ := if j < 385 then weightRowLLRLLRRLL j else weightRowLLRLLRRLR j
def weightRowLLRLLRRRLL (j : ℕ) : ℕ := if j < 391 then 1016988819593063 else 1018255628541713
def weightRowLLRLLRRRLRR (j : ℕ) : ℕ := if j < 394 then 1020726424399037 else 1021930045293105
def weightRowLLRLLRRRLR (j : ℕ) : ℕ := if j < 393 then 1019501557628335 else weightRowLLRLLRRRLRR j
def weightRowLLRLLRRRL (j : ℕ) : ℕ := if j < 392 then weightRowLLRLLRRRLL j else weightRowLLRLLRRRLR j
def weightRowLLRLLRRRRL (j : ℕ) : ℕ := if j < 396 then 1023112235637145 else 1024272809639187
def weightRowLLRLLRRRRRR (j : ℕ) : ℕ := if j < 399 then 1026528359820974 else 1027622958770473
def weightRowLLRLLRRRRR (j : ℕ) : ℕ := if j < 398 then 1025411580382767 else weightRowLLRLLRRRRRR j
def weightRowLLRLLRRRR (j : ℕ) : ℕ := if j < 397 then weightRowLLRLLRRRRL j else weightRowLLRLLRRRRR j
def weightRowLLRLLRRR (j : ℕ) : ℕ := if j < 395 then weightRowLLRLLRRRL j else weightRowLLRLLRRRR j
def weightRowLLRLLRR (j : ℕ) : ℕ := if j < 390 then weightRowLLRLLRRL j else weightRowLLRLLRRR j
def weightRowLLRLLR (j : ℕ) : ℕ := if j < 380 then weightRowLLRLLRL j else weightRowLLRLLRR j
def weightRowLLRLL (j : ℕ) : ℕ := if j < 360 then weightRowLLRLLL j else weightRowLLRLLR j
def weightRowLLRLRLLLLL (j : ℕ) : ℕ := if j < 401 then 1028695186905492 else 1029744852751791
def weightRowLLRLRLLLLRR (j : ℕ) : ℕ := if j < 404 then 1031775725902450 else 1032756544461198
def weightRowLLRLRLLLLR (j : ℕ) : ℕ := if j < 403 then 1030771763680584 else weightRowLLRLRLLLLRR j
def weightRowLLRLRLLLL (j : ℕ) : ℕ := if j < 402 then weightRowLLRLRLLLLL j else weightRowLLRLRLLLLR j
def weightRowLLRLRLLLRL (j : ℕ) : ℕ := if j < 406 then 1033714023227712 else 1034647964893762
def weightRowLLRLRLLLRRR (j : ℕ) : ℕ := if j < 409 then 1036444441758632 else 1037306576389294
def weightRowLLRLRLLLRR (j : ℕ) : ℕ := if j < 408 then 1035558170965785 else weightRowLLRLRLLLRRR j
def weightRowLLRLRLLLR (j : ℕ) : ℕ := if j < 407 then weightRowLLRLRLLLRL j else weightRowLLRLRLLLRR j
def weightRowLLRLRLLL (j : ℕ) : ℕ := if j < 405 then weightRowLLRLRLLLL j else weightRowLLRLRLLLR j
def weightRowLLRLRLLRLL (j : ℕ) : ℕ := if j < 411 then 1038144372770583 else 1038957627604796
def weightRowLLRLRLLRLRR (j : ℕ) : ℕ := if j < 414 then 1040509693350319 else 1041248091556116
def weightRowLLRLRLLRLR (j : ℕ) : ℕ := if j < 413 then 1039746136377339 else weightRowLLRLRLLRLRR j
def weightRowLLRLRLLRL (j : ℕ) : ℕ := if j < 412 then weightRowLLRLRLLRLL j else weightRowLLRLRLLRLR j
def weightRowLLRLRLLRRL (j : ℕ) : ℕ := if j < 416 then 1041961122790904 else 1042648577608161
def weightRowLLRLRLLRRRR (j : ℕ) : ℕ := if j < 419 then 1043945913951264 else 1044555370311617
def weightRowLLRLRLLRRR (j : ℕ) : ℕ := if j < 418 then 1043310245312131 else weightRowLLRLRLLRRRR j
def weightRowLLRLRLLRR (j : ℕ) : ℕ := if j < 417 then weightRowLLRLRLLRRL j else weightRowLLRLRLLRRR j
def weightRowLLRLRLLR (j : ℕ) : ℕ := if j < 415 then weightRowLLRLRLLRL j else weightRowLLRLRLLRR j
def weightRowLLRLRLL (j : ℕ) : ℕ := if j < 410 then weightRowLLRLRLLL j else weightRowLLRLRLLR j
def weightRowLLRLRLRLLL (j : ℕ) : ℕ := if j < 421 then 1045138399910230 else 1045694786988460
def weightRowLLRLRLRLLRR (j : ℕ) : ℕ := if j < 424 then 1046726764130605 else 1047201916238428
def weightRowLLRLRLRLLR (j : ℕ) : ℕ := if j < 423 then 1046224314505290 else weightRowLLRLRLRLLRR j
def weightRowLLRLRLRLL (j : ℕ) : ℕ := if j < 422 then weightRowLLRLRLRLLL j else weightRowLLRLRLRLLR j
def weightRowLLRLRLRLRL (j : ℕ) : ℕ := if j < 426 then 1047649549900131 else 1048069442877607
def weightRowLLRLRLRLRRR (j : ℕ) : ℕ := if j < 429 then 1048825111238880 else 1049160435537174
def weightRowLLRLRLRLRR (j : ℕ) : ℕ := if j < 428 then 1048461371616415 else weightRowLLRLRLRLRRR j
def weightRowLLRLRLRLR (j : ℕ) : ℕ := if j < 427 then weightRowLLRLRLRLRL j else weightRowLLRLRLRLRR j
def weightRowLLRLRLRL (j : ℕ) : ℕ := if j < 425 then weightRowLLRLRLRLL j else weightRowLLRLRLRLR j
def weightRowLLRLRLRRLL (j : ℕ) : ℕ := if j < 431 then 1049467116966349 else 1049744926637349
def weightRowLLRLRLRRLRR (j : ℕ) : ℕ := if j < 434 then 1050213008385826 else 1050402815901200
def weightRowLLRLRLRRLR (j : ℕ) : ℕ := if j < 433 then 1049993634309975 else weightRowLLRLRLRRLRR j
def weightRowLLRLRLRRL (j : ℕ) : ℕ := if j < 432 then weightRowLLRLRLRRLL j else weightRowLLRLRLRRLR j
def weightRowLLRLRLRRRL (j : ℕ) : ℕ := if j < 436 then 1050562822519959 else 1050692792526366
def weightRowLLRLRLRRRRR (j : ℕ) : ℕ := if j < 439 then 1050861672897918 else 1050900104868584
def weightRowLLRLRLRRRR (j : ℕ) : ℕ := if j < 438 then 1050792488817880 else weightRowLLRLRLRRRRR j
def weightRowLLRLRLRRR (j : ℕ) : ℕ := if j < 437 then weightRowLLRLRLRRRL j else weightRowLLRLRLRRRR j
def weightRowLLRLRLRR (j : ℕ) : ℕ := if j < 435 then weightRowLLRLRLRRL j else weightRowLLRLRLRRR j
def weightRowLLRLRLR (j : ℕ) : ℕ := if j < 430 then weightRowLLRLRLRL j else weightRowLLRLRLRR j
def weightRowLLRLRL (j : ℕ) : ℕ := if j < 420 then weightRowLLRLRLL j else weightRowLLRLRLR j
def weightRowLLRLRRLLLL (j : ℕ) : ℕ := if j < 441 then 1050907543423357 else 1050883745839751
def weightRowLLRLRRLLLRR (j : ℕ) : ℕ := if j < 444 then 1050741464243300 else 1050622487639043
def weightRowLLRLRRLLLR (j : ℕ) : ℕ := if j < 443 then 1050828467971932 else weightRowLLRLRRLLLRR j
def weightRowLLRLRRLLL (j : ℕ) : ℕ := if j < 442 then weightRowLLRLRRLLLL j else weightRowLLRLRRLLLR j
def weightRowLLRLRRLLRL (j : ℕ) : ℕ := if j < 446 then 1050471289698640 else 1050287620508342
def weightRowLLRLRRLLRRR (j : ℕ) : ℕ := if j < 449 then 1049821861411500 else 1049539264343060
def weightRowLLRLRRLLRR (j : ℕ) : ℕ := if j < 448 then 1050071228693607 else weightRowLLRLRRLLRRR j
def weightRowLLRLRRLLR (j : ℕ) : ℕ := if j < 447 then weightRowLLRLRRLLRL j else weightRowLLRLRRLLRR j
def weightRowLLRLRRLL (j : ℕ) : ℕ := if j < 445 then weightRowLLRLRRLLL j else weightRowLLRLRRLLR j
def weightRowLLRLRRLRLL (j : ℕ) : ℕ := if j < 451 then 1049223181685624 else 1048873356145116
def weightRowLLRLRRLRLRR (j : ℕ) : ℕ := if j < 454 then 1048071439735000 else 1047618826750257
def weightRowLLRLRRLRLR (j : ℕ) : ℕ := if j < 453 then 1048489528928303 else weightRowLLRLRRLRLRR j
def weightRowLLRLRRLRL (j : ℕ) : ℕ := if j < 452 then weightRowLLRLRRLRLL j else weightRowLLRLRRLRLR j
def weightRowLLRLRRLRRL (j : ℕ) : ℕ := if j < 456 then 1047131426636486 else 1046608974525568
def weightRowLLRLRRLRRRR (j : ℕ) : ℕ := if j < 459 then 1045457847139474 else 1044828634403745
def weightRowLLRLRRLRRR (j : ℕ) : ℕ := if j < 458 then 1046051204010912 else weightRowLLRLRRLRRRR j
def weightRowLLRLRRLRR (j : ℕ) : ℕ := if j < 457 then weightRowLLRLRRLRRL j else weightRowLLRLRRLRRR j
def weightRowLLRLRRLR (j : ℕ) : ℕ := if j < 455 then weightRowLLRLRRLRL j else weightRowLLRLRRLRR j
def weightRowLLRLRRL (j : ℕ) : ℕ := if j < 450 then weightRowLLRLRRLL j else weightRowLLRLRRLR j
def weightRowLLRLRRRLLL (j : ℕ) : ℕ := if j < 461 then 1044163294733693 else 1043461555488666
def weightRowLLRLRRRLLRR (j : ℕ) : ℕ := if j < 464 then 1041947779809160 else 1041135190166886
def weightRowLLRLRRRLLR (j : ℕ) : ℕ := if j < 463 then 1042723142449265 else weightRowLLRLRRRLLRR j
def weightRowLLRLRRRLL (j : ℕ) : ℕ := if j < 462 then weightRowLLRLRRRLLL j else weightRowLLRLRRRLLR j
def weightRowLLRLRRRLRL (j : ℕ) : ℕ := if j < 466 then 1040285094517583 else 1039397212244705
def weightRowLLRLRRRLRRR (j : ℕ) : ℕ := if j < 469 then 1037506957253564 else 1036504015168566
def weightRowLLRLRRRLRR (j : ℕ) : ℕ := if j < 468 then 1038471261111686 else weightRowLLRLRRRLRRR j
def weightRowLLRLRRRLR (j : ℕ) : ℕ := if j < 467 then weightRowLLRLRRRLRL j else weightRowLLRLRRRLRR j
def weightRowLLRLRRRL (j : ℕ) : ℕ := if j < 465 then weightRowLLRLRRRLL j else weightRowLLRLRRRLR j
def weightRowLLRLRRRRLL (j : ℕ) : ℕ := if j < 471 then 1035462147709656 else 1034381066076030
def weightRowLLRLRRRRLRR (j : ℕ) : ℕ := if j < 474 then 1032100096761335 else 1030899623132788
def weightRowLLRLRRRRLR (j : ℕ) : ℕ := if j < 473 then 1033260479804585 else weightRowLLRLRRRRLRR j
def weightRowLLRLRRRRL (j : ℕ) : ℕ := if j < 472 then weightRowLLRLRRRRLL j else weightRowLLRLRRRRLR j
def weightRowLLRLRRRRRL (j : ℕ) : ℕ := if j < 476 then 1029658763417289 else 1028377220416305
def weightRowLLRLRRRRRRR (j : ℕ) : ℕ := if j < 479 then 1025690887226871 else 1024285494078051
def weightRowLLRLRRRRRR (j : ℕ) : ℕ := if j < 478 then 1027054695225686 else weightRowLLRLRRRRRRR j
def weightRowLLRLRRRRR (j : ℕ) : ℕ := if j < 477 then weightRowLLRLRRRRRL j else weightRowLLRLRRRRRR j
def weightRowLLRLRRRR (j : ℕ) : ℕ := if j < 475 then weightRowLLRLRRRRL j else weightRowLLRLRRRRR j
def weightRowLLRLRRR (j : ℕ) : ℕ := if j < 470 then weightRowLLRLRRRL j else weightRowLLRLRRRR j
def weightRowLLRLRR (j : ℕ) : ℕ := if j < 460 then weightRowLLRLRRL j else weightRowLLRLRRR j
def weightRowLLRLR (j : ℕ) : ℕ := if j < 440 then weightRowLLRLRL j else weightRowLLRLRR j
def weightRowLLRL (j : ℕ) : ℕ := if j < 400 then weightRowLLRLL j else weightRowLLRLR j
def weightRowLLRRLLLLLL (j : ℕ) : ℕ := if j < 481 then 1022838211705303 else 1021348734293661
def weightRowLLRRLLLLLRR (j : ℕ) : ℕ := if j < 484 then 1018241962334831 else 1016624047371645
def weightRowLLRRLLLLLR (j : ℕ) : ℕ := if j < 483 then 1019816754278161 else weightRowLLRRLLLLLRR j
def weightRowLLRRLLLLL (j : ℕ) : ℕ := if j < 482 then weightRowLLRRLLLLLL j else weightRowLLRRLLLLLR j
def weightRowLLRRLLLLRL (j : ℕ) : ℕ := if j < 486 then 1014962696519430 else 1013257595122724
def weightRowLLRRLLLLRRR (j : ℕ) : ℕ := if j < 489 then 1009714873087443 else 1007876614123666
def weightRowLLRRLLLLRR (j : ℕ) : ℕ := if j < 488 then 1011508426730601 else weightRowLLRRLLLLRRR j
def weightRowLLRRLLLLR (j : ℕ) : ℕ := if j < 487 then weightRowLLRRLLLLRL j else weightRowLLRRLLLLRR j
def weightRowLLRRLLLL (j : ℕ) : ℕ := if j < 485 then weightRowLLRRLLLLL j else weightRowLLRRLLLLR j
def weightRowLLRRLLLRLL (j : ℕ) : ℕ := if j < 491 then 1005993327946411 else 1004064690830177
def weightRowLLRRLLLRLRR (j : ℕ) : ℕ := if j < 494 then 1000070059659102 else 998003408905188
def weightRowLLRRLLLRLR (j : ℕ) : ℕ := if j < 493 then 1002090377207421 else weightRowLLRRLLLRLRR j
def weightRowLLRRLLLRL (j : ℕ) : ℕ := if j < 492 then weightRowLLRRLLLRLL j else weightRowLLRRLLLRLR j
def weightRowLLRRLLLRRL (j : ℕ) : ℕ := if j < 496 then 995890093795107 else 993729781298166
def weightRowLLRRLLLRRRR (j : ℕ) : ℕ := if j < 499 then 989266822562441 else 986963500774687
def weightRowLLRRLLLRRR (j : ℕ) : ℕ := if j < 498 then 991522136493910 else weightRowLLRRLLLRRRR j
def weightRowLLRRLLLRR (j : ℕ) : ℕ := if j < 497 then weightRowLLRRLLLRRL j else weightRowLLRRLLLRRR j
def weightRowLLRRLLLR (j : ℕ) : ℕ := if j < 495 then weightRowLLRRLLLRL j else weightRowLLRRLLLRR j
def weightRowLLRRLLL (j : ℕ) : ℕ := if j < 490 then weightRowLLRRLLLL j else weightRowLLRRLLLR j
def weightRowLLRRLLRLLL (j : ℕ) : ℕ := if j < 501 then 984611830482632 else 982211469109488
def weightRowLLRRLLRLLRR (j : ℕ) : ℕ := if j < 504 then 977263293109648 else 974714783596448
def weightRowLLRRLLRLLR (j : ℕ) : ℕ := if j < 503 then 979762072139823 else weightRowLLRRLLRLLRR j
def weightRowLLRRLLRLL (j : ℕ) : ℕ := if j < 502 then weightRowLLRRLLRLLL j else weightRowLLRRLLRLLR j
def weightRowLLRRLLRLRL (j : ℕ) : ℕ := if j < 506 then 972116193209165 else 969467169578140
def weightRowLLRRLLRLRRR (j : ℕ) : ℕ := if j < 509 then 964016403152492 else 961213945634288
def weightRowLLRRLLRLRR (j : ℕ) : ℕ := if j < 508 then 966767358344998 else weightRowLLRRLLRLRRR j
def weightRowLLRRLLRLR (j : ℕ) : ℕ := if j < 507 then weightRowLLRRLLRLRL j else weightRowLLRRLLRLRR j
def weightRowLLRRLLRL (j : ℕ) : ℕ := if j < 505 then weightRowLLRRLLRLL j else weightRowLLRRLLRLR j
def weightRowLLRRLLRRLL (j : ℕ) : ℕ := if j < 511 then 958359625404712 else 955453080048440
def weightRowLLRRLLRRLRR (j : ℕ) : ℕ := if j < 514 then 953403362873125 else 954305411162838
def weightRowLLRRLLRRLR (j : ℕ) : ℕ := if j < 513 then 952493945110139 else weightRowLLRRLLRRLRR j
def weightRowLLRRLLRRL (j : ℕ) : ℕ := if j < 512 then weightRowLLRRLLRRLL j else weightRowLLRRLLRRLR j
def weightRowLLRRLLRRRL (j : ℕ) : ℕ := if j < 516 then 955200078366128 else 956087353125310
def weightRowLLRRLLRRRRR (j : ℕ) : ℕ := if j < 519 then 957839681176449 else 958704713058235
def weightRowLLRRLLRRRR (j : ℕ) : ℕ := if j < 518 then 956967224341244 else weightRowLLRRLLRRRRR j
def weightRowLLRRLLRRR (j : ℕ) : ℕ := if j < 517 then weightRowLLRRLLRRRL j else weightRowLLRRLLRRRR j
def weightRowLLRRLLRR (j : ℕ) : ℕ := if j < 515 then weightRowLLRRLLRRL j else weightRowLLRRLLRRR j
def weightRowLLRRLLR (j : ℕ) : ℕ := if j < 510 then weightRowLLRRLLRL j else weightRowLLRRLLRR j
def weightRowLLRRLL (j : ℕ) : ℕ := if j < 500 then weightRowLLRRLLL j else weightRowLLRRLLR j
def weightRowLLRRLRLLLL (j : ℕ) : ℕ := if j < 521 then 959562309681860 else 960412461013715
def weightRowLLRRLRLLLRR (j : ℕ) : ℕ := if j < 524 then 962090389042594 else 962918147057035
def weightRowLLRRLRLLLR (j : ℕ) : ℕ := if j < 523 then 961255157294528 else weightRowLLRRLRLLLRR j
def weightRowLLRRLRLLL (j : ℕ) : ℕ := if j < 522 then weightRowLLRRLRLLLL j else weightRowLLRRLRLLLR j
def weightRowLLRRLRLLRL (j : ℕ) : ℕ := if j < 526 then 963738422421077 else 964551206505356
def weightRowLLRRLRLLRRR (j : ℕ) : ℕ := if j < 529 then 966154267774234 else 966944529167264
def weightRowLLRRLRLLRR (j : ℕ) : ℕ := if j < 528 then 965356490971250 else weightRowLLRRLRLLRRR j
def weightRowLLRRLRLLR (j : ℕ) : ℕ := if j < 527 then weightRowLLRRLRLLRL j else weightRowLLRRLRLLRR j
def weightRowLLRRLRLL (j : ℕ) : ℕ := if j < 525 then weightRowLLRRLRLLL j else weightRowLLRRLRLLR j
def weightRowLLRRLRLRLL (j : ℕ) : ℕ := if j < 531 then 967727267704179 else 968502476243142
def weightRowLLRRLRLRLRR (j : ℕ) : ℕ := if j < 534 then 970030276302234 else 970782855091545
def weightRowLLRRLRLRLR (j : ℕ) : ℕ := if j < 533 then 969270147950093 else weightRowLLRRLRLRLRR j
def weightRowLLRRLRLRL (j : ℕ) : ℕ := if j < 532 then weightRowLLRRLRLRLL j else weightRowLLRRLRLRLR j
def weightRowLLRRLRLRRL (j : ℕ) : ℕ := if j < 536 then 971527878428322 else 972265340744735
def weightRowLLRRLRLRRRR (j : ℕ) : ℕ := if j < 539 then 973717561676131 else 974432310797314
def weightRowLLRRLRLRRR (j : ℕ) : ℕ := if j < 538 then 972995236798427 else weightRowLLRRLRLRRRR j
def weightRowLLRRLRLRR (j : ℕ) : ℕ := if j < 537 then weightRowLLRRLRLRRL j else weightRowLLRRLRLRRR j
def weightRowLLRRLRLR (j : ℕ) : ℕ := if j < 535 then weightRowLLRRLRLRL j else weightRowLLRRLRLRR j
def weightRowLLRRLRL (j : ℕ) : ℕ := if j < 530 then weightRowLLRRLRLL j else weightRowLLRRLRLR j
def weightRowLLRRLRRLLL (j : ℕ) : ℕ := if j < 541 then 975139479917848 else 975839065133719
def weightRowLLRRLRRLLRR (j : ℕ) : ℕ := if j < 544 then 977215469958345 else 977892283493304
def weightRowLLRRLRRLLR (j : ℕ) : ℕ := if j < 543 then 976531062884747 else weightRowLLRRLRRLLRR j
def weightRowLLRRLRRLL (j : ℕ) : ℕ := if j < 542 then weightRowLLRRLRRLLL j else weightRowLLRRLRRLLR j
def weightRowLLRRLRRLRL (j : ℕ) : ℕ := if j < 546 then 978561500983606 else 979223120282264
def weightRowLLRRLRRLRRR (j : ℕ) : ℕ := if j < 549 then 980523557535097 else 981162373025423
def weightRowLLRRLRRLRR (j : ℕ) : ℕ := if j < 548 then 979877139605191 else weightRowLLRRLRRLRRR j
def weightRowLLRRLRRLR (j : ℕ) : ℕ := if j < 547 then weightRowLLRRLRRLRL j else weightRowLLRRLRRLRR j
def weightRowLLRRLRRL (j : ℕ) : ℕ := if j < 545 then weightRowLLRRLRRLL j else weightRowLLRRLRRLR j
def weightRowLLRRLRRRLL (j : ℕ) : ℕ := if j < 551 then 981793585404287 else 982417194378478
def weightRowLLRRLRRRLRR (j : ℕ) : ℕ := if j < 554 then 983641602857453 else 984242403705439
def weightRowLLRRLRRRLR (j : ℕ) : ℕ := if j < 553 then 983033200037467 else weightRowLLRRLRRRLRR j
def weightRowLLRRLRRRL (j : ℕ) : ℕ := if j < 552 then weightRowLLRRLRRRLL j else weightRowLLRRLRRRLR j
def weightRowLLRRLRRRRL (j : ℕ) : ℕ := if j < 556 then 984835603843333 else 985421204932088
def weightRowLLRRLRRRRRR (j : ℕ) : ℕ := if j < 559 then 986569618626217 else 987132436586348
def weightRowLLRRLRRRRR (j : ℕ) : ℕ := if j < 558 then 985999209035861 else weightRowLLRRLRRRRRR j
def weightRowLLRRLRRRR (j : ℕ) : ℕ := if j < 557 then weightRowLLRRLRRRRL j else weightRowLLRRLRRRRR j
def weightRowLLRRLRRR (j : ℕ) : ℕ := if j < 555 then weightRowLLRRLRRRL j else weightRowLLRRLRRRR j
def weightRowLLRRLRR (j : ℕ) : ℕ := if j < 550 then weightRowLLRRLRRL j else weightRowLLRRLRRR j
def weightRowLLRRLR (j : ℕ) : ℕ := if j < 540 then weightRowLLRRLRL j else weightRowLLRRLRR j
def weightRowLLRRL (j : ℕ) : ℕ := if j < 520 then weightRowLLRRLL j else weightRowLLRRLR j
def weightRowLLRRRLLLLL (j : ℕ) : ℕ := if j < 561 then 987687666215337 else 988235311232442
def weightRowLLRRRLLLLRR (j : ℕ) : ℕ := if j < 564 then 989307864434881 else 989832782198662
def weightRowLLRRRLLLLR (j : ℕ) : ℕ := if j < 563 then 988775375781421 else weightRowLLRRRLLLLRR j
def weightRowLLRRRLLLL (j : ℕ) : ℕ := if j < 562 then weightRowLLRRRLLLLL j else weightRowLLRRRLLLLR j
def weightRowLLRRRLLLRL (j : ℕ) : ℕ := if j < 566 then 990350134516255 else 990859927273248
def weightRowLLRRRLLLRRR (j : ℕ) : ℕ := if j < 569 then 991856859885186 else 992344013762281
def weightRowLLRRRLLLRR (j : ℕ) : ℕ := if j < 568 then 991362166801806 else weightRowLLRRRLLLRRR j
def weightRowLLRRRLLLR (j : ℕ) : ℕ := if j < 567 then weightRowLLRRRLLLRL j else weightRowLLRRRLLLRR j
def weightRowLLRRRLLL (j : ℕ) : ℕ := if j < 565 then weightRowLLRRRLLLL j else weightRowLLRRRLLLR j
def weightRowLLRRRLLRLL (j : ℕ) : ℕ := if j < 571 then 992823636132200 else 993295735158879
def weightRowLLRRRLLRLRR (j : ℕ) : ℕ := if j < 574 then 994217398190304 else 994666980889036
def weightRowLLRRRLLRLR (j : ℕ) : ℕ := if j < 573 then 993760319475727 else weightRowLLRRRLLRLRR j
def weightRowLLRRRLLRL (j : ℕ) : ℕ := if j < 572 then weightRowLLRRRLLRLL j else weightRowLLRRRLLRLR j
def weightRowLLRRRLLRRL (j : ℕ) : ℕ := if j < 576 then 995109077641960 else 995543699007505
def weightRowLLRRRLLRRRR (j : ℕ) : ℕ := if j < 579 then 996390560281068 else 996802823791422
def weightRowLLRRRLLRRR (j : ℕ) : ℕ := if j < 578 then 995970856037309 else weightRowLLRRRLLRRRR j
def weightRowLLRRRLLRR (j : ℕ) : ℕ := if j < 577 then weightRowLLRRRLLRRL j else weightRowLLRRRLLRRR j
def weightRowLLRRRLLR (j : ℕ) : ℕ := if j < 575 then weightRowLLRRRLLRL j else weightRowLLRRRLLRR j
def weightRowLLRRRLL (j : ℕ) : ℕ := if j < 570 then weightRowLLRRRLLL j else weightRowLLRRRLLR j
def weightRowLLRRRLRLLL (j : ℕ) : ℕ := if j < 581 then 997207659128875 else 997605079366749
def weightRowLLRRRLRLLRR (j : ℕ) : ℕ := if j < 584 then 998377729431136 else 998752988013491
def weightRowLLRRRLRLLR (j : ℕ) : ℕ := if j < 583 then 997995098096179 else weightRowLLRRRLRLLRR j
def weightRowLLRRRLRLL (j : ℕ) : ℕ := if j < 582 then weightRowLLRRRLRLLL j else weightRowLLRRRLRLLR j
def weightRowLLRRRLRLRL (j : ℕ) : ℕ := if j < 586 then 999120889018115 else 999481448158015
def weightRowLLRRRLRLRRR (j : ℕ) : ℕ := if j < 589 then 1000180606417410 else 1000519239700325
def weightRowLLRRRLRLRR (j : ℕ) : ℕ := if j < 588 then 999834681689503 else weightRowLLRRRLRLRRR j
def weightRowLLRRRLRLR (j : ℕ) : ℕ := if j < 587 then weightRowLLRRRLRLRL j else weightRowLLRRRLRLRR j
def weightRowLLRRRLRL (j : ℕ) : ℕ := if j < 585 then weightRowLLRRRLRLL j else weightRowLLRRRLRLR j
def weightRowLLRRRLRRLL (j : ℕ) : ℕ := if j < 591 then 1000850599455888 else 1001174704166102
def weightRowLLRRRLRRLRR (j : ℕ) : ℕ := if j < 594 then 1001801225232527 else 1002103681423002
def weightRowLLRRRLRRLR (j : ℕ) : ℕ := if j < 593 then 1001491572882698 else weightRowLLRRRLRRLRR j
def weightRowLLRRRLRRL (j : ℕ) : ℕ := if j < 592 then weightRowLLRRRLRRLL j else weightRowLLRRRLRRLR j
def weightRowLLRRRLRRRL (j : ℕ) : ℕ := if j < 596 then 1002398962247563 else 1002687089091198
def weightRowLLRRRLRRRRR (j : ℕ) : ℕ := if j < 599 then 1003241969366697 else 1003508768576412
def weightRowLLRRRLRRRR (j : ℕ) : ℕ := if j < 598 then 1002968083935987 else weightRowLLRRRLRRRRR j
def weightRowLLRRRLRRR (j : ℕ) : ℕ := if j < 597 then weightRowLLRRRLRRRL j else weightRowLLRRRLRRRR j
def weightRowLLRRRLRR (j : ℕ) : ℕ := if j < 595 then weightRowLLRRRLRRL j else weightRowLLRRRLRRR j
def weightRowLLRRRLR (j : ℕ) : ℕ := if j < 590 then weightRowLLRRRLRL j else weightRowLLRRRLRR j
def weightRowLLRRRL (j : ℕ) : ℕ := if j < 580 then weightRowLLRRRLL j else weightRowLLRRRLR j
def weightRowLLRRRRLLLL (j : ℕ) : ℕ := if j < 601 then 1003768505372200 else 1004021204180826
def weightRowLLRRRRLLLRR (j : ℕ) : ℕ := if j < 604 then 1004505588676663 else 1004737326367832
def weightRowLLRRRRLLLR (j : ℕ) : ℕ := if j < 603 then 1004266890054498 else weightRowLLRRRRLLLRR j
def weightRowLLRRRRLLL (j : ℕ) : ℕ := if j < 602 then weightRowLLRRRRLLLL j else weightRowLLRRRRLLLR j
def weightRowLLRRRRLLRL (j : ℕ) : ℕ := if j < 606 then 1004962130091454 else 1005180027459832
def weightRowLLRRRRLLRRR (j : ℕ) : ℕ := if j < 609 then 1005595216860088 else 1005792567414628
def weightRowLLRRRRLLRR (j : ℕ) : ℕ := if j < 608 then 1005391046740073 else weightRowLLRRRRLLRRR j
def weightRowLLRRRRLLR (j : ℕ) : ℕ := if j < 607 then weightRowLLRRRRLLRL j else weightRowLLRRRRLLRR j
def weightRowLLRRRRLL (j : ℕ) : ℕ := if j < 605 then weightRowLLRRRRLLL j else weightRowLLRRRRLLR j
def weightRowLLRRRRLRLL (j : ℕ) : ℕ := if j < 611 then 1005983128671363 else 1006166931577011
def weightRowLLRRRRLRLRR (j : ℕ) : ℕ := if j < 614 then 1006514389554156 else 1006678109970008
def weightRowLLRRRRLRLR (j : ℕ) : ℕ := if j < 613 then 1006344007763494 else weightRowLLRRRRLRLRR j
def weightRowLLRRRRLRL (j : ℕ) : ℕ := if j < 612 then weightRowLLRRRRLRLL j else weightRowLLRRRRLRLR j
def weightRowLLRRRRLRRL (j : ℕ) : ℕ := if j < 616 then 1006835202736027 else 1006985702287492
def weightRowLLRRRRLRRRR (j : ℕ) : ℕ := if j < 619 then 1007267063077744 else 1007397996796277
def weightRowLLRRRRLRRR (j : ℕ) : ℕ := if j < 618 then 1007129643776371 else weightRowLLRRRRLRRRR j
def weightRowLLRRRRLRR (j : ℕ) : ℕ := if j < 617 then weightRowLLRRRRLRRL j else weightRowLLRRRRLRRR j
def weightRowLLRRRRLR (j : ℕ) : ℕ := if j < 615 then weightRowLLRRRRLRL j else weightRowLLRRRRLRR j
def weightRowLLRRRRL (j : ℕ) : ℕ := if j < 610 then weightRowLLRRRRLL j else weightRowLLRRRRLR j
def weightRowLLRRRRRLLL (j : ℕ) : ℕ := if j < 621 then 1007522482272741 else 1007640557590568
def weightRowLLRRRRRLLRR (j : ℕ) : ℕ := if j < 624 then 1007857633837056 else 1007956714705601
def weightRowLLRRRRRLLR (j : ℕ) : ℕ := if j < 623 then 1007752261582463 else weightRowLLRRRRRLLRR j
def weightRowLLRRRRRLL (j : ℕ) : ℕ := if j < 622 then weightRowLLRRRRRLLL j else weightRowLLRRRRRLLR j
def weightRowLLRRRRRLRL (j : ℕ) : ℕ := if j < 626 then 1008049545308717 else 1008136167543186
def weightRowLLRRRRRLRRR (j : ℕ) : ℕ := if j < 629 then 1008290958415181 else 1008359214788848
def weightRowLLRRRRRLRR (j : ℕ) : ℕ := if j < 628 then 1008216624088787 else weightRowLLRRRRRLRRR j
def weightRowLLRRRRRLR (j : ℕ) : ℕ := if j < 627 then weightRowLLRRRRRLRL j else weightRowLLRRRRRLRR j
def weightRowLLRRRRRL (j : ℕ) : ℕ := if j < 625 then weightRowLLRRRRRLL j else weightRowLLRRRRRLR j
def weightRowLLRRRRRRLL (j : ℕ) : ℕ := if j < 631 then 1008421438280061 else 1008477674769920
def weightRowLLRRRRRRLRR (j : ℕ) : ℕ := if j < 634 then 1008572374366601 else 1008610933353674
def weightRowLLRRRRRRLR (j : ℕ) : ℕ := if j < 633 then 1008527970957424 else weightRowLLRRRRRRLRR j
def weightRowLLRRRRRRL (j : ℕ) : ℕ := if j < 632 then weightRowLLRRRRRRLL j else weightRowLLRRRRRRLR j
def weightRowLLRRRRRRRL (j : ℕ) : ℕ := if j < 636 then 1008643697114293 else 1008670715690800
def weightRowLLRRRRRRRRR (j : ℕ) : ℕ := if j < 639 then 1008707721738301 else 1008717813593600
def weightRowLLRRRRRRRR (j : ℕ) : ℕ := if j < 638 then 1008692039979554 else weightRowLLRRRRRRRRR j
def weightRowLLRRRRRRR (j : ℕ) : ℕ := if j < 637 then weightRowLLRRRRRRRL j else weightRowLLRRRRRRRR j
def weightRowLLRRRRRR (j : ℕ) : ℕ := if j < 635 then weightRowLLRRRRRRL j else weightRowLLRRRRRRR j
def weightRowLLRRRRR (j : ℕ) : ℕ := if j < 630 then weightRowLLRRRRRL j else weightRowLLRRRRRR j
def weightRowLLRRRR (j : ℕ) : ℕ := if j < 620 then weightRowLLRRRRL j else weightRowLLRRRRR j
def weightRowLLRRR (j : ℕ) : ℕ := if j < 600 then weightRowLLRRRL j else weightRowLLRRRR j
def weightRowLLRR (j : ℕ) : ℕ := if j < 560 then weightRowLLRRL j else weightRowLLRRR j
def weightRowLLR (j : ℕ) : ℕ := if j < 480 then weightRowLLRL j else weightRowLLRR j
def weightRowLL (j : ℕ) : ℕ := if j < 320 then weightRowLLL j else weightRowLLR j
def weightRowLRLLLLLLLL (j : ℕ) : ℕ := if j < 641 then 1008722369048290 else 1008721442489020
def weightRowLRLLLLLLLRR (j : ℕ) : ℕ := if j < 644 then 1008703365339718 else 1008686328010444
def weightRowLRLLLLLLLR (j : ℕ) : ℕ := if j < 643 then 1008715089193817 else weightRowLRLLLLLLLRR j
def weightRowLRLLLLLLL (j : ℕ) : ℕ := if j < 642 then weightRowLRLLLLLLLL j else weightRowLRLLLLLLLR j
def weightRowLRLLLLLLRL (j : ℕ) : ℕ := if j < 646 then 1008664035204132 else 1008636545841120
def weightRowLRLLLLLLRRR (j : ℕ) : ℕ := if j < 649 then 1008566217784394 else 1008523501613129
def weightRowLRLLLLLLRR (j : ℕ) : ℕ := if j < 648 then 1008603919771777 else weightRowLRLLLLLLRRR j
def weightRowLRLLLLLLR (j : ℕ) : ℕ := if j < 647 then weightRowLRLLLLLLRL j else weightRowLRLLLLLLRR j
def weightRowLRLLLLLL (j : ℕ) : ℕ := if j < 645 then weightRowLRLLLLLLL j else weightRowLRLLLLLLR j
def weightRowLRLLLLLRLL (j : ℕ) : ℕ := if j < 651 then 1008475833945996 else 1008423278432921
def weightRowLRLLLLLRLRR (j : ℕ) : ℕ := if j < 654 then 1008303763326868 else 1008236935916494
def weightRowLRLLLLLRLR (j : ℕ) : ℕ := if j < 653 then 1008365899693843 else weightRowLRLLLLLRLRR j
def weightRowLRLLLLLRL (j : ℕ) : ℕ := if j < 652 then weightRowLRLLLLLRLL j else weightRowLRLLLLLRLR j
def weightRowLRLLLLLRRL (j : ℕ) : ℕ := if j < 656 then 1008165485041867 else 1008089479285115
def weightRowLRLLLLLRRRR (j : ℕ) : ℕ := if j < 659 then 1007924082518972 else 1007834833764435
def weightRowLRLLLLLRRR (j : ℕ) : ℕ := if j < 658 then 1008008988239723 else weightRowLRLLLLLRRRR j
def weightRowLRLLLLLRR (j : ℕ) : ℕ := if j < 657 then weightRowLRLLLLLRRL j else weightRowLRLLLLLRRR j
def weightRowLRLLLLLR (j : ℕ) : ℕ := if j < 655 then weightRowLRLLLLLRL j else weightRowLRLLLLLRR j
def weightRowLRLLLLL (j : ℕ) : ℕ := if j < 650 then weightRowLRLLLLLL j else weightRowLRLLLLLR j
def weightRowLRLLLLRLLL (j : ℕ) : ℕ := if j < 661 then 1007741314654521 else 1007643598913088
def weightRowLRLLLLRLLRR (j : ℕ) : ℕ := if j < 664 then 1007435877710392 else 1007326025002363
def weightRowLRLLLLRLLR (j : ℕ) : ℕ := if j < 663 then 1007541761318109 else weightRowLRLLLLRLLRR j
def weightRowLRLLLLRLL (j : ℕ) : ℕ := if j < 662 then weightRowLRLLLLRLLL j else weightRowLRLLLLRLLR j
def weightRowLRLLLLRLRL (j : ℕ) : ℕ := if j < 666 then 1007212281186909 else 1007094725346275
def weightRowLRLLLLRLRRR (j : ℕ) : ℕ := if j < 669 then 1006848499419055 else 1006719993024687
def weightRowLRLLLLRLRR (j : ℕ) : ℕ := if j < 668 then 1006973437661023 else weightRowLRLLLLRLRRR j
def weightRowLRLLLLRLR (j : ℕ) : ℕ := if j < 667 then weightRowLRLLLLRLRL j else weightRowLRLLLLRLRR j
def weightRowLRLLLLRL (j : ℕ) : ℕ := if j < 665 then weightRowLRLLLLRLL j else weightRowLRLLLLRLR j
def weightRowLRLLLLRRLL (j : ℕ) : ℕ := if j < 671 then 1006588002007790 else 1006452611032992
def weightRowLRLLLLRRLRR (j : ℕ) : ℕ := if j < 674 then 1006171973597613 else 1006026902223728
def weightRowLRLLLLRRLR (j : ℕ) : ℕ := if j < 673 then 1006313905908938 else weightRowLRLLLLRRLRR j
def weightRowLRLLLLRRL (j : ℕ) : ℕ := if j < 672 then weightRowLRLLLLRRLL j else weightRowLRLLLLRRLR j
def weightRowLRLLLLRRRL (j : ℕ) : ℕ := if j < 676 then 1005878781084167 else 1005727700657497
def weightRowLRLLLLRRRRR (j : ℕ) : ℕ := if j < 679 then 1005417029823014 else 1005257626367224
def weightRowLRLLLLRRRR (j : ℕ) : ℕ := if j < 678 then 1005573752613541 else weightRowLRLLLLRRRRR j
def weightRowLRLLLLRRR (j : ℕ) : ℕ := if j < 677 then weightRowLRLLLLRRRL j else weightRowLRLLLLRRRR j
def weightRowLRLLLLRR (j : ℕ) : ℕ := if j < 675 then weightRowLRLLLLRRL j else weightRowLRLLLLRRR j
def weightRowLRLLLLR (j : ℕ) : ℕ := if j < 670 then weightRowLRLLLLRL j else weightRowLRLLLLRR j
def weightRowLRLLLL (j : ℕ) : ℕ := if j < 660 then weightRowLRLLLLL j else weightRowLRLLLLR j
def weightRowLRLLLRLLLL (j : ℕ) : ℕ := if j < 681 then 1005095637547836 else 1004931159896701
def weightRowLRLLLRLLLRR (j : ℕ) : ℕ := if j < 684 then 1004595130436954 else 1004423777932346
def weightRowLRLLLRLLLR (j : ℕ) : ℕ := if j < 683 then 1004764291185750 else weightRowLRLLLRLLLRR j
def weightRowLRLLLRLLL (j : ℕ) : ℕ := if j < 682 then weightRowLRLLLRLLLL j else weightRowLRLLLRLLLR j
def weightRowLRLLLRLLRL (j : ℕ) : ℕ := if j < 686 then 1004250335224118 else 1004074905144770
def weightRowLRLLLRLLRRR (j : ℕ) : ℕ := if j < 689 then 1003718500665701 else 1003537738424903
def weightRowLRLLLRLLRR (j : ℕ) : ℕ := if j < 688 then 1003897591817342 else weightRowLRLLLRLLRRR j
def weightRowLRLLLRLLR (j : ℕ) : ℕ := if j < 687 then weightRowLRLLLRLLRL j else weightRowLRLLLRLLRR j
def weightRowLRLLLRLL (j : ℕ) : ℕ := if j < 685 then weightRowLRLLLRLLL j else weightRowLRLLLRLLR j
def weightRowLRLLLRLRLL (j : ℕ) : ℕ := if j < 691 then 1003355413151618 else 1003171634234628
def weightRowLRLLLRLRLRR (j : ℕ) : ℕ := if j < 694 then 1002800159748666 else 1002612689713239
def weightRowLRLLLRLRLR (j : ℕ) : ℕ := if j < 693 then 1002986512405388 else weightRowLRLLLRLRLRR j
def weightRowLRLLLRLRL (j : ℕ) : ℕ := if j < 692 then weightRowLRLLLRLRLL j else weightRowLRLLLRLRLR j
def weightRowLRLLLRLRRL (j : ℕ) : ℕ := if j < 696 then 1002424217122674 else 1002234858186166
def weightRowLRLLLRLRRRR (j : ℕ) : ℕ := if j < 699 then 1001853953105825 else 1001662646407129
def weightRowLRLLLRLRRR (j : ℕ) : ℕ := if j < 698 then 1002044730509459 else weightRowLRLLLRLRRRR j
def weightRowLRLLLRLRR (j : ℕ) : ℕ := if j < 697 then weightRowLRLLLRLRRL j else weightRowLRLLLRLRRR j
def weightRowLRLLLRLR (j : ℕ) : ℕ := if j < 695 then weightRowLRLLLRLRL j else weightRowLRLLLRLRR j
def weightRowLRLLLRL (j : ℕ) : ℕ := if j < 690 then weightRowLRLLLRLL j else weightRowLRLLLRLR j
def weightRowLRLLLRRLLL (j : ℕ) : ℕ := if j < 701 then 1001470932274956 else 1001278934011815
def weightRowLRLLLRRLLRR (j : ℕ) : ℕ := if j < 704 then 1000894585575008 else 1000702489312826
def weightRowLRLLLRRLLR (j : ℕ) : ℕ := if j < 703 then 1001086776372414 else weightRowLRLLLRRLLRR j
def weightRowLRLLLRRLL (j : ℕ) : ℕ := if j < 702 then weightRowLRLLLRRLLL j else weightRowLRLLLRRLLR j
def weightRowLRLLLRRLRL (j : ℕ) : ℕ := if j < 706 then 1000510616765565 else 1000319098610966
def weightRowLRLLLRRLRRR (j : ℕ) : ℕ := if j < 709 then 999937655750875 else 999747999996275
def weightRowLRLLLRRLRR (j : ℕ) : ℕ := if j < 708 then 1000128067036455 else weightRowLRLLLRRLRRR j
def weightRowLRLLLRRLR (j : ℕ) : ℕ := if j < 707 then weightRowLRLLLRRLRL j else weightRowLRLLLRRLRR j
def weightRowLRLLLRRL (j : ℕ) : ℕ := if j < 705 then weightRowLRLLLRRLL j else weightRowLRLLLRRLR j
def weightRowLRLLLRRRLL (j : ℕ) : ℕ := if j < 711 then 999559236559796 else 999371503785614
def weightRowLRLLLRRRLRR (j : ℕ) : ℕ := if j < 714 then 998999691458312 else 998815896487403
def weightRowLRLLLRRRLR (j : ℕ) : ℕ := if j < 713 then 999184941586978 else weightRowLRLLLRRRLRR j
def weightRowLRLLLRRRL (j : ℕ) : ℕ := if j < 712 then weightRowLRLLLRRRLL j else weightRowLRLLLRRRLR j
def weightRowLRLLLRRRRL (j : ℕ) : ℕ := if j < 716 then 998633701367669 else 998453252410496
def weightRowLRLLLRRRRRR (j : ℕ) : ℕ := if j < 719 then 998098186393879 else 997923870159287
def weightRowLRLLLRRRRR (j : ℕ) : ℕ := if j < 718 then 998274697557671 else weightRowLRLLLRRRRRR j
def weightRowLRLLLRRRR (j : ℕ) : ℕ := if j < 717 then weightRowLRLLLRRRRL j else weightRowLRLLLRRRRR j
def weightRowLRLLLRRR (j : ℕ) : ℕ := if j < 715 then weightRowLRLLLRRRL j else weightRowLRLLLRRRR j
def weightRowLRLLLRR (j : ℕ) : ℕ := if j < 710 then weightRowLRLLLRRL j else weightRowLRLLLRRR j
def weightRowLRLLLR (j : ℕ) : ℕ := if j < 700 then weightRowLRLLLRL j else weightRowLRLLLRR j
def weightRowLRLLL (j : ℕ) : ℕ := if j < 680 then weightRowLRLLLL j else weightRowLRLLLR j
def weightRowLRLLRLLLLL (j : ℕ) : ℕ := if j < 721 then 997751901762217 else 997582435791887
def weightRowLRLLRLLLLRR (j : ℕ) : ℕ := if j < 724 then 997251637969859 else 997090623816961
def weightRowLRLLRLLLLR (j : ℕ) : ℕ := if j < 723 then 997415628531239 else weightRowLRLLRLLLLRR j
def weightRowLRLLRLLLL (j : ℕ) : ℕ := if j < 722 then weightRowLRLLRLLLLL j else weightRowLRLLRLLLLR j
def weightRowLRLLRLLLRL (j : ℕ) : ℕ := if j < 726 then 996932747514474 else 996778172250200
def weightRowLRLLRLLLRRR (j : ℕ) : ℕ := if j < 729 then 996479586396433 else 996335911031557
def weightRowLRLLRLLLRR (j : ℕ) : ℕ := if j < 728 then 996627062971062 else weightRowLRLLRLLLRRR j
def weightRowLRLLRLLLR (j : ℕ) : ℕ := if j < 727 then weightRowLRLLRLLLRL j else weightRowLRLLRLLLRR j
def weightRowLRLLRLLL (j : ℕ) : ℕ := if j < 725 then weightRowLRLLRLLLL j else weightRowLRLLRLLLR j
def weightRowLRLLRLLRLL (j : ℕ) : ℕ := if j < 731 then 996196207181051 else 996060646962489
def weightRowLRLLRLLRLRR (j : ℕ) : ℕ := if j < 734 then 995802655038462 else 995680576756480
def weightRowLRLLRLLRLR (j : ℕ) : ℕ := if j < 733 then 995929404320087 else weightRowLRLLRLLRLRR j
def weightRowLRLLRLLRL (j : ℕ) : ℕ := if j < 732 then weightRowLRLLRLLRLL j else weightRowLRLLRLLRLR j
def weightRowLRLLRLLRRL (j : ℕ) : ℕ := if j < 736 then 995563348981205 else 995451153101921
def weightRowLRLLRLLRRRR (j : ℕ) : ℕ := if j < 739 then 995242592084371 else 995146599263301
def weightRowLRLLRLLRRR (j : ℕ) : ℕ := if j < 738 then 995344172404251 else weightRowLRLLRLLRRRR j
def weightRowLRLLRLLRR (j : ℕ) : ℕ := if j < 737 then weightRowLRLLRLLRRL j else weightRowLRLLRLLRRR j
def weightRowLRLLRLLR (j : ℕ) : ℕ := if j < 735 then weightRowLRLLRLLRL j else weightRowLRLLRLLRR j
def weightRowLRLLRLL (j : ℕ) : ℕ := if j < 730 then weightRowLRLLRLLL j else weightRowLRLLRLLR j
def weightRowLRLLRLRLLL (j : ℕ) : ℕ := if j < 741 then 995056383001303 else 994972134312356
def weightRowLRLLRLRLLRR (j : ℕ) : ℕ := if j < 744 then 994822313565673 else 994757133436122
def weightRowLRLLRLRLLR (j : ℕ) : ℕ := if j < 743 then 994894046178735 else weightRowLRLLRLRLLRR j
def weightRowLRLLRLRLL (j : ℕ) : ℕ := if j < 742 then weightRowLRLLRLRLLL j else weightRowLRLLRLRLLR j
def weightRowLRLLRLRLRL (j : ℕ) : ℕ := if j < 746 then 994698704765609 else 994647228557179
def weightRowLRLLRLRLRRR (j : ℕ) : ℕ := if j < 749 then 994565947766699 else 994536555464196
def weightRowLRLLRLRLRR (j : ℕ) : ℕ := if j < 748 then 994602907856440 else weightRowLRLLRLRLRRR j
def weightRowLRLLRLRLR (j : ℕ) : ℕ := if j < 747 then weightRowLRLLRLRLRL j else weightRowLRLLRLRLRR j
def weightRowLRLLRLRL (j : ℕ) : ℕ := if j < 745 then weightRowLRLLRLRLL j else weightRowLRLLRLRLR j
def weightRowLRLLRLRRLL (j : ℕ) : ℕ := if j < 751 then 994514940213435 else 994501313382608
def weightRowLRLLRLRRLRR (j : ℕ) : ℕ := if j < 754 then 994498881065219 else 994510508973700
def weightRowLRLLRLRRLR (j : ℕ) : ℕ := if j < 753 then 994495888459121 else weightRowLRLLRLRRLRR j
def weightRowLRLLRLRRL (j : ℕ) : ℕ := if j < 752 then weightRowLRLLRLRRLL j else weightRowLRLLRLRRLR j
def weightRowLRLLRLRRRL (j : ℕ) : ℕ := if j < 756 then 994530992123744 else 994560552636827
def weightRowLRLLRLRRRRR (j : ℕ) : ℕ := if j < 759 then 994647805245723 else 994705952640668
def weightRowLRLLRLRRRR (j : ℕ) : ℕ := if j < 758 then 994599414832741 else weightRowLRLLRLRRRRR j
def weightRowLRLLRLRRR (j : ℕ) : ℕ := if j < 757 then weightRowLRLLRLRRRL j else weightRowLRLLRLRRRR j
def weightRowLRLLRLRR (j : ℕ) : ℕ := if j < 755 then weightRowLRLLRLRRL j else weightRowLRLLRLRRR j
def weightRowLRLLRLR (j : ℕ) : ℕ := if j < 750 then weightRowLRLLRLRL j else weightRowLRLLRLRR j
def weightRowLRLLRL (j : ℕ) : ℕ := if j < 740 then weightRowLRLLRLL j else weightRowLRLLRLR j
def weightRowLRLLRRLLLL (j : ℕ) : ℕ := if j < 761 then 994774088029461 else 994852444687402
def weightRowLRLLRRLLLRR (j : ℕ) : ℕ := if j < 764 then 995040766328300 else 995151209328235
def weightRowLRLLRRLLLR (j : ℕ) : ℕ := if j < 763 then 994941258169739 else weightRowLRLLRRLLLRR j
def weightRowLRLLRRLLL (j : ℕ) : ℕ := if j < 762 then weightRowLRLLRRLLLL j else weightRowLRLLRRLLLR j
def weightRowLRLLRRLLRL (j : ℕ) : ℕ := if j < 766 then 995272829664859 else 995405872180603
def weightRowLRLLRRLLRRR (j : ℕ) : ℕ := if j < 769 then 995707214957203 else 995876016792543
def weightRowLRLLRRLLRR (j : ℕ) : ℕ := if j < 768 then 995550584082072 else weightRowLRLLRRLLRRR j
def weightRowLRLLRRLLR (j : ℕ) : ℕ := if j < 767 then weightRowLRLLRRLLRL j else weightRowLRLLRRLLRR j
def weightRowLRLLRRLL (j : ℕ) : ℕ := if j < 765 then weightRowLRLLRRLLL j else weightRowLRLLRRLLR j
def weightRowLRLLRRLRLL (j : ℕ) : ℕ := if j < 771 then 996041925596916 else 996204958856424
def weightRowLRLLRRLRLRR (j : ℕ) : ℕ := if j < 774 then 996522469253048 else 996676981928485
def weightRowLRLLRRLRLR (j : ℕ) : ℕ := if j < 773 then 996365134170839 else weightRowLRLLRRLRLRR j
def weightRowLRLLRRLRL (j : ℕ) : ℕ := if j < 772 then weightRowLRLLRRLRLL j else weightRowLRLLRRLRLR j
def weightRowLRLLRRLRRL (j : ℕ) : ℕ := if j < 776 then 996828690134548 else 996977611920002
def weightRowLRLLRRLRRRR (j : ℕ) : ℕ := if j < 779 then 997267168977302 else 997407840897938
def weightRowLRLLRRLRRR (j : ℕ) : ℕ := if j < 778 then 997123765444370 else weightRowLRLLRRLRRRR j
def weightRowLRLLRRLRR (j : ℕ) : ℕ := if j < 777 then weightRowLRLLRRLRRL j else weightRowLRLLRRLRRR j
def weightRowLRLLRRLR (j : ℕ) : ℕ := if j < 775 then weightRowLRLLRRLRL j else weightRowLRLLRRLRR j
def weightRowLRLLRRL (j : ℕ) : ℕ := if j < 770 then weightRowLRLLRRLL j else weightRowLRLLRRLR j
def weightRowLRLLRRRLLL (j : ℕ) : ℕ := if j < 781 then 997545799694248 else 997681063962362
def weightRowLRLLRRRLLRR (j : ℕ) : ℕ := if j < 784 then 997943583835181 else 998070877166681
def weightRowLRLLRRRLLR (j : ℕ) : ℕ := if j < 783 then 997813652405883 else weightRowLRLLRRRLLRR j
def weightRowLRLLRRRLL (j : ℕ) : ℕ := if j < 782 then weightRowLRLLRRRLLL j else weightRowLRLLRRRLLR j
def weightRowLRLLRRRLRL (j : ℕ) : ℕ := if j < 786 then 998195551422120 else 998317625727803
def weightRowLRLLRRRLRRR (j : ℕ) : ℕ := if j < 789 then 998554051513328 else 998668441761622
def weightRowLRLLRRRLRR (j : ℕ) : ℕ := if j < 788 then 998437119313833 else weightRowLRLLRRRLRRR j
def weightRowLRLLRRRLR (j : ℕ) : ℕ := if j < 787 then weightRowLRLLRRRLRL j else weightRowLRLLRRRLRR j
def weightRowLRLLRRRL (j : ℕ) : ℕ := if j < 785 then weightRowLRLLRRRLL j else weightRowLRLLRRRLR j
def weightRowLRLLRRRRLL (j : ℕ) : ℕ := if j < 791 then 998780309595448 else 998889674652104
def weightRowLRLLRRRRLRR (j : ℕ) : ℕ := if j < 794 then 999100975480805 else 999202951022533
def weightRowLRLLRRRRLR (j : ℕ) : ℕ := if j < 793 then 998996556668603 else weightRowLRLLRRRRLRR j
def weightRowLRLLRRRRL (j : ℕ) : ℕ := if j < 792 then weightRowLRLLRRRRLL j else weightRowLRLLRRRRLR j
def weightRowLRLLRRRRRL (j : ℕ) : ℕ := if j < 796 then 999302503324668 else 999399652514228
def weightRowLRLLRRRRRRR (j : ℕ) : ℕ := if j < 799 then 999586822538744 else 999676884099892
def weightRowLRLLRRRRRR (j : ℕ) : ℕ := if j < 798 then 999494418813432 else weightRowLRLLRRRRRRR j
def weightRowLRLLRRRRR (j : ℕ) : ℕ := if j < 797 then weightRowLRLLRRRRRL j else weightRowLRLLRRRRRR j
def weightRowLRLLRRRR (j : ℕ) : ℕ := if j < 795 then weightRowLRLLRRRRL j else weightRowLRLLRRRRR j
def weightRowLRLLRRR (j : ℕ) : ℕ := if j < 790 then weightRowLRLLRRRL j else weightRowLRLLRRRR j
def weightRowLRLLRR (j : ℕ) : ℕ := if j < 780 then weightRowLRLLRRL j else weightRowLRLLRRR j
def weightRowLRLLR (j : ℕ) : ℕ := if j < 760 then weightRowLRLLRL j else weightRowLRLLRR j
def weightRowLRLL (j : ℕ) : ℕ := if j < 720 then weightRowLRLLL j else weightRowLRLLR j
def weightRowLRLRLLLLLL (j : ℕ) : ℕ := if j < 801 then 999764623998883 else 999850062828983
def weightRowLRLRLLLLLRR (j : ℕ) : ℕ := if j < 804 then 1000014120105689 else 1000092780185769
def weightRowLRLRLLLLLR (j : ℕ) : ℕ := if j < 803 then 999933221273691 else weightRowLRLRLLLLLRR j
def weightRowLRLRLLLLL (j : ℕ) : ℕ := if j < 802 then weightRowLRLRLLLLLL j else weightRowLRLRLLLLLR j
def weightRowLRLRLLLLRL (j : ℕ) : ℕ := if j < 806 then 1000169222461748 else 1000243467967359
def weightRowLRLRLLLLRRR (j : ℕ) : ℕ := if j < 809 then 1000385453225194 else 1000453235464208
def weightRowLRLRLLLLRR (j : ℕ) : ℕ := if j < 808 then 1000315537821121 else weightRowLRLRLLLLRRR j
def weightRowLRLRLLLLR (j : ℕ) : ℕ := if j < 807 then weightRowLRLRLLLLRL j else weightRowLRLRLLLLRR j
def weightRowLRLRLLLL (j : ℕ) : ℕ := if j < 805 then weightRowLRLRLLLLL j else weightRowLRLRLLLLR j
def weightRowLRLRLLLRLL (j : ℕ) : ℕ := if j < 811 then 1000518905904078 else 1000582485990792
def weightRowLRLRLLLRLRR (j : ℕ) : ℕ := if j < 814 then 1000703461281669 else 1000760899767004
def weightRowLRLRLLLRLR (j : ℕ) : ℕ := if j < 813 then 1000643997249180 else weightRowLRLRLLLRLRR j
def weightRowLRLRLLLRL (j : ℕ) : ℕ := if j < 812 then weightRowLRLRLLLRLL j else weightRowLRLRLLLRLR j
def weightRowLRLRLLLRRL (j : ℕ) : ℕ := if j < 816 then 1000816334458960 else 1000869787185025
def weightRowLRLRLLLRRRR (j : ℕ) : ℕ := if j < 819 then 1000970834409956 else 1001018472920224
def weightRowLRLRLLLRRR (j : ℕ) : ℕ := if j < 818 then 1000921279845063 else weightRowLRLRLLLRRRR j
def weightRowLRLRLLLRR (j : ℕ) : ℕ := if j < 817 then weightRowLRLRLLLRRL j else weightRowLRLRLLLRRR j
def weightRowLRLRLLLR (j : ℕ) : ℕ := if j < 815 then weightRowLRLRLLLRL j else weightRowLRLRLLLRR j
def weightRowLRLRLLL (j : ℕ) : ℕ := if j < 810 then weightRowLRLRLLLL j else weightRowLRLRLLLR j
def weightRowLRLRLLRLLL (j : ℕ) : ℕ := if j < 821 then 1001064217484620 else 1001108090278705
def weightRowLRLRLLRLLRR (j : ℕ) : ℕ := if j < 824 then 1001190309583520 else 1001228700766261
def weightRowLRLRLLRLLR (j : ℕ) : ℕ := if j < 823 then 1001150113543402 else weightRowLRLRLLRLLRR j
def weightRowLRLRLLRLL (j : ℕ) : ℕ := if j < 822 then weightRowLRLRLLRLLL j else weightRowLRLRLLRLLR j
def weightRowLRLRLLRLRL (j : ℕ) : ℕ := if j < 826 then 1001265309519703 else 1001300158331255
def weightRowLRLRLLRLRRR (j : ℕ) : ℕ := if j < 829 then 1001364666365577 else 1001394370845615
def weightRowLRLRLLRLRR (j : ℕ) : ℕ := if j < 828 then 1001333269746095 else weightRowLRLRLLRLRRR j
def weightRowLRLRLLRLR (j : ℕ) : ℕ := if j < 827 then weightRowLRLRLLRLRL j else weightRowLRLRLLRLRR j
def weightRowLRLRLLRL (j : ℕ) : ℕ := if j < 825 then weightRowLRLRLLRLL j else weightRowLRLRLLRLR j
def weightRowLRLRLLRRLL (j : ℕ) : ℕ := if j < 831 then 1001422405895050 else 1001448794273980
def weightRowLRLRLLRRLRR (j : ℕ) : ℕ := if j < 834 then 1001496722306857 else 1001518307721973
def weightRowLRLRLLRRLR (j : ℕ) : ℕ := if j < 833 then 1001473558792074 else weightRowLRLRLLRRLRR j
def weightRowLRLRLLRRL (j : ℕ) : ℕ := if j < 832 then weightRowLRLRLLRRLL j else weightRowLRLRLLRRLR j
def weightRowLRLRLLRRRL (j : ℕ) : ℕ := if j < 836 then 1001538337985414 else 1001556836087734
def weightRowLRLRLLRRRRR (j : ℕ) : ℕ := if j < 839 then 1001589327973095 else 1001603367933551
def weightRowLRLRLLRRRR (j : ℕ) : ℕ := if j < 838 then 1001573825060229 else weightRowLRLRLLRRRRR j
def weightRowLRLRLLRRR (j : ℕ) : ℕ := if j < 837 then weightRowLRLRLLRRRL j else weightRowLRLRLLRRRR j
def weightRowLRLRLLRR (j : ℕ) : ℕ := if j < 835 then weightRowLRLRLLRRL j else weightRowLRLRLLRRR j
def weightRowLRLRLLR (j : ℕ) : ℕ := if j < 830 then weightRowLRLRLLRL j else weightRowLRLRLLRR j
def weightRowLRLRLL (j : ℕ) : ℕ := if j < 820 then weightRowLRLRLLL j else weightRowLRLRLLR j
def weightRowLRLRLRLLLL (j : ℕ) : ℕ := if j < 841 then 1001615968083951 else 1001627151599852
def weightRowLRLRLRLLLRR (j : ℕ) : ℕ := if j < 844 then 1001645361584663 else 1001652434553004
def weightRowLRLRLRLLLR (j : ℕ) : ℕ := if j < 843 then 1001636941688061 else weightRowLRLRLRLLLRR j
def weightRowLRLRLRLLL (j : ℕ) : ℕ := if j < 842 then weightRowLRLRLRLLLL j else weightRowLRLRLRLLLR j
def weightRowLRLRLRLLRL (j : ℕ) : ℕ := if j < 846 then 1001658183881658 else 1001662632882367
def weightRowLRLRLRLLRRR (j : ℕ) : ℕ := if j < 849 then 1001667723250134 else 1001668411337506
def weightRowLRLRLRLLRR (j : ℕ) : ℕ := if j < 848 then 1001665804887939 else weightRowLRLRLRLLRRR j
def weightRowLRLRLRLLR (j : ℕ) : ℕ := if j < 847 then weightRowLRLRLRLLRL j else weightRowLRLRLRLLRR j
def weightRowLRLRLRLL (j : ℕ) : ℕ := if j < 845 then weightRowLRLRLRLLL j else weightRowLRLRLRLLR j
def weightRowLRLRLRLRLL (j : ℕ) : ℕ := if j < 851 then 1001667892533229 else 1001666190232878
def weightRowLRLRLRLRLRR (j : ℕ) : ℕ := if j < 854 then 1001659328774817 else 1001654216449969
def weightRowLRLRLRLRLR (j : ℕ) : ℕ := if j < 853 then 1001663327842196 else weightRowLRLRLRLRLRR j
def weightRowLRLRLRLRL (j : ℕ) : ℕ := if j < 852 then weightRowLRLRLRLRLL j else weightRowLRLRLRLRLR j
def weightRowLRLRLRLRRL (j : ℕ) : ℕ := if j < 856 then 1001648014290138 else 1001640745718707
def weightRowLRLRLRLRRRR (j : ℕ) : ℕ := if j < 859 then 1001623103024657 else 1001612775731572
def weightRowLRLRLRLRRR (j : ℕ) : ℕ := if j < 858 then 1001632434157560 else weightRowLRLRLRLRRRR j
def weightRowLRLRLRLRR (j : ℕ) : ℕ := if j < 857 then weightRowLRLRLRLRRL j else weightRowLRLRLRLRRR j
def weightRowLRLRLRLR (j : ℕ) : ℕ := if j < 855 then weightRowLRLRLRLRL j else weightRowLRLRLRLRR j
def weightRowLRLRLRL (j : ℕ) : ℕ := if j < 850 then weightRowLRLRLRLL j else weightRowLRLRLRLR j
def weightRowLRLRLRRLLL (j : ℕ) : ℕ := if j < 861 then 1001601475681005 else 1001589226264260
def weightRowLRLRLRRLLRR (j : ℕ) : ℕ := if j < 864 then 1001561972825086 else 1001547015505106
def weightRowLRLRLRRLLR (j : ℕ) : ℕ := if j < 863 then 1001576050858685 else weightRowLRLRLRRLLRR j
def weightRowLRLRLRRLL (j : ℕ) : ℕ := if j < 862 then weightRowLRLRLRRLLL j else weightRowLRLRLRRLLR j
def weightRowLRLRLRRLRL (j : ℕ) : ℕ := if j < 866 then 1001531202218563 else 1001514556260766
def weightRowLRLRLRRLRRR (j : ℕ) : ℕ := if j < 869 then 1001478859373704 else 1001459854887807
def weightRowLRLRLRRLRR (j : ℕ) : ℕ := if j < 868 then 1001497100899787 else weightRowLRLRLRRLRRR j
def weightRowLRLRLRRLR (j : ℕ) : ℕ := if j < 867 then weightRowLRLRLRRLRL j else weightRowLRLRLRRLRR j
def weightRowLRLRLRRL (j : ℕ) : ℕ := if j < 865 then weightRowLRLRLRRLL j else weightRowLRLRLRRLR j
def weightRowLRLRLRRRLL (j : ℕ) : ℕ := if j < 871 then 1001440110611766 else 1001419649676773
def weightRowLRLRLRRRLRR (j : ℕ) : ℕ := if j < 874 then 1001376670144843 else 1001354197591595
def weightRowLRLRLRRRLR (j : ℕ) : ℕ := if j < 873 then 1001398495172635 else weightRowLRLRLRRRLRR j
def weightRowLRLRLRRRL (j : ℕ) : ℕ := if j < 872 then weightRowLRLRLRRRLL j else weightRowLRLRLRRRLR j
def weightRowLRLRLRRRRL (j : ℕ) : ℕ := if j < 876 then 1001331100460789 else 1001307401646979
def weightRowLRLRLRRRRRR (j : ℕ) : ℕ := if j < 879 then 1001258290263276 else 1001232923187810
def weightRowLRLRLRRRRR (j : ℕ) : ℕ := if j < 878 then 1001283123988285 else weightRowLRLRLRRRRRR j
def weightRowLRLRLRRRR (j : ℕ) : ℕ := if j < 877 then weightRowLRLRLRRRRL j else weightRowLRLRLRRRRR j
def weightRowLRLRLRRR (j : ℕ) : ℕ := if j < 875 then weightRowLRLRLRRRL j else weightRowLRLRLRRRR j
def weightRowLRLRLRR (j : ℕ) : ℕ := if j < 870 then weightRowLRLRLRRL j else weightRowLRLRLRRR j
def weightRowLRLRLR (j : ℕ) : ℕ := if j < 860 then weightRowLRLRLRL j else weightRowLRLRLRR j
def weightRowLRLRL (j : ℕ) : ℕ := if j < 840 then weightRowLRLRLL j else weightRowLRLRLR j
def weightRowLRLRRLLLLL (j : ℕ) : ℕ := if j < 881 then 1001207045411836 else 1001180679516158
def weightRowLRLRRLLLLRR (j : ℕ) : ℕ := if j < 884 then 1001126573323476 else 1001098877812674
def weightRowLRLRRLLLLR (j : ℕ) : ℕ := if j < 883 then 1001153848009155 else weightRowLRLRRLLLLRR j
def weightRowLRLRRLLLL (j : ℕ) : ℕ := if j < 882 then weightRowLRLRRLLLLL j else weightRowLRLRRLLLLR j
def weightRowLRLRRLLLRL (j : ℕ) : ℕ := if j < 886 then 1001070783747820 else 1001042313314066
def weightRowLRLRRLLLRRR (j : ℕ) : ℕ := if j < 889 then 1000984331629969 else 1000954864288847
def weightRowLRLRRLLLRR (j : ℕ) : ℕ := if j < 888 then 1001013488607168 else weightRowLRLRRLLLRRR j
def weightRowLRLRRLLLR (j : ℕ) : ℕ := if j < 887 then weightRowLRLRRLLLRL j else weightRowLRLRRLLLRR j
def weightRowLRLRRLLL (j : ℕ) : ℕ := if j < 885 then weightRowLRLRRLLLL j else weightRowLRLRRLLLR j
def weightRowLRLRRLLRLL (j : ℕ) : ℕ := if j < 891 then 1000925108390105 else 1000895085636341
def weightRowLRLRRLLRLRR (j : ℕ) : ℕ := if j < 894 then 1000834325833427 else 1000803631637544
def weightRowLRLRRLLRLR (j : ℕ) : ℕ := if j < 893 then 1000864817622756 else weightRowLRLRRLLRLRR j
def weightRowLRLRRLLRL (j : ℕ) : ℕ := if j < 892 then weightRowLRLRRLLRLL j else weightRowLRLRRLLRLR j
def weightRowLRLRRLLRRL (j : ℕ) : ℕ := if j < 896 then 1000772756285588 else 1000741720905479
def weightRowLRLRRLLRRRR (j : ℕ) : ℕ := if j < 899 then 1000679253936208 else 1000647863954733
def weightRowLRLRRLLRRR (j : ℕ) : ℕ := if j < 898 then 1000710546498671 else weightRowLRLRRLLRRRR j
def weightRowLRLRRLLRR (j : ℕ) : ℕ := if j < 897 then weightRowLRLRRLLRRL j else weightRowLRLRRLLRRR j
def weightRowLRLRRLLR (j : ℕ) : ℕ := if j < 895 then weightRowLRLRRLLRL j else weightRowLRLRRLLRR j
def weightRowLRLRRLL (j : ℕ) : ℕ := if j < 890 then weightRowLRLRRLLL j else weightRowLRLRRLLR j
def weightRowLRLRRLRLLL (j : ℕ) : ℕ := if j < 901 then 1000616397152448 else 1000584873985034
def weightRowLRLRRLRLLRR (j : ℕ) : ℕ := if j < 904 then 1000521739640117 else 1000490168623978
def weightRowLRLRRLRLLR (j : ℕ) : ℕ := if j < 903 then 1000553314761522 else weightRowLRLRRLRLLRR j
def weightRowLRLRRLRLL (j : ℕ) : ℕ := if j < 902 then weightRowLRLRRLRLLL j else weightRowLRLRRLRLLR j
def weightRowLRLRRLRLRL (j : ℕ) : ℕ := if j < 906 then 1000458621556945 else 1000427118119226
def weightRowLRLRRLRLRRR (j : ℕ) : ℕ := if j < 909 then 1000364320008145 else 1000333063837498
def weightRowLRLRRLRLRR (j : ℕ) : ℕ := if j < 908 then 1000395677823027 else weightRowLRLRRLRLRRR j
def weightRowLRLRRLRLR (j : ℕ) : ℕ := if j < 907 then weightRowLRLRRLRLRL j else weightRowLRLRRLRLRR j
def weightRowLRLRRLRL (j : ℕ) : ℕ := if j < 905 then weightRowLRLRRLRLL j else weightRowLRLRRLRLR j
def weightRowLRLRRLRRLL (j : ℕ) : ℕ := if j < 911 then 1000301928292617 else 1000270932169087
def weightRowLRLRRLRRLRR (j : ℕ) : ℕ := if j < 914 then 1000209432410938 else 1000178965395982
def weightRowLRLRRLRRLR (j : ℕ) : ℕ := if j < 913 then 1000240094071927 else weightRowLRLRRLRRLRR j
def weightRowLRLRRLRRL (j : ℕ) : ℕ := if j < 912 then weightRowLRLRRLRRLL j else weightRowLRLRRLRRLR j
def weightRowLRLRRLRRRL (j : ℕ) : ℕ := if j < 916 then 1000148711032220 else 1000118687115298
def weightRowLRLRRLRRRRR (j : ℕ) : ℕ := if j < 919 then 1000059400727697 else 1000030172756641
def weightRowLRLRRLRRRR (j : ℕ) : ℕ := if j < 918 then 1000088911226473 else weightRowLRLRRLRRRRR j
def weightRowLRLRRLRRR (j : ℕ) : ℕ := if j < 917 then weightRowLRLRRLRRRL j else weightRowLRLRRLRRRR j
def weightRowLRLRRLRR (j : ℕ) : ℕ := if j < 915 then weightRowLRLRRLRRL j else weightRowLRLRRLRRR j
def weightRowLRLRRLR (j : ℕ) : ℕ := if j < 910 then weightRowLRLRRLRL j else weightRowLRLRRLRR j
def weightRowLRLRRL (j : ℕ) : ℕ := if j < 900 then weightRowLRLRRLL j else weightRowLRLRRLR j
def weightRowLRLRRRLLLL (j : ℕ) : ℕ := if j < 921 then 1000001244221665 else 999972631796740
def weightRowLRLRRRLLLRR (j : ℕ) : ℕ := if j < 924 then 999916420770099 else 999888854297869
def weightRowLRLRRRLLLR (j : ℕ) : ℕ := if j < 923 then 999944351916310 else weightRowLRLRRRLLLRR j
def weightRowLRLRRRLLL (j : ℕ) : ℕ := if j < 922 then weightRowLRLRRRLLLL j else weightRowLRLRRRLLLR j
def weightRowLRLRRRLLRL (j : ℕ) : ℕ := if j < 926 then 999861668184114 else 999834877852706
def weightRowLRLRRRLLRRR (j : ℕ) : ℕ := if j < 929 then 999782544896743 else 999757031767789
def weightRowLRLRRRLLRR (j : ℕ) : ℕ := if j < 928 then 999808498461475 else weightRowLRLRRRLLRRR j
def weightRowLRLRRRLLR (j : ℕ) : ℕ := if j < 927 then weightRowLRLRRRLLRL j else weightRowLRLRRRLLRR j
def weightRowLRLRRRLL (j : ℕ) : ℕ := if j < 925 then weightRowLRLRRRLLL j else weightRowLRLRRRLLR j
def weightRowLRLRRRLRLL (j : ℕ) : ℕ := if j < 931 then 999731973401266 else 999707383835553
def weightRowLRLRRRLRLRR (j : ℕ) : ℕ := if j < 934 then 999659665784416 else 999636563882740
def weightRowLRLRRRLRLR (j : ℕ) : ℕ := if j < 933 then 999683276815051 else weightRowLRLRRRLRLRR j
def weightRowLRLRRRLRL (j : ℕ) : ℕ := if j < 932 then weightRowLRLRRRLRLL j else weightRowLRLRRRLRLR j
def weightRowLRLRRRLRRL (j : ℕ) : ℕ := if j < 936 then 999613983937661 else 999591938459420
def weightRowLRLRRRLRRRR (j : ℕ) : ℕ := if j < 939 then 999549499321333 else 999529129040613
def weightRowLRLRRRLRRR (j : ℕ) : ℕ := if j < 938 then 999570439634856 else weightRowLRLRRRLRRRR j
def weightRowLRLRRRLRR (j : ℕ) : ℕ := if j < 937 then weightRowLRLRRRLRRL j else weightRowLRLRRRLRRR j
def weightRowLRLRRRLR (j : ℕ) : ℕ := if j < 935 then weightRowLRLRRRLRL j else weightRowLRLRRRLRR j
def weightRowLRLRRRL (j : ℕ) : ℕ := if j < 930 then weightRowLRLRRRLL j else weightRowLRLRRRLR j
def weightRowLRLRRRRLLL (j : ℕ) : ℕ := if j < 941 then 999509339972659 else 999490142949379
def weightRowLRLRRRRLLRR (j : ℕ) : ℕ := if j < 944 then 999453566586210 else 999436207112651
def weightRowLRLRRRRLLR (j : ℕ) : ℕ := if j < 943 then 999471548448305 else weightRowLRLRRRRLLRR j
def weightRowLRLRRRRLL (j : ℕ) : ℕ := if j < 942 then weightRowLRLRRRRLLL j else weightRowLRLRRRRLLR j
def weightRowLRLRRRRLRL (j : ℕ) : ℕ := if j < 946 then 999419479403459 else 999403392454157
def weightRowLRLRRRRLRRR (j : ℕ) : ℕ := if j < 949 then 999373174875802 else 999359060276077
def weightRowLRLRRRRLRR (j : ℕ) : ℕ := if j < 948 then 999387954873307 else weightRowLRLRRRRLRRR j
def weightRowLRLRRRRLR (j : ℕ) : ℕ := if j < 947 then weightRowLRLRRRRLRL j else weightRowLRLRRRRLRR j
def weightRowLRLRRRRL (j : ℕ) : ℕ := if j < 945 then weightRowLRLRRRRLL j else weightRowLRLRRRRLR j
def weightRowLRLRRRRRLL (j : ℕ) : ℕ := if j < 951 then 999345618481262 else 999332856484262
def weightRowLRLRRRRRLRR (j : ℕ) : ℕ := if j < 954 then 999309397742201 else 999298712848578
def weightRowLRLRRRRRLR (j : ℕ) : ℕ := if j < 953 then 999320780856768 else weightRowLRLRRRRRLRR j
def weightRowLRLRRRRRL (j : ℕ) : ℕ := if j < 952 then weightRowLRLRRRRRLL j else weightRowLRLRRRRRLR j
def weightRowLRLRRRRRRL (j : ℕ) : ℕ := if j < 956 then 999288731441324 else 999279458335988
def weightRowLRLRRRRRRRR (j : ℕ) : ℕ := if j < 959 then 999263053999817 else 999255930084299
def weightRowLRLRRRRRRR (j : ℕ) : ℕ := if j < 958 then 999270897890914 else weightRowLRLRRRRRRRR j
def weightRowLRLRRRRRR (j : ℕ) : ℕ := if j < 957 then weightRowLRLRRRRRRL j else weightRowLRLRRRRRRR j
def weightRowLRLRRRRR (j : ℕ) : ℕ := if j < 955 then weightRowLRLRRRRRL j else weightRowLRLRRRRRR j
def weightRowLRLRRRR (j : ℕ) : ℕ := if j < 950 then weightRowLRLRRRRL j else weightRowLRLRRRRR j
def weightRowLRLRRR (j : ℕ) : ℕ := if j < 940 then weightRowLRLRRRL j else weightRowLRLRRRR j
def weightRowLRLRR (j : ℕ) : ℕ := if j < 920 then weightRowLRLRRL j else weightRowLRLRRR j
def weightRowLRLR (j : ℕ) : ℕ := if j < 880 then weightRowLRLRL j else weightRowLRLRR j
def weightRowLRL (j : ℕ) : ℕ := if j < 800 then weightRowLRLL j else weightRowLRLR j
def weightRowLRRLLLLLLL (j : ℕ) : ℕ := if j < 961 then 999249529086288 else 999243853460404
def weightRowLRRLLLLLLRR (j : ℕ) : ℕ := if j < 964 then 999234685660599 else 999231195889600
def weightRowLRRLLLLLLR (j : ℕ) : ℕ := if j < 963 then 999238905166243 else weightRowLRRLLLLLLRR j
def weightRowLRRLLLLLL (j : ℕ) : ℕ := if j < 962 then weightRowLRRLLLLLLL j else weightRowLRRLLLLLLR j
def weightRowLRRLLLLLRL (j : ℕ) : ℕ := if j < 966 then 999228436280767 else 999226406735003
def weightRowLRRLLLLLRRR (j : ℕ) : ℕ := if j < 969 then 999224534754566 else 999224689415377
def weightRowLRRLLLLLRR (j : ℕ) : ℕ := if j < 968 then 999225106618500 else weightRowLRRLLLLLRRR j
def weightRowLRRLLLLLR (j : ℕ) : ℕ := if j < 967 then weightRowLRRLLLLLRL j else weightRowLRRLLLLLRR j
def weightRowLRRLLLLL (j : ℕ) : ℕ := if j < 965 then weightRowLRRLLLLLL j else weightRowLRRLLLLLR j
def weightRowLRRLLLLRLL (j : ℕ) : ℕ := if j < 971 then 999225568313647 else 999227168594218
def weightRowLRRLLLLRLRR (j : ℕ) : ℕ := if j < 974 then 999232518991255 else 999236260481230
def weightRowLRRLLLLRLR (j : ℕ) : ℕ := if j < 973 then 999229486825572 else weightRowLRRLLLLRLRR j
def weightRowLRRLLLLRL (j : ℕ) : ℕ := if j < 972 then weightRowLRRLLLLRLL j else weightRowLRRLLLLRLR j
def weightRowLRRLLLLRRL (j : ℕ) : ℕ := if j < 976 then 999240706083134 else 999245849973462
def weightRowLRRLLLLRRRR (j : ℕ) : ℕ := if j < 979 then 999258206216149 else 999265403785231
def weightRowLRRLLLLRRR (j : ℕ) : ℕ := if j < 978 then 999251685708662 else weightRowLRRLLLLRRRR j
def weightRowLRRLLLLRR (j : ℕ) : ℕ := if j < 977 then weightRowLRRLLLLRRL j else weightRowLRRLLLLRRR j
def weightRowLRRLLLLR (j : ℕ) : ℕ := if j < 975 then weightRowLRRLLLLRL j else weightRowLRRLLLLRR j
def weightRowLRRLLLL (j : ℕ) : ℕ := if j < 970 then weightRowLRRLLLLL j else weightRowLRRLLLLR j
def weightRowLRRLLLRLLL (j : ℕ) : ℕ := if j < 981 then 999273270057947 else 999281796019826
def weightRowLRRLLLRLLRR (j : ℕ) : ℕ := if j < 984 then 999300787614536 else 999311231851424
def weightRowLRRLLLRLLR (j : ℕ) : ℕ := if j < 983 then 999290971990550 else weightRowLRRLLLRLLRR j
def weightRowLRRLLLRLL (j : ℕ) : ℕ := if j < 982 then weightRowLRRLLLRLLL j else weightRowLRRLLLRLLR j
def weightRowLRRLLLRLRL (j : ℕ) : ℕ := if j < 986 then 999322292966483 else 999333958520916
def weightRowLRRLLLRLRRR (j : ℕ) : ℕ := if j < 989 then 999359049613649 else 999372446665577
def weightRowLRRLLLRLRR (j : ℕ) : ℕ := if j < 988 then 999346215362088 else weightRowLRRLLLRLRRR j
def weightRowLRRLLLRLR (j : ℕ) : ℕ := if j < 987 then weightRowLRRLLLRLRL j else weightRowLRRLLLRLRR j
def weightRowLRRLLLRL (j : ℕ) : ℕ := if j < 985 then weightRowLRRLLLRLL j else weightRowLRRLLLRLR j
def weightRowLRRLLLRRLL (j : ℕ) : ℕ := if j < 991 then 999386391164120 else 999400867001650
def weightRowLRRLLLRRLRR (j : ℕ) : ℕ := if j < 994 then 999431344432216 else 999447309947950
def weightRowLRRLLLRRLR (j : ℕ) : ℕ := if j < 993 then 999415857306417 else weightRowLRRLLLRRLRR j
def weightRowLRRLLLRRL (j : ℕ) : ℕ := if j < 992 then weightRowLRRLLLRRLL j else weightRowLRRLLLRRLR j
def weightRowLRRLLLRRRL (j : ℕ) : ℕ := if j < 996 then 999463734627105 else 999480598437120
def weightRowLRRLLLRRRRR (j : ℕ) : ℕ := if j < 999 then 999515559224823 else 999533612010160
def weightRowLRRLLLRRRR (j : ℕ) : ℕ := if j < 998 then 999497880528666 else weightRowLRRLLLRRRRR j
def weightRowLRRLLLRRR (j : ℕ) : ℕ := if j < 997 then weightRowLRRLLLRRRL j else weightRowLRRLLLRRRR j
def weightRowLRRLLLRR (j : ℕ) : ℕ := if j < 995 then weightRowLRRLLLRRL j else weightRowLRRLLLRRR j
def weightRowLRRLLLR (j : ℕ) : ℕ := if j < 990 then weightRowLRRLLLRL j else weightRowLRRLLLRR j
def weightRowLRRLLL (j : ℕ) : ℕ := if j < 980 then weightRowLRRLLLL j else weightRowLRRLLLR j
def weightRowLRRLLRLLLL (j : ℕ) : ℕ := if j < 1001 then 999552015519708 else 999570745527847
def weightRowLRRLLRLLLRR (j : ℕ) : ℕ := if j < 1004 then 999609083766684 else 999628639141333
def weightRowLRRLLRLLLR (j : ℕ) : ℕ := if j < 1003 then 999589776937075 else weightRowLRRLLRLLLRR j
def weightRowLRRLLRLLL (j : ℕ) : ℕ := if j < 1002 then weightRowLRRLLRLLLL j else weightRowLRRLLRLLLR j
def weightRowLRRLLRLLRL (j : ℕ) : ℕ := if j < 1006 then 999648415279515 else 999668383481919
def weightRowLRRLLRLLRRR (j : ℕ) : ℕ := if j < 1009 then 999708776622566 else 999729139466954
def weightRowLRRLLRLLRR (j : ℕ) : ℕ := if j < 1008 then 999688514119686 else weightRowLRRLLRLLRRR j
def weightRowLRRLLRLLR (j : ℕ) : ℕ := if j < 1007 then weightRowLRRLLRLLRL j else weightRowLRRLLRLLRR j
def weightRowLRRLLRLL (j : ℕ) : ℕ := if j < 1005 then weightRowLRRLLRLLL j else weightRowLRRLLRLLR j
def weightRowLRRLLRLRLL (j : ℕ) : ℕ := if j < 1011 then 999749570163836 else 999770035246610
def weightRowLRRLLRLRLRR (j : ℕ) : ℕ := if j < 1014 then 999810929741707 else 999831287221820
def weightRowLRRLLRLRLR (j : ℕ) : ℕ := if j < 1013 then 999790500258809 else weightRowLRRLLRLRLRR j
def weightRowLRRLLRLRL (j : ℕ) : ℕ := if j < 1012 then weightRowLRRLLRLRLL j else weightRowLRRLLRLRLR j
def weightRowLRRLLRLRRL (j : ℕ) : ℕ := if j < 1016 then 999851535198289 else 999871635130155
def weightRowLRRLLRLRRRR (j : ℕ) : ℕ := if j < 1019 then 999911231418580 else 999930645376583
def weightRowLRRLLRLRRR (j : ℕ) : ℕ := if j < 1018 then 999891547423517 else weightRowLRRLLRLRRRR j
def weightRowLRRLLRLRR (j : ℕ) : ℕ := if j < 1017 then weightRowLRRLLRLRRL j else weightRowLRRLLRLRRR j
def weightRowLRRLLRLR (j : ℕ) : ℕ := if j < 1015 then weightRowLRRLLRLRL j else weightRowLRRLLRLRR j
def weightRowLRRLLRL (j : ℕ) : ℕ := if j < 1010 then weightRowLRRLLRLL j else weightRowLRRLLRLR j
def weightRowLRRLLRRLLL (j : ℕ) : ℕ := if j < 1021 then 999949746466616 else 999968490752312
def weightRowLRRLLRRLLRR (j : ℕ) : ℕ := if j < 1024 then 1000004727557333 else 1000022126555283
def weightRowLRRLLRRLLR (j : ℕ) : ℕ := if j < 1023 then 999986833178435 else weightRowLRRLLRRLLRR j
def weightRowLRRLLRRLL (j : ℕ) : ℕ := if j < 1022 then weightRowLRRLLRRLLL j else weightRowLRRLLRRLLR j
def weightRowLRRLLRRLRL (j : ℕ) : ℕ := if j < 1026 then 1000038981678713 else 1000055243260300
def weightRowLRRLLRRLRRR (j : ℕ) : ℕ := if j < 1029 then 1000086021694243 else 1000100556411131
def weightRowLRRLLRRLRR (j : ℕ) : ℕ := if j < 1028 then 1000070920282422 else weightRowLRRLLRRLRRR j
def weightRowLRRLLRRLR (j : ℕ) : ℕ := if j < 1027 then weightRowLRRLLRRLRL j else weightRowLRRLLRRLRR j
def weightRowLRRLLRRL (j : ℕ) : ℕ := if j < 1025 then weightRowLRRLLRRLL j else weightRowLRRLLRRLR j
def weightRowLRRLLRRRLL (j : ℕ) : ℕ := if j < 1031 then 1000114533314092 else 1000127961249192
def weightRowLRRLLRRRLRR (j : ℕ) : ℕ := if j < 1034 then 1000153205421933 else 1000165039171845
def weightRowLRRLLRRRLR (j : ℕ) : ℕ := if j < 1033 then 1000140849026984 else weightRowLRRLLRRRLRR j
def weightRowLRRLLRRRL (j : ℕ) : ℕ := if j < 1032 then weightRowLRRLLRRRLL j else weightRowLRRLLRRRLR j
def weightRowLRRLLRRRRL (j : ℕ) : ℕ := if j < 1036 then 1000176358977293 else 1000187173501040
def weightRowLRRLLRRRRRR (j : ℕ) : ℕ := if j < 1039 then 1000207321162024 else 1000216671430603
def weightRowLRRLLRRRRR (j : ℕ) : ℕ := if j < 1038 then 1000197491367473 else weightRowLRRLLRRRRRR j
def weightRowLRRLLRRRR (j : ℕ) : ℕ := if j < 1037 then weightRowLRRLLRRRRL j else weightRowLRRLLRRRRR j
def weightRowLRRLLRRR (j : ℕ) : ℕ := if j < 1035 then weightRowLRRLLRRRL j else weightRowLRRLLRRRR j
def weightRowLRRLLRR (j : ℕ) : ℕ := if j < 1030 then weightRowLRRLLRRL j else weightRowLRRLLRRR j
def weightRowLRRLLR (j : ℕ) : ℕ := if j < 1020 then weightRowLRRLLRL j else weightRowLRRLLRR j
def weightRowLRRLL (j : ℕ) : ℕ := if j < 1000 then weightRowLRRLLL j else weightRowLRRLLR j
def weightRowLRRLRLLLLL (j : ℕ) : ℕ := if j < 1041 then 1000225550679023 else 1000233967372430
def weightRowLRRLRLLLLRR (j : ℕ) : ℕ := if j < 1044 then 1000249446748044 else 1000256526152084
def weightRowLRRLRLLLLR (j : ℕ) : ℕ := if j < 1043 then 1000241929934736 else weightRowLRRLRLLLLRR j
def weightRowLRRLRLLLL (j : ℕ) : ℕ := if j < 1042 then weightRowLRRLRLLLLL j else weightRowLRRLRLLLLR j
def weightRowLRRLRLLLRL (j : ℕ) : ℕ := if j < 1046 then 1000263176443642 else 1000269405875994
def weightRowLRRLRLLLRRR (j : ℕ) : ℕ := if j < 1049 then 1000280634955239 else 1000285650886046
def weightRowLRRLRLLLRR (j : ℕ) : ℕ := if j < 1048 then 1000275222658340 else weightRowLRRLRLLLRRR j
def weightRowLRRLRLLLR (j : ℕ) : ℕ := if j < 1047 then weightRowLRRLRLLLRL j else weightRowLRRLRLLLRR j
def weightRowLRRLRLLL (j : ℕ) : ℕ := if j < 1045 then weightRowLRRLRLLLL j else weightRowLRRLRLLLR j
def weightRowLRRLRLLRLL (j : ℕ) : ℕ := if j < 1051 then 1000290278524348 else 1000294525897402
def weightRowLRRLRLLRLRR (j : ℕ) : ℕ := if j < 1054 then 1000301911721793 else 1000305065990966
def weightRowLRRLRLLRLR (j : ℕ) : ℕ := if j < 1053 then 1000298400985576 else weightRowLRRLRLLRLRR j
def weightRowLRRLRLLRL (j : ℕ) : ℕ := if j < 1052 then weightRowLRRLRLLRLL j else weightRowLRRLRLLRLR j
def weightRowLRRLRLLRRL (j : ℕ) : ℕ := if j < 1056 then 1000307871629451 else 1000310336424489
def weightRowLRRLRLLRRRR (j : ℕ) : ℕ := if j < 1059 then 1000314274384294 else 1000315762873008
def weightRowLRRLRLLRRR (j : ℕ) : ℕ := if j < 1058 then 1000312468113651 else weightRowLRRLRLLRRRR j
def weightRowLRRLRLLRR (j : ℕ) : ℕ := if j < 1057 then weightRowLRRLRLLRRL j else weightRowLRRLRLLRRR j
def weightRowLRRLRLLR (j : ℕ) : ℕ := if j < 1055 then weightRowLRRLRLLRL j else weightRowLRRLRLLRR j
def weightRowLRRLRLL (j : ℕ) : ℕ := if j < 1050 then weightRowLRRLRLLL j else weightRowLRRLRLLR j
def weightRowLRRLRLRLLL (j : ℕ) : ℕ := if j < 1061 then 1000316941165067 else 1000317816793893
def weightRowLRRLRLRLLRR (j : ℕ) : ℕ := if j < 1064 then 1000318689932976 else 1000318702245913
def weightRowLRRLRLRLLR (j : ℕ) : ℕ := if j < 1063 then 1000318397240503 else weightRowLRRLRLRLLRR j
def weightRowLRRLRLRLL (j : ℕ) : ℕ := if j < 1062 then weightRowLRRLRLRLLL j else weightRowLRRLRLRLLR j
def weightRowLRRLRLRLRL (j : ℕ) : ℕ := if j < 1066 then 1000318441499900 else 1000317914960977
def weightRowLRRLRLRLRRR (j : ℕ) : ℕ := if j < 1069 then 1000316093292642 else 1000314812417812
def weightRowLRRLRLRLRR (j : ℕ) : ℕ := if j < 1068 then 1000317129840106 else weightRowLRRLRLRLRRR j
def weightRowLRRLRLRLR (j : ℕ) : ℕ := if j < 1067 then weightRowLRRLRLRLRL j else weightRowLRRLRLRLRR j
def weightRowLRRLRLRL (j : ℕ) : ℕ := if j < 1065 then weightRowLRRLRLRLL j else weightRowLRRLRLRLR j
def weightRowLRRLRLRRLL (j : ℕ) : ℕ := if j < 1071 then 1000313294258187 else 1000311545799168
def weightRowLRRLRLRRLRR (j : ℕ) : ℕ := if j < 1074 then 1000307385635589 else 1000304987611333
def weightRowLRRLRLRRLR (j : ℕ) : ℕ := if j < 1073 then 1000309573968466 else weightRowLRRLRLRRLRR j
def weightRowLRRLRLRRL (j : ℕ) : ℕ := if j < 1072 then weightRowLRRLRLRRLL j else weightRowLRRLRLRRLR j
def weightRowLRRLRLRRRL (j : ℕ) : ℕ := if j < 1076 then 1000302386647276 else 1000299589435272
def weightRowLRRLRLRRRRR (j : ℕ) : ℕ := if j < 1079 then 1000293432733237 else 1000290086323822
def weightRowLRRLRLRRRR (j : ℕ) : ℕ := if j < 1078 then 1000296602606955 else weightRowLRRLRLRRRRR j
def weightRowLRRLRLRRR (j : ℕ) : ℕ := if j < 1077 then weightRowLRRLRLRRRL j else weightRowLRRLRLRRRR j
def weightRowLRRLRLRR (j : ℕ) : ℕ := if j < 1075 then weightRowLRRLRLRRL j else weightRowLRRLRLRRR j
def weightRowLRRLRLR (j : ℕ) : ℕ := if j < 1070 then weightRowLRRLRLRL j else weightRowLRRLRLRR j
def weightRowLRRLRL (j : ℕ) : ℕ := if j < 1060 then weightRowLRRLRLL j else weightRowLRRLRLR j
def weightRowLRRLRRLLLL (j : ℕ) : ℕ := if j < 1081 then 1000286569826714 else 1000282889627731
def weightRowLRRLRRLLLRR (j : ℕ) : ℕ := if j < 1084 then 1000275063353617 else 1000270929734897
def weightRowLRRLRRLLLR (j : ℕ) : ℕ := if j < 1083 then 1000279052050028 else weightRowLRRLRRLLLRR j
def weightRowLRRLRRLLL (j : ℕ) : ℕ := if j < 1082 then weightRowLRRLRRLLLL j else weightRowLRRLRRLLLR j
def weightRowLRRLRRLLRL (j : ℕ) : ℕ := if j < 1086 then 1000266657326183 else 1000262252195248
def weightRowLRRLRRLLRRR (j : ℕ) : ℕ := if j < 1089 then 1000253067712322 else 1000248300169042
def weightRowLRRLRRLLRR (j : ℕ) : ℕ := if j < 1088 then 1000257720344858 else weightRowLRRLRRLLRRR j
def weightRowLRRLRRLLR (j : ℕ) : ℕ := if j < 1087 then weightRowLRRLRRLLRL j else weightRowLRRLRRLLRR j
def weightRowLRRLRRLL (j : ℕ) : ℕ := if j < 1085 then weightRowLRRLRRLLL j else weightRowLRRLRRLLR j
def weightRowLRRLRRLRLL (j : ℕ) : ℕ := if j < 1091 then 1000243423520066 else 1000238443503652
def weightRowLRRLRRLRLRR (j : ℕ) : ℕ := if j < 1094 then 1000228195984986 else 1000222939621411
def weightRowLRRLRRLRLR (j : ℕ) : ℕ := if j < 1093 then 1000233365790833 else weightRowLRRLRRLRLRR j
def weightRowLRRLRRLRL (j : ℕ) : ℕ := if j < 1092 then weightRowLRRLRRLRLL j else weightRowLRRLRRLRLR j
def weightRowLRRLRRLRRL (j : ℕ) : ℕ := if j < 1096 then 1000217602166912 else 1000212189019386
def weightRowLRRLRRLRRRR (j : ℕ) : ℕ := if j < 1099 then 1000201156889866 else 1000195548355498
def weightRowLRRLRRLRRR (j : ℕ) : ℕ := if j < 1098 then 1000206705507415 else weightRowLRRLRRLRRRR j
def weightRowLRRLRRLRR (j : ℕ) : ℕ := if j < 1097 then weightRowLRRLRRLRRL j else weightRowLRRLRRLRRR j
def weightRowLRRLRRLR (j : ℕ) : ℕ := if j < 1095 then weightRowLRRLRRLRL j else weightRowLRRLRRLRR j
def weightRowLRRLRRL (j : ℕ) : ℕ := if j < 1090 then weightRowLRRLRRLL j else weightRowLRRLRRLR j
def weightRowLRRLRRRLLL (j : ℕ) : ℕ := if j < 1101 then 1000189885022572 else 1000184171938469
def weightRowLRRLRRRLLRR (j : ℕ) : ℕ := if j < 1104 then 1000172616349616 else 1000166783581888
def weightRowLRRLRRRLLR (j : ℕ) : ℕ := if j < 1103 then 1000178414079316 else weightRowLRRLRRRLLRR j
def weightRowLRRLRRRLL (j : ℕ) : ℕ := if j < 1102 then weightRowLRRLRRRLLL j else weightRowLRRLRRRLLR j
def weightRowLRRLRRRLRL (j : ℕ) : ℕ := if j < 1106 then 1000160920536309 else 1000155031900367
def weightRowLRRLRRRLRRR (j : ℕ) : ℕ := if j < 1109 then 1000143196241862 else 1000137258227799
def weightRowLRRLRRRLRR (j : ℕ) : ℕ := if j < 1108 then 1000149122288520 else weightRowLRRLRRRLRRR j
def weightRowLRRLRRRLR (j : ℕ) : ℕ := if j < 1107 then weightRowLRRLRRRLRL j else weightRowLRRLRRRLRR j
def weightRowLRRLRRRL (j : ℕ) : ℕ := if j < 1105 then weightRowLRRLRRRLL j else weightRowLRRLRRRLR j
def weightRowLRRLRRRRLL (j : ℕ) : ℕ := if j < 1111 then 1000131312639724 else 1000125363796716
def weightRowLRRLRRRRLRR (j : ℕ) : ℕ := if j < 1114 then 1000113473248790 else 1000107539807740
def weightRowLRRLRRRRLR (j : ℕ) : ℕ := if j < 1113 then 1000119415943226 else weightRowLRRLRRRRLRR j
def weightRowLRRLRRRRL (j : ℕ) : ℕ := if j < 1112 then weightRowLRRLRRRRLL j else weightRowLRRLRRRRLR j
def weightRowLRRLRRRRRL (j : ℕ) : ℕ := if j < 1116 then 1000101619638924 else 1000095716685437
def weightRowLRRLRRRRRRR (j : ℕ) : ℕ := if j < 1119 then 1000083977816510 else 1000078149406189
def weightRowLRRLRRRRRR (j : ℕ) : ℕ := if j < 1118 then 1000089834814361 else weightRowLRRLRRRRRRR j
def weightRowLRRLRRRRR (j : ℕ) : ℕ := if j < 1117 then weightRowLRRLRRRRRL j else weightRowLRRLRRRRRR j
def weightRowLRRLRRRR (j : ℕ) : ℕ := if j < 1115 then weightRowLRRLRRRRL j else weightRowLRRLRRRRR j
def weightRowLRRLRRR (j : ℕ) : ℕ := if j < 1110 then weightRowLRRLRRRL j else weightRowLRRLRRRR j
def weightRowLRRLRR (j : ℕ) : ℕ := if j < 1100 then weightRowLRRLRRL j else weightRowLRRLRRR j
def weightRowLRRLR (j : ℕ) : ℕ := if j < 1080 then weightRowLRRLRL j else weightRowLRRLRR j
def weightRowLRRL (j : ℕ) : ℕ := if j < 1040 then weightRowLRRLL j else weightRowLRRLR j
def weightRowLRRRLLLLLL (j : ℕ) : ℕ := if j < 1121 then 1000072353220959 else 1000066592821411
def weightRowLRRRLLLLLRR (j : ℕ) : ℕ := if j < 1124 then 1000055193235603 else 1000049560783790
def weightRowLRRRLLLLLR (j : ℕ) : ℕ := if j < 1123 then 1000060871690954 else weightRowLRRRLLLLLRR j
def weightRowLRRRLLLLL (j : ℕ) : ℕ := if j < 1122 then weightRowLRRRLLLLLL j else weightRowLRRRLLLLLR j
def weightRowLRRRLLLLRL (j : ℕ) : ℕ := if j < 1126 then 1000043977586173 else 1000038446815463
def weightRowLRRRLLLLRRR (j : ℕ) : ℕ := if j < 1129 then 1000027554854890 else 1000022199619273
def weightRowLRRRLLLLRR (j : ℕ) : ℕ := if j < 1128 then 1000032971566259 else weightRowLRRRLLLLRRR j
def weightRowLRRRLLLLR (j : ℕ) : ℕ := if j < 1127 then weightRowLRRRLLLLRL j else weightRowLRRRLLLLRR j
def weightRowLRRRLLLL (j : ℕ) : ℕ := if j < 1125 then weightRowLRRRLLLLL j else weightRowLRRRLLLLR j
def weightRowLRRRLLLRLL (j : ℕ) : ℕ := if j < 1131 then 1000016908718783 else 1000011684934124
def weightRowLRRRLLLRLRR (j : ℕ) : ℕ := if j < 1134 then 1000001449441130 else 999996442899930
def weightRowLRRRLLLRLR (j : ℕ) : ℕ := if j < 1133 then 1000006530967222 else weightRowLRRRLLLRLRR j
def weightRowLRRRLLLRL (j : ℕ) : ℕ := if j < 1132 then weightRowLRRRLLLRLL j else weightRowLRRRLLLRLR j
def weightRowLRRRLLLRRL (j : ℕ) : ℕ := if j < 1136 then 999991513808667 else 999986664553280
def weightRowLRRRLLLRRRR (j : ℕ) : ℕ := if j < 1139 then 999977214698068 else 999972618474196
def weightRowLRRRLLLRRR (j : ℕ) : ℕ := if j < 1138 then 999981897440551 else weightRowLRRRLLLRRRR j
def weightRowLRRRLLLRR (j : ℕ) : ℕ := if j < 1137 then weightRowLRRRLLLRRL j else weightRowLRRRLLLRRR j
def weightRowLRRRLLLR (j : ℕ) : ℕ := if j < 1135 then weightRowLRRRLLLRL j else weightRowLRRRLLLRR j
def weightRowLRRRLLL (j : ℕ) : ℕ := if j < 1130 then weightRowLRRRLLLL j else weightRowLRRRLLLR j
def weightRowLRRRLLRLLL (j : ℕ) : ℕ := if j < 1141 then 999968110838066 else 999963693779572
def weightRowLRRRLLRLLRR (j : ℕ) : ℕ := if j < 1144 then 999955138958975 else 999951004780661
def weightRowLRRRLLRLLR (j : ℕ) : ℕ := if j < 1143 then 999959369209383 else weightRowLRRRLLRLLRR j
def weightRowLRRRLLRLL (j : ℕ) : ℕ := if j < 1142 then weightRowLRRRLLRLLL j else weightRowLRRRLLRLLR j
def weightRowLRRRLLRLRL (j : ℕ) : ℕ := if j < 1146 then 999946968347656 else 999943031254136
def weightRowLRRRLLRLRRR (j : ℕ) : ℕ := if j < 1149 then 999935461067585 else 999931830768542
def weightRowLRRRLLRLRR (j : ℕ) : ℕ := if j < 1148 then 999939195015324 else weightRowLRRRLLRLRRR j
def weightRowLRRRLLRLR (j : ℕ) : ℕ := if j < 1147 then weightRowLRRRLLRLRL j else weightRowLRRRLLRLRR j
def weightRowLRRRLLRL (j : ℕ) : ℕ := if j < 1145 then weightRowLRRRLLRLL j else weightRowLRRRLLRLR j
def weightRowLRRRLLRRLL (j : ℕ) : ℕ := if j < 1151 then 999928305397194 else 999924886154068
def weightRowLRRRLLRRLRR (j : ℕ) : ℕ := if j < 1154 then 999918370463148 else 999915276025509
def weightRowLRRRLLRRLR (j : ℕ) : ℕ := if j < 1153 then 999921574161367 else weightRowLRRRLLRRLRR j
def weightRowLRRRLLRRL (j : ℕ) : ℕ := if j < 1152 then weightRowLRRRLLRRLL j else weightRowLRRRLLRRLR j
def weightRowLRRRLLRRRL (j : ℕ) : ℕ := if j < 1156 then 999912291736795 else 999909418407819
def weightRowLRRRLLRRRRR (j : ℕ) : ℕ := if j < 1159 then 999904007486110 else 999901471129565
def weightRowLRRRLLRRRR (j : ℕ) : ℕ := if j < 1158 then 999906656772098 else weightRowLRRRLLRRRRR j
def weightRowLRRRLLRRR (j : ℕ) : ℕ := if j < 1157 then weightRowLRRRLLRRRL j else weightRowLRRRLLRRRR j
def weightRowLRRRLLRR (j : ℕ) : ℕ := if j < 1155 then weightRowLRRRLLRRL j else weightRowLRRRLLRRR j
def weightRowLRRRLLR (j : ℕ) : ℕ := if j < 1150 then weightRowLRRRLLRL j else weightRowLRRRLLRR j
def weightRowLRRRLL (j : ℕ) : ℕ := if j < 1140 then weightRowLRRRLLL j else weightRowLRRRLLR j
def weightRowLRRRLRLLLL (j : ℕ) : ℕ := if j < 1161 then 999899048205696 else 999896739141562
def weightRowLRRRLRLLLRR (j : ℕ) : ℕ := if j < 1164 then 999892463921850 else 999890498242548
def weightRowLRRRLRLLLR (j : ℕ) : ℕ := if j < 1163 then 999894544288377 else weightRowLRRRLRLLLRR j
def weightRowLRRRLRLLL (j : ℕ) : ℕ := if j < 1162 then weightRowLRRRLRLLLL j else weightRowLRRRLRLLLR j
def weightRowLRRRLRLLRL (j : ℕ) : ℕ := if j < 1166 then 999888647376277 else 999886911374475
def weightRowLRRRLRLLRRR (j : ℕ) : ℕ := if j < 1169 then 999883783800754 else 999882391963757
def weightRowLRRRLRLLRR (j : ℕ) : ℕ := if j < 1168 then 999885290214638 else weightRowLRRRLRLLRRR j
def weightRowLRRRLRLLR (j : ℕ) : ℕ := if j < 1167 then weightRowLRRRLRLLRL j else weightRowLRRRLRLLRR j
def weightRowLRRRLRLL (j : ℕ) : ℕ := if j < 1165 then weightRowLRRRLRLLL j else weightRowLRRRLRLLR j
def weightRowLRRRLRLRLL (j : ℕ) : ℕ := if j < 1171 then 999881114462010 else 999879950981799
def weightRowLRRRLRLRLRR (j : ℕ) : ℕ := if j < 1174 then 999877964473878 else 999877140463126
def weightRowLRRRLRLRLR (j : ℕ) : ℕ := if j < 1173 then 999878901137852 else weightRowLRRRLRLRLRR j
def weightRowLRRRLRLRL (j : ℕ) : ℕ := if j < 1172 then weightRowLRRRLRLRLL j else weightRowLRRRLRLRLR j
def weightRowLRRRLRLRRL (j : ℕ) : ℕ := if j < 1176 then 999876428508967 else 999875827945500
def weightRowLRRRLRLRRRR (j : ℕ) : ℕ := if j < 1179 then 999874957984427 else 999874686914380
def weightRowLRRRLRLRRR (j : ℕ) : ℕ := if j < 1178 then 999875338038171 else weightRowLRRRLRLRRRR j
def weightRowLRRRLRLRR (j : ℕ) : ℕ := if j < 1177 then weightRowLRRRLRLRRL j else weightRowLRRRLRLRRR j
def weightRowLRRRLRLR (j : ℕ) : ℕ := if j < 1175 then weightRowLRRRLRLRL j else weightRowLRRRLRLRR j
def weightRowLRRRLRL (j : ℕ) : ℕ := if j < 1170 then weightRowLRRRLRLL j else weightRowLRRRLRLR j
def weightRowLRRRLRRLLL (j : ℕ) : ℕ := if j < 1181 then 999874523891506 else 999874467913356
def weightRowLRRRLRRLLRR (j : ℕ) : ℕ := if j < 1184 then 999874672756282 else 999874931249621
def weightRowLRRRLRRLLR (j : ℕ) : ℕ := if j < 1183 then 999874517912299 else weightRowLRRRLRRLLRR j
def weightRowLRRRLRRLL (j : ℕ) : ℕ := if j < 1182 then weightRowLRRRLRRLLL j else weightRowLRRRLRRLLR j
def weightRowLRRRLRRLRL (j : ℕ) : ℕ := if j < 1186 then 999875292133812 else 999875754088366
def weightRowLRRRLRRLRRR (j : ℕ) : ℕ := if j < 1189 then 999876975621895 else 999877732257859
def weightRowLRRRLRRLRR (j : ℕ) : ℕ := if j < 1188 then 999876315731675 else weightRowLRRRLRRLRRR j
def weightRowLRRRLRRLR (j : ℕ) : ℕ := if j < 1187 then weightRowLRRRLRRLRL j else weightRowLRRRLRRLRR j
def weightRowLRRRLRRL (j : ℕ) : ℕ := if j < 1185 then weightRowLRRRLRRLL j else weightRowLRRRLRRLR j
def weightRowLRRRLRRRLL (j : ℕ) : ℕ := if j < 1191 then 999878584080021 else 999879529471416
def weightRowLRRRLRRRLRR (j : ℕ) : ℕ := if j < 1194 then 999881694212951 else 999882910051147
def weightRowLRRRLRRRLR (j : ℕ) : ℕ := if j < 1193 then 999880566758658 else weightRowLRRRLRRRLRR j
def weightRowLRRRLRRRL (j : ℕ) : ℕ := if j < 1192 then weightRowLRRRLRRRLL j else weightRowLRRRLRRRLR j
def weightRowLRRRLRRRRL (j : ℕ) : ℕ := if j < 1196 then 999884212436810 else 999885599481327
def weightRowLRRRLRRRRRR (j : ℕ) : ℕ := if j < 1199 then 999888619738375 else 999890248923102
def weightRowLRRRLRRRRR (j : ℕ) : ℕ := if j < 1198 then 999887069245033 else weightRowLRRRLRRRRRR j
def weightRowLRRRLRRRR (j : ℕ) : ℕ := if j < 1197 then weightRowLRRRLRRRRL j else weightRowLRRRLRRRRR j
def weightRowLRRRLRRR (j : ℕ) : ℕ := if j < 1195 then weightRowLRRRLRRRL j else weightRowLRRRLRRRR j
def weightRowLRRRLRR (j : ℕ) : ℕ := if j < 1190 then weightRowLRRRLRRL j else weightRowLRRRLRRR j
def weightRowLRRRLR (j : ℕ) : ℕ := if j < 1180 then weightRowLRRRLRL j else weightRowLRRRLRR j
def weightRowLRRRL (j : ℕ) : ℕ := if j < 1160 then weightRowLRRRLL j else weightRowLRRRLR j
def weightRowLRRRRLLLLL (j : ℕ) : ℕ := if j < 1201 then 999891954713480 else 999893734977546
def weightRowLRRRRLLLLRR (j : ℕ) : ℕ := if j < 1204 then 999897510175430 else 999899500625829
def weightRowLRRRRLLLLR (j : ℕ) : ℕ := if j < 1203 then 999895587538382 else weightRowLRRRRLLLLRR j
def weightRowLRRRRLLLL (j : ℕ) : ℕ := if j < 1202 then weightRowLRRRRLLLLL j else weightRowLRRRRLLLLR j
def weightRowLRRRRLLLRL (j : ℕ) : ℕ := if j < 1206 then 999901556585790 else 999903675712000
def weightRowLRRRRLLLRRR (j : ℕ) : ℕ := if j < 1209 then 999908093900943 else 999910388092522
def weightRowLRRRRLLLRR (j : ℕ) : ℕ := if j < 1208 then 999905855623057 else weightRowLRRRRLLLRRR j
def weightRowLRRRRLLLR (j : ℕ) : ℕ := if j < 1207 then weightRowLRRRRLLLRL j else weightRowLRRRRLLLRR j
def weightRowLRRRRLLL (j : ℕ) : ℕ := if j < 1205 then weightRowLRRRRLLLL j else weightRowLRRRRLLLR j
def weightRowLRRRRLLRLL (j : ℕ) : ℕ := if j < 1211 then 999912735711078 else 999915134237885
def weightRowLRRRRLLRLRR (j : ℕ) : ℕ := if j < 1214 then 999920073790949 else 999922609634308
def weightRowLRRRRLLRLR (j : ℕ) : ℕ := if j < 1213 then 999917581123809 else weightRowLRRRRLLRLRR j
def weightRowLRRRRLLRL (j : ℕ) : ℕ := if j < 1212 then weightRowLRRRRLLRLL j else weightRowLRRRRLLRLR j
def weightRowLRRRRLLRRL (j : ℕ) : ℕ := if j < 1216 then 999925186023505 else 999927800304518
def weightRowLRRRRLLRRRR (j : ℕ) : ℕ := if j < 1219 then 999933131818421 else 999935843641282
def weightRowLRRRRLLRRR (j : ℕ) : ℕ := if j < 1218 then 999930449801464 else weightRowLRRRRLLRRRR j
def weightRowLRRRRLLRR (j : ℕ) : ℕ := if j < 1217 then weightRowLRRRRLLRRL j else weightRowLRRRRLLRRR j
def weightRowLRRRRLLR (j : ℕ) : ℕ := if j < 1215 then weightRowLRRRRLLRL j else weightRowLRRRRLLRR j
def weightRowLRRRRLL (j : ℕ) : ℕ := if j < 1210 then weightRowLRRRRLLL j else weightRowLRRRRLLR j
def weightRowLRRRRLRLLL (j : ℕ) : ℕ := if j < 1221 then 999938582539644 else 999941345768745
def weightRowLRRRRLRLLRR (j : ℕ) : ℕ := if j < 1224 then 999946934180169 else 999949753819082
def weightRowLRRRRLRLLR (j : ℕ) : ℕ := if j < 1223 then 999944130571433 else weightRowLRRRRLRLLRR j
def weightRowLRRRRLRLL (j : ℕ) : ℕ := if j < 1222 then weightRowLRRRRLRLLL j else weightRowLRRRRLRLLR j
def weightRowLRRRRLRLRL (j : ℕ) : ℕ := if j < 1226 then 999952586706052 else 999955430054844
def weightRowLRRRRLRLRRR (j : ℕ) : ℕ := if j < 1229 then 999961136985407 else 999963994993844
def weightRowLRRRRLRLRR (j : ℕ) : ℕ := if j < 1228 then 999958281077271 else weightRowLRRRRLRLRRR j
def weightRowLRRRRLRLR (j : ℕ) : ℕ := if j < 1227 then weightRowLRRRRLRLRL j else weightRowLRRRRLRLRR j
def weightRowLRRRRLRL (j : ℕ) : ℕ := if j < 1225 then weightRowLRRRRLRLL j else weightRowLRRRRLRLR j
def weightRowLRRRRLRRLL (j : ℕ) : ℕ := if j < 1231 then 999966852321979 else 999969706196357
def weightRowLRRRRLRRLRR (j : ℕ) : ℕ := if j < 1234 then 999975392540079 else 999978219519890
def weightRowLRRRRLRRLR (j : ℕ) : ℕ := if j < 1233 then 999972553853050 else weightRowLRRRRLRRLRR j
def weightRowLRRRRLRRL (j : ℕ) : ℕ := if j < 1232 then weightRowLRRRRLRRLL j else weightRowLRRRRLRRLR j
def weightRowLRRRRLRRRL (j : ℕ) : ℕ := if j < 1236 then 999981032071857 else 999983827494852
def weightRowLRRRRLRRRRR (j : ℕ) : ℕ := if j < 1239 then 999989356262535 else 999992084326098
def weightRowLRRRRLRRRR (j : ℕ) : ℕ := if j < 1238 then 999986603109840 else weightRowLRRRRLRRRRR j
def weightRowLRRRRLRRR (j : ℕ) : ℕ := if j < 1237 then weightRowLRRRRLRRRL j else weightRowLRRRRLRRRR j
def weightRowLRRRRLRR (j : ℕ) : ℕ := if j < 1235 then weightRowLRRRRLRRL j else weightRowLRRRRLRRR j
def weightRowLRRRRLR (j : ℕ) : ℕ := if j < 1230 then weightRowLRRRRLRL j else weightRowLRRRRLRR j
def weightRowLRRRRL (j : ℕ) : ℕ := if j < 1220 then weightRowLRRRRLL j else weightRowLRRRRLR j
def weightRowLRRRRRLLLL (j : ℕ) : ℕ := if j < 1241 then 999994784703877 else 999997454832207
def weightRowLRRRRRLLLRR (j : ℕ) : ℕ := if j < 1244 then 1000002694267864 else 1000005258638589
def weightRowLRRRRRLLLR (j : ℕ) : ℕ := if j < 1243 then 1000000092183245 else weightRowLRRRRRLLLRR j
def weightRowLRRRRRLLL (j : ℕ) : ℕ := if j < 1242 then weightRowLRRRRRLLLL j else weightRowLRRRRRLLLR j
def weightRowLRRRRRLLRL (j : ℕ) : ℕ := if j < 1246 then 1000007782892593 else 1000010264674730
def weightRowLRRRRRLLRRR (j : ℕ) : ℕ := if j < 1249 then 1000015091659845 else 1000017432419038
def weightRowLRRRRRLLRR (j : ℕ) : ℕ := if j < 1248 then 1000012701680630 else weightRowLRRRRRLLRRR j
def weightRowLRRRRRLLR (j : ℕ) : ℕ := if j < 1247 then weightRowLRRRRRLLRL j else weightRowLRRRRRLLRR j
def weightRowLRRRRRLL (j : ℕ) : ℕ := if j < 1245 then weightRowLRRRRRLLL j else weightRowLRRRRRLLR j
def weightRowLRRRRRLRLL (j : ℕ) : ℕ := if j < 1251 then 1000019721825237 else 1000021957809132
def weightRowLRRRRRLRLRR (j : ℕ) : ℕ := if j < 1254 then 1000026261571294 else 1000028325559742
def weightRowLRRRRRLRLR (j : ℕ) : ℕ := if j < 1253 then 1000024138368437 else weightRowLRRRRRLRLRR j
def weightRowLRRRRRLRL (j : ℕ) : ℕ := if j < 1252 then weightRowLRRRRRLRLL j else weightRowLRRRRRLRLR j
def weightRowLRRRRRLRRL (j : ℕ) : ℕ := if j < 1256 then 1000030328553238 else 1000032268852234
def weightRowLRRRRRLRRRR (j : ℕ) : ℕ := if j < 1259 then 1000035954995384 else 1000037697878425
def weightRowLRRRRRLRRR (j : ℕ) : ℕ := if j < 1258 then 1000034144841814 else weightRowLRRRRRLRRRR j
def weightRowLRRRRRLRR (j : ℕ) : ℕ := if j < 1257 then weightRowLRRRRRLRRL j else weightRowLRRRRRLRRR j
def weightRowLRRRRRLR (j : ℕ) : ℕ := if j < 1255 then weightRowLRRRRRLRL j else weightRowLRRRRRLRR j
def weightRowLRRRRRL (j : ℕ) : ℕ := if j < 1250 then weightRowLRRRRRLL j else weightRowLRRRRRLR j
def weightRowLRRRRRRLLL (j : ℕ) : ℕ := if j < 1261 then 1000039372152299 else 1000040976578123
def weightRowLRRRRRRLLRR (j : ℕ) : ℕ := if j < 1264 then 1000043971452487 else 1000045359957694
def weightRowLRRRRRRLLR (j : ℕ) : ℕ := if j < 1263 then 1000042510020695 else weightRowLRRRRRRLLRR j
def weightRowLRRRRRRLL (j : ℕ) : ℕ := if j < 1262 then weightRowLRRRRRRLLL j else weightRowLRRRRRRLLR j
def weightRowLRRRRRRLRL (j : ℕ) : ℕ := if j < 1266 then 1000046674736347 else 1000047915108493
def weightRowLRRRRRRLRRR (j : ℕ) : ℕ := if j < 1269 then 1000050170539026 else 1000051184876058
def weightRowLRRRRRRLRR (j : ℕ) : ℕ := if j < 1268 then 1000049080518433 else weightRowLRRRRRRLRRR j
def weightRowLRRRRRRLR (j : ℕ) : ℕ := if j < 1267 then weightRowLRRRRRRLRL j else weightRowLRRRRRRLRR j
def weightRowLRRRRRRL (j : ℕ) : ℕ := if j < 1265 then weightRowLRRRRRRLL j else weightRowLRRRRRRLR j
def weightRowLRRRRRRRLL (j : ℕ) : ℕ := if j < 1271 then 1000052123372676 else 1000052986013891
def weightRowLRRRRRRRLRR (j : ℕ) : ℕ := if j < 1274 then 1000054484406924 else 1000055120879516
def weightRowLRRRRRRRLR (j : ℕ) : ℕ := if j < 1273 then 1000053772931139 else weightRowLRRRRRRRLRR j
def weightRowLRRRRRRRL (j : ℕ) : ℕ := if j < 1272 then weightRowLRRRRRRRLL j else weightRowLRRRRRRRLR j
def weightRowLRRRRRRRRL (j : ℕ) : ℕ := if j < 1276 then 1000055682947722 else 1000056171375735
def weightRowLRRRRRRRRRR (j : ℕ) : ℕ := if j < 1279 then 1000056931224386 else 1000057205044878
def weightRowLRRRRRRRRR (j : ℕ) : ℕ := if j < 1278 then 1000056587098036 else weightRowLRRRRRRRRRR j
def weightRowLRRRRRRRR (j : ℕ) : ℕ := if j < 1277 then weightRowLRRRRRRRRL j else weightRowLRRRRRRRRR j
def weightRowLRRRRRRR (j : ℕ) : ℕ := if j < 1275 then weightRowLRRRRRRRL j else weightRowLRRRRRRRR j
def weightRowLRRRRRR (j : ℕ) : ℕ := if j < 1270 then weightRowLRRRRRRL j else weightRowLRRRRRRR j
def weightRowLRRRRR (j : ℕ) : ℕ := if j < 1260 then weightRowLRRRRRL j else weightRowLRRRRRR j
def weightRowLRRRR (j : ℕ) : ℕ := if j < 1240 then weightRowLRRRRL j else weightRowLRRRRR j
def weightRowLRRR (j : ℕ) : ℕ := if j < 1200 then weightRowLRRRL j else weightRowLRRRR j
def weightRowLRR (j : ℕ) : ℕ := if j < 1120 then weightRowLRRL j else weightRowLRRR j
def weightRowLR (j : ℕ) : ℕ := if j < 960 then weightRowLRL j else weightRowLRR j
def weightRowL (j : ℕ) : ℕ := if j < 640 then weightRowLL j else weightRowLR j
def weightRowRLLLLLLLLL (j : ℕ) : ℕ := if j < 1281 then 1000057410035064 else 1000057547861157
def weightRowRLLLLLLLLRR (j : ℕ) : ℕ := if j < 1284 then 1000057629670952 else 1000057577754501
def weightRowRLLLLLLLLR (j : ℕ) : ℕ := if j < 1283 then 1000057620385307 else weightRowRLLLLLLLLRR j
def weightRowRLLLLLLLL (j : ℕ) : ℕ := if j < 1282 then weightRowRLLLLLLLLL j else weightRowRLLLLLLLLR j
def weightRowRLLLLLLLRL (j : ℕ) : ℕ := if j < 1286 then 1000057466645361 else 1000057298325964
def weightRowRLLLLLLLRRR (j : ℕ) : ℕ := if j < 1289 then 1000056797851411 else 1000056469526506
def weightRowRLLLLLLLRR (j : ℕ) : ℕ := if j < 1288 then 1000057074751791 else weightRowRLLLLLLLRRR j
def weightRowRLLLLLLLR (j : ℕ) : ℕ := if j < 1287 then weightRowRLLLLLLLRL j else weightRowRLLLLLLLRR j
def weightRowRLLLLLLL (j : ℕ) : ℕ := if j < 1285 then weightRowRLLLLLLLL j else weightRowRLLLLLLLR j
def weightRowRLLLLLLRLL (j : ℕ) : ℕ := if j < 1291 then 1000056091651915 else 1000055666075665
def weightRowRLLLLLLRLRR (j : ℕ) : ℕ := if j < 1294 then 1000054679076510 else 1000054121215998
def weightRowRLLLLLLRLR (j : ℕ) : ℕ := if j < 1293 then 1000055194619018 else weightRowRLLLLLLRLRR j
def weightRowRLLLLLLRL (j : ℕ) : ℕ := if j < 1292 then weightRowRLLLLLLRLL j else weightRowRLLLLLLRLR j
def weightRowRLLLLLLRRL (j : ℕ) : ℕ := if j < 1296 then 1000053522778709 else 1000052885479288
def weightRowRLLLLLLRRRR (j : ℕ) : ℕ := if j < 1299 then 1000051501020044 else 1000050757157096
def weightRowRLLLLLLRRR (j : ℕ) : ℕ := if j < 1298 then 1000052211005851 else weightRowRLLLLLLRRRR j
def weightRowRLLLLLLRR (j : ℕ) : ℕ := if j < 1297 then weightRowRLLLLLLRRL j else weightRowRLLLLLLRRR j
def weightRowRLLLLLLR (j : ℕ) : ℕ := if j < 1295 then weightRowRLLLLLLRL j else weightRowRLLLLLLRR j
def weightRowRLLLLLL (j : ℕ) : ℕ := if j < 1290 then weightRowRLLLLLLL j else weightRowRLLLLLLR j
def weightRowRLLLLLRLLL (j : ℕ) : ℕ := if j < 1301 then 1000049981025882 else 1000049174208982
def weightRowRLLLLLRLLRR (j : ℕ) : ℕ := if j < 1304 then 1000047474717389 else 1000046585076995
def weightRowRLLLLLRLLR (j : ℕ) : ℕ := if j < 1303 then 1000048338262753 else weightRowRLLLLLRLLRR j
def weightRowRLLLLLRLL (j : ℕ) : ℕ := if j < 1302 then weightRowRLLLLLRLLL j else weightRowRLLLLLRLLR j
def weightRowRLLLLLRLRL (j : ℕ) : ℕ := if j < 1306 then 1000045670819658 else 1000044733397524
def weightRowRLLLLLRLRRR (j : ℕ) : ℕ := if j < 1309 then 1000042794738198 else 1000041796276294
def weightRowRLLLLLRLRR (j : ℕ) : ℕ := if j < 1308 then 1000043774236872 else weightRowRLLLLLRLRRR j
def weightRowRLLLLLRLR (j : ℕ) : ℕ := if j < 1307 then weightRowRLLLLLRLRL j else weightRowRLLLLLRLRR j
def weightRowRLLLLLRL (j : ℕ) : ℕ := if j < 1305 then weightRowRLLLLLRLL j else weightRowRLLLLLRLR j
def weightRowRLLLLLRRLL (j : ℕ) : ℕ := if j < 1311 then 1000040780200335 else 1000039747833965
def weightRowRLLLLLRRLRR (j : ℕ) : ℕ := if j < 1314 then 1000037639397463 else 1000036565847791
def weightRowRLLLLLRRLR (j : ℕ) : ℕ := if j < 1313 then 1000038700475389 else weightRowRLLLLLRRLRR j
def weightRowRLLLLLRRL (j : ℕ) : ℕ := if j < 1312 then weightRowRLLLLLRRLL j else weightRowRLLLLLRRLR j
def weightRowRLLLLLRRRL (j : ℕ) : ℕ := if j < 1316 then 1000035481048820 else 1000034386197944
def weightRowRLLLLLRRRRR (j : ℕ) : ℕ := if j < 1319 then 1000032171005392 else 1000031052934161
def weightRowRLLLLLRRRR (j : ℕ) : ℕ := if j < 1318 then 1000033282467604 else weightRowRLLLLLRRRRR j
def weightRowRLLLLLRRR (j : ℕ) : ℕ := if j < 1317 then weightRowRLLLLLRRRL j else weightRowRLLLLLRRRR j
def weightRowRLLLLLRR (j : ℕ) : ℕ := if j < 1315 then weightRowRLLLLLRRL j else weightRowRLLLLLRRR j
def weightRowRLLLLLR (j : ℕ) : ℕ := if j < 1310 then weightRowRLLLLLRL j else weightRowRLLLLLRR j
def weightRowRLLLLL (j : ℕ) : ℕ := if j < 1300 then weightRowRLLLLLL j else weightRowRLLLLLR j
def weightRowRLLLLRLLLL (j : ℕ) : ℕ := if j < 1321 then 1000029929352134 else 1000028801333018
def weightRowRLLLLRLLLRR (j : ℕ) : ℕ := if j < 1324 then 1000026536156449 else 1000025401024872
def weightRowRLLLLRLLLR (j : ℕ) : ℕ := if j < 1323 then 1000027669926116 else weightRowRLLLLRLLLRR j
def weightRowRLLLLRLLL (j : ℕ) : ℕ := if j < 1322 then weightRowRLLLLRLLLL j else weightRowRLLLLRLLLR j
def weightRowRLLLLRLLRL (j : ℕ) : ℕ := if j < 1326 then 1000024265508201 else 1000023130559335
def weightRowRLLLLRLLRRR (j : ℕ) : ℕ := if j < 1329 then 1000020866057809 else 1000019738292533
def weightRowRLLLLRLLRR (j : ℕ) : ℕ := if j < 1328 then 1000021997107387 else weightRowRLLLLRLLRRR j
def weightRowRLLLLRLLR (j : ℕ) : ℕ := if j < 1327 then weightRowRLLLLRLLRL j else weightRowRLLLLRLLRR j
def weightRowRLLLLRLL (j : ℕ) : ℕ := if j < 1325 then weightRowRLLLLRLLL j else weightRowRLLLLRLLR j
def weightRowRLLLLRLRLL (j : ℕ) : ℕ := if j < 1331 then 1000018614670099 else 1000017496025798
def weightRowRLLLLRLRLRR (j : ℕ) : ℕ := if j < 1334 then 1000015276897341 else 1000014177968788
def weightRowRLLLLRLRLR (j : ℕ) : ℕ := if j < 1333 then 1000016383171808 else weightRowRLLLLRLRLRR j
def weightRowRLLLLRLRL (j : ℕ) : ℕ := if j < 1332 then weightRowRLLLLRLRLL j else weightRowRLLLLRLRLR j
def weightRowRLLLLRLRRL (j : ℕ) : ℕ := if j < 1336 then 1000013087129864 else 1000012005101763
def weightRowRLLLLRLRRRR (j : ℕ) : ℕ := if j < 1339 then 1000009870251101 else 1000008818759699
def weightRowRLLLLRLRRR (j : ℕ) : ℕ := if j < 1338 then 1000010932583306 else weightRowRLLLLRLRRRR j
def weightRowRLLLLRLRR (j : ℕ) : ℕ := if j < 1337 then weightRowRLLLLRLRRL j else weightRowRLLLLRLRRR j
def weightRowRLLLLRLR (j : ℕ) : ℕ := if j < 1335 then weightRowRLLLLRLRL j else weightRowRLLLLRLRR j
def weightRowRLLLLRL (j : ℕ) : ℕ := if j < 1330 then weightRowRLLLLRLL j else weightRowRLLLLRLR j
def weightRowRLLLLRRLLL (j : ℕ) : ℕ := if j < 1341 then 1000007778741754 else 1000006750808187
def weightRowRLLLLRRLLRR (j : ℕ) : ℕ := if j < 1344 then 1000004733530199 else 1000003745300454
def weightRowRLLLLRRLLR (j : ℕ) : ℕ := if j < 1343 then 1000005735548351 else weightRowRLLLLRRLLRR j
def weightRowRLLLLRRLL (j : ℕ) : ℕ := if j < 1342 then weightRowRLLLLRRLLL j else weightRowRLLLLRRLLR j
def weightRowRLLLLRRLRL (j : ℕ) : ℕ := if j < 1346 then 1000002771384783 else 1000001812287970
def weightRowRLLLLRRLRRR (j : ℕ) : ℕ := if j < 1349 then 999999940466713 else 999999028649041
def weightRowRLLLLRRLRR (j : ℕ) : ℕ := if j < 1348 then 1000000868494094 else weightRowRLLLLRRLRRR j
def weightRowRLLLLRRLR (j : ℕ) : ℕ := if j < 1347 then weightRowRLLLLRRLRL j else weightRowRLLLLRRLRR j
def weightRowRLLLLRRL (j : ℕ) : ℕ := if j < 1345 then weightRowRLLLLRRLL j else weightRowRLLLLRRLR j
def weightRowRLLLLRRRLL (j : ℕ) : ℕ := if j < 1351 then 999998133464135 else 999997255315083
def weightRowRLLLLRRRLRR (j : ℕ) : ℕ := if j < 1354 then 999995551638184 else 999994726818383
def weightRowRLLLLRRRLR (j : ℕ) : ℕ := if j < 1353 then 999996394585193 else weightRowRLLLLRRRLRR j
def weightRowRLLLLRRRL (j : ℕ) : ℕ := if j < 1352 then weightRowRLLLLRRRLL j else weightRowRLLLLRRRLR j
def weightRowRLLLLRRRRL (j : ℕ) : ℕ := if j < 1356 then 999993920450916 else 999993132841914
def weightRowRLLLLRRRRRR (j : ℕ) : ℕ := if j < 1359 then 999991615030037 else 999990885346251
def weightRowRLLLLRRRRR (j : ℕ) : ℕ := if j < 1358 then 999992364278708 else weightRowRLLLLRRRRRR j
def weightRowRLLLLRRRR (j : ℕ) : ℕ := if j < 1357 then weightRowRLLLLRRRRL j else weightRowRLLLLRRRRR j
def weightRowRLLLLRRR (j : ℕ) : ℕ := if j < 1355 then weightRowRLLLLRRRL j else weightRowRLLLLRRRR j
def weightRowRLLLLRR (j : ℕ) : ℕ := if j < 1350 then weightRowRLLLLRRL j else weightRowRLLLLRRR j
def weightRowRLLLLR (j : ℕ) : ℕ := if j < 1340 then weightRowRLLLLRL j else weightRowRLLLLRR j
def weightRowRLLLL (j : ℕ) : ℕ := if j < 1320 then weightRowRLLLLL j else weightRowRLLLLR j
def weightRowRLLLRLLLLL (j : ℕ) : ℕ := if j < 1361 then 999990175459519 else 999989485584041
def weightRowRLLLRLLLLRR (j : ℕ) : ℕ := if j < 1364 then 999988166635071 else 999987537902049
def weightRowRLLLRLLLLR (j : ℕ) : ℕ := if j < 1363 then 999988815916259 else weightRowRLLLRLLLLRR j
def weightRowRLLLRLLLL (j : ℕ) : ℕ := if j < 1362 then weightRowRLLLRLLLLL j else weightRowRLLLRLLLLR j
def weightRowRLLLRLLLRL (j : ℕ) : ℕ := if j < 1366 then 999986929861659 else 999986342641479
def weightRowRLLLRLLLRRR (j : ℕ) : ℕ := if j < 1369 then 999985231088969 else 999984706929382
def weightRowRLLLRLLLRR (j : ℕ) : ℕ := if j < 1368 then 999985776352424 else weightRowRLLLRLLLRRR j
def weightRowRLLLRLLLR (j : ℕ) : ℕ := if j < 1367 then weightRowRLLLRLLLRL j else weightRowRLLLRLLLRR j
def weightRowRLLLRLLL (j : ℕ) : ℕ := if j < 1365 then weightRowRLLLRLLLL j else weightRowRLLLRLLLR j
def weightRowRLLLRLLRLL (j : ℕ) : ℕ := if j < 1371 then 999984203935947 else 999983722155198
def weightRowRLLLRLLRLRR (j : ℕ) : ℕ := if j < 1374 then 999982822340546 else 999982404323070
def weightRowRLLLRLLRLR (j : ℕ) : ℕ := if j < 1373 then 999983261618152 else weightRowRLLLRLLRLRR j
def weightRowRLLLRLLRL (j : ℕ) : ℕ := if j < 1372 then weightRowRLLLRLLRLL j else weightRowRLLLRLLRLR j
def weightRowRLLLRLLRRL (j : ℕ) : ℕ := if j < 1376 then 999982007551611 else 999981631997492
def weightRowRLLLRLLRRRR (j : ℕ) : ℕ := if j < 1379 then 999980944355198 else 999980632139043
def weightRowRLLLRLLRRR (j : ℕ) : ℕ := if j < 1378 then 999981277617712 else weightRowRLLLRLLRRRR j
def weightRowRLLLRLLRR (j : ℕ) : ℕ := if j < 1377 then weightRowRLLLRLLRRL j else weightRowRLLLRLLRRR j
def weightRowRLLLRLLR (j : ℕ) : ℕ := if j < 1375 then weightRowRLLLRLLRL j else weightRowRLLLRLLRR j
def weightRowRLLLRLL (j : ℕ) : ℕ := if j < 1370 then weightRowRLLLRLLL j else weightRowRLLLRLLR j
def weightRowRLLLRLRLLL (j : ℕ) : ℕ := if j < 1381 then 999980340884759 else 999980070494529
def weightRowRLLLRLRLLRR (j : ℕ) : ℕ := if j < 1384 then 999979591849803 else 999979383335286
def weightRowRLLLRLRLLR (j : ℕ) : ℕ := if j < 1383 then 999979820857452 else weightRowRLLLRLRLLRR j
def weightRowRLLLRLRLL (j : ℕ) : ℕ := if j < 1382 then weightRowRLLLRLRLLL j else weightRowRLLLRLRLLR j
def weightRowRLLLRLRLRL (j : ℕ) : ℕ := if j < 1386 then 999979195165288 else 999979027179139
def weightRowRLLLRLRLRRR (j : ℕ) : ℕ := if j < 1389 then 999978751056993 else 999978642541719
def weightRowRLLLRLRLRR (j : ℕ) : ℕ := if j < 1388 then 999978879204375 else weightRowRLLLRLRLRRR j
def weightRowRLLLRLRLR (j : ℕ) : ℕ := if j < 1387 then weightRowRLLLRLRLRL j else weightRowRLLLRLRLRR j
def weightRowRLLLRLRL (j : ℕ) : ℕ := if j < 1385 then weightRowRLLLRLRLL j else weightRowRLLLRLRLR j
def weightRowRLLLRLRRLL (j : ℕ) : ℕ := if j < 1391 then 999978553452268 else 999978483571613
def weightRowRLLLRLRRLRR (j : ℕ) : ℕ := if j < 1394 then 999978400516464 else 999978386856605
def weightRowRLLLRLRRLR (j : ℕ) : ℕ := if j < 1393 then 999978432672250 else weightRowRLLLRLRRLRR j
def weightRowRLLLRLRRL (j : ℕ) : ℕ := if j < 1392 then weightRowRLLLRLRRLL j else weightRowRLLLRLRRLR j
def weightRowRLLLRLRRRL (j : ℕ) : ℕ := if j < 1396 then 999978391435349 else 999978413985978
def weightRowRLLLRLRRRRR (j : ℕ) : ℕ := if j < 1399 then 999978511890670 else 999978586666769
def weightRowRLLLRLRRRR (j : ℕ) : ℕ := if j < 1398 then 999978454232650 else weightRowRLLLRLRRRRR j
def weightRowRLLLRLRRR (j : ℕ) : ℕ := if j < 1397 then weightRowRLLLRLRRRL j else weightRowRLLLRLRRRR j
def weightRowRLLLRLRR (j : ℕ) : ℕ := if j < 1395 then weightRowRLLLRLRRL j else weightRowRLLLRLRRR j
def weightRowRLLLRLR (j : ℕ) : ℕ := if j < 1390 then weightRowRLLLRLRL j else weightRowRLLLRLRR j
def weightRowRLLLRL (j : ℕ) : ℕ := if j < 1380 then weightRowRLLLRLL j else weightRowRLLLRLR j
def weightRowRLLLRRLLLL (j : ℕ) : ℕ := if j < 1401 then 999978678259377 else 999978786358903
def weightRowRLLLRRLLLRR (j : ℕ) : ℕ := if j < 1404 then 999979050801892 else 999979206488558
def weightRowRLLLRRLLLR (j : ℕ) : ℕ := if j < 1403 then 999978910648010 else weightRowRLLLRRLLLRR j
def weightRowRLLLRRLLL (j : ℕ) : ℕ := if j < 1402 then weightRowRLLLRRLLLL j else weightRowRLLLRRLLLR j
def weightRowRLLLRRLLRL (j : ℕ) : ℕ := if j < 1406 then 999979377369109 else 999979563098018
def weightRowRLLLRRLLRRR (j : ℕ) : ℕ := if j < 1409 then 999979977687354 else 999980205826127
def weightRowRLLLRRLLRR (j : ℕ) : ℕ := if j < 1408 then 999979763323411 else weightRowRLLLRRLLRRR j
def weightRowRLLLRRLLR (j : ℕ) : ℕ := if j < 1407 then weightRowRLLLRRLLRL j else weightRowRLLLRRLLRR j
def weightRowRLLLRRLL (j : ℕ) : ℕ := if j < 1405 then weightRowRLLLRRLLL j else weightRowRLLLRRLLR j
def weightRowRLLLRRLRLL (j : ℕ) : ℕ := if j < 1411 then 999980447370514 else 999980701946081
def weightRowRLLLRRLRLRR (j : ℕ) : ℕ := if j < 1414 then 999981248668639 else 999981540043235
def weightRowRLLLRRLRLR (j : ℕ) : ℕ := if j < 1413 then 999980969173461 else weightRowRLLLRRLRLRR j
def weightRowRLLLRRLRL (j : ℕ) : ℕ := if j < 1412 then weightRowRLLLRRLRLL j else weightRowRLLLRRLRLR j
def weightRowRLLLRRLRRL (j : ℕ) : ℕ := if j < 1416 then 999981842904786 else 999982156857033
def weightRowRLLLRRLRRRR (j : ℕ) : ℕ := if j < 1419 then 999982816431291 else 999983161244349
def weightRowRLLLRRLRRR (j : ℕ) : ℕ := if j < 1418 then 999982481500202 else weightRowRLLLRRLRRRR j
def weightRowRLLLRRLRR (j : ℕ) : ℕ := if j < 1417 then weightRowRLLLRRLRRL j else weightRowRLLLRRLRRR j
def weightRowRLLLRRLR (j : ℕ) : ℕ := if j < 1415 then weightRowRLLLRRLRL j else weightRowRLLLRRLRR j
def weightRowRLLLRRL (j : ℕ) : ℕ := if j < 1410 then weightRowRLLLRRLL j else weightRowRLLLRRLR j
def weightRowRLLLRRRLLL (j : ℕ) : ℕ := if j < 1421 then 999983515530765 else 999983878879547
def weightRowRLLLRRRLLRR (j : ℕ) : ℕ := if j < 1424 then 999984631110041 else 999985019160413
def weightRowRLLLRRRLLR (j : ℕ) : ℕ := if j < 1423 then 999984250877607 else weightRowRLLLRRRLLRR j
def weightRowRLLLRRRLL (j : ℕ) : ℕ := if j < 1422 then weightRowRLLLRRRLLL j else weightRowRLLLRRRLLR j
def weightRowRLLLRRRLRL (j : ℕ) : ℕ := if j < 1426 then 999985414611037 else 999985817043253
def weightRowRLLLRRRLRRR (j : ℕ) : ℕ := if j < 1429 then 999986641174648 else 999987062034167
def weightRowRLLLRRRLRR (j : ℕ) : ℕ := if j < 1428 then 999986226037711 else weightRowRLLLRRRLRRR j
def weightRowRLLLRRRLR (j : ℕ) : ℕ := if j < 1427 then weightRowRLLLRRRLRL j else weightRowRLLLRRRLRR j
def weightRowRLLLRRRL (j : ℕ) : ℕ := if j < 1425 then weightRowRLLLRRRLL j else weightRowRLLLRRRLR j
def weightRowRLLLRRRRLL (j : ℕ) : ℕ := if j < 1431 then 999987488196512 else 999987919242345
def weightRowRLLLRRRRLRR (j : ℕ) : ℕ := if j < 1434 then 999988794310865 else 999989237499430
def weightRowRLLLRRRRLR (j : ℕ) : ℕ := if j < 1433 then 999988354753023 else weightRowRLLLRRRRLRR j
def weightRowRLLLRRRRL (j : ℕ) : ℕ := if j < 1432 then weightRowRLLLRRRRLL j else weightRowRLLLRRRRLR j
def weightRowRLLLRRRRRL (j : ℕ) : ℕ := if j < 1436 then 999989683903785 else 999990133110775
def weightRowRLLLRRRRRRR (j : ℕ) : ℕ := if j < 1439 then 999991038290522 else 999991493448249
def weightRowRLLLRRRRRR (j : ℕ) : ℕ := if j < 1438 then 999990584709288 else weightRowRLLLRRRRRRR j
def weightRowRLLLRRRRR (j : ℕ) : ℕ := if j < 1437 then weightRowRLLLRRRRRL j else weightRowRLLLRRRRRR j
def weightRowRLLLRRRR (j : ℕ) : ℕ := if j < 1435 then weightRowRLLLRRRRL j else weightRowRLLLRRRRR j
def weightRowRLLLRRR (j : ℕ) : ℕ := if j < 1430 then weightRowRLLLRRRL j else weightRowRLLLRRRR j
def weightRowRLLLRR (j : ℕ) : ℕ := if j < 1420 then weightRowRLLLRRL j else weightRowRLLLRRR j
def weightRowRLLLR (j : ℕ) : ℕ := if j < 1400 then weightRowRLLLRL j else weightRowRLLLRR j
def weightRowRLLL (j : ℕ) : ℕ := if j < 1360 then weightRowRLLLL j else weightRowRLLLR j
def weightRowRLLRLLLLLL (j : ℕ) : ℕ := if j < 1441 then 999991949779077 else 999992406882708
def weightRowRLLRLLLLLRR (j : ℕ) : ℕ := if j < 1444 then 999993321824203 else 999993778879252
def weightRowRLLRLLLLLR (j : ℕ) : ℕ := if j < 1443 then 999992864362196 else weightRowRLLRLLLLLRR j
def weightRowRLLRLLLLL (j : ℕ) : ℕ := if j < 1442 then weightRowRLLRLLLLLL j else weightRowRLLRLLLLLR j
def weightRowRLLRLLLLRL (j : ℕ) : ℕ := if j < 1446 then 999994235141976 else 999994690231367
def weightRowRLLRLLLLRRR (j : ℕ) : ℕ := if j < 1449 then 999995595389379 else 999996044719967
def weightRowRLLRLLLLRR (j : ℕ) : ℕ := if j < 1448 then 999995143771021 else weightRowRLLRLLLLRRR j
def weightRowRLLRLLLLR (j : ℕ) : ℕ := if j < 1447 then weightRowRLLRLLLLRL j else weightRowRLLRLLLLRR j
def weightRowRLLRLLLL (j : ℕ) : ℕ := if j < 1445 then weightRowRLLRLLLLL j else weightRowRLLRLLLLR j
def weightRowRLLRLLLRLL (j : ℕ) : ℕ := if j < 1451 then 999996491401635 else 999996935078786
def weightRowRLLRLLLRLRR (j : ℕ) : ℕ := if j < 1454 then 999997812026295 else 999998244615284
def weightRowRLLRLLLRLR (j : ℕ) : ℕ := if j < 1453 then 999997375401606 else weightRowRLLRLLLRLRR j
def weightRowRLLRLLLRL (j : ℕ) : ℕ := if j < 1452 then weightRowRLLRLLLRLL j else weightRowRLLRLLLRLR j
def weightRowRLLRLLLRRL (j : ℕ) : ℕ := if j < 1456 then 999998672837459 else 999999096368375
def weightRowRLLRLLLRRRR (j : ℕ) : ℕ := if j < 1459 then 999999928093249 else 1000000335673542
def weightRowRLLRLLLRRR (j : ℕ) : ℕ := if j < 1458 then 999999514890464 else weightRowRLLRLLLRRRR j
def weightRowRLLRLLLRR (j : ℕ) : ℕ := if j < 1457 then weightRowRLLRLLLRRL j else weightRowRLLRLLLRRR j
def weightRowRLLRLLLR (j : ℕ) : ℕ := if j < 1455 then weightRowRLLRLLLRL j else weightRowRLLRLLLRR j
def weightRowRLLRLLL (j : ℕ) : ℕ := if j < 1450 then weightRowRLLRLLLL j else weightRowRLLRLLLR j
def weightRowRLLRLLRLLL (j : ℕ) : ℕ := if j < 1461 then 1000000737335644 else 1000001132791541
def weightRowRLLRLLRLLRR (j : ℕ) : ℕ := if j < 1464 then 1000001903972224 else 1000002279161088
def weightRowRLLRLLRLLR (j : ℕ) : ℕ := if j < 1463 then 1000001521761095 else weightRowRLLRLLRLLRR j
def weightRowRLLRLLRLL (j : ℕ) : ℕ := if j < 1462 then weightRowRLLRLLRLLL j else weightRowRLLRLLRLLR j
def weightRowRLLRLLRLRL (j : ℕ) : ℕ := if j < 1466 then 1000002647072261 else 1000003007458900
def weightRowRLLRLLRLRRR (j : ℕ) : ℕ := if j < 1469 then 1000003704715122 else 1000004041135401
def weightRowRLLRLLRLRR (j : ℕ) : ℕ := if j < 1468 then 1000003360082915 else weightRowRLLRLLRLRRR j
def weightRowRLLRLLRLR (j : ℕ) : ℕ := if j < 1467 then weightRowRLLRLLRLRL j else weightRowRLLRLLRLRR j
def weightRowRLLRLLRL (j : ℕ) : ℕ := if j < 1465 then weightRowRLLRLLRLL j else weightRowRLLRLLRLR j
def weightRowRLLRLLRRLL (j : ℕ) : ℕ := if j < 1471 then 1000004369132840 else 1000004688505881
def weightRowRLLRLLRRLRR (j : ℕ) : ℕ := if j < 1474 then 1000005300620101 else 1000005593006112
def weightRowRLLRLLRRLR (j : ℕ) : ℕ := if j < 1473 then 1000004999062453 else weightRowRLLRLLRRLRR j
def weightRowRLLRLLRRL (j : ℕ) : ℕ := if j < 1472 then weightRowRLLRLLRRLL j else weightRowRLLRLLRRLR j
def weightRowRLLRLLRRRL (j : ℕ) : ℕ := if j < 1476 then 1000005876057626 else 1000006149621752
def weightRowRLLRLLRRRRR (j : ℕ) : ℕ := if j < 1479 then 1000006667726709 else 1000006912012472
def weightRowRLLRLLRRRR (j : ℕ) : ℕ := if j < 1478 then 1000006413555667 else weightRowRLLRLLRRRRR j
def weightRowRLLRLLRRR (j : ℕ) : ℕ := if j < 1477 then weightRowRLLRLLRRRL j else weightRowRLLRLLRRRR j
def weightRowRLLRLLRR (j : ℕ) : ℕ := if j < 1475 then weightRowRLLRLLRRL j else weightRowRLLRLLRRR j
def weightRowRLLRLLR (j : ℕ) : ℕ := if j < 1470 then weightRowRLLRLLRL j else weightRowRLLRLLRR j
def weightRowRLLRLL (j : ℕ) : ℕ := if j < 1460 then weightRowRLLRLLL j else weightRowRLLRLLR j
def weightRowRLLRLRLLLL (j : ℕ) : ℕ := if j < 1481 then 1000007146300880 else 1000007370490262
def weightRowRLLRLRLLLRR (j : ℕ) : ℕ := if j < 1484 then 1000007788217679 else 1000007981604946
def weightRowRLLRLRLLLR (j : ℕ) : ℕ := if j < 1483 then 1000007584489419 else weightRowRLLRLRLLLRR j
def weightRowRLLRLRLLL (j : ℕ) : ℕ := if j < 1482 then weightRowRLLRLRLLLL j else weightRowRLLRLRLLLR j
def weightRowRLLRLRLLRL (j : ℕ) : ℕ := if j < 1486 then 1000008164591741 else 1000008337129233
def weightRowRLLRLRLLRRR (j : ℕ) : ℕ := if j < 1489 then 1000008650714351 else 1000008791717715
def weightRowRLLRLRLLRR (j : ℕ) : ℕ := if j < 1488 then 1000008499179261 else weightRowRLLRLRLLRRR j
def weightRowRLLRLRLLR (j : ℕ) : ℕ := if j < 1487 then weightRowRLLRLRLLRL j else weightRowRLLRLRLLRR j
def weightRowRLLRLRLL (j : ℕ) : ℕ := if j < 1485 then weightRowRLLRLRLLL j else weightRowRLLRLRLLR j
def weightRowRLLRLRLRLL (j : ℕ) : ℕ := if j < 1491 then 1000008922183253 else 1000009042115532
def weightRowRLLRLRLRLRR (j : ℕ) : ℕ := if j < 1494 then 1000009250451776 else 1000009338917955
def weightRowRLLRLRLRLR (j : ℕ) : ℕ := if j < 1493 then 1000009151529765 else weightRowRLLRLRLRLRR j
def weightRowRLLRLRLRL (j : ℕ) : ℕ := if j < 1492 then weightRowRLLRLRLRLL j else weightRowRLLRLRLRLR j
def weightRowRLLRLRLRRL (j : ℕ) : ℕ := if j < 1496 then 1000009416975203 else 1000009484680864
def weightRowRLLRLRLRRRR (j : ℕ) : ℕ := if j < 1499 then 1000009589318549 else 1000009626416734
def weightRowRLLRLRLRRR (j : ℕ) : ℕ := if j < 1498 then 1000009542102649 else weightRowRLLRLRLRRRR j
def weightRowRLLRLRLRR (j : ℕ) : ℕ := if j < 1497 then weightRowRLLRLRLRRL j else weightRowRLLRLRLRRR j
def weightRowRLLRLRLR (j : ℕ) : ℕ := if j < 1495 then weightRowRLLRLRLRL j else weightRowRLLRLRLRR j
def weightRowRLLRLRL (j : ℕ) : ℕ := if j < 1490 then weightRowRLLRLRLL j else weightRowRLLRLRLR j
def weightRowRLLRLRRLLL (j : ℕ) : ℕ := if j < 1501 then 1000009653495440 else 1000009670662850
def weightRowRLLRLRRLLRR (j : ℕ) : ℕ := if j < 1504 then 1000009675745399 else 1000009663925339
def weightRowRLLRLRRLLR (j : ℕ) : ℕ := if j < 1503 then 1000009678036953 else weightRowRLLRLRRLLRR j
def weightRowRLLRLRRLL (j : ℕ) : ℕ := if j < 1502 then weightRowRLLRLRRLLL j else weightRowRLLRLRRLLR j
def weightRowRLLRLRRLRL (j : ℕ) : ℕ := if j < 1506 then 1000009642723251 else 1000009612294752
def weightRowRLLRLRRLRRR (j : ℕ) : ℕ := if j < 1509 then 1000009524425474 else 1000009467339759
def weightRowRLLRLRRLRR (j : ℕ) : ℕ := if j < 1508 then 1000009572804399 else weightRowRLLRLRRLRRR j
def weightRowRLLRLRRLR (j : ℕ) : ℕ := if j < 1507 then weightRowRLLRLRRLRL j else weightRowRLLRLRRLRR j
def weightRowRLLRLRRL (j : ℕ) : ℕ := if j < 1505 then weightRowRLLRLRRLL j else weightRowRLLRLRRLR j
def weightRowRLLRLRRRLL (j : ℕ) : ℕ := if j < 1511 then 1000009401737292 else 1000009327816111
def weightRowRLLRLRRRLRR (j : ℕ) : ℕ := if j < 1514 then 1000009155848113 else 1000009058234857
def weightRowRLLRLRRRLR (j : ℕ) : ℕ := if j < 1513 then 1000009245781981 else weightRowRLLRLRRRLRR j
def weightRowRLLRLRRRL (j : ℕ) : ℕ := if j < 1512 then weightRowRLLRLRRRLL j else weightRowRLLRLRRRLR j
def weightRowRLLRLRRRRL (j : ℕ) : ℕ := if j < 1516 then 1000008953169386 else 1000008840885366
def weightRowRLLRLRRRRRR (j : ℕ) : ℕ := if j < 1519 then 1000008595626685 else 1000008463148583
def weightRowRLLRLRRRRR (j : ℕ) : ℕ := if j < 1518 then 1000008721622605 else weightRowRLLRLRRRRRR j
def weightRowRLLRLRRRR (j : ℕ) : ℕ := if j < 1517 then weightRowRLLRLRRRRL j else weightRowRLLRLRRRRR j
def weightRowRLLRLRRR (j : ℕ) : ℕ := if j < 1515 then weightRowRLLRLRRRL j else weightRowRLLRLRRRR j
def weightRowRLLRLRR (j : ℕ) : ℕ := if j < 1510 then weightRowRLLRLRRL j else weightRowRLLRLRRR j
def weightRowRLLRLR (j : ℕ) : ℕ := if j < 1500 then weightRowRLLRLRL j else weightRowRLLRLRR j
def weightRowRLLRL (j : ℕ) : ℕ := if j < 1480 then weightRowRLLRLL j else weightRowRLLRLR j
def weightRowRLLRRLLLLL (j : ℕ) : ℕ := if j < 1521 then 1000008324444271 else 1000008179774297
def weightRowRLLRRLLLLRR (j : ℕ) : ℕ := if j < 1524 then 1000007873599815 else 1000007712635290
def weightRowRLLRRLLLLR (j : ℕ) : ℕ := if j < 1523 then 1000008029403351 else weightRowRLLRRLLLLRR j
def weightRowRLLRRLLLL (j : ℕ) : ℕ := if j < 1522 then weightRowRLLRRLLLLL j else weightRowRLLRRLLLLR j
def weightRowRLLRRLLLRL (j : ℕ) : ℕ := if j < 1526 then 1000007546784103 else 1000007376322806
def weightRowRLLRRLLLRRR (j : ℕ) : ℕ := if j < 1529 then 1000007022684001 else 1000006840065848
def weightRowRLLRRLLLRR (j : ℕ) : ℕ := if j < 1528 then 1000007201529643 else weightRowRLLRRLLLRRR j
def weightRowRLLRRLLLR (j : ℕ) : ℕ := if j < 1527 then weightRowRLLRRLLLRL j else weightRowRLLRRLLLRR j
def weightRowRLLRRLLL (j : ℕ) : ℕ := if j < 1525 then weightRowRLLRRLLLL j else weightRowRLLRRLLLR j
def weightRowRLLRRLLRLL (j : ℕ) : ℕ := if j < 1531 then 1000006653955141 else 1000006464631218
def weightRowRLLRRLLRLRR (j : ℕ) : ℕ := if j < 1534 then 1000006077454186 else 1000005880150890
def weightRowRLLRRLLRLR (j : ℕ) : ℕ := if j < 1533 then 1000006272372169 else weightRowRLLRRLLRLRR j
def weightRowRLLRRLLRL (j : ℕ) : ℕ := if j < 1532 then weightRowRLLRRLLRLL j else weightRowRLLRRLLRLR j
def weightRowRLLRRLLRRL (j : ℕ) : ℕ := if j < 1536 then 1000005680732634 else 1000005479465789
def weightRowRLLRRLLRRRR (j : ℕ) : ℕ := if j < 1539 then 1000005072427436 else 1000004867161976
def weightRowRLLRRLLRRR (j : ℕ) : ℕ := if j < 1538 then 1000005276612003 else weightRowRLLRRLLRRRR j
def weightRowRLLRRLLRR (j : ℕ) : ℕ := if j < 1537 then weightRowRLLRRLLRRL j else weightRowRLLRRLLRRR j
def weightRowRLLRRLLR (j : ℕ) : ℕ := if j < 1535 then weightRowRLLRRLLRL j else weightRowRLLRRLLRR j
def weightRowRLLRRLL (j : ℕ) : ℕ := if j < 1530 then weightRowRLLRRLLL j else weightRowRLLRRLLR j
def weightRowRLLRRLRLLL (j : ℕ) : ℕ := if j < 1541 then 1000004661058425 else 1000004454352581
def weightRowRLLRRLRLLRR (j : ℕ) : ℕ := if j < 1544 then 1000004040042638 else 1000003832875805
def weightRowRLLRRLRLLR (j : ℕ) : ℕ := if j < 1543 then 1000004247273312 else weightRowRLLRRLRLLRR j
def weightRowRLLRRLRLL (j : ℕ) : ℕ := if j < 1542 then weightRowRLLRRLRLLL j else weightRowRLLRRLRLLR j
def weightRowRLLRRLRLRL (j : ℕ) : ℕ := if j < 1546 then 1000003625981369 else 1000003419561271
def weightRowRLLRRLRLRRR (j : ℕ) : ℕ := if j < 1549 then 1000003008919258 else 1000002805068868
def weightRowRLLRRLRLRR (j : ℕ) : ℕ := if j < 1548 then 1000003213810917 else weightRowRLLRRLRLRRR j
def weightRowRLLRRLRLR (j : ℕ) : ℕ := if j < 1547 then weightRowRLLRRLRLRL j else weightRowRLLRRLRLRR j
def weightRowRLLRRLRL (j : ℕ) : ℕ := if j < 1545 then weightRowRLLRRLRLL j else weightRowRLLRRLRLR j
def weightRowRLLRRLRRLL (j : ℕ) : ℕ := if j < 1551 then 1000002602436026 else 1000002401190792
def weightRowRLLRRLRRLRR (j : ℕ) : ℕ := if j < 1554 then 1000002003512783 else 1000001807389763
def weightRowRLLRRLRRLR (j : ℕ) : ℕ := if j < 1553 then 1000002201497089 else weightRowRLLRRLRRLRR j
def weightRowRLLRRLRRL (j : ℕ) : ℕ := if j < 1552 then weightRowRLLRRLRRLL j else weightRowRLLRRLRRLR j
def weightRowRLLRRLRRRL (j : ℕ) : ℕ := if j < 1556 then 1000001613274020 else 1000001421305727
def weightRowRLLRRLRRRRR (j : ℕ) : ℕ := if j < 1559 then 1000001044343579 else 1000000859601707
def weightRowRLLRRLRRRR (j : ℕ) : ℕ := if j < 1558 then 1000001231619320 else weightRowRLLRRLRRRRR j
def weightRowRLLRRLRRR (j : ℕ) : ℕ := if j < 1557 then weightRowRLLRRLRRRL j else weightRowRLLRRLRRRR j
def weightRowRLLRRLRR (j : ℕ) : ℕ := if j < 1555 then weightRowRLLRRLRRL j else weightRowRLLRRLRRR j
def weightRowRLLRRLR (j : ℕ) : ℕ := if j < 1550 then weightRowRLLRRLRL j else weightRowRLLRRLRR j
def weightRowRLLRRL (j : ℕ) : ℕ := if j < 1540 then weightRowRLLRRLL j else weightRowRLLRRLR j
def weightRowRLLRRRLLLL (j : ℕ) : ℕ := if j < 1561 then 1000000677511412 else 1000000498184984
def weightRowRLLRRRLLLRR (j : ℕ) : ℕ := if j < 1564 then 1000000148246301 else 999999977832275
def weightRowRLLRRRLLLR (j : ℕ) : ℕ := if j < 1563 then 1000000321729380 else weightRowRLLRRRLLLRR j
def weightRowRLLRRRLLL (j : ℕ) : ℕ := if j < 1562 then weightRowRLLRRRLLLL j else weightRowRLLRRRLLLR j
def weightRowRLLRRRLLRL (j : ℕ) : ℕ := if j < 1566 then 999999810578736 else 999999646572105
def weightRowRLLRRRLLRRR (j : ℕ) : ℕ := if j < 1569 then 999999328620667 else 999999174824359
def weightRowRLLRRRLLRR (j : ℕ) : ℕ := if j < 1568 then 999999485893870 else weightRowRLLRRRLLRRR j
def weightRowRLLRRRLLR (j : ℕ) : ℕ := if j < 1567 then weightRowRLLRRRLLRL j else weightRowRLLRRRLLRR j
def weightRowRLLRRRLL (j : ℕ) : ℕ := if j < 1565 then weightRowRLLRRRLLL j else weightRowRLLRRRLLR j
def weightRowRLLRRRLRLL (j : ℕ) : ℕ := if j < 1571 then 999999024572120 else 999998877926512
def weightRowRLLRRRLRLRR (j : ℕ) : ℕ := if j < 1574 then 999998595682861 else 999998460187608
def weightRowRLLRRRLRLR (j : ℕ) : ℕ := if j < 1573 then 999998734945566 else weightRowRLLRRRLRLRR j
def weightRowRLLRRRLRL (j : ℕ) : ℕ := if j < 1572 then weightRowRLLRRRLRLL j else weightRowRLLRRRLRLR j
def weightRowRLLRRRLRRL (j : ℕ) : ℕ := if j < 1576 then 999998328504726 else 999998200674924
def weightRowRLLRRRLRRRR (j : ℕ) : ℕ := if j < 1579 then 999997956716817 else 999997840649593
def weightRowRLLRRRLRRR (j : ℕ) : ℕ := if j < 1578 then 999998076734778 else weightRowRLLRRRLRRRR j
def weightRowRLLRRRLRR (j : ℕ) : ℕ := if j < 1577 then weightRowRLLRRRLRRL j else weightRowRLLRRRLRRR j
def weightRowRLLRRRLR (j : ℕ) : ℕ := if j < 1575 then weightRowRLLRRRLRL j else weightRowRLLRRRLRR j
def weightRowRLLRRRL (j : ℕ) : ℕ := if j < 1570 then weightRowRLLRRRLL j else weightRowRLLRRRLR j
def weightRowRLLRRRRLLL (j : ℕ) : ℕ := if j < 1581 then 999997728557769 else 999997620462194
def weightRowRLLRRRRLLRR (j : ℕ) : ℕ := if j < 1584 then 999997416324595 else 999997320305913
def weightRowRLLRRRRLLR (j : ℕ) : ℕ := if j < 1583 then 999997516379983 else weightRowRLLRRRRLLRR j
def weightRowRLLRRRRLL (j : ℕ) : ℕ := if j < 1582 then weightRowRLLRRRRLLL j else weightRowRLLRRRRLLR j
def weightRowRLLRRRRLRL (j : ℕ) : ℕ := if j < 1586 then 999997228330319 else 999997140400779
def weightRowRLLRRRRLRRR (j : ℕ) : ℕ := if j < 1589 then 999996976675083 else 999996900868455
def weightRowRLLRRRRLRR (j : ℕ) : ℕ := if j < 1588 then 999997056516915 else weightRowRLLRRRRLRRR j
def weightRowRLLRRRRLR (j : ℕ) : ℕ := if j < 1587 then weightRowRLLRRRRLRL j else weightRowRLLRRRRLRR j
def weightRowRLLRRRRL (j : ℕ) : ℕ := if j < 1585 then weightRowRLLRRRRLL j else weightRowRLLRRRRLR j
def weightRowRLLRRRRRLL (j : ℕ) : ℕ := if j < 1591 then 999996829087093 else 999996761318023
def weightRowRLLRRRRRLRR (j : ℕ) : ℕ := if j < 1594 then 999996637750179 else 999996581910987
def weightRowRLLRRRRRLR (j : ℕ) : ℕ := if j < 1593 then 999996697545321 else weightRowRLLRRRRRLRR j
def weightRowRLLRRRRRL (j : ℕ) : ℕ := if j < 1592 then weightRowRLLRRRRRLL j else weightRowRLLRRRRRLR j
def weightRowRLLRRRRRRL (j : ℕ) : ℕ := if j < 1596 then 999996530003408 else 999996482000454
def weightRowRLLRRRRRRRR (j : ℕ) : ℕ := if j < 1599 then 999996397587653 else 999996361111244
def weightRowRLLRRRRRRR (j : ℕ) : ℕ := if j < 1598 then 999996437872558 else weightRowRLLRRRRRRRR j
def weightRowRLLRRRRRR (j : ℕ) : ℕ := if j < 1597 then weightRowRLLRRRRRRL j else weightRowRLLRRRRRRR j
def weightRowRLLRRRRR (j : ℕ) : ℕ := if j < 1595 then weightRowRLLRRRRRL j else weightRowRLLRRRRRR j
def weightRowRLLRRRR (j : ℕ) : ℕ := if j < 1590 then weightRowRLLRRRRL j else weightRowRLLRRRRR j
def weightRowRLLRRR (j : ℕ) : ℕ := if j < 1580 then weightRowRLLRRRL j else weightRowRLLRRRR j
def weightRowRLLRR (j : ℕ) : ℕ := if j < 1560 then weightRowRLLRRL j else weightRowRLLRRR j
def weightRowRLLR (j : ℕ) : ℕ := if j < 1520 then weightRowRLLRL j else weightRowRLLRR j
def weightRowRLL (j : ℕ) : ℕ := if j < 1440 then weightRowRLLL j else weightRowRLLR j
def weightRowRLRLLLLLLL (j : ℕ) : ℕ := if j < 1601 then 999996328406483 else 999996299434241
def weightRowRLRLLLLLLRR (j : ℕ) : ℕ := if j < 1604 then 999996252519845 else 999996234488696
def weightRowRLRLLLLLLR (j : ℕ) : ℕ := if j < 1603 then 999996274153184 else weightRowRLRLLLLLLRR j
def weightRowRLRLLLLLL (j : ℕ) : ℕ := if j < 1602 then weightRowRLRLLLLLLL j else weightRowRLRLLLLLLR j
def weightRowRLRLLLLLRL (j : ℕ) : ℕ := if j < 1606 then 999996220012219 else 999996209040981
def weightRowRLRLLLLLRRR (j : ℕ) : ℕ := if j < 1609 then 999996197407331 else 999996196637105
def weightRowRLRLLLLLRR (j : ℕ) : ℕ := if j < 1608 then 999996201523703 else weightRowRLRLLLLLRRR j
def weightRowRLRLLLLLR (j : ℕ) : ℕ := if j < 1607 then weightRowRLRLLLLLRL j else weightRowRLRLLLLLRR j
def weightRowRLRLLLLL (j : ℕ) : ℕ := if j < 1605 then weightRowRLRLLLLLL j else weightRowRLRLLLLLR j
def weightRowRLRLLLLRLL (j : ℕ) : ℕ := if j < 1611 then 999996199156632 else 999996204907953
def weightRowRLRLLLLRLRR (j : ℕ) : ℕ := if j < 1614 then 999996225866729 else 999996240951058
def weightRowRLRLLLLRLR (j : ℕ) : ℕ := if j < 1613 then 999996213831613 else weightRowRLRLLLLRLRR j
def weightRowRLRLLLLRL (j : ℕ) : ℕ := if j < 1612 then weightRowRLRLLLLRLL j else weightRowRLRLLLLRLR j
def weightRowRLRLLLLRRL (j : ℕ) : ℕ := if j < 1616 then 999996259021062 else 999996280011979
def weightRowRLRLLLLRRRR (j : ℕ) : ℕ := if j < 1619 then 999996330491769 else 999996359845580
def weightRowRLRLLLLRRR (j : ℕ) : ℕ := if j < 1618 then 999996303857887 else weightRowRLRLLLLRRRR j
def weightRowRLRLLLLRR (j : ℕ) : ℕ := if j < 1617 then weightRowRLRLLLLRRL j else weightRowRLRLLLLRRR j
def weightRowRLRLLLLR (j : ℕ) : ℕ := if j < 1615 then weightRowRLRLLLLRL j else weightRowRLRLLLLRR j
def weightRowRLRLLLL (j : ℕ) : ℕ := if j < 1610 then weightRowRLRLLLLL j else weightRowRLRLLLLR j
def weightRowRLRLLLRLLL (j : ℕ) : ℕ := if j < 1621 then 999996391850308 else 999996426436044
def weightRowRLRLLLRLLRR (j : ℕ) : ℕ := if j < 1624 then 999996503066766 else 999996544967994
def weightRowRLRLLLRLLR (j : ℕ) : ℕ := if j < 1623 then 999996463532037 else weightRowRLRLLLRLLRR j
def weightRowRLRLLLRLL (j : ℕ) : ℕ := if j < 1622 then weightRowRLRLLLRLLL j else weightRowRLRLLLRLLR j
def weightRowRLRLLLRLRL (j : ℕ) : ℕ := if j < 1626 then 999996589162834 else 999996635577808
def weightRowRLRLLLRLRRR (j : ℕ) : ℕ := if j < 1629 then 999996734771658 else 999996787401164
def weightRowRLRLLLRLRR (j : ℕ) : ℕ := if j < 1628 then 999996684138909 else weightRowRLRLLLRLRRR j
def weightRowRLRLLLRLR (j : ℕ) : ℕ := if j < 1627 then weightRowRLRLLLRLRL j else weightRowRLRLLLRLRR j
def weightRowRLRLLLRL (j : ℕ) : ℕ := if j < 1625 then weightRowRLRLLLRLL j else weightRowRLRLLLRLR j
def weightRowRLRLLLRRLL (j : ℕ) : ℕ := if j < 1631 then 999996841952182 else 999996898349171
def weightRowRLRLLLRRLRR (j : ℕ) : ℕ := if j < 1634 then 999997016377751 else 999997077857282
def weightRowRLRLLLRRLR (j : ℕ) : ℕ := if j < 1633 then 999996956516349 else weightRowRLRLLLRRLRR j
def weightRowRLRLLLRRL (j : ℕ) : ℕ := if j < 1632 then weightRowRLRLLLRRLL j else weightRowRLRLLLRRLR j
def weightRowRLRLLLRRRL (j : ℕ) : ℕ := if j < 1636 then 999997140878775 else 999997205366039
def weightRowRLRLLLRRRRR (j : ℕ) : ℕ := if j < 1639 then 999997338433343 else 999997406861373
def weightRowRLRLLLRRRR (j : ℕ) : ℕ := if j < 1638 then 999997271242919 else weightRowRLRLLLRRRRR j
def weightRowRLRLLLRRR (j : ℕ) : ℕ := if j < 1637 then weightRowRLRLLLRRRL j else weightRowRLRLLLRRRR j
def weightRowRLRLLLRR (j : ℕ) : ℕ := if j < 1635 then weightRowRLRLLLRRL j else weightRowRLRLLLRRR j
def weightRowRLRLLLR (j : ℕ) : ℕ := if j < 1630 then weightRowRLRLLLRL j else weightRowRLRLLLRR j
def weightRowRLRLLL (j : ℕ) : ℕ := if j < 1620 then weightRowRLRLLLL j else weightRowRLRLLLR j
def weightRowRLRLLRLLLL (j : ℕ) : ℕ := if j < 1641 then 999997476451262 else 999997547127497
def weightRowRLRLLRLLLRR (j : ℕ) : ℕ := if j < 1644 then 999997691438426 else 999997764923715
def weightRowRLRLLRLLLR (j : ℕ) : ℕ := if j < 1643 then 999997618814849 else weightRowRLRLLRLLLRR j
def weightRowRLRLLRLLL (j : ℕ) : ℕ := if j < 1642 then weightRowRLRLLRLLLL j else weightRowRLRLLRLLLR j
def weightRowRLRLLRLLRL (j : ℕ) : ℕ := if j < 1646 then 999997839196632 else 999997914183565
def weightRowRLRLLRLLRRR (j : ℕ) : ℕ := if j < 1649 then 999998066007671 else 999998142700388
def weightRowRLRLLRLLRR (j : ℕ) : ℕ := if j < 1648 then 999997989811422 else weightRowRLRLLRLLRRR j
def weightRowRLRLLRLLR (j : ℕ) : ℕ := if j < 1647 then weightRowRLRLLRLLRL j else weightRowRLRLLRLLRR j
def weightRowRLRLLRLL (j : ℕ) : ℕ := if j < 1645 then weightRowRLRLLRLLL j else weightRowRLRLLRLLR j
def weightRowRLRLLRLRLL (j : ℕ) : ℕ := if j < 1651 then 999998219818294 else 999998297290800
def weightRowRLRLLRLRLRR (j : ℕ) : ℕ := if j < 1654 then 999998453020947 else 999998531141214
def weightRowRLRLLRLRLR (j : ℕ) : ℕ := if j < 1653 then 999998375048048 else weightRowRLRLLRLRLRR j
def weightRowRLRLLRLRL (j : ℕ) : ℕ := if j < 1652 then weightRowRLRLLRLRLL j else weightRowRLRLLRLRLR j
def weightRowRLRLLRLRRL (j : ℕ) : ℕ := if j < 1656 then 999998609341411 else 999998687554984
def weightRowRLRLLRLRRRR (j : ℕ) : ℕ := if j < 1659 then 999998843760660 else 999998921624381
def weightRowRLRLLRLRRR (j : ℕ) : ℕ := if j < 1658 then 999998765716295 else weightRowRLRLLRLRRRR j
def weightRowRLRLLRLRR (j : ℕ) : ℕ := if j < 1657 then weightRowRLRLLRLRRL j else weightRowRLRLLRLRRR j
def weightRowRLRLLRLR (j : ℕ) : ℕ := if j < 1655 then weightRowRLRLLRLRL j else weightRowRLRLLRLRR j
def weightRowRLRLLRL (j : ℕ) : ℕ := if j < 1650 then weightRowRLRLLRLL j else weightRowRLRLLRLR j
def weightRowRLRLLRRLLL (j : ℕ) : ℕ := if j < 1661 then 999998999244781 else 999999076560235
def weightRowRLRLLRRLLRR (j : ℕ) : ℕ := if j < 1664 then 999999230035248 else 999999306077091
def weightRowRLRLLRRLLR (j : ℕ) : ℕ := if j < 1663 then 999999153510201 else weightRowRLRLLRRLLRR j
def weightRowRLRLLRRLL (j : ℕ) : ℕ := if j < 1662 then weightRowRLRLLRRLLL j else weightRowRLRLLRRLLR j
def weightRowRLRLLRRLRL (j : ℕ) : ℕ := if j < 1666 then 999999381578614 else 999999456483897
def weightRowRLRLLRRLRRR (j : ℕ) : ℕ := if j < 1669 then 999999604288215 else 999999677081632
def weightRowRLRLLRRLRR (j : ℕ) : ℕ := if j < 1668 then 999999530738246 else weightRowRLRLLRRLRRR j
def weightRowRLRLLRRLR (j : ℕ) : ℕ := if j < 1667 then weightRowRLRLLRRLRL j else weightRowRLRLLRRLRR j
def weightRowRLRLLRRL (j : ℕ) : ℕ := if j < 1665 then weightRowRLRLLRRLL j else weightRowRLRLLRRLR j
def weightRowRLRLLRRRLL (j : ℕ) : ℕ := if j < 1671 then 999999749067621 else 999999820196622
def weightRowRLRLLRRRLRR (j : ℕ) : ℕ := if j < 1674 then 999999959692150 else 1000000027966338
def weightRowRLRLLRRRLR (j : ℕ) : ℕ := if j < 1673 then 999999890420418 else weightRowRLRLLRRRLRR j
def weightRowRLRLLRRRL (j : ℕ) : ℕ := if j < 1672 then weightRowRLRLLRRRLL j else weightRowRLRLLRRRLR j
def weightRowRLRLLRRRRL (j : ℕ) : ℕ := if j < 1676 then 1000000095198897 else 1000000161347156
def weightRowRLRLLRRRRRR (j : ℕ) : ℕ := if j < 1679 then 1000000290227261 else 1000000352880970
def weightRowRLRLLRRRRR (j : ℕ) : ℕ := if j < 1678 then 1000000226369877 else weightRowRLRLLRRRRRR j
def weightRowRLRLLRRRR (j : ℕ) : ℕ := if j < 1677 then weightRowRLRLLRRRRL j else weightRowRLRLLRRRRR j
def weightRowRLRLLRRR (j : ℕ) : ℕ := if j < 1675 then weightRowRLRLLRRRL j else weightRowRLRLLRRRR j
def weightRowRLRLLRR (j : ℕ) : ℕ := if j < 1670 then weightRowRLRLLRRL j else weightRowRLRLLRRR j
def weightRowRLRLLR (j : ℕ) : ℕ := if j < 1660 then weightRowRLRLLRL j else weightRowRLRLLRR j
def weightRowRLRLL (j : ℕ) : ℕ := if j < 1640 then weightRowRLRLLL j else weightRowRLRLLR j
def weightRowRLRLRLLLLL (j : ℕ) : ℕ := if j < 1681 then 1000000414294138 else 1000000474431379
def weightRowRLRLRLLLLRR (j : ℕ) : ℕ := if j < 1684 then 1000000590744019 else 1000000646856153
def weightRowRLRLRLLLLR (j : ℕ) : ℕ := if j < 1683 then 1000000533258802 else weightRowRLRLRLLLLRR j
def weightRowRLRLRLLLL (j : ℕ) : ℕ := if j < 1682 then weightRowRLRLRLLLLL j else weightRowRLRLRLLLLR j
def weightRowRLRLRLLLRL (j : ℕ) : ℕ := if j < 1686 then 1000000701565847 else 1000000754845267
def weightRowRLRLRLLLRRR (j : ℕ) : ℕ := if j < 1689 then 1000000857009621 else 1000000905846561
def weightRowRLRLRLLLRR (j : ℕ) : ℕ := if j < 1688 then 1000000806668114 else weightRowRLRLRLLLRRR j
def weightRowRLRLRLLLR (j : ℕ) : ℕ := if j < 1687 then weightRowRLRLRLLLRL j else weightRowRLRLRLLLRR j
def weightRowRLRLRLLL (j : ℕ) : ℕ := if j < 1685 then weightRowRLRLRLLLL j else weightRowRLRLRLLLR j
def weightRowRLRLRLLRLL (j : ℕ) : ℕ := if j < 1691 then 1000000953157247 else 1000000998921536
def weightRowRLRLRLLRLRR (j : ℕ) : ℕ := if j < 1694 then 1000001085738050 else 1000001126757694
def weightRowRLRLRLLRLR (j : ℕ) : ℕ := if j < 1693 then 1000001043120824 else weightRowRLRLRLLRLRR j
def weightRowRLRLRLLRL (j : ℕ) : ℕ := if j < 1692 then weightRowRLRLRLLRLL j else weightRowRLRLRLLRLR j
def weightRowRLRLRLLRRL (j : ℕ) : ℕ := if j < 1696 then 1000001166165769 else 1000001203949822
def weightRowRLRLRLLRRRR (j : ℕ) : ℕ := if j < 1699 then 1000001274603677 else 1000001307456183
def weightRowRLRLRLLRRR (j : ℕ) : ℕ := if j < 1698 then 1000001240098926 else weightRowRLRLRLLRRRR j
def weightRowRLRLRLLRR (j : ℕ) : ℕ := if j < 1697 then weightRowRLRLRLLRRL j else weightRowRLRLRLLRRR j
def weightRowRLRLRLLR (j : ℕ) : ℕ := if j < 1695 then weightRowRLRLRLLRL j else weightRowRLRLRLLRR j
def weightRowRLRLRLL (j : ℕ) : ℕ := if j < 1690 then weightRowRLRLRLLL j else weightRowRLRLRLLR j
def weightRowRLRLRLRLLL (j : ℕ) : ℕ := if j < 1701 then 1000001338650058 else 1000001368180412
def weightRowRLRLRLRLLRR (j : ℕ) : ℕ := if j < 1704 then 1000001422238424 else 1000001446763687
def weightRowRLRLRLRLLR (j : ℕ) : ℕ := if j < 1703 then 1000001396043844 else weightRowRLRLRLRLLRR j
def weightRowRLRLRLRLL (j : ℕ) : ℕ := if j < 1702 then weightRowRLRLRLRLLL j else weightRowRLRLRLRLLR j
def weightRowRLRLRLRLRL (j : ℕ) : ℕ := if j < 1706 then 1000001469620618 else 1000001490811636
def weightRowRLRLRLRLRRR (j : ℕ) : ℕ := if j < 1709 then 1000001528212698 else 1000001544434616
def weightRowRLRLRLRLRR (j : ℕ) : ℕ := if j < 1708 then 1000001510340581 else weightRowRLRLRLRLRRR j
def weightRowRLRLRLRLR (j : ℕ) : ℕ := if j < 1707 then weightRowRLRLRLRLRL j else weightRowRLRLRLRLRR j
def weightRowRLRLRLRL (j : ℕ) : ℕ := if j < 1705 then weightRowRLRLRLRLL j else weightRowRLRLRLRLR j
def weightRowRLRLRLRRLL (j : ℕ) : ℕ := if j < 1711 then 1000001559014336 else 1000001571961208
def weightRowRLRLRLRRLRR (j : ℕ) : ℕ := if j < 1714 then 1000001593000431 else 1000001601118048
def weightRowRLRLRLRRLR (j : ℕ) : ℕ := if j < 1713 then 1000001583285910 else weightRowRLRLRLRRLRR j
def weightRowRLRLRLRRL (j : ℕ) : ℕ := if j < 1712 then weightRowRLRLRLRRLL j else weightRowRLRLRLRRLR j
def weightRowRLRLRLRRRL (j : ℕ) : ℕ := if j < 1716 then 1000001607653301 else 1000001612621972
def weightRowRLRLRLRRRRR (j : ℕ) : ℕ := if j < 1719 then 1000001617928753 else 1000001618304408
def weightRowRLRLRLRRRR (j : ℕ) : ℕ := if j < 1718 then 1000001616041060 else weightRowRLRLRLRRRRR j
def weightRowRLRLRLRRR (j : ℕ) : ℕ := if j < 1717 then weightRowRLRLRLRRRL j else weightRowRLRLRLRRRR j
def weightRowRLRLRLRR (j : ℕ) : ℕ := if j < 1715 then weightRowRLRLRLRRL j else weightRowRLRLRLRRR j
def weightRowRLRLRLR (j : ℕ) : ℕ := if j < 1710 then weightRowRLRLRLRL j else weightRowRLRLRLRR j
def weightRowRLRLRL (j : ℕ) : ℕ := if j < 1700 then weightRowRLRLRLL j else weightRowRLRLRLR j
def weightRowRLRLRRLLLL (j : ℕ) : ℕ := if j < 1721 then 1000001617188518 else 1000001614602688
def weightRowRLRLRRLLLRR (j : ℕ) : ℕ := if j < 1724 then 1000001605113005 else 1000001598257653
def weightRowRLRLRRLLLR (j : ℕ) : ℕ := if j < 1723 then 1000001610569603 else weightRowRLRLRRLLLRR j
def weightRowRLRLRRLLL (j : ℕ) : ℕ := if j < 1722 then weightRowRLRLRRLLLL j else weightRowRLRLRRLLLR j
def weightRowRLRLRRLLRL (j : ℕ) : ℕ := if j < 1726 then 1000001590029304 else 1000001580454671
def weightRowRLRLRRLLRRR (j : ℕ) : ℕ := if j < 1729 then 1000001557378020 else 1000001543933940
def weightRowRLRLRRLLRR (j : ℕ) : ℕ := if j < 1728 then 1000001569561397 else weightRowRLRLRRLLRRR j
def weightRowRLRLRRLLR (j : ℕ) : ℕ := if j < 1727 then weightRowRLRLRRLLRL j else weightRowRLRLRRLLRR j
def weightRowRLRLRRLL (j : ℕ) : ℕ := if j < 1725 then weightRowRLRLRRLLL j else weightRowRLRLRRLLR j
def weightRowRLRLRRLRLL (j : ℕ) : ℕ := if j < 1731 then 1000001529259385 else 1000001513385374
def weightRowRLRLRRLRLRR (j : ℕ) : ℕ := if j < 1734 then 1000001478166818 else 1000001458887955
def weightRowRLRLRRLRLR (j : ℕ) : ℕ := if j < 1733 then 1000001496343685 else weightRowRLRLRRLRLRR j
def weightRowRLRLRRLRL (j : ℕ) : ℕ := if j < 1732 then weightRowRLRLRRLRLL j else weightRowRLRLRRLRLR j
def weightRowRLRLRRLRRL (j : ℕ) : ℕ := if j < 1736 then 1000001438540929 else 1000001417160181
def weightRowRLRLRRLRRRR (j : ℕ) : ℕ := if j < 1739 then 1000001371438109 else 1000001347168378
def weightRowRLRLRRLRRR (j : ℕ) : ℕ := if j < 1738 then 1000001394780725 else weightRowRLRLRRLRRRR j
def weightRowRLRLRRLRR (j : ℕ) : ℕ := if j < 1737 then weightRowRLRLRRLRRL j else weightRowRLRLRRLRRR j
def weightRowRLRLRRLR (j : ℕ) : ℕ := if j < 1735 then weightRowRLRLRRLRL j else weightRowRLRLRRLRR j
def weightRowRLRLRRL (j : ℕ) : ℕ := if j < 1730 then weightRowRLRLRRLL j else weightRowRLRLRRLR j
def weightRowRLRLRRRLLL (j : ℕ) : ℕ := if j < 1741 then 1000001322008029 else 1000001295993979
def weightRowRLRLRRRLLRR (j : ℕ) : ℕ := if j < 1744 then 1000001241554277 else 1000001213204180
def weightRowRLRLRRRLLR (j : ℕ) : ℕ := if j < 1743 then 1000001269163519 else weightRowRLRLRRRLLRR j
def weightRowRLRLRRRLL (j : ℕ) : ℕ := if j < 1742 then weightRowRLRLRRRLLL j else weightRowRLRLRRRLLR j
def weightRowRLRLRRRLRL (j : ℕ) : ℕ := if j < 1746 then 1000001184151406 else 1000001154434350
def weightRowRLRLRRRLRRR (j : ℕ) : ℕ := if j < 1749 then 1000001093161800 else 1000001061683800
def weightRowRLRLRRRLRR (j : ℕ) : ℕ := if j < 1748 then 1000001124091581 else weightRowRLRLRRRLRRR j
def weightRowRLRLRRRLR (j : ℕ) : ℕ := if j < 1747 then weightRowRLRLRRRLRL j else weightRowRLRLRRRLRR j
def weightRowRLRLRRRL (j : ℕ) : ℕ := if j < 1745 then weightRowRLRLRRRLL j else weightRowRLRLRRRLR j
def weightRowRLRLRRRRLL (j : ℕ) : ℕ := if j < 1751 then 1000001029696425 else 1000000997238528
def weightRowRLRLRRRRLRR (j : ℕ) : ℕ := if j < 1754 then 1000000931066385 else 1000000897429525
def weightRowRLRLRRRRLR (j : ℕ) : ℕ := if j < 1753 then 1000000964348932 else weightRowRLRLRRRRLRR j
def weightRowRLRLRRRRL (j : ℕ) : ℕ := if j < 1752 then weightRowRLRLRRRRLL j else weightRowRLRLRRRRLR j
def weightRowRLRLRRRRRL (j : ℕ) : ℕ := if j < 1756 then 1000000863476833 else 1000000829246599
def weightRowRLRLRRRRRRR (j : ℕ) : ℕ := if j < 1759 then 1000000760105448 else 1000000725269778
def weightRowRLRLRRRRRR (j : ℕ) : ℕ := if j < 1758 then 1000000794776877 else weightRowRLRLRRRRRRR j
def weightRowRLRLRRRRR (j : ℕ) : ℕ := if j < 1757 then weightRowRLRLRRRRRL j else weightRowRLRLRRRRRR j
def weightRowRLRLRRRR (j : ℕ) : ℕ := if j < 1755 then weightRowRLRLRRRRL j else weightRowRLRLRRRRR j
def weightRowRLRLRRR (j : ℕ) : ℕ := if j < 1750 then weightRowRLRLRRRL j else weightRowRLRLRRRR j
def weightRowRLRLRR (j : ℕ) : ℕ := if j < 1740 then weightRowRLRLRRL j else weightRowRLRLRRR j
def weightRowRLRLR (j : ℕ) : ℕ := if j < 1720 then weightRowRLRLRL j else weightRowRLRLRR j
def weightRowRLRL (j : ℕ) : ℕ := if j < 1680 then weightRowRLRLL j else weightRowRLRLR j
def weightRowRLRRLLLLLL (j : ℕ) : ℕ := if j < 1761 then 1000000690306982 else 1000000655253786
def weightRowRLRRLLLLLRR (j : ℕ) : ℕ := if j < 1764 then 1000000585020904 else 1000000549912375
def weightRowRLRRLLLLLR (j : ℕ) : ℕ := if j < 1763 then 1000000620146483 else weightRowRLRRLLLLLRR j
def weightRowRLRRLLLLL (j : ℕ) : ℕ := if j < 1762 then weightRowRLRRLLLLLL j else weightRowRLRRLLLLLR j
def weightRowRLRRLLLLRL (j : ℕ) : ℕ := if j < 1766 then 1000000514855683 else 1000000479885042
def weightRowRLRRLLLLRRR (j : ℕ) : ℕ := if j < 1769 then 1000000410335689 else 1000000375822227
def weightRowRLRRLLLLRR (j : ℕ) : ℕ := if j < 1768 then 1000000445034057 else weightRowRLRRLLLLRRR j
def weightRowRLRRLLLLR (j : ℕ) : ℕ := if j < 1767 then weightRowRLRRLLLLRL j else weightRowRLRRLLLLRR j
def weightRowRLRRLLLL (j : ℕ) : ℕ := if j < 1765 then weightRowRLRRLLLLL j else weightRowRLRRLLLLR j
def weightRowRLRRLLLRLL (j : ℕ) : ℕ := if j < 1771 then 1000000341525251 else 1000000307475604
def weightRowRLRRLLLRLRR (j : ℕ) : ℕ := if j < 1774 then 1000000240237808 else 1000000207107399
def weightRowRLRRLLLRLR (j : ℕ) : ℕ := if j < 1773 then 1000000273703363 else weightRowRLRRLLLRLRR j
def weightRowRLRRLLLRL (j : ℕ) : ℕ := if j < 1772 then weightRowRLRRLLLRLL j else weightRowRLRRLLLRLR j
def weightRowRLRRLLLRRL (j : ℕ) : ℕ := if j < 1776 then 1000000174339745 else 1000000141961586
def weightRowRLRRLLLRRRR (j : ℕ) : ℕ := if j < 1779 then 1000000078476202 else 1000000047417893
def weightRowRLRRLLLRRR (j : ℕ) : ℕ := if j < 1778 then 1000000109998763 else weightRowRLRRLLLRRRR j
def weightRowRLRRLLLRR (j : ℕ) : ℕ := if j < 1777 then weightRowRLRRLLLRRL j else weightRowRLRRLLLRRR j
def weightRowRLRRLLLR (j : ℕ) : ℕ := if j < 1775 then weightRowRLRRLLLRL j else weightRowRLRRLLLRR j
def weightRowRLRRLLL (j : ℕ) : ℕ := if j < 1770 then weightRowRLRRLLLL j else weightRowRLRRLLLR j
def weightRowRLRRLLRLLL (j : ℕ) : ℕ := if j < 1781 then 1000000016846870 else 999999986785196
def weightRowRLRRLLRLLRR (j : ℕ) : ℕ := if j < 1784 then 999999928273213 else 999999899862055
def weightRowRLRRLLRLLR (j : ℕ) : ℕ := if j < 1783 then 999999957253951 else weightRowRLRRLLRLLRR j
def weightRowRLRRLLRLL (j : ℕ) : ℕ := if j < 1782 then weightRowRLRRLLRLLL j else weightRowRLRRLLRLLR j
def weightRowRLRRLLRLRL (j : ℕ) : ℕ := if j < 1786 then 999999872038532 else 999999844819675
def weightRowRLRRLLRLRRR (j : ℕ) : ℕ := if j < 1789 then 999999792258952 else 999999766946009
def weightRowRLRRLLRLRR (j : ℕ) : ℕ := if j < 1788 then 999999818221490 else weightRowRLRRLLRLRRR j
def weightRowRLRRLLRLR (j : ℕ) : ℕ := if j < 1787 then weightRowRLRRLLRLRL j else weightRowRLRRLLRLRR j
def weightRowRLRRLLRL (j : ℕ) : ℕ := if j < 1785 then weightRowRLRRLLRLL j else weightRowRLRRLLRLR j
def weightRowRLRRLLRRLL (j : ℕ) : ℕ := if j < 1791 then 999999742295587 else 999999718319589
def weightRowRLRRLLRRLRR (j : ℕ) : ℕ := if j < 1794 then 999999672433457 else 999999650542134
def weightRowRLRRLLRRLR (j : ℕ) : ℕ := if j < 1793 then 999999695028913 else weightRowRLRRLLRRLRR j
def weightRowRLRRLLRRL (j : ℕ) : ℕ := if j < 1792 then weightRowRLRRLLRRLL j else weightRowRLRRLLRRLR j
def weightRowRLRRLLRRRL (j : ℕ) : ℕ := if j < 1796 then 999999629362895 else 999999608902742
def weightRowRLRRLLRRRRR (j : ℕ) : ℕ := if j < 1799 then 999999570163131 else 999999551893169
def weightRowRLRRLLRRRR (j : ℕ) : ℕ := if j < 1798 then 999999589167759 else weightRowRLRRLLRRRRR j
def weightRowRLRRLLRRR (j : ℕ) : ℕ := if j < 1797 then weightRowRLRRLLRRRL j else weightRowRLRRLLRRRR j
def weightRowRLRRLLRR (j : ℕ) : ℕ := if j < 1795 then weightRowRLRRLLRRL j else weightRowRLRRLLRRR j
def weightRowRLRRLLR (j : ℕ) : ℕ := if j < 1790 then weightRowRLRRLLRL j else weightRowRLRRLLRR j
def weightRowRLRRLL (j : ℕ) : ℕ := if j < 1780 then weightRowRLRRLLL j else weightRowRLRRLLR j
def weightRowRLRRLRLLLL (j : ℕ) : ℕ := if j < 1801 then 999999534361335 else 999999517570263
def weightRowRLRRLRLLLRR (j : ℕ) : ℕ := if j < 1804 then 999999486216941 else 999999471656027
def weightRowRLRRLRLLLR (j : ℕ) : ℕ := if j < 1803 then 999999501521782 else weightRowRLRRLRLLLRR j
def weightRowRLRRLRLLL (j : ℕ) : ℕ := if j < 1802 then weightRowRLRRLRLLLL j else weightRowRLRRLRLLLR j
def weightRowRLRRLRLLRL (j : ℕ) : ℕ := if j < 1806 then 999999457838592 else 999999444763474
def weightRowRLRRLRLLRRR (j : ℕ) : ℕ := if j < 1809 then 999999420832089 else 999999409970116
def weightRowRLRRLRLLRR (j : ℕ) : ℕ := if j < 1808 then 999999432428816 else weightRowRLRRLRLLRRR j
def weightRowRLRRLRLLR (j : ℕ) : ℕ := if j < 1807 then weightRowRLRRLRLLRL j else weightRowRLRRLRLLRR j
def weightRowRLRRLRLL (j : ℕ) : ℕ := if j < 1805 then weightRowRLRRLRLLL j else weightRowRLRRLRLLR j
def weightRowRLRRLRLRLL (j : ℕ) : ℕ := if j < 1811 then 999999399839090 else 999999390434596
def weightRowRLRRLRLRLRR (j : ℕ) : ℕ := if j < 1814 then 999999373784621 else 999999366527454
def weightRowRLRRLRLRLR (j : ℕ) : ℕ := if j < 1813 then 999999381751629 else weightRowRLRRLRLRLRR j
def weightRowRLRRLRLRL (j : ℕ) : ℕ := if j < 1812 then weightRowRLRRLRLRLL j else weightRowRLRRLRLRLR j
def weightRowRLRRLRLRRL (j : ℕ) : ℕ := if j < 1816 then 999999359973485 else 999999354115562
def weightRowRLRRLRLRRRR (j : ℕ) : ℕ := if j < 1819 then 999999344456832 else 999999340639362
def weightRowRLRRLRLRRR (j : ℕ) : ℕ := if j < 1818 then 999999348946047 else weightRowRLRRLRLRRRR j
def weightRowRLRRLRLRR (j : ℕ) : ℕ := if j < 1817 then weightRowRLRRLRLRRL j else weightRowRLRRLRLRRR j
def weightRowRLRRLRLR (j : ℕ) : ℕ := if j < 1815 then weightRowRLRRLRLRL j else weightRowRLRRLRLRR j
def weightRowRLRRLRL (j : ℕ) : ℕ := if j < 1810 then weightRowRLRRLRLL j else weightRowRLRRLRLR j
def weightRowRLRRLRRLLL (j : ℕ) : ℕ := if j < 1821 then 999999337484647 else 999999334983289
def weightRowRLRRLRRLLRR (j : ℕ) : ℕ := if j < 1824 then 999999331901094 else 999999331299559
def weightRowRLRRLRRLLR (j : ℕ) : ℕ := if j < 1823 then 999999333125494 else weightRowRLRRLRRLLRR j
def weightRowRLRRLRRLL (j : ℕ) : ℕ := if j < 1822 then weightRowRLRRLRRLLL j else weightRowRLRRLRRLLR j
def weightRowRLRRLRRLRL (j : ℕ) : ℕ := if j < 1826 then 999999331310024 else 999999331921296
def weightRowRLRRLRRLRRR (j : ℕ) : ℕ := if j < 1829 then 999999334899985 else 999999337243557
def weightRowRLRRLRRLRR (j : ℕ) : ℕ := if j < 1828 then 999999333121879 else weightRowRLRRLRRLRRR j
def weightRowRLRRLRRLR (j : ℕ) : ℕ := if j < 1827 then weightRowRLRRLRRLRL j else weightRowRLRRLRRLRR j
def weightRowRLRRLRRL (j : ℕ) : ℕ := if j < 1825 then weightRowRLRRLRRLL j else weightRowRLRRLRRLR j
def weightRowRLRRLRRRLL (j : ℕ) : ℕ := if j < 1831 then 999999340140279 else 999999343577594
def weightRowRLRRLRRRLRR (j : ℕ) : ℕ := if j < 1834 then 999999352022675 else 999999357004268
def weightRowRLRRLRRRLR (j : ℕ) : ℕ := if j < 1833 then 999999347542722 else weightRowRLRRLRRRLRR j
def weightRowRLRRLRRRL (j : ℕ) : ℕ := if j < 1832 then weightRowRLRRLRRRLL j else weightRowRLRRLRRRLR j
def weightRowRLRRLRRRRL (j : ℕ) : ℕ := if j < 1836 then 999999362474141 else 999999368418768
def weightRowRLRRLRRRRRR (j : ℕ) : ℕ := if j < 1839 then 999999381677453 else 999999388963771
def weightRowRLRRLRRRRR (j : ℕ) : ℕ := if j < 1838 then 999999374824475 else weightRowRLRRLRRRRRR j
def weightRowRLRRLRRRR (j : ℕ) : ℕ := if j < 1837 then weightRowRLRRLRRRRL j else weightRowRLRRLRRRRR j
def weightRowRLRRLRRR (j : ℕ) : ℕ := if j < 1835 then weightRowRLRRLRRRL j else weightRowRLRRLRRRR j
def weightRowRLRRLRR (j : ℕ) : ℕ := if j < 1830 then weightRowRLRRLRRL j else weightRowRLRRLRRR j
def weightRowRLRRLR (j : ℕ) : ℕ := if j < 1820 then weightRowRLRRLRL j else weightRowRLRRLRR j
def weightRowRLRRL (j : ℕ) : ℕ := if j < 1800 then weightRowRLRRLL j else weightRowRLRRLR j
def weightRowRLRRRLLLLL (j : ℕ) : ℕ := if j < 1841 then 999999396669393 else 999999404780188
def weightRowRLRRRLLLLRR (j : ℕ) : ℕ := if j < 1844 then 999999422160387 else 999999431401182
def weightRowRLRRRLLLLR (j : ℕ) : ℕ := if j < 1843 then 999999413281945 else weightRowRLRRRLLLLRR j
def weightRowRLRRRLLLL (j : ℕ) : ℕ := if j < 1842 then weightRowRLRRRLLLLL j else weightRowRLRRRLLLLR j
def weightRowRLRRRLLLRL (j : ℕ) : ℕ := if j < 1846 then 999999440989956 else 999999450912305
def weightRowRLRRRLLLRRR (j : ℕ) : ℕ := if j < 1849 then 999999471700043 else 999999482536585
def weightRowRLRRRLLLRR (j : ℕ) : ℕ := if j < 1848 then 999999461153810 else weightRowRLRRRLLLRRR j
def weightRowRLRRRLLLR (j : ℕ) : ℕ := if j < 1847 then weightRowRLRRRLLLRL j else weightRowRLRRRLLLRR j
def weightRowRLRRRLLL (j : ℕ) : ℕ := if j < 1845 then weightRowRLRRRLLLL j else weightRowRLRRRLLLR j
def weightRowRLRRRLLRLL (j : ℕ) : ℕ := if j < 1851 then 999999493649032 else 999999505023009
def weightRowRLRRRLLRLRR (j : ℕ) : ℕ := if j < 1854 then 999999528498256 else 999999540571013
def weightRowRLRRRLLRLR (j : ℕ) : ℕ := if j < 1853 then 999999516644179 else weightRowRLRRRLLRLRR j
def weightRowRLRRRLLRL (j : ℕ) : ℕ := if j < 1852 then weightRowRLRRRLLRLL j else weightRowRLRRRLLRLR j
def weightRowRLRRRLLRRL (j : ℕ) : ℕ := if j < 1856 then 999999552848292 else 999999565316015
def weightRowRLRRRLLRRRR (j : ℕ) : ℕ := if j < 1859 then 999999590766934 else 999999603722457
def weightRowRLRRRLLRRR (j : ℕ) : ℕ := if j < 1858 then 999999577960192 else weightRowRLRRRLLRRRR j
def weightRowRLRRRLLRR (j : ℕ) : ℕ := if j < 1857 then weightRowRLRRRLLRRL j else weightRowRLRRRLLRRR j
def weightRowRLRRRLLR (j : ℕ) : ℕ := if j < 1855 then weightRowRLRRRLLRL j else weightRowRLRRRLLRR j
def weightRowRLRRRLL (j : ℕ) : ℕ := if j < 1850 then weightRowRLRRRLLL j else weightRowRLRRRLLR j
def weightRowRLRRRLRLLL (j : ℕ) : ℕ := if j < 1861 then 999999616813092 else 999999630025297
def weightRowRLRRRLRLLRR (j : ℕ) : ℕ := if j < 1864 then 999999656760913 else 999999670257933
def weightRowRLRRRLRLLR (j : ℕ) : ℕ := if j < 1863 then 999999643345660 else weightRowRLRRRLRLLRR j
def weightRowRLRRRLRLL (j : ℕ) : ℕ := if j < 1862 then weightRowRLRRRLRLLL j else weightRowRLRRRLRLLR j
def weightRowRLRRRLRLRL (j : ℕ) : ℕ := if j < 1866 then 999999683823756 else 999999697445579
def weightRowRLRRRLRLRRR (j : ℕ) : ℕ := if j < 1869 then 999999724806875 else 999999738521622
def weightRowRLRRRLRLRR (j : ℕ) : ℕ := if j < 1868 then 999999711110770 else weightRowRLRRRLRLRRR j
def weightRowRLRRRLRLR (j : ℕ) : ℕ := if j < 1867 then weightRowRLRRRLRLRL j else weightRowRLRRRLRLRR j
def weightRowRLRRRLRL (j : ℕ) : ℕ := if j < 1865 then weightRowRLRRRLRLL j else weightRowRLRRRLRLR j
def weightRowRLRRRLRRLL (j : ℕ) : ℕ := if j < 1871 then 999999752242930 else 999999765958914
def weightRowRLRRRLRRLRR (j : ℕ) : ℕ := if j < 1874 then 999999793328382 else 999999806959126
def weightRowRLRRRLRRLR (j : ℕ) : ℕ := if j < 1873 then 999999779657890 else weightRowRLRRRLRRLRR j
def weightRowRLRRRLRRL (j : ℕ) : ℕ := if j < 1872 then weightRowRLRRRLRRLL j else weightRowRLRRRLRRLR j
def weightRowRLRRRLRRRL (j : ℕ) : ℕ := if j < 1876 then 999999820539077 else 999999834057411
def weightRowRLRRRLRRRRR (j : ℕ) : ℕ := if j < 1879 then 999999860867077 else 999999874137917
def weightRowRLRRRLRRRR (j : ℕ) : ℕ := if j < 1878 then 999999847503532 else weightRowRLRRRLRRRRR j
def weightRowRLRRRLRRR (j : ℕ) : ℕ := if j < 1877 then weightRowRLRRRLRRRL j else weightRowRLRRRLRRRR j
def weightRowRLRRRLRR (j : ℕ) : ℕ := if j < 1875 then weightRowRLRRRLRRL j else weightRowRLRRRLRRR j
def weightRowRLRRRLR (j : ℕ) : ℕ := if j < 1870 then weightRowRLRRRLRL j else weightRowRLRRRLRR j
def weightRowRLRRRL (j : ℕ) : ℕ := if j < 1860 then weightRowRLRRRLL j else weightRowRLRRRLR j
def weightRowRLRRRRLLLL (j : ℕ) : ℕ := if j < 1881 then 999999887306164 else 999999900362172
def weightRowRLRRRRLLLRR (j : ℕ) : ℕ := if j < 1884 then 999999926100133 else 999999938764044
def weightRowRLRRRRLLLR (j : ℕ) : ℕ := if j < 1883 then 999999913296544 else weightRowRLRRRRLLLRR j
def weightRowRLRRRRLLL (j : ℕ) : ℕ := if j < 1882 then weightRowRLRRRRLLLL j else weightRowRLRRRRLLLR j
def weightRowRLRRRRLLRL (j : ℕ) : ℕ := if j < 1886 then 999999951279640 else 999999963638540
def weightRowRLRRRRLLRRR (j : ℕ) : ℕ := if j < 1889 then 999999987854047 else 999999999695210
def weightRowRLRRRRLLRR (j : ℕ) : ℕ := if j < 1888 then 999999975832627 else weightRowRLRRRRLLRRR j
def weightRowRLRRRRLLR (j : ℕ) : ℕ := if j < 1887 then weightRowRLRRRRLLRL j else weightRowRLRRRRLLRR j
def weightRowRLRRRRLL (j : ℕ) : ℕ := if j < 1885 then weightRowRLRRRRLLL j else weightRowRLRRRRLLR j
def weightRowRLRRRRLRLL (j : ℕ) : ℕ := if j < 1891 then 1000000011348794 else 1000000022807745
def weightRowRLRRRRLRLRR (j : ℕ) : ℕ := if j < 1894 then 1000000045114886 else 1000000055950324
def weightRowRLRRRRLRLR (j : ℕ) : ℕ := if j < 1893 then 1000000034065280 else weightRowRLRRRRLRLRR j
def weightRowRLRRRRLRL (j : ℕ) : ℕ := if j < 1892 then weightRowRLRRRRLRLL j else weightRowRLRRRRLRLR j
def weightRowRLRRRRLRRL (j : ℕ) : ℕ := if j < 1896 then 1000000066565624 else 1000000076955094
def weightRowRLRRRRLRRRR (j : ℕ) : ℕ := if j < 1899 then 1000000097035132 else 1000000106715680
def weightRowRLRRRRLRRR (j : ℕ) : ℕ := if j < 1898 then 1000000087113312 else weightRowRLRRRRLRRRR j
def weightRowRLRRRRLRR (j : ℕ) : ℕ := if j < 1897 then weightRowRLRRRRLRRL j else weightRowRLRRRRLRRR j
def weightRowRLRRRRLR (j : ℕ) : ℕ := if j < 1895 then weightRowRLRRRRLRL j else weightRowRLRRRRLRR j
def weightRowRLRRRRL (j : ℕ) : ℕ := if j < 1890 then weightRowRLRRRRLL j else weightRowRLRRRRLR j
def weightRowRLRRRRRLLL (j : ℕ) : ℕ := if j < 1901 then 1000000116150357 else 1000000125334836
def weightRowRLRRRRRLLRR (j : ℕ) : ℕ := if j < 1904 then 1000000142937256 else 1000000151347904
def weightRowRLRRRRRLLR (j : ℕ) : ℕ := if j < 1903 then 1000000134265063 else weightRowRLRRRRRLLRR j
def weightRowRLRRRRRLL (j : ℕ) : ℕ := if j < 1902 then weightRowRLRRRRRLLL j else weightRowRLRRRRRLLR j
def weightRowRLRRRRRLRL (j : ℕ) : ℕ := if j < 1906 then 1000000159493764 else 1000000167371864
def weightRowRLRRRRRLRRR (j : ℕ) : ℕ := if j < 1909 then 1000000182314216 else 1000000189373850
def weightRowRLRRRRRLRR (j : ℕ) : ℕ := if j < 1908 then 1000000174979495 else weightRowRLRRRRRLRRR j
def weightRowRLRRRRRLR (j : ℕ) : ℕ := if j < 1907 then weightRowRLRRRRRLRL j else weightRowRLRRRRRLRR j
def weightRowRLRRRRRL (j : ℕ) : ℕ := if j < 1905 then weightRowRLRRRRRLL j else weightRowRLRRRRRLR j
def weightRowRLRRRRRRLL (j : ℕ) : ℕ := if j < 1911 then 1000000196156478 else 1000000202660444
def weightRowRLRRRRRRLRR (j : ℕ) : ℕ := if j < 1914 then 1000000214827039 else 1000000220487628
def weightRowRLRRRRRRLR (j : ℕ) : ℕ := if j < 1913 then 1000000208884346 else weightRowRLRRRRRRLRR j
def weightRowRLRRRRRRL (j : ℕ) : ℕ := if j < 1912 then weightRowRLRRRRRRLL j else weightRowRLRRRRRRLR j
def weightRowRLRRRRRRRL (j : ℕ) : ℕ := if j < 1916 then 1000000225865468 else 1000000230960160
def weightRowRLRRRRRRRRR (j : ℕ) : ℕ := if j < 1919 then 1000000240299717 else 1000000244544989
def weightRowRLRRRRRRRR (j : ℕ) : ℕ := if j < 1918 then 1000000235771548 else weightRowRLRRRRRRRRR j
def weightRowRLRRRRRRR (j : ℕ) : ℕ := if j < 1917 then weightRowRLRRRRRRRL j else weightRowRLRRRRRRRR j
def weightRowRLRRRRRR (j : ℕ) : ℕ := if j < 1915 then weightRowRLRRRRRRL j else weightRowRLRRRRRRR j
def weightRowRLRRRRR (j : ℕ) : ℕ := if j < 1910 then weightRowRLRRRRRL j else weightRowRLRRRRRR j
def weightRowRLRRRR (j : ℕ) : ℕ := if j < 1900 then weightRowRLRRRRL j else weightRowRLRRRRR j
def weightRowRLRRR (j : ℕ) : ℕ := if j < 1880 then weightRowRLRRRL j else weightRowRLRRRR j
def weightRowRLRR (j : ℕ) : ℕ := if j < 1840 then weightRowRLRRL j else weightRowRLRRR j
def weightRowRLR (j : ℕ) : ℕ := if j < 1760 then weightRowRLRL j else weightRowRLRR j
def weightRowRL (j : ℕ) : ℕ := if j < 1600 then weightRowRLL j else weightRowRLR j
def weightRowRRLLLLLLLL (j : ℕ) : ℕ := if j < 1921 then 1000000248507917 else 1000000252189288
def weightRowRRLLLLLLLRR (j : ℕ) : ℕ := if j < 1924 then 1000000258711619 else 1000000261555265
def weightRowRRLLLLLLLR (j : ℕ) : ℕ := if j < 1923 then 1000000255590111 else weightRowRRLLLLLLLRR j
def weightRowRRLLLLLLL (j : ℕ) : ℕ := if j < 1922 then weightRowRRLLLLLLLL j else weightRowRRLLLLLLLR j
def weightRowRRLLLLLLRL (j : ℕ) : ℕ := if j < 1926 then 1000000264122715 else 1000000266415844
def weightRowRRLLLLLLRRR (j : ℕ) : ℕ := if j < 1929 then 1000000270187673 else 1000000271671139
def weightRowRRLLLLLLRR (j : ℕ) : ℕ := if j < 1928 then 1000000268436735 else weightRowRRLLLLLLRRR j
def weightRowRRLLLLLLR (j : ℕ) : ℕ := if j < 1927 then weightRowRRLLLLLLRL j else weightRowRRLLLLLLRR j
def weightRowRRLLLLLL (j : ℕ) : ℕ := if j < 1925 then weightRowRRLLLLLLL j else weightRowRRLLLLLLR j
def weightRowRRLLLLLRLL (j : ℕ) : ℕ := if j < 1931 then 1000000272889807 else 1000000273846539
def weightRowRRLLLLLRLRR (j : ℕ) : ℕ := if j < 1934 then 1000000274986558 else 1000000275176467
def weightRowRRLLLLLRLR (j : ℕ) : ℕ := if j < 1933 then 1000000274544382 else weightRowRRLLLLLRLRR j
def weightRowRRLLLLLRL (j : ℕ) : ℕ := if j < 1932 then weightRowRRLLLLLRLL j else weightRowRRLLLLLRLR j
def weightRowRRLLLLLRRL (j : ℕ) : ℕ := if j < 1936 then 1000000275117675 else 1000000274813912
def weightRowRRLLLLLRRRR (j : ℕ) : ℕ := if j < 1939 then 1000000273487184 else 1000000272472451
def weightRowRRLLLLLRRR (j : ℕ) : ℕ := if j < 1938 then 1000000274269068 else weightRowRRLLLLLRRRR j
def weightRowRRLLLLLRR (j : ℕ) : ℕ := if j < 1937 then weightRowRRLLLLLRRL j else weightRowRRLLLLLRRR j
def weightRowRRLLLLLR (j : ℕ) : ℕ := if j < 1935 then weightRowRRLLLLLRL j else weightRowRRLLLLLRR j
def weightRowRRLLLLL (j : ℕ) : ℕ := if j < 1930 then weightRowRRLLLLLL j else weightRowRRLLLLLR j
def weightRowRRLLLLRLLL (j : ℕ) : ℕ := if j < 1941 then 1000000271229202 else 1000000269761910
def weightRowRRLLLLRLLRR (j : ℕ) : ℕ := if j < 1944 then 1000000266173730 else 1000000264062424
def weightRowRRLLLLRLLR (j : ℕ) : ℕ := if j < 1943 then 1000000268075175 else weightRowRRLLLLRLLRR j
def weightRowRRLLLLRLL (j : ℕ) : ℕ := if j < 1942 then weightRowRRLLLLRLLL j else weightRowRRLLLLRLLR j
def weightRowRRLLLLRLRL (j : ℕ) : ℕ := if j < 1946 then 1000000261746224 else 1000000259230207
def weightRowRRLLLLRLRRR (j : ℕ) : ℕ := if j < 1949 then 1000000253619546 else 1000000250535557
def weightRowRRLLLLRLRR (j : ℕ) : ℕ := if j < 1948 then 1000000256519554 else weightRowRRLLLLRLRRR j
def weightRowRRLLLLRLR (j : ℕ) : ℕ := if j < 1947 then weightRowRRLLLLRLRL j else weightRowRRLLLLRLRR j
def weightRowRRLLLLRL (j : ℕ) : ℕ := if j < 1945 then weightRowRRLLLLRLL j else weightRowRRLLLLRLR j
def weightRowRRLLLLRRLL (j : ℕ) : ℕ := if j < 1951 then 1000000247273047 else 1000000243837560
def weightRowRRLLLLRRLRR (j : ℕ) : ℕ := if j < 1954 then 1000000236470204 else 1000000232549779
def weightRowRRLLLLRRLR (j : ℕ) : ℕ := if j < 1953 then 1000000240234716 else weightRowRRLLLLRRLRR j
def weightRowRRLLLLRRL (j : ℕ) : ℕ := if j < 1952 then weightRowRRLLLLRRLL j else weightRowRRLLLLRRLR j
def weightRowRRLLLLRRRL (j : ℕ) : ℕ := if j < 1956 then 1000000228479256 else 1000000224264502
def weightRowRRLLLLRRRRR (j : ℕ) : ℕ := if j < 1959 then 1000000215426008 else 1000000210814220
def weightRowRRLLLLRRRR (j : ℕ) : ℕ := if j < 1958 then 1000000219911434 else weightRowRRLLLLRRRRR j
def weightRowRRLLLLRRR (j : ℕ) : ℕ := if j < 1957 then weightRowRRLLLLRRRL j else weightRowRRLLLLRRRR j
def weightRowRRLLLLRR (j : ℕ) : ℕ := if j < 1955 then weightRowRRLLLLRRL j else weightRowRRLLLLRRR j
def weightRowRRLLLLR (j : ℕ) : ℕ := if j < 1950 then weightRowRRLLLLRL j else weightRowRRLLLLRR j
def weightRowRRLLLL (j : ℕ) : ℕ := if j < 1940 then weightRowRRLLLLL j else weightRowRRLLLLR j
def weightRowRRLLLRLLLL (j : ℕ) : ℕ := if j < 1961 then 1000000206082094 else 1000000201235681
def weightRowRRLLLRLLLRR (j : ℕ) : ℕ := if j < 1964 then 1000000191224293 else 1000000186071495
def weightRowRRLLLRLLLR (j : ℕ) : ℕ := if j < 1963 then 1000000196281053 else weightRowRRLLLRLLLRR j
def weightRowRRLLLRLLL (j : ℕ) : ℕ := if j < 1962 then weightRowRRLLLRLLLL j else weightRowRRLLLRLLLR j
def weightRowRRLLLRLLRL (j : ℕ) : ℕ := if j < 1966 then 1000000180828756 else 1000000175502170
def weightRowRRLLLRLLRRR (j : ℕ) : ℕ := if j < 1969 then 1000000164621797 else 1000000159080140
def weightRowRRLLLRLLRR (j : ℕ) : ℕ := if j < 1968 then 1000000170097826 else weightRowRRLLLRLLRRR j
def weightRowRRLLLRLLR (j : ℕ) : ℕ := if j < 1967 then weightRowRRLLLRLLRL j else weightRowRRLLLRLLRR j
def weightRowRRLLLRLL (j : ℕ) : ℕ := if j < 1965 then weightRowRRLLLRLLL j else weightRowRRLLLRLLR j
def weightRowRRLLLRLRLL (j : ℕ) : ℕ := if j < 1971 then 1000000153478889 else 1000000147824049
def weightRowRRLLLRLRLRR (j : ℕ) : ℕ := if j < 1974 then 1000000136377449 else 1000000130597513
def weightRowRRLLLRLRLR (j : ℕ) : ℕ := if j < 1973 then 1000000142121591 else weightRowRRLLLRLRLRR j
def weightRowRRLLLRLRL (j : ℕ) : ℕ := if j < 1972 then weightRowRRLLLRLRLL j else weightRowRRLLLRLRLR j
def weightRowRRLLLRLRRL (j : ℕ) : ℕ := if j < 1976 then 1000000124787625 else 1000000118953575
def weightRowRRLLLRLRRRR (j : ℕ) : ℕ := if j < 1979 then 1000000107235854 else 1000000101363457
def weightRowRRLLLRLRRR (j : ℕ) : ℕ := if j < 1978 then 1000000113101095 else weightRowRRLLLRLRRRR j
def weightRowRRLLLRLRR (j : ℕ) : ℕ := if j < 1977 then weightRowRRLLLRLRRL j else weightRowRRLLLRLRRR j
def weightRowRRLLLRLR (j : ℕ) : ℕ := if j < 1975 then weightRowRRLLLRLRL j else weightRowRRLLLRLRR j
def weightRowRRLLLRL (j : ℕ) : ℕ := if j < 1970 then weightRowRRLLLRLL j else weightRowRRLLLRLR j
def weightRowRRLLLRRLLL (j : ℕ) : ℕ := if j < 1981 then 1000000095489435 else 1000000089619247
def weightRowRRLLLRRLLRR (j : ℕ) : ℕ := if j < 1984 then 1000000077911800 else 1000000072085043
def weightRowRRLLLRRLLR (j : ℕ) : ℕ := if j < 1983 then 1000000083758270 else weightRowRRLLLRRLLRR j
def weightRowRRLLLRRLL (j : ℕ) : ℕ := if j < 1982 then weightRowRRLLLRRLLL j else weightRowRRLLLRRLLR j
def weightRowRRLLLRRLRL (j : ℕ) : ℕ := if j < 1986 then 1000000066283118 else 1000000060511044
def weightRowRRLLLRRLRRR (j : ℕ) : ℕ := if j < 1989 then 1000000049076044 else 1000000043422655
def weightRowRRLLLRRLRR (j : ℕ) : ℕ := if j < 1988 then 1000000054773746 else weightRowRRLLLRRLRRR j
def weightRowRRLLLRRLR (j : ℕ) : ℕ := if j < 1987 then weightRowRRLLLRRLRL j else weightRowRRLLLRRLRR j
def weightRowRRLLLRRL (j : ℕ) : ℕ := if j < 1985 then weightRowRRLLLRRLL j else weightRowRRLLLRRLR j
def weightRowRRLLLRRRLL (j : ℕ) : ℕ := if j < 1991 then 1000000037818186 else 1000000032267132
def weightRowRRLLLRRRLRR (j : ℕ) : ℕ := if j < 1994 then 1000000021342678 else 1000000015977686
def weightRowRRLLLRRRLR (j : ℕ) : ℕ := if j < 1993 then 1000000026773875 else weightRowRRLLLRRRLRR j
def weightRowRRLLLRRRL (j : ℕ) : ℕ := if j < 1992 then weightRowRRLLLRRRLL j else weightRowRRLLLRRRLR j
def weightRowRRLLLRRRRL (j : ℕ) : ℕ := if j < 1996 then 1000000010682919 else 1000000005462272
def weightRowRRLLLRRRRRR (j : ℕ) : ℕ := if j < 1999 then 999999995258287 else 999999990282095
def weightRowRRLLLRRRRR (j : ℕ) : ℕ := if j < 1998 then 1000000000319515 else weightRowRRLLLRRRRRR j
def weightRowRRLLLRRRR (j : ℕ) : ℕ := if j < 1997 then weightRowRRLLLRRRRL j else weightRowRRLLLRRRRR j
def weightRowRRLLLRRR (j : ℕ) : ℕ := if j < 1995 then weightRowRRLLLRRRL j else weightRowRRLLLRRRR j
def weightRowRRLLLRR (j : ℕ) : ℕ := if j < 1990 then weightRowRRLLLRRL j else weightRowRRLLLRRR j
def weightRowRRLLLR (j : ℕ) : ℕ := if j < 1980 then weightRowRRLLLRL j else weightRowRRLLLRR j
def weightRowRRLLL (j : ℕ) : ℕ := if j < 1960 then weightRowRRLLLL j else weightRowRRLLLR j
def weightRowRRLLRLLLLL (j : ℕ) : ℕ := if j < 2001 then 999999985394313 else 999999980598181
def weightRowRRLLRLLLLRR (j : ℕ) : ℕ := if j < 2004 then 999999971293138 else 999999966790020
def weightRowRRLLRLLLLR (j : ℕ) : ℕ := if j < 2003 then 999999975896801 else weightRowRRLLRLLLLRR j
def weightRowRRLLRLLLL (j : ℕ) : ℕ := if j < 2002 then weightRowRRLLRLLLLL j else weightRowRRLLRLLLLR j
def weightRowRRLLRLLLRL (j : ℕ) : ℕ := if j < 2006 then 999999962390130 else 999999958096014
def weightRowRRLLRLLLRRR (j : ℕ) : ℕ := if j < 2009 then 999999949834573 else 999999945871626
def weightRowRRLLRLLLRR (j : ℕ) : ℕ := if j < 2008 then 999999953910075 else weightRowRRLLRLLLRRR j
def weightRowRRLLRLLLR (j : ℕ) : ℕ := if j < 2007 then weightRowRRLLRLLLRL j else weightRowRRLLRLLLRR j
def weightRowRRLLRLLL (j : ℕ) : ℕ := if j < 2005 then weightRowRRLLRLLLL j else weightRowRRLLRLLLR j
def weightRowRRLLRLLRLL (j : ℕ) : ℕ := if j < 2011 then 999999942023209 else 999999938291153
def weightRowRRLLRLLRLRR (j : ℕ) : ℕ := if j < 2014 then 999999931182735 else 999999927809320
def weightRowRRLLRLLRLR (j : ℕ) : ℕ := if j < 2013 then 999999934677147 else weightRowRRLLRLLRLRR j
def weightRowRRLLRLLRL (j : ℕ) : ℕ := if j < 2012 then weightRowRRLLRLLRLL j else weightRowRRLLRLLRLR j
def weightRowRRLLRLLRRL (j : ℕ) : ℕ := if j < 2016 then 999999924558163 else 999999921430384
def weightRowRRLLRLLRRRR (j : ℕ) : ℕ := if j < 2019 then 999999915548730 else 999999912796395
def weightRowRRLLRLLRRR (j : ℕ) : ℕ := if j < 2018 then 999999918426959 else weightRowRRLLRLLRRRR j
def weightRowRRLLRLLRR (j : ℕ) : ℕ := if j < 2017 then weightRowRRLLRLLRRL j else weightRowRRLLRLLRRR j
def weightRowRRLLRLLR (j : ℕ) : ℕ := if j < 2015 then weightRowRRLLRLLRL j else weightRowRRLLRLLRR j
def weightRowRRLLRLL (j : ℕ) : ℕ := if j < 2010 then weightRowRRLLRLLL j else weightRowRRLLRLLR j
def weightRowRRLLRLRLLL (j : ℕ) : ℕ := if j < 2021 then 999999910170518 else 999999907671526
def weightRowRRLLRLRLLRR (j : ℕ) : ℕ := if j < 2024 then 999999903055239 else 999999900938134
def weightRowRRLLRLRLLR (j : ℕ) : ℕ := if j < 2023 then 999999905299713 else weightRowRRLLRLRLLRR j
def weightRowRRLLRLRLL (j : ℕ) : ℕ := if j < 2022 then weightRowRRLLRLRLLL j else weightRowRRLLRLRLLR j
def weightRowRRLLRLRLRL (j : ℕ) : ℕ := if j < 2026 then 999999898948300 else 999999897085511
def weightRowRRLLRLRLRRR (j : ℕ) : ℕ := if j < 2029 then 999999893739551 else 999999892255317
def weightRowRRLLRLRLRR (j : ℕ) : ℕ := if j < 2028 then 999999895349419 else weightRowRRLLRLRLRRR j
def weightRowRRLLRLRLR (j : ℕ) : ℕ := if j < 2027 then weightRowRRLLRLRLRL j else weightRowRRLLRLRLRR j
def weightRowRRLLRLRL (j : ℕ) : ℕ := if j < 2025 then weightRowRRLLRLRLL j else weightRowRRLLRLRLR j
def weightRowRRLLRLRRLL (j : ℕ) : ℕ := if j < 2031 then 999999890896010 else 999999889660810
def weightRowRRLLRLRRLRR (j : ℕ) : ℕ := if j < 2034 then 999999887558889 else 999999886689983
def weightRowRRLLRLRRLR (j : ℕ) : ℕ := if j < 2033 then 999999888548783 else weightRowRRLLRLRRLRR j
def weightRowRRLLRLRRL (j : ℕ) : ℕ := if j < 2032 then weightRowRRLLRLRRLL j else weightRowRRLLRLRRLR j
def weightRowRRLLRLRRRL (j : ℕ) : ℕ := if j < 2036 then 999999885940818 else 999999885310048
def weightRowRRLLRLRRRRR (j : ℕ) : ℕ := if j < 2039 then 999999884397838 else 999999884113244
def weightRowRRLLRLRRRR (j : ℕ) : ℕ := if j < 2038 then 999999884796233 else weightRowRRLLRLRRRRR j
def weightRowRRLLRLRRR (j : ℕ) : ℕ := if j < 2037 then weightRowRRLLRLRRRL j else weightRowRRLLRLRRRR j
def weightRowRRLLRLRR (j : ℕ) : ℕ := if j < 2035 then weightRowRRLLRLRRL j else weightRowRRLLRLRRR j
def weightRowRRLLRLR (j : ℕ) : ℕ := if j < 2030 then weightRowRRLLRLRL j else weightRowRRLLRLRR j
def weightRowRRLLRL (j : ℕ) : ℕ := if j < 2020 then weightRowRRLLRLL j else weightRowRRLLRLR j
def weightRowRRLLRRLLLL (j : ℕ) : ℕ := if j < 2041 then 999999883940744 else 999999883878552
def weightRowRRLLRRLLLRR (j : ℕ) : ℕ := if j < 2044 then 999999884077556 else 999999884334806
def weightRowRRLLRRLLLR (j : ℕ) : ℕ := if j < 2043 then 999999883924802 else weightRowRRLLRRLLLRR j
def weightRowRRLLRRLLL (j : ℕ) : ℕ := if j < 2042 then weightRowRRLLRRLLLL j else weightRowRRLLRRLLLR j
def weightRowRRLLRRLLRL (j : ℕ) : ℕ := if j < 2046 then 999999884694478 else 999999885154433
def weightRowRRLLRRLLRRR (j : ℕ) : ℕ := if j < 2049 then 999999886366353 else 999999887113765
def weightRowRRLLRRLLRR (j : ℕ) : ℕ := if j < 2048 then 999999885712475 else weightRowRRLLRRLLRRR j
def weightRowRRLLRRLLR (j : ℕ) : ℕ := if j < 2047 then weightRowRRLLRRLLRL j else weightRowRRLLRRLLRR j
def weightRowRRLLRRLL (j : ℕ) : ℕ := if j < 2045 then weightRowRRLLRRLLL j else weightRowRRLLRRLLR j
def weightRowRRLLRRLRLL (j : ℕ) : ℕ := if j < 2051 then 999999887952360 else 999999888879744
def weightRowRRLLRRLRLRR (j : ℕ) : ℕ := if j < 2054 then 999999890991102 else 999999892170099
def weightRowRRLLRRLRLR (j : ℕ) : ℕ := if j < 2053 then 999999889893482 else weightRowRRLLRRLRLRR j
def weightRowRRLLRRLRL (j : ℕ) : ℕ := if j < 2052 then weightRowRRLLRRLRLL j else weightRowRRLLRRLRLR j
def weightRowRRLLRRLRRL (j : ℕ) : ℕ := if j < 2056 then 999999893427939 else 999999894762059
def weightRowRRLLRRLRRRR (j : ℕ) : ℕ := if j < 2059 then 999999897648779 else 999999899196150
def weightRowRRLLRRLRRR (j : ℕ) : ℕ := if j < 2058 then 999999896169874 else weightRowRRLLRRLRRRR j
def weightRowRRLLRRLRR (j : ℕ) : ℕ := if j < 2057 then weightRowRRLLRRLRRL j else weightRowRRLLRRLRRR j
def weightRowRRLLRRLR (j : ℕ) : ℕ := if j < 2055 then weightRowRRLLRRLRL j else weightRowRRLLRRLRR j
def weightRowRRLLRRL (j : ℕ) : ℕ := if j < 2050 then weightRowRRLLRRLL j else weightRowRRLLRRLR j
def weightRowRRLLRRRLLL (j : ℕ) : ℕ := if j < 2061 then 999999900809350 else 999999902485730
def weightRowRRLLRRRLLRR (j : ℕ) : ℕ := if j < 2064 then 999999906017396 else 999999907867351
def weightRowRRLLRRRLLR (j : ℕ) : ℕ := if j < 2063 then 999999904222633 else weightRowRRLLRRRLLRR j
def weightRowRRLLRRRLL (j : ℕ) : ℕ := if j < 2062 then weightRowRRLLRRRLLL j else weightRowRRLLRRRLLR j
def weightRowRRLLRRRLRL (j : ℕ) : ℕ := if j < 2066 then 999999909769832 else 999999911722175
def weightRowRRLLRRRLRRR (j : ℕ) : ℕ := if j < 2069 then 999999915765809 else 999999917851802
def weightRowRRLLRRRLRR (j : ℕ) : ℕ := if j < 2068 then 999999913721718 else weightRowRRLLRRRLRRR j
def weightRowRRLLRRRLR (j : ℕ) : ℕ := if j < 2067 then weightRowRRLLRRRLRL j else weightRowRRLLRRRLRR j
def weightRowRRLLRRRL (j : ℕ) : ℕ := if j < 2065 then weightRowRRLLRRRLL j else weightRowRRLLRRRLR j
def weightRowRRLLRRRRLL (j : ℕ) : ℕ := if j < 2071 then 999999919977064 else 999999922138977
def weightRowRRLLRRRRLRR (j : ℕ) : ℕ := if j < 2074 then 999999926562355 else 999999928818669
def weightRowRRLLRRRRLR (j : ℕ) : ℕ := if j < 2073 then 999999924334936 else weightRowRRLLRRRRLRR j
def weightRowRRLLRRRRL (j : ℕ) : ℕ := if j < 2072 then weightRowRRLLRRRRLL j else weightRowRRLLRRRRLR j
def weightRowRRLLRRRRRL (j : ℕ) : ℕ := if j < 2076 then 999999931101332 else 999999933407824
def weightRowRRLLRRRRRRR (j : ℕ) : ℕ := if j < 2079 then 999999938082338 else 999999940445451
def weightRowRRLLRRRRRR (j : ℕ) : ℕ := if j < 2078 then 999999935735649 else weightRowRRLLRRRRRRR j
def weightRowRRLLRRRRR (j : ℕ) : ℕ := if j < 2077 then weightRowRRLLRRRRRL j else weightRowRRLLRRRRRR j
def weightRowRRLLRRRR (j : ℕ) : ℕ := if j < 2075 then weightRowRRLLRRRRL j else weightRowRRLLRRRRR j
def weightRowRRLLRRR (j : ℕ) : ℕ := if j < 2070 then weightRowRRLLRRRL j else weightRowRRLLRRRR j
def weightRowRRLLRR (j : ℕ) : ℕ := if j < 2060 then weightRowRRLLRRL j else weightRowRRLLRRR j
def weightRowRRLLR (j : ℕ) : ℕ := if j < 2040 then weightRowRRLLRL j else weightRowRRLLRR j
def weightRowRRLL (j : ℕ) : ℕ := if j < 2000 then weightRowRRLLL j else weightRowRRLLR j
def weightRowRRLRLLLLLL (j : ℕ) : ℕ := if j < 2081 then 999999942822577 else 999999945211339
def weightRowRRLRLLLLLRR (j : ℕ) : ℕ := if j < 2084 then 999999950014422 else 999999952424159
def weightRowRRLRLLLLLR (j : ℕ) : ℕ := if j < 2083 then 999999947609391 else weightRowRRLRLLLLLRR j
def weightRowRRLRLLLLL (j : ℕ) : ℕ := if j < 2082 then weightRowRRLRLLLLLL j else weightRowRRLRLLLLLR j
def weightRowRRLRLLLLRL (j : ℕ) : ℕ := if j < 2086 then 999999954836363 else 999999957248835
def weightRowRRLRLLLLRRR (j : ℕ) : ℕ := if j < 2089 then 999999962065985 else 999999964466466
def weightRowRRLRLLLLRR (j : ℕ) : ℕ := if j < 2088 then 999999959659415 else weightRowRRLRLLLLRRR j
def weightRowRRLRLLLLR (j : ℕ) : ℕ := if j < 2087 then weightRowRRLRLLLLRL j else weightRowRRLRLLLLRR j
def weightRowRRLRLLLL (j : ℕ) : ℕ := if j < 2085 then weightRowRRLRLLLLL j else weightRowRRLRLLLLR j
def weightRowRRLRLLLRLL (j : ℕ) : ℕ := if j < 2091 then 999999966858825 else 999999969241069
def weightRowRRLRLLLRLRR (j : ℕ) : ℕ := if j < 2094 then 999999973967473 else 999999976307875
def weightRowRRLRLLLRLR (j : ℕ) : ℕ := if j < 2093 then 999999971611252 else weightRowRRLRLLLRLRR j
def weightRowRRLRLLLRL (j : ℕ) : ℕ := if j < 2092 then weightRowRRLRLLLRLL j else weightRowRRLRLLLRLR j
def weightRowRRLRLLLRRL (j : ℕ) : ℕ := if j < 2096 then 999999978630650 else 999999980934037
def weightRowRRLRLLLRRRR (j : ℕ) : ℕ := if j < 2099 then 999999985475837 else 999999987710969
def weightRowRRLRLLLRRR (j : ℕ) : ℕ := if j < 2098 then 999999983216320 else weightRowRRLRLLLRRRR j
def weightRowRRLRLLLRR (j : ℕ) : ℕ := if j < 2097 then weightRowRRLRLLLRRL j else weightRowRRLRLLLRRR j
def weightRowRRLRLLLR (j : ℕ) : ℕ := if j < 2095 then weightRowRRLRLLLRL j else weightRowRRLRLLLRR j
def weightRowRRLRLLL (j : ℕ) : ℕ := if j < 2090 then weightRowRRLRLLLL j else weightRowRRLRLLLR j
def weightRowRRLRLLRLLL (j : ℕ) : ℕ := if j < 2101 then 999999989920151 else 999999992101866
def weightRowRRLRLLRLLRR (j : ℕ) : ℕ := if j < 2104 then 999999996377078 else 999999998467793
def weightRowRRLRLLRLLR (j : ℕ) : ℕ := if j < 2103 then 999999994254646 else weightRowRRLRLLRLLRR j
def weightRowRRLRLLRLL (j : ℕ) : ℕ := if j < 2102 then weightRowRRLRLLRLLL j else weightRowRRLRLLRLLR j
def weightRowRRLRLLRLRL (j : ℕ) : ℕ := if j < 2106 then 1000000000525480 else 1000000002548874
def weightRowRRLRLLRLRRR (j : ℕ) : ℕ := if j < 2109 then 1000000006487990 else 1000000008401442
def weightRowRRLRLLRLRR (j : ℕ) : ℕ := if j < 2108 then 1000000004536764 else weightRowRRLRLLRLRRR j
def weightRowRRLRLLRLR (j : ℕ) : ℕ := if j < 2107 then weightRowRRLRLLRLRL j else weightRowRRLRLLRLRR j
def weightRowRRLRLLRL (j : ℕ) : ℕ := if j < 2105 then weightRowRRLRLLRLL j else weightRowRRLRLLRLR j
def weightRowRRLRLLRRLL (j : ℕ) : ℕ := if j < 2111 then 1000000010276064 else 1000000012110849
def weightRowRRLRLLRRLRR (j : ℕ) : ℕ := if j < 2114 then 1000000015657144 else 1000000017366897
def weightRowRRLRLLRRLR (j : ℕ) : ℕ := if j < 2113 then 1000000013904844 else weightRowRRLRLLRRLRR j
def weightRowRRLRLLRRL (j : ℕ) : ℕ := if j < 2112 then weightRowRRLRLLRRLL j else weightRowRRLRLLRRLR j
def weightRowRRLRLLRRRL (j : ℕ) : ℕ := if j < 2116 then 1000000019033304 else 1000000020655612
def weightRowRRLRLLRRRRR (j : ℕ) : ℕ := if j < 2119 then 1000000023765183 else 1000000025251197
def weightRowRRLRLLRRRR (j : ℕ) : ℕ := if j < 2118 then 1000000022233121 else weightRowRRLRLLRRRRR j
def weightRowRRLRLLRRR (j : ℕ) : ℕ := if j < 2117 then weightRowRRLRLLRRRL j else weightRowRRLRLLRRRR j
def weightRowRRLRLLRR (j : ℕ) : ℕ := if j < 2115 then weightRowRRLRLLRRL j else weightRowRRLRLLRRR j
def weightRowRRLRLLR (j : ℕ) : ℕ := if j < 2110 then weightRowRRLRLLRL j else weightRowRRLRLLRR j
def weightRowRRLRLL (j : ℕ) : ℕ := if j < 2100 then weightRowRRLRLLL j else weightRowRRLRLLR j
def weightRowRRLRLRLLLL (j : ℕ) : ℕ := if j < 2121 then 1000000026690612 else 1000000028082927
def weightRowRRLRLRLLLRR (j : ℕ) : ℕ := if j < 2124 then 1000000030724495 else 1000000031972986
def weightRowRRLRLRLLLR (j : ℕ) : ℕ := if j < 2123 then 1000000029427690 else weightRowRRLRLRLLLRR j
def weightRowRRLRLRLLL (j : ℕ) : ℕ := if j < 2122 then weightRowRRLRLRLLLL j else weightRowRRLRLRLLLR j
def weightRowRRLRLRLLRL (j : ℕ) : ℕ := if j < 2126 then 1000000033172853 else 1000000034323835
def weightRowRRLRLRLLRRR (j : ℕ) : ℕ := if j < 2129 then 1000000036478318 else 1000000037481523
def weightRowRRLRLRLLRR (j : ℕ) : ℕ := if j < 2128 then 1000000035425713 else weightRowRRLRLRLLRRR j
def weightRowRRLRLRLLR (j : ℕ) : ℕ := if j < 2127 then weightRowRRLRLRLLRL j else weightRowRRLRLRLLRR j
def weightRowRRLRLRLL (j : ℕ) : ℕ := if j < 2125 then weightRowRRLRLRLLL j else weightRowRRLRLRLLR j
def weightRowRRLRLRLRLL (j : ℕ) : ℕ := if j < 2131 then 1000000038435246 else 1000000039339450
def weightRowRRLRLRLRLRR (j : ℕ) : ℕ := if j < 2134 then 1000000040999360 else 1000000041755203
def weightRowRRLRLRLRLR (j : ℕ) : ℕ := if j < 2133 then 1000000040194139 else weightRowRRLRLRLRLRR j
def weightRowRRLRLRLRL (j : ℕ) : ℕ := if j < 2132 then weightRowRRLRLRLRLL j else weightRowRRLRLRLRLR j
def weightRowRRLRLRLRRL (j : ℕ) : ℕ := if j < 2136 then 1000000042461798 else 1000000043119313
def weightRowRRLRLRLRRRR (j : ℕ) : ℕ := if j < 2139 then 1000000044287980 else 1000000044799666
def weightRowRRLRLRLRRR (j : ℕ) : ℕ := if j < 2138 then 1000000043727958 else weightRowRRLRLRLRRRR j
def weightRowRRLRLRLRR (j : ℕ) : ℕ := if j < 2137 then weightRowRRLRLRLRRL j else weightRowRRLRLRLRRR j
def weightRowRRLRLRLR (j : ℕ) : ℕ := if j < 2135 then weightRowRRLRLRLRL j else weightRowRRLRLRLRR j
def weightRowRRLRLRL (j : ℕ) : ℕ := if j < 2130 then weightRowRRLRLRLL j else weightRowRRLRLRLR j
def weightRowRRLRLRRLLL (j : ℕ) : ℕ := if j < 2141 then 1000000045263336 else 1000000045679349
def weightRowRRLRLRRLLRR (j : ℕ) : ℕ := if j < 2144 then 1000000046370010 else 1000000046645546
def weightRowRRLRLRRLLR (j : ℕ) : ℕ := if j < 2143 then 1000000046048098 else weightRowRRLRLRRLLRR j
def weightRowRRLRLRRLL (j : ℕ) : ℕ := if j < 2142 then weightRowRRLRLRRLLL j else weightRowRRLRLRRLLR j
def weightRowRRLRLRRLRL (j : ℕ) : ℕ := if j < 2146 then 1000000046875201 else 1000000047059498
def weightRowRRLRLRRLRRR (j : ℕ) : ℕ := if j < 2149 then 1000000047294271 else 1000000047345947
def weightRowRRLRLRRLRR (j : ℕ) : ℕ := if j < 2148 then 1000000047198993 else weightRowRRLRLRRLRRR j
def weightRowRRLRLRRLR (j : ℕ) : ℕ := if j < 2147 then weightRowRRLRLRRLRL j else weightRowRRLRLRRLRR j
def weightRowRRLRLRRL (j : ℕ) : ℕ := if j < 2145 then weightRowRRLRLRRLL j else weightRowRRLRLRRLR j
def weightRowRRLRLRRRLL (j : ℕ) : ℕ := if j < 2151 then 1000000047354662 else 1000000047321085
def weightRowRRLRLRRRLRR (j : ℕ) : ℕ := if j < 2154 then 1000000047129859 else 1000000046973674
def weightRowRRLRLRRRLR (j : ℕ) : ℕ := if j < 2153 then 1000000047245911 else weightRowRRLRLRRRLRR j
def weightRowRRLRLRRRL (j : ℕ) : ℕ := if j < 2152 then weightRowRRLRLRRRLL j else weightRowRRLRLRRRLR j
def weightRowRRLRLRRRRL (j : ℕ) : ℕ := if j < 2156 then 1000000046778121 else 1000000046543990
def weightRowRRLRLRRRRRR (j : ℕ) : ℕ := if j < 2159 then 1000000045963252 else 1000000045618323
def weightRowRRLRLRRRRR (j : ℕ) : ℕ := if j < 2158 then 1000000046272091 else weightRowRRLRLRRRRRR j
def weightRowRRLRLRRRR (j : ℕ) : ℕ := if j < 2157 then weightRowRRLRLRRRRL j else weightRowRRLRLRRRRR j
def weightRowRRLRLRRR (j : ℕ) : ℕ := if j < 2155 then weightRowRRLRLRRRL j else weightRowRRLRLRRRR j
def weightRowRRLRLRR (j : ℕ) : ℕ := if j < 2150 then weightRowRRLRLRRL j else weightRowRRLRLRRR j
def weightRowRRLRLR (j : ℕ) : ℕ := if j < 2140 then weightRowRRLRLRL j else weightRowRRLRLRR j
def weightRowRRLRL (j : ℕ) : ℕ := if j < 2120 then weightRowRRLRLL j else weightRowRRLRLR j
def weightRowRRLRRLLLLL (j : ℕ) : ℕ := if j < 2161 then 1000000045238171 else 1000000044823679
def weightRowRRLRRLLLLRR (j : ℕ) : ℕ := if j < 2164 then 1000000043895296 else 1000000043383248
def weightRowRRLRRLLLLR (j : ℕ) : ℕ := if j < 2163 then 1000000044375749 else weightRowRRLRRLLLLRR j
def weightRowRRLRRLLLL (j : ℕ) : ℕ := if j < 2162 then weightRowRRLRRLLLLL j else weightRowRRLRRLLLLR j
def weightRowRRLRRLLLRL (j : ℕ) : ℕ := if j < 2166 then 1000000042840549 else 1000000042268153
def weightRowRRLRRLLLRRR (j : ℕ) : ℕ := if j < 2169 then 1000000041038147 else 1000000040382497
def weightRowRRLRRLLLRR (j : ℕ) : ℕ := if j < 2168 then 1000000041667027 else weightRowRRLRRLLLRRR j
def weightRowRRLRRLLLR (j : ℕ) : ℕ := if j < 2167 then weightRowRRLRRLLLRL j else weightRowRRLRRLLLRR j
def weightRowRRLRRLLL (j : ℕ) : ℕ := if j < 2165 then weightRowRRLRRLLLL j else weightRowRRLRRLLLR j
def weightRowRRLRRLLRLL (j : ℕ) : ℕ := if j < 2171 then 1000000039701073 else 1000000038994876
def weightRowRRLRRLLRLRR (j : ℕ) : ℕ := if j < 2174 then 1000000037512197 else 1000000036737746
def weightRowRRLRRLLRLR (j : ℕ) : ℕ := if j < 2173 then 1000000038264913 else weightRowRRLRRLLRLRR j
def weightRowRRLRRLLRL (j : ℕ) : ℕ := if j < 2172 then weightRowRRLRRLLRLL j else weightRowRRLRRLLRLR j
def weightRowRRLRRLLRRL (j : ℕ) : ℕ := if j < 2176 then 1000000035942582 else 1000000035127729
def weightRowRRLRRLLRRRR (j : ℕ) : ℕ := if j < 2179 then 1000000033443060 else 1000000032575298
def weightRowRRLRRLLRRR (j : ℕ) : ℕ := if j < 2178 then 1000000034294213 else weightRowRRLRRLLRRRR j
def weightRowRRLRRLLRR (j : ℕ) : ℕ := if j < 2177 then weightRowRRLRRLLRRL j else weightRowRRLRRLLRRR j
def weightRowRRLRRLLR (j : ℕ) : ℕ := if j < 2175 then weightRowRRLRRLLRL j else weightRowRRLRRLLRR j
def weightRowRRLRRLL (j : ℕ) : ℕ := if j < 2170 then weightRowRRLRRLLL j else weightRowRRLRRLLR j
def weightRowRRLRRLRLLL (j : ℕ) : ℕ := if j < 2181 then 1000000031691953 else 1000000030794050
def weightRowRRLRRLRLLRR (j : ℕ) : ℕ := if j < 2184 then 1000000028958652 else 1000000028023190
def weightRowRRLRRLRLLR (j : ℕ) : ℕ := if j < 2183 then 1000000029882610 else weightRowRRLRRLRLLRR j
def weightRowRRLRRLRLL (j : ℕ) : ℕ := if j < 2182 then weightRowRRLRRLRLLL j else weightRowRRLRRLRLLR j
def weightRowRRLRRLRLRL (j : ℕ) : ℕ := if j < 2186 then 1000000027077235 else 1000000026121790
def weightRowRRLRRLRLRRR (j : ℕ) : ℕ := if j < 2189 then 1000000024186413 else 1000000023208452
def weightRowRRLRRLRLRR (j : ℕ) : ℕ := if j < 2188 then 1000000025157853 else weightRowRRLRRLRLRRR j
def weightRowRRLRRLRLR (j : ℕ) : ℕ := if j < 2187 then weightRowRRLRRLRLRL j else weightRowRRLRRLRLRR j
def weightRowRRLRRLRL (j : ℕ) : ℕ := if j < 2185 then weightRowRRLRRLRLL j else weightRowRRLRRLRLR j
def weightRowRRLRRLRRLL (j : ℕ) : ℕ := if j < 2191 then 1000000022224944 else 1000000021236852
def weightRowRRLRRLRRLRR (j : ℕ) : ℕ := if j < 2194 then 1000000019250721 else 1000000018254555
def weightRowRRLRRLRRLR (j : ℕ) : ℕ := if j < 2193 then 1000000020245130 else weightRowRRLRRLRRLRR j
def weightRowRRLRRLRRL (j : ℕ) : ℕ := if j < 2192 then weightRowRRLRRLRRLL j else weightRowRRLRRLRRLR j
def weightRowRRLRRLRRRL (j : ℕ) : ℕ := if j < 2196 then 1000000017257553 else 1000000016260619
def weightRowRRLRRLRRRRR (j : ℕ) : ℕ := if j < 2199 then 1000000014270519 else 1000000013279094
def weightRowRRLRRLRRRR (j : ℕ) : ℕ := if j < 2198 then 1000000015264648 else weightRowRRLRRLRRRRR j
def weightRowRRLRRLRRR (j : ℕ) : ℕ := if j < 2197 then weightRowRRLRRLRRRL j else weightRowRRLRRLRRRR j
def weightRowRRLRRLRR (j : ℕ) : ℕ := if j < 2195 then weightRowRRLRRLRRL j else weightRowRRLRRLRRR j
def weightRowRRLRRLR (j : ℕ) : ℕ := if j < 2190 then weightRowRRLRRLRL j else weightRowRRLRRLRR j
def weightRowRRLRRL (j : ℕ) : ℕ := if j < 2180 then weightRowRRLRRLL j else weightRowRRLRRLR j
def weightRowRRLRRRLLLL (j : ℕ) : ℕ := if j < 2201 then 1000000012291224 else 1000000011307743
def weightRowRRLRRRLLLRR (j : ℕ) : ℕ := if j < 2204 then 1000000009357199 else 1000000008391721
def weightRowRRLRRRLLLR (j : ℕ) : ℕ := if j < 2203 then 1000000010329468 else weightRowRRLRRRLLLRR j
def weightRowRRLRRRLLL (j : ℕ) : ℕ := if j < 2202 then weightRowRRLRRRLLLL j else weightRowRRLRRRLLLR j
def weightRowRRLRRRLLRL (j : ℕ) : ℕ := if j < 2206 then 1000000007433800 else 1000000006484184
def weightRowRRLRRRLLRRR (j : ℕ) : ℕ := if j < 2209 then 1000000004612767 else 1000000003692368
def weightRowRRLRRRLLRR (j : ℕ) : ℕ := if j < 2208 then 1000000005543602 else weightRowRRLRRRLLRRR j
def weightRowRRLRRRLLR (j : ℕ) : ℕ := if j < 2207 then weightRowRRLRRRLLRL j else weightRowRRLRRRLLRR j
def weightRowRRLRRRLL (j : ℕ) : ℕ := if j < 2205 then weightRowRRLRRRLLL j else weightRowRRLRRRLLR j
def weightRowRRLRRRLRLL (j : ℕ) : ℕ := if j < 2211 then 1000000002783080 else 1000000001885554
def weightRowRRLRRRLRLRR (j : ℕ) : ℕ := if j < 2214 then 1000000000128297 else 999999999269769
def weightRowRRLRRRLRLR (j : ℕ) : ℕ := if j < 2213 then 1000000001000422 else weightRowRRLRRRLRLRR j
def weightRowRRLRRRLRL (j : ℕ) : ℕ := if j < 2212 then weightRowRRLRRRLRLL j else weightRowRRLRRRLRLR j
def weightRowRRLRRRLRRL (j : ℕ) : ℕ := if j < 2216 then 999999998425409 else 999999997595765
def weightRowRRLRRRLRRRR (j : ℕ) : ℕ := if j < 2219 then 999999995982716 else 999999995200300
def weightRowRRLRRRLRRR (j : ℕ) : ℕ := if j < 2218 then 999999996781365 else weightRowRRLRRRLRRRR j
def weightRowRRLRRRLRR (j : ℕ) : ℕ := if j < 2217 then weightRowRRLRRRLRRL j else weightRowRRLRRRLRRR j
def weightRowRRLRRRLR (j : ℕ) : ℕ := if j < 2215 then weightRowRRLRRRLRL j else weightRowRRLRRRLRR j
def weightRowRRLRRRL (j : ℕ) : ℕ := if j < 2210 then weightRowRRLRRRLL j else weightRowRRLRRRLR j
def weightRowRRLRRRRLLL (j : ℕ) : ℕ := if j < 2221 then 999999994434581 else 999999993686000
def weightRowRRLRRRRLLRR (j : ℕ) : ℕ := if j < 2224 then 999999992241898 else 999999991547149
def weightRowRRLRRRRLLR (j : ℕ) : ℕ := if j < 2223 then 999999992954973 else weightRowRRLRRRRLLRR j
def weightRowRRLRRRRLL (j : ℕ) : ℕ := if j < 2222 then weightRowRRLRRRRLLL j else weightRowRRLRRRRLLR j
def weightRowRRLRRRRLRL (j : ℕ) : ℕ := if j < 2226 then 999999990871076 else 999999990214009
def weightRowRRLRRRRLRRR (j : ℕ) : ℕ := if j < 2229 then 999999988958100 else 999999988359805
def weightRowRRLRRRRLRR (j : ℕ) : ℕ := if j < 2228 then 999999989576256 else weightRowRRLRRRRLRRR j
def weightRowRRLRRRRLR (j : ℕ) : ℕ := if j < 2227 then weightRowRRLRRRRLRL j else weightRowRRLRRRRLRR j
def weightRowRRLRRRRL (j : ℕ) : ℕ := if j < 2225 then weightRowRRLRRRRLL j else weightRowRRLRRRRLR j
def weightRowRRLRRRRRLL (j : ℕ) : ℕ := if j < 2231 then 999999987781611 else 999999987223737
def weightRowRRLRRRRRLRR (j : ℕ) : ℕ := if j < 2234 then 999999986169709 else 999999985673883
def weightRowRRLRRRRRLR (j : ℕ) : ℕ := if j < 2233 then 999999986686378 else weightRowRRLRRRRRLRR j
def weightRowRRLRRRRRL (j : ℕ) : ℕ := if j < 2232 then weightRowRRLRRRRRLL j else weightRowRRLRRRRRLR j
def weightRowRRLRRRRRRL (j : ℕ) : ℕ := if j < 2236 then 999999985199032 else 999999984745265
def weightRowRRLRRRRRRRR (j : ℕ) : ℕ := if j < 2239 then 999999983901316 else 999999983511250
def weightRowRRLRRRRRRR (j : ℕ) : ℕ := if j < 2238 then 999999984312670 else weightRowRRLRRRRRRRR j
def weightRowRRLRRRRRR (j : ℕ) : ℕ := if j < 2237 then weightRowRRLRRRRRRL j else weightRowRRLRRRRRRR j
def weightRowRRLRRRRR (j : ℕ) : ℕ := if j < 2235 then weightRowRRLRRRRRL j else weightRowRRLRRRRRR j
def weightRowRRLRRRR (j : ℕ) : ℕ := if j < 2230 then weightRowRRLRRRRL j else weightRowRRLRRRRR j
def weightRowRRLRRR (j : ℕ) : ℕ := if j < 2220 then weightRowRRLRRRL j else weightRowRRLRRRR j
def weightRowRRLRR (j : ℕ) : ℕ := if j < 2200 then weightRowRRLRRL j else weightRowRRLRRR j
def weightRowRRLR (j : ℕ) : ℕ := if j < 2160 then weightRowRRLRL j else weightRowRRLRR j
def weightRowRRL (j : ℕ) : ℕ := if j < 2080 then weightRowRRLL j else weightRowRRLR j
def weightRowRRRLLLLLLL (j : ℕ) : ℕ := if j < 2241 then 999999983142498 else 999999982795066
def weightRowRRRLLLLLLRR (j : ℕ) : ℕ := if j < 2244 then 999999982164089 else 999999981880458
def weightRowRRRLLLLLLR (j : ℕ) : ℕ := if j < 2243 then 999999982468941 else weightRowRRRLLLLLLRR j
def weightRowRRRLLLLLL (j : ℕ) : ℕ := if j < 2242 then weightRowRRRLLLLLLL j else weightRowRRRLLLLLLR j
def weightRowRRRLLLLLRL (j : ℕ) : ℕ := if j < 2246 then 999999981617975 else 999999981376550
def weightRowRRRLLLLLRRR (j : ℕ) : ℕ := if j < 2249 then 999999980956423 else 999999980777448
def weightRowRRRLLLLLRR (j : ℕ) : ℕ := if j < 2248 then 999999981156075 else weightRowRRRLLLLLRRR j
def weightRowRRRLLLLLR (j : ℕ) : ℕ := if j < 2247 then weightRowRRRLLLLLRL j else weightRowRRRLLLLLRR j
def weightRowRRRLLLLL (j : ℕ) : ℕ := if j < 2245 then weightRowRRRLLLLLL j else weightRowRRRLLLLLR j
def weightRowRRRLLLLRLL (j : ℕ) : ℕ := if j < 2251 then 999999980618990 else 999999980480870
def weightRowRRRLLLLRLRR (j : ℕ) : ℕ := if j < 2254 then 999999980264849 else 999999980186511
def weightRowRRRLLLLRLR (j : ℕ) : ℕ := if j < 2253 then 999999980362894 else weightRowRRRLLLLRLRR j
def weightRowRRRLLLLRL (j : ℕ) : ℕ := if j < 2252 then weightRowRRRLLLLRLL j else weightRowRRRLLLLRLR j
def weightRowRRRLLLLRRL (j : ℕ) : ℕ := if j < 2256 then 999999980127637 else 999999980087971
def weightRowRRRLLLLRRRR (j : ℕ) : ℕ := if j < 2259 then 999999980065169 else 999999980081451
def weightRowRRRLLLLRRR (j : ℕ) : ℕ := if j < 2258 then 999999980067243 else weightRowRRRLLLLRRRR j
def weightRowRRRLLLLRR (j : ℕ) : ℕ := if j < 2257 then weightRowRRRLLLLRRL j else weightRowRRRLLLLRRR j
def weightRowRRRLLLLR (j : ℕ) : ℕ := if j < 2255 then weightRowRRRLLLLRL j else weightRowRRRLLLLRR j
def weightRowRRRLLLL (j : ℕ) : ℕ := if j < 2250 then weightRowRRRLLLLL j else weightRowRRRLLLLR j
def weightRowRRRLLLRLLL (j : ℕ) : ℕ := if j < 2261 then 999999980115781 else 999999980167835
def weightRowRRRLLLRLLRR (j : ℕ) : ℕ := if j < 2264 then 999999980323768 else 999999980426947
def weightRowRRRLLLRLLR (j : ℕ) : ℕ := if j < 2263 then 999999980237279 else weightRowRRRLLLRLLRR j
def weightRowRRRLLLRLL (j : ℕ) : ℕ := if j < 2262 then weightRowRRRLLLRLLL j else weightRowRRRLLLRLLR j
def weightRowRRRLLLRLRL (j : ℕ) : ℕ := if j < 2266 then 999999980546448 else 999999980681897
def weightRowRRRLLLRLRRR (j : ℕ) : ℕ := if j < 2269 then 999999980999086 else 999999981180031
def weightRowRRRLLLRLRR (j : ℕ) : ℕ := if j < 2268 then 999999980832907 else weightRowRRRLLLRLRRR j
def weightRowRRRLLLRLR (j : ℕ) : ℕ := if j < 2267 then weightRowRRRLLLRLRL j else weightRowRRRLLLRLRR j
def weightRowRRRLLLRL (j : ℕ) : ℕ := if j < 2265 then weightRowRRRLLLRLL j else weightRowRRRLLLRLR j
def weightRowRRRLLLRRLL (j : ℕ) : ℕ := if j < 2271 then 999999981375333 else 999999981584575
def weightRowRRRLLLRRLRR (j : ℕ) : ℕ := if j < 2274 then 999999982043182 else 999999982291683
def weightRowRRRLLLRRLR (j : ℕ) : ℕ := if j < 2273 then 999999981807334 else weightRowRRRLLLRRLRR j
def weightRowRRRLLLRRL (j : ℕ) : ℕ := if j < 2272 then weightRowRRRLLLRRLL j else weightRowRRRLLLRRLR j
def weightRowRRRLLLRRRL (j : ℕ) : ℕ := if j < 2276 then 999999982552397 else 999999982824882
def weightRowRRRLLLRRRRR (j : ℕ) : ℕ := if j < 2279 then 999999983403364 else 999999983708457
def weightRowRRRLLLRRRR (j : ℕ) : ℕ := if j < 2278 then 999999983108688 else weightRowRRRLLLRRRRR j
def weightRowRRRLLLRRR (j : ℕ) : ℕ := if j < 2277 then weightRowRRRLLLRRRL j else weightRowRRRLLLRRRR j
def weightRowRRRLLLRR (j : ℕ) : ℕ := if j < 2275 then weightRowRRRLLLRRL j else weightRowRRRLLLRRR j
def weightRowRRRLLLR (j : ℕ) : ℕ := if j < 2270 then weightRowRRRLLLRL j else weightRowRRRLLLRR j
def weightRowRRRLLL (j : ℕ) : ℕ := if j < 2260 then weightRowRRRLLLL j else weightRowRRRLLLR j
def weightRowRRRLLRLLLL (j : ℕ) : ℕ := if j < 2281 then 999999984023508 else 999999984348061
def weightRowRRRLLRLLLRR (j : ℕ) : ℕ := if j < 2284 then 999999985023826 else 999999985374116
def weightRowRRRLLRLLLR (j : ℕ) : ℕ := if j < 2283 then 999999984681653 else weightRowRRRLLRLLLRR j
def weightRowRRRLLRLLL (j : ℕ) : ℕ := if j < 2282 then weightRowRRRLLRLLLL j else weightRowRRRLLRLLLR j
def weightRowRRRLLRLLRL (j : ℕ) : ℕ := if j < 2286 then 999999985732064 else 999999986097208
def weightRowRRRLLRLLRRR (j : ℕ) : ℕ := if j < 2289 then 999999986847245 else 999999987231223
def weightRowRRRLLRLLRR (j : ℕ) : ℕ := if j < 2288 then 999999986469087 else weightRowRRRLLRLLRRR j
def weightRowRRRLLRLLR (j : ℕ) : ℕ := if j < 2287 then weightRowRRRLLRLLRL j else weightRowRRRLLRLLRR j
def weightRowRRRLLRLL (j : ℕ) : ℕ := if j < 2285 then weightRowRRRLLRLLL j else weightRowRRRLLRLLR j
def weightRowRRRLLRLRLL (j : ℕ) : ℕ := if j < 2291 then 999999987620568 else 999999988014828
def weightRowRRRLLRLRLRR (j : ℕ) : ℕ := if j < 2294 then 999999988816303 else 999999989222631
def weightRowRRRLLRLRLR (j : ℕ) : ℕ := if j < 2293 then 999999988413555 else weightRowRRRLLRLRLRR j
def weightRowRRRLLRLRL (j : ℕ) : ℕ := if j < 2292 then weightRowRRRLLRLRLL j else weightRowRRRLLRLRLR j
def weightRowRRRLLRLRRL (j : ℕ) : ℕ := if j < 2296 then 999999989632103 else 999999990044286
def weightRowRRRLLRLRRRR (j : ℕ) : ℕ := if j < 2299 then 999999990875082 else 999999991292856
def weightRowRRRLLRLRRR (j : ℕ) : ℕ := if j < 2298 then 999999990458753 else weightRowRRRLLRLRRRR j
def weightRowRRRLLRLRR (j : ℕ) : ℕ := if j < 2297 then weightRowRRRLLRLRRL j else weightRowRRRLLRLRRR j
def weightRowRRRLLRLR (j : ℕ) : ℕ := if j < 2295 then weightRowRRRLLRLRL j else weightRowRRRLLRLRR j
def weightRowRRRLLRL (j : ℕ) : ℕ := if j < 2290 then weightRowRRRLLRLL j else weightRowRRRLLRLR j
def weightRowRRRLLRRLLL (j : ℕ) : ℕ := if j < 2301 then 999999991711666 else 999999992131107
def weightRowRRRLLRRLLRR (j : ℕ) : ℕ := if j < 2304 then 999999992970298 else 1000000000000000
def weightRowRRRLLRRLLR (j : ℕ) : ℕ := if j < 2303 then 999999992550781 else weightRowRRRLLRRLLRR j
def weightRowRRRLLRRLL (j : ℕ) : ℕ := if j < 2302 then weightRowRRRLLRRLLL j else weightRowRRRLLRRLLR j
def weightRowRRRLLRRL (j : ℕ) : ℕ := if j < 2305 then weightRowRRRLLRRLL j else 1000000000000000
def weightRowRRRLLRR (j : ℕ) : ℕ := if j < 2310 then weightRowRRRLLRRL j else 1000000000000000
def weightRowRRRLLR (j : ℕ) : ℕ := if j < 2300 then weightRowRRRLLRL j else weightRowRRRLLRR j
def weightRowRRRLL (j : ℕ) : ℕ := if j < 2280 then weightRowRRRLLL j else weightRowRRRLLR j
def weightRowRRRLRLLLLL (j : ℕ) : ℕ := if j < 2321 then 1000000000000000 else 1000000000095587
def weightRowRRRLRLLLLRR (j : ℕ) : ℕ := if j < 2324 then 1000000000795009 else 1000000001135139
def weightRowRRRLRLLLLR (j : ℕ) : ℕ := if j < 2323 then 1000000000448422 else weightRowRRRLRLLLLRR j
def weightRowRRRLRLLLL (j : ℕ) : ℕ := if j < 2322 then weightRowRRRLRLLLLL j else weightRowRRRLRLLLLR j
def weightRowRRRLRLLLRL (j : ℕ) : ℕ := if j < 2326 then 1000000001468613 else 1000000001795241
def weightRowRRRLRLLLRRR (j : ℕ) : ℕ := if j < 2329 then 1000000002427249 else 1000000002732297
def weightRowRRRLRLLLRR (j : ℕ) : ℕ := if j < 2328 then 1000000002114844 else weightRowRRRLRLLLRRR j
def weightRowRRRLRLLLR (j : ℕ) : ℕ := if j < 2327 then weightRowRRRLRLLLRL j else weightRowRRRLRLLLRR j
def weightRowRRRLRLLL (j : ℕ) : ℕ := if j < 2325 then weightRowRRRLRLLLL j else weightRowRRRLRLLLR j
def weightRowRRRLRLLRLL (j : ℕ) : ℕ := if j < 2331 then 1000000003029836 else 1000000003319724
def weightRowRRRLRLLRLRR (j : ℕ) : ℕ := if j < 2334 then 1000000003876022 else 1000000004142195
def weightRowRRRLRLLRLR (j : ℕ) : ℕ := if j < 2333 then 1000000003601827 else weightRowRRRLRLLRLRR j
def weightRowRRRLRLLRL (j : ℕ) : ℕ := if j < 2332 then weightRowRRRLRLLRLL j else weightRowRRRLRLLRLR j
def weightRowRRRLRLLRRL (j : ℕ) : ℕ := if j < 2336 then 1000000004400242 else 1000000004650065
def weightRowRRRLRLLRRRR (j : ℕ) : ℕ := if j < 2339 then 1000000005124705 else 1000000005349374
def weightRowRRRLRLLRRR (j : ℕ) : ℕ := if j < 2338 then 1000000004891579 else weightRowRRRLRLLRRRR j
def weightRowRRRLRLLRR (j : ℕ) : ℕ := if j < 2337 then weightRowRRRLRLLRRL j else weightRowRRRLRLLRRR j
def weightRowRRRLRLLR (j : ℕ) : ℕ := if j < 2335 then weightRowRRRLRLLRL j else weightRowRRRLRLLRR j
def weightRowRRRLRLL (j : ℕ) : ℕ := if j < 2330 then weightRowRRRLRLLL j else weightRowRRRLRLLR j
def weightRowRRRLRLRLLL (j : ℕ) : ℕ := if j < 2341 then 1000000005565526 else 1000000005773109
def weightRowRRRLRLRLLRR (j : ℕ) : ℕ := if j < 2344 then 1000000006162406 else 1000000006344059
def weightRowRRRLRLRLLR (j : ℕ) : ℕ := if j < 2343 then 1000000005972081 else weightRowRRRLRLRLLRR j
def weightRowRRRLRLRLL (j : ℕ) : ℕ := if j < 2342 then weightRowRRRLRLRLLL j else weightRowRRRLRLRLLR j
def weightRowRRRLRLRLRL (j : ℕ) : ℕ := if j < 2346 then 1000000006517020 else 1000000006681280
def weightRowRRRLRLRLRRR (j : ℕ) : ℕ := if j < 2349 then 1000000006983695 else 1000000007121868
def weightRowRRRLRLRLRR (j : ℕ) : ℕ := if j < 2348 then 1000000006836836 else weightRowRRRLRLRLRRR j
def weightRowRRRLRLRLR (j : ℕ) : ℕ := if j < 2347 then weightRowRRRLRLRLRL j else weightRowRRRLRLRLRR j
def weightRowRRRLRLRL (j : ℕ) : ℕ := if j < 2345 then weightRowRRRLRLRLL j else weightRowRRRLRLRLR j
def weightRowRRRLRLRRLL (j : ℕ) : ℕ := if j < 2351 then 1000000007251378 else 1000000007372251
def weightRowRRRLRLRRLRR (j : ℕ) : ℕ := if j < 2354 then 1000000007588235 else 1000000007683438
def weightRowRRRLRLRRLR (j : ℕ) : ℕ := if j < 2353 then 1000000007484523 else weightRowRRRLRLRRLRR j
def weightRowRRRLRLRRL (j : ℕ) : ℕ := if j < 2352 then weightRowRRRLRLRRLL j else weightRowRRRLRLRRLR j
def weightRowRRRLRLRRRL (j : ℕ) : ℕ := if j < 2356 then 1000000007770187 else 1000000007848543
def weightRowRRRLRLRRRRR (j : ℕ) : ℕ := if j < 2359 then 1000000007980360 else 1000000008033976
def weightRowRRRLRLRRRR (j : ℕ) : ℕ := if j < 2358 then 1000000007918576 else weightRowRRRLRLRRRRR j
def weightRowRRRLRLRRR (j : ℕ) : ℕ := if j < 2357 then weightRowRRRLRLRRRL j else weightRowRRRLRLRRRR j
def weightRowRRRLRLRR (j : ℕ) : ℕ := if j < 2355 then weightRowRRRLRLRRL j else weightRowRRRLRLRRR j
def weightRowRRRLRLR (j : ℕ) : ℕ := if j < 2350 then weightRowRRRLRLRL j else weightRowRRRLRLRR j
def weightRowRRRLRL (j : ℕ) : ℕ := if j < 2340 then weightRowRRRLRLL j else weightRowRRRLRLR j
def weightRowRRRLRRLLLL (j : ℕ) : ℕ := if j < 2361 then 1000000008079511 else 1000000008117056
def weightRowRRRLRRLLLRR (j : ℕ) : ℕ := if j < 2364 then 1000000008168578 else 1000000008182764
def weightRowRRRLRRLLLR (j : ℕ) : ℕ := if j < 2363 then 1000000008146711 else weightRowRRRLRRLLLRR j
def weightRowRRRLRRLLL (j : ℕ) : ℕ := if j < 2362 then weightRowRRRLRRLLLL j else weightRowRRRLRRLLLR j
def weightRowRRRLRRLLRL (j : ℕ) : ℕ := if j < 2366 then 1000000008189385 else 1000000008188556
def weightRowRRRLRRLLRRR (j : ℕ) : ℕ := if j < 2369 then 1000000008165049 else 1000000008142628
def weightRowRRRLRRLLRR (j : ℕ) : ℕ := if j < 2368 then 1000000008180402 else weightRowRRRLRRLLRRR j
def weightRowRRRLRRLLR (j : ℕ) : ℕ := if j < 2367 then weightRowRRRLRRLLRL j else weightRowRRRLRRLLRR j
def weightRowRRRLRRLL (j : ℕ) : ℕ := if j < 2365 then weightRowRRRLRRLLL j else weightRowRRRLRRLLR j
def weightRowRRRLRRLRLL (j : ℕ) : ℕ := if j < 2371 then 1000000008113274 else 1000000008077127
def weightRowRRRLRRLRLRR (j : ℕ) : ℕ := if j < 2374 then 1000000007985028 else 1000000007929371
def weightRowRRRLRRLRLR (j : ℕ) : ℕ := if j < 2373 then 1000000008034329 else weightRowRRRLRRLRLRR j
def weightRowRRRLRRLRL (j : ℕ) : ℕ := if j < 2372 then weightRowRRRLRRLRLL j else weightRowRRRLRRLRLR j
def weightRowRRRLRRLRRL (j : ℕ) : ℕ := if j < 2376 then 1000000007867512 else 1000000007799607
def weightRowRRRLRRLRRRR (j : ℕ) : ℕ := if j < 2379 then 1000000007646294 else 1000000007561211
def weightRowRRRLRRLRRR (j : ℕ) : ℕ := if j < 2378 then 1000000007725814 else weightRowRRRLRRLRRRR j
def weightRowRRRLRRLRR (j : ℕ) : ℕ := if j < 2377 then weightRowRRRLRRLRRL j else weightRowRRRLRRLRRR j
def weightRowRRRLRRLR (j : ℕ) : ℕ := if j < 2375 then weightRowRRRLRRLRL j else weightRowRRRLRRLRR j
def weightRowRRRLRRL (j : ℕ) : ℕ := if j < 2370 then weightRowRRRLRRLL j else weightRowRRRLRRLR j
def weightRowRRRLRRRLLL (j : ℕ) : ℕ := if j < 2381 then 1000000007470729 else 1000000007375017
def weightRowRRRLRRRLLRR (j : ℕ) : ℕ := if j < 2384 then 1000000007168582 else 1000000007058203
def weightRowRRRLRRRLLR (j : ℕ) : ℕ := if j < 2383 then 1000000007274244 else weightRowRRRLRRRLLRR j
def weightRowRRRLRRRLL (j : ℕ) : ℕ := if j < 2382 then weightRowRRRLRRRLLL j else weightRowRRRLRRRLLR j
def weightRowRRRLRRRLRL (j : ℕ) : ℕ := if j < 2386 then 1000000006943280 else 1000000006823990
def weightRowRRRLRRRLRRR (j : ℕ) : ℕ := if j < 2389 then 1000000006573013 else 1000000006441680
def weightRowRRRLRRRLRR (j : ℕ) : ℕ := if j < 2388 then 1000000006700509 else weightRowRRRLRRRLRRR j
def weightRowRRRLRRRLR (j : ℕ) : ℕ := if j < 2387 then weightRowRRRLRRRLRL j else weightRowRRRLRRRLRR j
def weightRowRRRLRRRL (j : ℕ) : ℕ := if j < 2385 then weightRowRRRLRRRLL j else weightRowRRRLRRRLR j
def weightRowRRRLRRRRLL (j : ℕ) : ℕ := if j < 2391 then 1000000006306689 else 1000000006168219
def weightRowRRRLRRRRLRR (j : ℕ) : ℕ := if j < 2394 then 1000000005881553 else 1000000005733715
def weightRowRRRLRRRRLR (j : ℕ) : ℕ := if j < 2393 then 1000000006026447 else weightRowRRRLRRRRLRR j
def weightRowRRRLRRRRL (j : ℕ) : ℕ := if j < 2392 then weightRowRRRLRRRRLL j else weightRowRRRLRRRRLR j
def weightRowRRRLRRRRRL (j : ℕ) : ℕ := if j < 2396 then 1000000005583113 else 1000000005429923
def weightRowRRRLRRRRRRR (j : ℕ) : ℕ := if j < 2399 then 1000000005116492 else 1000000004956603
def weightRowRRRLRRRRRR (j : ℕ) : ℕ := if j < 2398 then 1000000005274324 else weightRowRRRLRRRRRRR j
def weightRowRRRLRRRRR (j : ℕ) : ℕ := if j < 2397 then weightRowRRRLRRRRRL j else weightRowRRRLRRRRRR j
def weightRowRRRLRRRR (j : ℕ) : ℕ := if j < 2395 then weightRowRRRLRRRRL j else weightRowRRRLRRRRR j
def weightRowRRRLRRR (j : ℕ) : ℕ := if j < 2390 then weightRowRRRLRRRL j else weightRowRRRLRRRR j
def weightRowRRRLRR (j : ℕ) : ℕ := if j < 2380 then weightRowRRRLRRL j else weightRowRRRLRRR j
def weightRowRRRLR (j : ℕ) : ℕ := if j < 2360 then weightRowRRRLRL j else weightRowRRRLRR j
def weightRowRRRL (j : ℕ) : ℕ := if j < 2320 then weightRowRRRLL j else weightRowRRRLR j
def weightRowRRRRLLLLLL (j : ℕ) : ℕ := if j < 2401 then 1000000004794831 else 1000000004631352
def weightRowRRRRLLLLLRR (j : ℕ) : ℕ := if j < 2404 then 1000000004299958 else 1000000004132383
def weightRowRRRRLLLLLR (j : ℕ) : ℕ := if j < 2403 then 1000000004466337 else weightRowRRRRLLLLLRR j
def weightRowRRRRLLLLL (j : ℕ) : ℕ := if j < 2402 then weightRowRRRRLLLLLL j else weightRowRRRRLLLLLR j
def weightRowRRRRLLLLRL (j : ℕ) : ℕ := if j < 2406 then 1000000003963782 else 1000000003794320
def weightRowRRRRLLLLRRR (j : ℕ) : ℕ := if j < 2409 then 1000000003453472 else 1000000003282408
def weightRowRRRRLLLLRR (j : ℕ) : ℕ := if j < 2408 then 1000000003624163 else weightRowRRRRLLLLRRR j
def weightRowRRRRLLLLR (j : ℕ) : ℕ := if j < 2407 then weightRowRRRRLLLLRL j else weightRowRRRRLLLLRR j
def weightRowRRRRLLLL (j : ℕ) : ℕ := if j < 2405 then weightRowRRRRLLLLL j else weightRowRRRRLLLLR j
def weightRowRRRRLLLRLL (j : ℕ) : ℕ := if j < 2411 then 1000000003111128 else 1000000002939790
def weightRowRRRRLLLRLRR (j : ℕ) : ℕ := if j < 2414 then 1000000002597549 else 1000000002426945
def weightRowRRRRLLLRLR (j : ℕ) : ℕ := if j < 2413 then 1000000002768547 else weightRowRRRRLLLRLRR j
def weightRowRRRRLLLRL (j : ℕ) : ℕ := if j < 2412 then weightRowRRRRLLLRLL j else weightRowRRRRLLLRLR j
def weightRowRRRRLLLRRL (j : ℕ) : ℕ := if j < 2416 then 1000000002256882 else 1000000002087501
def weightRowRRRRLLLRRRR (j : ℕ) : ℕ := if j < 2419 then 1000000001751347 else 1000000001584846
def weightRowRRRRLLLRRR (j : ℕ) : ℕ := if j < 2418 then 1000000001918944 else weightRowRRRRLLLRRRR j
def weightRowRRRRLLLRR (j : ℕ) : ℕ := if j < 2417 then weightRowRRRRLLLRRL j else weightRowRRRRLLLRRR j
def weightRowRRRRLLLR (j : ℕ) : ℕ := if j < 2415 then weightRowRRRRLLLRL j else weightRowRRRRLLLRR j
def weightRowRRRRLLL (j : ℕ) : ℕ := if j < 2410 then weightRowRRRRLLLL j else weightRowRRRRLLLR j
def weightRowRRRRLLRLLL (j : ℕ) : ℕ := if j < 2421 then 1000000001419570 else 1000000001255650
def weightRowRRRRLLRLLRR (j : ℕ) : ℕ := if j < 2424 then 1000000000932369 else 1000000000773249
def weightRowRRRRLLRLLR (j : ℕ) : ℕ := if j < 2423 then 1000000001093209 else weightRowRRRRLLRLLRR j
def weightRowRRRRLLRLL (j : ℕ) : ℕ := if j < 2422 then weightRowRRRRLLRLLL j else weightRowRRRRLLRLLR j
def weightRowRRRRLLRLRL (j : ℕ) : ℕ := if j < 2426 then 1000000000615965 else 1000000000460627
def weightRowRRRRLLRLRRR (j : ℕ) : ℕ := if j < 2429 then 1000000000156220 else 1000000000007358
def weightRowRRRRLLRLRR (j : ℕ) : ℕ := if j < 2428 then 1000000000307344 else weightRowRRRRLLRLRRR j
def weightRowRRRRLLRLR (j : ℕ) : ℕ := if j < 2427 then weightRowRRRRLLRLRL j else weightRowRRRRLLRLRR j
def weightRowRRRRLLRL (j : ℕ) : ℕ := if j < 2425 then weightRowRRRRLLRLL j else weightRowRRRRLLRLR j
def weightRowRRRRLLR (j : ℕ) : ℕ := if j < 2430 then weightRowRRRRLLRL j else 1000000000000000
def weightRowRRRRLL (j : ℕ) : ℕ := if j < 2420 then weightRowRRRRLLL j else weightRowRRRRLLR j
def weightRowRRRRL (j : ℕ) : ℕ := if j < 2440 then weightRowRRRRLL j else 1000000000000000
def weightRowRRRRRRLRRRR (j : ℕ) : ℕ := if j < 2539 then 1000000000070767 else 1000000000130881
def weightRowRRRRRRLRRR (j : ℕ) : ℕ := if j < 2538 then 1000000000009589 else weightRowRRRRRRLRRRR j
def weightRowRRRRRRLRR (j : ℕ) : ℕ := if j < 2537 then 1000000000000000 else weightRowRRRRRRLRRR j
def weightRowRRRRRRLR (j : ℕ) : ℕ := if j < 2535 then 1000000000000000 else weightRowRRRRRRLRR j
def weightRowRRRRRRL (j : ℕ) : ℕ := if j < 2530 then 1000000000000000 else weightRowRRRRRRLR j
def weightRowRRRRRRRLLL (j : ℕ) : ℕ := if j < 2541 then 1000000000189892 else 1000000000247767
def weightRowRRRRRRRLLRR (j : ℕ) : ℕ := if j < 2544 then 1000000000359966 else 1000000000414227
def weightRowRRRRRRRLLR (j : ℕ) : ℕ := if j < 2543 then 1000000000304469 else weightRowRRRRRRRLLRR j
def weightRowRRRRRRRLL (j : ℕ) : ℕ := if j < 2542 then weightRowRRRRRRRLLL j else weightRowRRRRRRRLLR j
def weightRowRRRRRRRLRL (j : ℕ) : ℕ := if j < 2546 then 1000000000467223 else 1000000000518926
def weightRowRRRRRRRLRRR (j : ℕ) : ℕ := if j < 2549 then 1000000000618351 else 1000000000666026
def weightRowRRRRRRRLRR (j : ℕ) : ℕ := if j < 2548 then 1000000000569310 else weightRowRRRRRRRLRRR j
def weightRowRRRRRRRLR (j : ℕ) : ℕ := if j < 2547 then weightRowRRRRRRRLRL j else weightRowRRRRRRRLRR j
def weightRowRRRRRRRL (j : ℕ) : ℕ := if j < 2545 then weightRowRRRRRRRLL j else weightRowRRRRRRRLR j
def weightRowRRRRRRRRLL (j : ℕ) : ℕ := if j < 2551 then 1000000000712314 else 1000000000757196
def weightRowRRRRRRRRLRR (j : ℕ) : ℕ := if j < 2554 then 1000000000842670 else 1000000000883232
def weightRowRRRRRRRRLR (j : ℕ) : ℕ := if j < 2553 then 1000000000800653 else weightRowRRRRRRRRLRR j
def weightRowRRRRRRRRL (j : ℕ) : ℕ := if j < 2552 then weightRowRRRRRRRRLL j else weightRowRRRRRRRRLR j
def weightRowRRRRRRRRRL (j : ℕ) : ℕ := if j < 2556 then 1000000000922327 else 1000000000959942
def weightRowRRRRRRRRRRR (j : ℕ) : ℕ := if j < 2559 then 1000000001030697 else 1000000001063821
def weightRowRRRRRRRRRR (j : ℕ) : ℕ := if j < 2558 then 1000000000996068 else weightRowRRRRRRRRRRR j
def weightRowRRRRRRRRR (j : ℕ) : ℕ := if j < 2557 then weightRowRRRRRRRRRL j else weightRowRRRRRRRRRR j
def weightRowRRRRRRRR (j : ℕ) : ℕ := if j < 2555 then weightRowRRRRRRRRL j else weightRowRRRRRRRRR j
def weightRowRRRRRRR (j : ℕ) : ℕ := if j < 2550 then weightRowRRRRRRRL j else weightRowRRRRRRRR j
def weightRowRRRRRR (j : ℕ) : ℕ := if j < 2540 then weightRowRRRRRRL j else weightRowRRRRRRR j
def weightRowRRRRR (j : ℕ) : ℕ := if j < 2520 then 1000000000000000 else weightRowRRRRRR j
def weightRowRRRR (j : ℕ) : ℕ := if j < 2480 then weightRowRRRRL j else weightRowRRRRR j
def weightRowRRR (j : ℕ) : ℕ := if j < 2400 then weightRowRRRL j else weightRowRRRR j
def weightRowRR (j : ℕ) : ℕ := if j < 2240 then weightRowRRL j else weightRowRRR j
def weightRowR (j : ℕ) : ℕ := if j < 1920 then weightRowRL j else weightRowRR j
def weightRow (j : ℕ) : ℕ := if j < 1280 then weightRowL j else weightRowR j

def kernelDen : ℕ := 32896
def weightDen : ℕ := 1000000000000000
def kernelN (i : ℕ) : ℕ := 256-i
def weightN (j : ℕ) : ℕ := if j < 2560 then weightRow j else weightDen


/-- Primitive recursive sum; its bridge to finite sums is proved below. -/
def sumN (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => sumN f n + f n

lemma sumN_eq_sum_range (f : ℕ → ℕ) (n : ℕ) :
    sumN f n = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp [sumN]
  | succ n ih => simp only [sumN, sum_range_succ, ih]

def coverRec (q : ℕ) : ℕ := sumN (fun i => kernelN (255-i)*weightN (q+i)) 256
def energyAN : ℕ := sumN (fun i => kernelN i ^ 2) 256
def weightNormN : ℕ := sumN (fun j => weightN j ^ 2) 2560
def energyBZ : ℤ := (weightNormN:ℤ) - 9 * 256 * weightDen^2

noncomputable def p (i : ℕ) : ℝ := (kernelN i:ℝ)/kernelDen
noncomputable def wRight (j : ℕ) : ℝ := (weightN j:ℝ)/weightDen
def wLeft (_j : ℕ) : ℝ := 1
noncomputable def a : ℝ := 256 * ∑ i ∈ range 256, p i^2
noncomputable def b : ℝ := 1 + (∑ j ∈ range 2560, wRight j^2)/256 - 10

lemma kernel_mass_integer : sumN kernelN 256 = kernelDen := by
  decide +kernel

lemma kernel_nonnegative (i : ℕ) : 0 ≤ p i := by
  unfold p
  positivity

lemma kernel_mass : (∑ i ∈ range 256, p i) = 1 := by
  have hi : (∑ i ∈ range 256, kernelN i) = kernelDen := by
    simpa only [sumN_eq_sum_range] using kernel_mass_integer
  have hr : (∑ i ∈ range 256, (kernelN i:ℝ)) = (kernelDen:ℝ) := by
    exact_mod_cast hi
  unfold p
  rw [← sum_div, hr]
  norm_num [kernelDen]

lemma kernel_formula (i : ℕ) : p i = ((256-i:ℕ):ℝ)/32896 := rfl

lemma left_tail (j : ℕ) : wLeft j = 1 := rfl

lemma right_tail (j : ℕ) (hj : 2560 ≤ j) : wRight j = 1 := by
  unfold wRight weightN
  rw [if_neg (by omega)]
  norm_num [weightDen]

lemma left_cover (q : ℕ) :
    1 ≤ ∑ i ∈ range 256, p i*wLeft (q+i) := by
  simp only [wLeft, mul_one, kernel_mass, le_refl]

lemma right_cover_eq (q : ℕ) :
    (∑ i ∈ range 256, p (255-i)*wRight (q+i)) =
      (coverRec q:ℝ)/(kernelDen*weightDen) := by
  unfold p wRight coverRec
  rw [sumN_eq_sum_range]
  simp_rw [div_mul_div_comm, ← sum_div]
  push_cast
  rfl

lemma a_eq_integer : a = 256*(energyAN:ℝ)/(kernelDen:ℝ)^2 := by
  unfold a p energyAN
  rw [sumN_eq_sum_range]
  simp_rw [div_pow, ← sum_div]
  push_cast
  ring

lemma b_eq_integer : b = (energyBZ:ℝ)/((weightDen:ℝ)^2*256) := by
  unfold b wRight energyBZ weightNormN
  rw [sumN_eq_sum_range]
  simp_rw [div_pow, ← sum_div]
  push_cast
  norm_num [weightDen]
  ring

lemma cover_block_0 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*0+i.val) := by
  decide +kernel

lemma cover_block_1 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*1+i.val) := by
  decide +kernel

lemma cover_block_2 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*2+i.val) := by
  decide +kernel

lemma cover_block_3 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*3+i.val) := by
  decide +kernel

lemma cover_block_4 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*4+i.val) := by
  decide +kernel

lemma cover_block_5 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*5+i.val) := by
  decide +kernel

lemma cover_block_6 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*6+i.val) := by
  decide +kernel

lemma cover_block_7 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*7+i.val) := by
  decide +kernel

lemma cover_block_8 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*8+i.val) := by
  decide +kernel

lemma cover_block_9 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*9+i.val) := by
  decide +kernel

lemma cover_block_10 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*10+i.val) := by
  decide +kernel

lemma cover_block_11 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*11+i.val) := by
  decide +kernel

lemma cover_block_12 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*12+i.val) := by
  decide +kernel

lemma cover_block_13 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*13+i.val) := by
  decide +kernel

lemma cover_block_14 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*14+i.val) := by
  decide +kernel

lemma cover_block_15 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*15+i.val) := by
  decide +kernel

lemma cover_block_16 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*16+i.val) := by
  decide +kernel

lemma cover_block_17 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*17+i.val) := by
  decide +kernel

lemma cover_block_18 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*18+i.val) := by
  decide +kernel

lemma cover_block_19 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*19+i.val) := by
  decide +kernel

lemma cover_block_20 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*20+i.val) := by
  decide +kernel

lemma cover_block_21 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*21+i.val) := by
  decide +kernel

lemma cover_block_22 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*22+i.val) := by
  decide +kernel

lemma cover_block_23 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*23+i.val) := by
  decide +kernel

lemma cover_block_24 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*24+i.val) := by
  decide +kernel

lemma cover_block_25 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*25+i.val) := by
  decide +kernel

lemma cover_block_26 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*26+i.val) := by
  decide +kernel

lemma cover_block_27 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*27+i.val) := by
  decide +kernel

lemma cover_block_28 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*28+i.val) := by
  decide +kernel

lemma cover_block_29 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*29+i.val) := by
  decide +kernel

lemma cover_block_30 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*30+i.val) := by
  decide +kernel

lemma cover_block_31 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*31+i.val) := by
  decide +kernel

lemma cover_block_32 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*32+i.val) := by
  decide +kernel

lemma cover_block_33 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*33+i.val) := by
  decide +kernel

lemma cover_block_34 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*34+i.val) := by
  decide +kernel

lemma cover_block_35 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*35+i.val) := by
  decide +kernel

lemma cover_block_36 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*36+i.val) := by
  decide +kernel

lemma cover_block_37 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*37+i.val) := by
  decide +kernel

lemma cover_block_38 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*38+i.val) := by
  decide +kernel

lemma cover_block_39 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*39+i.val) := by
  decide +kernel

lemma cover_block_40 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*40+i.val) := by
  decide +kernel

lemma cover_block_41 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*41+i.val) := by
  decide +kernel

lemma cover_block_42 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*42+i.val) := by
  decide +kernel

lemma cover_block_43 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*43+i.val) := by
  decide +kernel

lemma cover_block_44 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*44+i.val) := by
  decide +kernel

lemma cover_block_45 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*45+i.val) := by
  decide +kernel

lemma cover_block_46 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*46+i.val) := by
  decide +kernel

lemma cover_block_47 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*47+i.val) := by
  decide +kernel

lemma cover_block_48 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*48+i.val) := by
  decide +kernel

lemma cover_block_49 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*49+i.val) := by
  decide +kernel

lemma cover_block_50 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*50+i.val) := by
  decide +kernel

lemma cover_block_51 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*51+i.val) := by
  decide +kernel

lemma cover_block_52 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*52+i.val) := by
  decide +kernel

lemma cover_block_53 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*53+i.val) := by
  decide +kernel

lemma cover_block_54 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*54+i.val) := by
  decide +kernel

lemma cover_block_55 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*55+i.val) := by
  decide +kernel

lemma cover_block_56 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*56+i.val) := by
  decide +kernel

lemma cover_block_57 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*57+i.val) := by
  decide +kernel

lemma cover_block_58 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*58+i.val) := by
  decide +kernel

lemma cover_block_59 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*59+i.val) := by
  decide +kernel

lemma cover_block_60 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*60+i.val) := by
  decide +kernel

lemma cover_block_61 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*61+i.val) := by
  decide +kernel

lemma cover_block_62 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*62+i.val) := by
  decide +kernel

lemma cover_block_63 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*63+i.val) := by
  decide +kernel

lemma cover_block_64 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*64+i.val) := by
  decide +kernel

lemma cover_block_65 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*65+i.val) := by
  decide +kernel

lemma cover_block_66 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*66+i.val) := by
  decide +kernel

lemma cover_block_67 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*67+i.val) := by
  decide +kernel

lemma cover_block_68 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*68+i.val) := by
  decide +kernel

lemma cover_block_69 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*69+i.val) := by
  decide +kernel

lemma cover_block_70 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*70+i.val) := by
  decide +kernel

lemma cover_block_71 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*71+i.val) := by
  decide +kernel

lemma cover_block_72 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*72+i.val) := by
  decide +kernel

lemma cover_block_73 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*73+i.val) := by
  decide +kernel

lemma cover_block_74 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*74+i.val) := by
  decide +kernel

lemma cover_block_75 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*75+i.val) := by
  decide +kernel

lemma cover_block_76 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*76+i.val) := by
  decide +kernel

lemma cover_block_77 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*77+i.val) := by
  decide +kernel

lemma cover_block_78 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*78+i.val) := by
  decide +kernel

lemma cover_block_79 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*79+i.val) := by
  decide +kernel

lemma cover_block_80 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*80+i.val) := by
  decide +kernel

lemma cover_block_81 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*81+i.val) := by
  decide +kernel

lemma cover_block_82 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*82+i.val) := by
  decide +kernel

lemma cover_block_83 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*83+i.val) := by
  decide +kernel

lemma cover_block_84 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*84+i.val) := by
  decide +kernel

lemma cover_block_85 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*85+i.val) := by
  decide +kernel

lemma cover_block_86 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*86+i.val) := by
  decide +kernel

lemma cover_block_87 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*87+i.val) := by
  decide +kernel

lemma cover_block_88 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*88+i.val) := by
  decide +kernel

lemma cover_block_89 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*89+i.val) := by
  decide +kernel

lemma cover_block_90 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*90+i.val) := by
  decide +kernel

lemma cover_block_91 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*91+i.val) := by
  decide +kernel

lemma cover_block_92 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*92+i.val) := by
  decide +kernel

lemma cover_block_93 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*93+i.val) := by
  decide +kernel

lemma cover_block_94 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*94+i.val) := by
  decide +kernel

lemma cover_block_95 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*95+i.val) := by
  decide +kernel

lemma cover_block_96 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*96+i.val) := by
  decide +kernel

lemma cover_block_97 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*97+i.val) := by
  decide +kernel

lemma cover_block_98 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*98+i.val) := by
  decide +kernel

lemma cover_block_99 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*99+i.val) := by
  decide +kernel

lemma cover_block_100 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*100+i.val) := by
  decide +kernel

lemma cover_block_101 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*101+i.val) := by
  decide +kernel

lemma cover_block_102 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*102+i.val) := by
  decide +kernel

lemma cover_block_103 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*103+i.val) := by
  decide +kernel

lemma cover_block_104 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*104+i.val) := by
  decide +kernel

lemma cover_block_105 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*105+i.val) := by
  decide +kernel

lemma cover_block_106 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*106+i.val) := by
  decide +kernel

lemma cover_block_107 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*107+i.val) := by
  decide +kernel

lemma cover_block_108 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*108+i.val) := by
  decide +kernel

lemma cover_block_109 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*109+i.val) := by
  decide +kernel

lemma cover_block_110 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*110+i.val) := by
  decide +kernel

lemma cover_block_111 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*111+i.val) := by
  decide +kernel

lemma cover_block_112 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*112+i.val) := by
  decide +kernel

lemma cover_block_113 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*113+i.val) := by
  decide +kernel

lemma cover_block_114 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*114+i.val) := by
  decide +kernel

lemma cover_block_115 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*115+i.val) := by
  decide +kernel

lemma cover_block_116 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*116+i.val) := by
  decide +kernel

lemma cover_block_117 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*117+i.val) := by
  decide +kernel

lemma cover_block_118 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*118+i.val) := by
  decide +kernel

lemma cover_block_119 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*119+i.val) := by
  decide +kernel

lemma cover_block_120 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*120+i.val) := by
  decide +kernel

lemma cover_block_121 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*121+i.val) := by
  decide +kernel

lemma cover_block_122 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*122+i.val) := by
  decide +kernel

lemma cover_block_123 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*123+i.val) := by
  decide +kernel

lemma cover_block_124 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*124+i.val) := by
  decide +kernel

lemma cover_block_125 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*125+i.val) := by
  decide +kernel

lemma cover_block_126 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*126+i.val) := by
  decide +kernel

lemma cover_block_127 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*127+i.val) := by
  decide +kernel

lemma cover_block_128 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*128+i.val) := by
  decide +kernel

lemma cover_block_129 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*129+i.val) := by
  decide +kernel

lemma cover_block_130 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*130+i.val) := by
  decide +kernel

lemma cover_block_131 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*131+i.val) := by
  decide +kernel

lemma cover_block_132 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*132+i.val) := by
  decide +kernel

lemma cover_block_133 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*133+i.val) := by
  decide +kernel

lemma cover_block_134 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*134+i.val) := by
  decide +kernel

lemma cover_block_135 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*135+i.val) := by
  decide +kernel

lemma cover_block_136 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*136+i.val) := by
  decide +kernel

lemma cover_block_137 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*137+i.val) := by
  decide +kernel

lemma cover_block_138 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*138+i.val) := by
  decide +kernel

lemma cover_block_139 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*139+i.val) := by
  decide +kernel

lemma cover_block_140 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*140+i.val) := by
  decide +kernel

lemma cover_block_141 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*141+i.val) := by
  decide +kernel

lemma cover_block_142 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*142+i.val) := by
  decide +kernel

lemma cover_block_143 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*143+i.val) := by
  decide +kernel

lemma cover_block_144 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*144+i.val) := by
  decide +kernel

lemma cover_block_145 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*145+i.val) := by
  decide +kernel

lemma cover_block_146 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*146+i.val) := by
  decide +kernel

lemma cover_block_147 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*147+i.val) := by
  decide +kernel

lemma cover_block_148 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*148+i.val) := by
  decide +kernel

lemma cover_block_149 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*149+i.val) := by
  decide +kernel

lemma cover_block_150 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*150+i.val) := by
  decide +kernel

lemma cover_block_151 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*151+i.val) := by
  decide +kernel

lemma cover_block_152 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*152+i.val) := by
  decide +kernel

lemma cover_block_153 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*153+i.val) := by
  decide +kernel

lemma cover_block_154 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*154+i.val) := by
  decide +kernel

lemma cover_block_155 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*155+i.val) := by
  decide +kernel

lemma cover_block_156 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*156+i.val) := by
  decide +kernel

lemma cover_block_157 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*157+i.val) := by
  decide +kernel

lemma cover_block_158 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*158+i.val) := by
  decide +kernel

lemma cover_block_159 : ∀ i : Fin 16,
    kernelDen*weightDen ≤ coverRec (16*159+i.val) := by
  decide +kernel

lemma cover_last : kernelDen*weightDen ≤ coverRec 2560 := by
  decide +kernel

lemma covers_integer (q : ℕ) (hq : q ≤ 2560) :
    kernelDen*weightDen ≤ coverRec q := by
  have blocks : ∀ b : Fin 160, ∀ i : Fin 16,
      kernelDen*weightDen ≤ coverRec (16*b.val+i.val) := by
    intro b
    fin_cases b
    · exact cover_block_0
    · exact cover_block_1
    · exact cover_block_2
    · exact cover_block_3
    · exact cover_block_4
    · exact cover_block_5
    · exact cover_block_6
    · exact cover_block_7
    · exact cover_block_8
    · exact cover_block_9
    · exact cover_block_10
    · exact cover_block_11
    · exact cover_block_12
    · exact cover_block_13
    · exact cover_block_14
    · exact cover_block_15
    · exact cover_block_16
    · exact cover_block_17
    · exact cover_block_18
    · exact cover_block_19
    · exact cover_block_20
    · exact cover_block_21
    · exact cover_block_22
    · exact cover_block_23
    · exact cover_block_24
    · exact cover_block_25
    · exact cover_block_26
    · exact cover_block_27
    · exact cover_block_28
    · exact cover_block_29
    · exact cover_block_30
    · exact cover_block_31
    · exact cover_block_32
    · exact cover_block_33
    · exact cover_block_34
    · exact cover_block_35
    · exact cover_block_36
    · exact cover_block_37
    · exact cover_block_38
    · exact cover_block_39
    · exact cover_block_40
    · exact cover_block_41
    · exact cover_block_42
    · exact cover_block_43
    · exact cover_block_44
    · exact cover_block_45
    · exact cover_block_46
    · exact cover_block_47
    · exact cover_block_48
    · exact cover_block_49
    · exact cover_block_50
    · exact cover_block_51
    · exact cover_block_52
    · exact cover_block_53
    · exact cover_block_54
    · exact cover_block_55
    · exact cover_block_56
    · exact cover_block_57
    · exact cover_block_58
    · exact cover_block_59
    · exact cover_block_60
    · exact cover_block_61
    · exact cover_block_62
    · exact cover_block_63
    · exact cover_block_64
    · exact cover_block_65
    · exact cover_block_66
    · exact cover_block_67
    · exact cover_block_68
    · exact cover_block_69
    · exact cover_block_70
    · exact cover_block_71
    · exact cover_block_72
    · exact cover_block_73
    · exact cover_block_74
    · exact cover_block_75
    · exact cover_block_76
    · exact cover_block_77
    · exact cover_block_78
    · exact cover_block_79
    · exact cover_block_80
    · exact cover_block_81
    · exact cover_block_82
    · exact cover_block_83
    · exact cover_block_84
    · exact cover_block_85
    · exact cover_block_86
    · exact cover_block_87
    · exact cover_block_88
    · exact cover_block_89
    · exact cover_block_90
    · exact cover_block_91
    · exact cover_block_92
    · exact cover_block_93
    · exact cover_block_94
    · exact cover_block_95
    · exact cover_block_96
    · exact cover_block_97
    · exact cover_block_98
    · exact cover_block_99
    · exact cover_block_100
    · exact cover_block_101
    · exact cover_block_102
    · exact cover_block_103
    · exact cover_block_104
    · exact cover_block_105
    · exact cover_block_106
    · exact cover_block_107
    · exact cover_block_108
    · exact cover_block_109
    · exact cover_block_110
    · exact cover_block_111
    · exact cover_block_112
    · exact cover_block_113
    · exact cover_block_114
    · exact cover_block_115
    · exact cover_block_116
    · exact cover_block_117
    · exact cover_block_118
    · exact cover_block_119
    · exact cover_block_120
    · exact cover_block_121
    · exact cover_block_122
    · exact cover_block_123
    · exact cover_block_124
    · exact cover_block_125
    · exact cover_block_126
    · exact cover_block_127
    · exact cover_block_128
    · exact cover_block_129
    · exact cover_block_130
    · exact cover_block_131
    · exact cover_block_132
    · exact cover_block_133
    · exact cover_block_134
    · exact cover_block_135
    · exact cover_block_136
    · exact cover_block_137
    · exact cover_block_138
    · exact cover_block_139
    · exact cover_block_140
    · exact cover_block_141
    · exact cover_block_142
    · exact cover_block_143
    · exact cover_block_144
    · exact cover_block_145
    · exact cover_block_146
    · exact cover_block_147
    · exact cover_block_148
    · exact cover_block_149
    · exact cover_block_150
    · exact cover_block_151
    · exact cover_block_152
    · exact cover_block_153
    · exact cover_block_154
    · exact cover_block_155
    · exact cover_block_156
    · exact cover_block_157
    · exact cover_block_158
    · exact cover_block_159
  by_cases hq' : q < 2560
  · have hb : q/16 < 160 := by omega
    have hi : q%16 < 16 := Nat.mod_lt _ (by decide)
    have h := blocks ⟨q/16,hb⟩ ⟨q%16,hi⟩
    have he : 16*(q/16)+q%16=q := by omega
    simpa only [he] using h
  · have he : q=2560 := by omega
    simpa only [he] using cover_last

lemma energyA_integer_positive : 0 < energyAN := by decide +kernel
lemma energyB_integer_positive : 0 < energyBZ := by decide +kernel
lemma coefficient_integer :
    (energyAN:ℤ)*energyBZ*(1000000:ℤ)^2 <
      (942811:ℤ)^2*kernelDen^2*weightDen^2 := by
  decide +kernel


lemma right_cover (q : ℕ) (hq : q ≤ 2560) :
    1 ≤ ∑ i ∈ range 256, p (255-i)*wRight (q+i) := by
  rw [right_cover_eq]
  apply (le_div_iff₀ (by norm_num [kernelDen,weightDen])).mpr
  simp only [one_mul]
  exact_mod_cast covers_integer q hq

lemma a_positive : 0 < a := by
  rw [a_eq_integer]
  have ha : 0 < (energyAN:ℝ) := by exact_mod_cast energyA_integer_positive
  exact div_pos (mul_pos (by norm_num) ha) (by norm_num [kernelDen])

lemma b_positive : 0 < b := by
  rw [b_eq_integer]
  have hb : 0 < (energyBZ:ℝ) := by exact_mod_cast energyB_integer_positive
  exact div_pos hb (by norm_num [weightDen])

lemma coefficient_improved : a*b < (942811/1000000:ℝ)^2 := by
  rw [a_eq_integer,b_eq_integer]
  have hab : (energyAN:ℝ)*(energyBZ:ℝ)*(1000000:ℝ)^2 <
      (942811:ℝ)^2*(kernelDen:ℝ)^2*(weightDen:ℝ)^2 := by
    exact_mod_cast coefficient_integer
  generalize hA : (energyAN:ℝ) = A at hab ⊢
  generalize hB : (energyBZ:ℝ) = B at hab ⊢
  norm_num [kernelDen,weightDen] at hab ⊢
  nlinarith only [hab]

lemma b_general :
    1+((∑ j ∈ range 2560, wLeft j^2)+(∑ j ∈ range 2560, wRight j^2))/256-2*10=b := by
  unfold wLeft b
  simp
  ring

/-- Complete finite asymmetric certificate; no analytic premises. -/
theorem certificate :
    (∀ i < 256, 0 ≤ p i) ∧
    (∑ i ∈ range 256, p i)=1 ∧
    (∀ j, 2560 ≤ j → wLeft j=1) ∧
    (∀ j, 2560 ≤ j → wRight j=1) ∧
    (∀ q ≤ 2560, 1 ≤ ∑ i ∈ range 256, p i*wLeft (q+i)) ∧
    (∀ q ≤ 2560, 1 ≤ ∑ i ∈ range 256, p (255-i)*wRight (q+i)) ∧
    0<a ∧ 0<b ∧ a*b<(942811/1000000:ℝ)^2 := by
  exact ⟨fun i _ => kernel_nonnegative i, kernel_mass,
    fun j _ => left_tail j, right_tail, fun q _ => left_cover q,
    right_cover, a_positive, b_positive, coefficient_improved⟩

#print axioms certificate
end SidonAsymmetricData

namespace Submissions.Erdos30SidonUpperBound942811.Declan

/-- Standard unordered-sum uniqueness, including repeated summands. -/
def IsSidon (A : Finset ℤ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- A one-sided eventual bound for every finite interval Sidon set. -/
abbrev statement : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ A : Finset ℤ, A ⊆ Finset.Ico 0 (N : ℤ) → IsSidon A →
      (A.card : ℝ) ≤ Real.sqrt N +
        (942811 / 1000000 : ℝ) * Real.sqrt (Real.sqrt N) + C

theorem proof : statement := by
  have ha : 0 < SidonAsymmetric.aValue 256 SidonAsymmetricData.p := by
    simpa [SidonAsymmetric.aValue, SidonAsymmetricData.a] using SidonAsymmetricData.a_positive
  have hb : 0 < SidonAsymmetric.rightBValue 256 10 SidonAsymmetricData.wRight := by
    simpa [SidonAsymmetric.rightBValue, SidonAsymmetricData.b] using SidonAsymmetricData.b_positive
  have hab : SidonAsymmetric.aValue 256 SidonAsymmetricData.p *
      SidonAsymmetric.rightBValue 256 10 SidonAsymmetricData.wRight <
      (942811 / 1000000 : ℝ)^2 := by
    simpa [SidonAsymmetric.aValue, SidonAsymmetric.rightBValue,
      SidonAsymmetricData.a, SidonAsymmetricData.b] using SidonAsymmetricData.coefficient_improved
  exact SidonAsymmetric.eventual_bound_left_one 256 10 (by decide)
    SidonAsymmetricData.p SidonAsymmetricData.wRight (942811 / 1000000)
    (fun i _ => SidonAsymmetricData.kernel_nonnegative i)
    SidonAsymmetricData.kernel_mass SidonAsymmetricData.right_tail
    SidonAsymmetricData.right_cover ha hb (by norm_num) hab

#print axioms proof

end Submissions.Erdos30SidonUpperBound942811.Declan
