import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

open scoped BigOperators
open Filter

/-
Density bound 3/4 for the distinct-factor form of Erdős 786(i), sharpening the
7/8 bound of the refutation artifact on this problem (whose good/bad-prime
machinery is reused verbatim). The only new ingredient is the Bonferroni
inequality 2·Σ|F_p| ≤ 2·|∪F_p| + Σ_{p≠q}|F_p ∩ F_q| in place of the weaker
three-term inequality used there, which improves the final polynomial to
(λ - 1/2)(1 - λ) ≥ 0 on the selected mass window λ ∈ [1/2, 1].
-/

namespace Submissions.Erdos786DistinctDensityLe34.Bonferroni

def IsMulCardSet (A : Set ℕ) : Prop :=
  ∀ U V : Finset ℕ, (U : Set ℕ) ⊆ A → (V : Set ℕ) ⊆ A →
    U.prod id = V.prod id → U.card = V.card

def Good (A : Set ℕ) (p : ℕ) : Prop :=
  {x : ℕ | x ∈ A ∧ p * x ∈ A}.Infinite

def Bad (A : Set ℕ) (p : ℕ) : Prop := p.Prime ∧ ¬ Good A p

lemma realize_list (A : Set ℕ) (L : List ℕ)
    (hL : ∀ p ∈ L, p.Prime ∧ Good A p) (T : ℕ) :
    ∃ U V : Finset ℕ,
      (∀ u ∈ U, u ∈ A ∧ T < u) ∧
      (∀ v ∈ V, v ∈ A ∧ T < v) ∧
      U.card = V.card ∧ V.prod id = L.prod * U.prod id := by
  classical
  induction L with
  | nil => exact ⟨∅, ∅, by simp, by simp, by simp, by simp⟩
  | cons p L ih =>
    obtain ⟨U, V, hU, hV, hcard, hprod⟩ := ih (fun q hq => hL q (by simp [hq]))
    have hp := (hL p (by simp)).1
    obtain ⟨x, hxA, hx⟩ := (hL p (by simp)).2.exists_gt (T + U.sup id + V.sup id)
    have hxU : x ∉ U := by
      intro h
      have : x ≤ U.sup id := Finset.le_sup (f := id) h
      omega
    have hpxV : p * x ∉ V := by
      intro h
      have hv : p*x ≤ V.sup id := Finset.le_sup (f := id) h
      have : x ≤ p * x := Nat.le_mul_of_pos_left x hp.pos
      omega
    refine ⟨insert x U, insert (p*x) V, ?_, ?_, ?_, ?_⟩
    · intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact ⟨hxA.1, by omega⟩
      · exact hU u hu
    · intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact ⟨hxA.2, lt_of_lt_of_le (by omega) (Nat.le_mul_of_pos_left x hp.pos)⟩
      · exact hV v hv
    · simp [Finset.card_insert_of_notMem hxU, Finset.card_insert_of_notMem hpxV, hcard]
    · rw [Finset.prod_insert hpxV, Finset.prod_insert hxU, List.prod_cons, hprod]
      simp only [id_eq]
      ring

lemma bad_divisor (A : Set ℕ) (h0 : 0 ∉ A) (hA : IsMulCardSet A)
    {a : ℕ} (ha : a ∈ A) : ∃ p, Bad A p ∧ p ∣ a := by
  classical
  by_contra h
  push Not at h
  have ha0 : a ≠ 0 := by aesop
  have hg : ∀ p ∈ a.primeFactorsList, p.Prime ∧ Good A p := by
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactorsList hp
    have hdvd := Nat.dvd_of_mem_primeFactorsList hp
    refine ⟨hprime, ?_⟩
    by_contra hb
    exact h p ⟨hprime, hb⟩ hdvd
  obtain ⟨U, V, hU, hV, hcard, hprod⟩ := realize_list A a.primeFactorsList hg a
  have haU : a ∉ U := by
    intro hm
    exact (lt_irrefl a) (hU a hm).2
  have hc := hA (insert a U) V (by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ha
      · exact (hU x hx).1) (by
      intro x hx
      exact (hV x hx).1) (by
      rw [Finset.prod_insert haU, hprod, Nat.prod_primeFactorsList ha0]
      rfl)
  rw [Finset.card_insert_of_notMem haU, hcard] at hc
  omega

lemma bonferroni_card (S : Finset ℕ) (F : ℕ → Finset ℕ) :
    2 * (∑ p ∈ S, (F p).card) ≤
      2 * (S.biUnion F).card +
        ∑ p ∈ S, ∑ q ∈ S, (if p = q then 0 else (F p ∩ F q).card) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have hI : (F a ∩ S.biUnion F).card ≤ ∑ p ∈ S, (F a ∩ F p).card := by
      rw [Finset.inter_biUnion]
      exact Finset.card_biUnion_le
    have hU := Finset.card_union_add_card_inter (F a) (S.biUnion F)
    have hsym : ∀ p ∈ S, (if p = a then 0 else (F p ∩ F a).card) = (F a ∩ F p).card := by
      intro p hp
      have : p ≠ a := fun h => ha (h ▸ hp)
      rw [if_neg this, Finset.inter_comm]
    have hrow : ∀ q ∈ S, (if a = q then 0 else (F a ∩ F q).card) = (F a ∩ F q).card := by
      intro q hq
      have : a ≠ q := fun h => ha (h ▸ hq)
      rw [if_neg this]
    rw [Finset.sum_insert ha, Finset.biUnion_insert, Finset.sum_insert ha, Finset.sum_insert ha,
      if_pos rfl, Finset.sum_congr rfl hrow]
    have hinner : ∀ p ∈ S, (∑ q ∈ insert a S, (if p = q then 0 else (F p ∩ F q).card))
        = (F a ∩ F p).card + ∑ q ∈ S, (if p = q then 0 else (F p ∩ F q).card) := by
      intro p hp
      rw [Finset.sum_insert ha, hsym p hp]
    rw [Finset.sum_congr rfl hinner, Finset.sum_add_distrib]
    omega

noncomputable def elems (A : Set ℕ) (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 N).filter (fun a => a ∈ A)

noncomputable def badPrimes (A : Set ℕ) (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (N+1)).filter (Bad A)

noncomputable def count (A : Set ℕ) (N : ℕ) : ℕ := (elems A N).card

lemma mem_elems {A : Set ℕ} {N a : ℕ} : a ∈ elems A N ↔ 1 ≤ a ∧ a ≤ N ∧ a ∈ A := by
  classical
  simp only [elems, Finset.mem_filter, Finset.mem_Icc]
  tauto

lemma card_multiples_Icc (N p : ℕ) :
    ((Finset.Icc 1 N).filter fun a => p ∣ a).card = N / p := by
  classical
  rw [← Nat.card_multiples' N p]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
  omega

lemma finite_bad_support_bound (A : Set ℕ) (h0 : 0 ∉ A) (hA : IsMulCardSet A) (N : ℕ) :
    (count A N : ℝ) ≤ N * ∑ p ∈ badPrimes A N, (1 / (p : ℝ)) := by
  classical
  let S := badPrimes A N
  let F := fun p => (Finset.Icc 1 N).filter fun a => p ∣ a
  have hsub : elems A N ⊆ S.biUnion F := by
    intro a ha
    obtain ⟨ha1, haN, haA⟩ := mem_elems.mp ha
    obtain ⟨p, hp, hd⟩ := bad_divisor A h0 hA haA
    apply Finset.mem_biUnion.mpr
    refine ⟨p, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
        have := Nat.le_of_dvd ha1 hd
        omega), hp⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨ha1,haN⟩,hd⟩
  have hb : count A N ≤ ∑ p ∈ S, N / p := by
    calc
      count A N ≤ (S.biUnion F).card := Finset.card_le_card hsub
      _ ≤ ∑ p ∈ S, (F p).card := Finset.card_biUnion_le
      _ = _ := by simp [F, card_multiples_Icc]
  calc
    (count A N : ℝ) ≤ ∑ p ∈ S, ((N / p : ℕ) : ℝ) := by exact_mod_cast hb
    _ ≤ ∑ p ∈ S, (N : ℝ) / p := Finset.sum_le_sum (fun _ _ => Nat.cast_div_le)
    _ = _ := by simp [S, Finset.mul_sum, div_eq_mul_inv]

lemma select_mass (S : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ p ∈ S, 0 ≤ w p ∧ w p ≤ 1/2)
    (hS : 1/2 ≤ ∑ p ∈ S, w p) :
    ∃ T ⊆ S, 1/2 ≤ ∑ p ∈ T, w p ∧ (∑ p ∈ T, w p) ≤ 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp at hS; linarith
  | @insert p S hp ih =>
    by_cases hs : 1/2 ≤ ∑ q ∈ S, w q
    · obtain ⟨T, hT, hTl, hTu⟩ := ih (fun q hq => hw q (Finset.mem_insert_of_mem hq)) hs
      exact ⟨T, hT.trans (Finset.subset_insert ..), hTl, hTu⟩
    · refine ⟨insert p S, Finset.Subset.refl _, hS, ?_⟩
      rw [Finset.sum_insert hp]
      have := (hw p (Finset.mem_insert_self p S)).2
      linarith

noncomputable def dilated (A : Set ℕ) (N p : ℕ) : Finset ℕ :=
  (elems A (N/p)).image (fun a => p*a)

lemma card_dilated (A : Set ℕ) (N p : ℕ) (hp : 0 < p) :
    (dilated A N p).card = count A (N/p) := by
  classical
  apply Finset.card_image_of_injective
  intro a b hab
  exact Nat.eq_of_mul_eq_mul_left hp hab

lemma dilated_subset {A : Set ℕ} {N p : ℕ} (hp : 0 < p) :
    dilated A N p ⊆ (Finset.Icc 1 N).filter (fun x => p ∣ x) := by
  classical
  intro x hx
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨ha1, haN, _⟩ := mem_elems.mp ha
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨by nlinarith, ?_⟩, dvd_mul_right p a⟩
  exact (Nat.mul_le_mul_left p haN).trans (Nat.mul_div_le N p)

lemma card_dilated_inter_le {A : Set ℕ} {N p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    (dilated A N p ∩ dilated A N q).card ≤ N/(p*q) := by
  classical
  rw [← card_multiples_Icc N (p*q)]
  apply Finset.card_le_card
  intro x hx
  have hpx := Finset.mem_filter.mp (dilated_subset hp.pos (Finset.mem_inter.mp hx).1)
  have hqx := Finset.mem_filter.mp (dilated_subset hq.pos (Finset.mem_inter.mp hx).2)
  exact Finset.mem_filter.mpr ⟨hpx.1,
    Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.coprime_primes hp hq).mpr hpq) hpx.2 hqx.2⟩

lemma bad_overlap_bound (A : Set ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, Bad A p) :
    ∃ K : ℕ, ∀ p ∈ S, ∀ a ∈ A, p*a ∈ A → p*a ≤ K := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert p S hp ih =>
    obtain ⟨K, hK⟩ := ih (fun q hq => hS q (Finset.mem_insert_of_mem hq))
    have hf : {x : ℕ | x ∈ A ∧ p*x ∈ A}.Finite :=
      Set.not_infinite.mp (hS p (Finset.mem_insert_self p S)).2
    obtain ⟨M, hM⟩ := hf.bddAbove
    refine ⟨max K (p*M), ?_⟩
    intro q hq a ha hqa
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact (Nat.mul_le_mul_left q (hM ⟨ha,hqa⟩)).trans (le_max_right ..)
    · exact (hK q hq a ha hqa).trans (le_max_left ..)

lemma count_union_bound (A : Set ℕ) (N K : ℕ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, 0 < p)
    (hK : ∀ p ∈ S, ∀ a ∈ A, p*a ∈ A → p*a ≤ K) :
    count A N + (S.biUnion (dilated A N)).card ≤ N + K := by
  classical
  have hu : elems A N ∪ S.biUnion (dilated A N) ⊆ Finset.Icc 1 N := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Finset.mem_Icc.mpr ⟨(mem_elems.mp hx).1,(mem_elems.mp hx).2.1⟩
    · obtain ⟨p,hp,hx⟩ := Finset.mem_biUnion.mp hx
      exact (Finset.mem_filter.mp (dilated_subset (hS p hp) hx)).1
  have hi : elems A N ∩ S.biUnion (dilated A N) ⊆ Finset.Icc 1 K := by
    intro x hx
    obtain ⟨hxA, hxU⟩ := Finset.mem_inter.mp hx
    obtain ⟨p,hp,hx⟩ := Finset.mem_biUnion.mp hxU
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_Icc.mpr ⟨(mem_elems.mp hxA).1,
      hK p hp a (mem_elems.mp ha).2.2 (mem_elems.mp hxA).2.2⟩
  have hu' : (elems A N ∪ S.biUnion (dilated A N)).card ≤ N := by
    simpa using Finset.card_le_card hu
  have hi' : (elems A N ∩ S.biUnion (dilated A N)).card ≤ K := by
    simpa using Finset.card_le_card hi
  have he := Finset.card_union_add_card_inter (elems A N) (S.biUnion (dilated A N))
  unfold count
  omega

lemma double_inter_bound (A : Set ℕ) (N : ℕ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) :
    (∑ p ∈ S, ∑ q ∈ S, ((if p = q then 0 else (dilated A N p ∩ dilated A N q).card : ℕ) : ℝ)) ≤
      N * (∑ p ∈ S, 1/(p:ℝ))^2 := by
  classical
  have hb : ∀ p ∈ S, ∀ q ∈ S,
      ((if p = q then 0 else (dilated A N p ∩ dilated A N q).card : ℕ) : ℝ) ≤ (N:ℝ)/(p*q) := by
    intro p hp q hq
    by_cases he : p=q
    · rw [if_pos he]
      simp only [Nat.cast_zero]
      positivity
    · rw [if_neg he]
      have hc := card_dilated_inter_le (A:=A) (N:=N) (hS p hp) (hS q hq) he
      calc
        ((dilated A N p ∩ dilated A N q).card : ℝ) ≤ ((N/(p*q):ℕ):ℝ) := by exact_mod_cast hc
        _ ≤ (N:ℝ)/(p*q) := by simpa using (Nat.cast_div_le (m:=N) (n:=p*q) (α:=ℝ))
  calc
    _ ≤ ∑ p ∈ S, ∑ q ∈ S, (N:ℝ)/(p*q) :=
      Finset.sum_le_sum (fun p hp => Finset.sum_le_sum (hb p hp))
    _ = _ := by
      simp [Finset.mul_sum, pow_two, div_eq_mul_inv, mul_comm]

lemma not_eventually_dense (A : Set ℕ) (h0 : 0 ∉ A) (hA : IsMulCardSet A)
    (c : ℝ) (hc : 3/4 < c)
    (N0 : ℕ) (hden : ∀ N ≥ N0, c*N ≤ count A N) : False := by
  classical
  let M := N0+1
  have hMpos : (0:ℝ) < M := by dsimp [M]; positivity
  have hm := hden M (by dsimp [M]; omega)
  have hs := finite_bad_support_bound A h0 hA M
  have hmass : (1/2:ℝ) ≤ ∑ p ∈ badPrimes A M, 1/(p:ℝ) := by
    by_contra hlt
    push Not at hlt
    have : (count A M : ℝ) < M * (1/2) := lt_of_le_of_lt hs (by nlinarith)
    nlinarith
  have hbad : ∀ p ∈ badPrimes A M, Bad A p := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  obtain ⟨S, hsub, hSl, hSu⟩ := select_mass (badPrimes A M) (fun p => 1/(p:ℝ))
    (by
      intro p hp
      have hp2 : (2:ℝ) ≤ p := by exact_mod_cast (hbad p hp).1.two_le
      exact ⟨by positivity, (div_le_iff₀ (by linarith : (0:ℝ)<p)).mpr (by linarith)⟩)
    hmass
  have hS : ∀ p ∈ S, Bad A p := fun p hp => hbad p (hsub hp)
  obtain ⟨K,hK⟩ := bad_overlap_bound A S hS
  let L : ℕ := ∏ p ∈ S, p
  have hL : 0 < L := Finset.prod_pos (fun p hp => (hS p hp).1.pos)
  -- choose N so large that the slack 2*(c-3/4)*(1+λ)*N beats 2K
  obtain ⟨T0, hT0⟩ : ∃ T0 : ℕ, (2*K:ℝ) < (c - 3/4) * T0 := by
    obtain ⟨T0, hT0⟩ := exists_nat_gt ((2*K:ℝ) / (c - 3/4))
    refine ⟨T0, ?_⟩
    have hpos : (0:ℝ) < c - 3/4 := by linarith
    rw [div_lt_iff₀ hpos] at hT0
    linarith
  let T := N0+T0+1
  let N := L*T
  have hT : T ≤ N := Nat.le_mul_of_pos_left T hL
  have hN : N0 ≤ N := by dsimp [T] at hT; omega
  have hNK : (2*K:ℝ) < (c - 3/4) * N := by
    have hTN : (T0:ℝ) ≤ N := by
      have : T0 ≤ N := by dsimp [T] at hT; omega
      exact_mod_cast this
    have hpos : (0:ℝ) < c - 3/4 := by linarith
    nlinarith
  have hdiv : ∀ p ∈ S, p ∣ N ∧ N0 ≤ N/p := by
    intro p hp
    have hpL : p ∣ L := Finset.dvd_prod_of_mem id hp
    have hpl : p ≤ L := Nat.le_of_dvd hL hpL
    refine ⟨dvd_mul_of_dvd_left hpL T, ?_⟩
    have htdiv : T ≤ N/p := (Nat.le_div_iff_mul_le (hS p hp).1.pos).mpr (by
      dsimp [N]
      nlinarith)
    dsimp [T] at htdiv
    omega
  let lam : ℝ := ∑ p ∈ S, 1/(p:ℝ)
  have hsum : c*N*lam ≤ ∑ p ∈ S, (count A (N/p):ℝ) := by
    calc
      _ = ∑ p ∈ S, c*N/p := by
        dsimp [lam]
        simp [Finset.mul_sum, div_eq_mul_inv]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro p hp
        have hc := hden (N/p) (hdiv p hp).2
        rw [Nat.cast_div (hdiv p hp).1 (by exact_mod_cast (hS p hp).1.ne_zero)] at hc
        simpa only [mul_div_assoc] using hc
  have hbonf := bonferroni_card S (dilated A N)
  have hunion := count_union_bound A N K S (fun p hp => (hS p hp).1.pos) hK
  have hcards : (∑ p ∈ S, (dilated A N p).card) = ∑ p ∈ S, count A (N/p) := by
    apply Finset.sum_congr rfl
    intro p hp
    exact card_dilated A N p (hS p hp).1.pos
  rw [hcards] at hbonf
  have hfinite : 2*count A N + 2*(∑ p ∈ S, count A (N/p)) ≤
      2*N+2*K+∑ p ∈ S, ∑ q ∈ S, (if p = q then 0 else (dilated A N p ∩ dilated A N q).card) := by
    omega
  have hreal : (2:ℝ)*count A N + 2*(∑ p ∈ S, (count A (N/p):ℝ)) ≤
      2*N+2*K+∑ p ∈ S, ∑ q ∈ S,
        ((if p = q then 0 else (dilated A N p ∩ dilated A N q).card : ℕ) : ℝ) := by
    exact_mod_cast hfinite
  have hdouble := double_inter_bound A N S (fun p hp => (hS p hp).1)
  change _ ≤ (N:ℝ)*lam^2 at hdouble
  have hmain : (2:ℝ)*c*N + 2*c*N*lam ≤ 2*N+2*K+N*lam^2 := by
    have hc := hden N hN
    nlinarith
  -- on the window 1/2 ≤ lam ≤ 1 the 3/4-polynomial is nonnegative
  have hpoly : (0:ℝ) ≤ 2*(3/4)*(1+lam) - 2 - lam^2 := by
    have : 0 ≤ (lam-1/2)*(1-lam) := mul_nonneg (by dsimp [lam]; linarith)
      (by dsimp [lam]; linarith)
    nlinarith
  have hn0 : (0:ℝ) ≤ N := Nat.cast_nonneg N
  have hlam0 : (0:ℝ) ≤ lam := by dsimp [lam]; linarith
  -- 2*c*N*(1+lam) ≤ 2N + 2K + N lam^2 ≤ 2N + 2K + N(2*(3/4)(1+lam) - 2)
  -- gives 2*(c-3/4)*(1+lam)*N ≤ 2K, contradicting hNK since 1+lam ≥ 1
  have h1 : (2:ℝ)*(c-3/4)*(1+lam)*N ≤ 2*K := by nlinarith
  have h2 : (c-3/4)*N ≤ (2:ℝ)*(c-3/4)*(1+lam)*N := by
    have hpos : (0:ℝ) ≤ c - 3/4 := by linarith
    nlinarith
  linarith

open scoped Topology

noncomputable abbrev partialDensity (A : Set ℕ) (n : ℕ) : ℝ :=
  ((((A ∩ Set.univ) ∩ Set.Iio n).ncard : ℕ) : ℝ) /
    ((((Set.univ : Set ℕ) ∩ Set.Iio n).ncard : ℕ) : ℝ)

def HasDensity (A : Set ℕ) (δ : ℝ) : Prop :=
  Tendsto (partialDensity A) atTop (𝓝 δ)

lemma partialDensity_succ (A : Set ℕ) (h0 : 0 ∉ A) (N : ℕ) :
    partialDensity A (N+1) = (count A N : ℝ)/(N+1) := by
  classical
  have hnum : (A ∩ Set.univ) ∩ Set.Iio (N+1) = (elems A N : Set ℕ) := by
    ext a
    simp only [Set.mem_inter_iff, Set.mem_univ, and_true, Set.mem_Iio,
      Finset.mem_coe, mem_elems]
    constructor
    · rintro ⟨ha,hn⟩
      have : a ≠ 0 := by intro he; exact h0 (he ▸ ha)
      exact ⟨by omega, by omega, ha⟩
    · rintro ⟨ha1,haN,ha⟩
      exact ⟨ha,by omega⟩
  have hden : (Set.univ : Set ℕ) ∩ Set.Iio (N+1) = (Finset.range (N+1) : Set ℕ) := by
    ext a
    simp
  simp only [partialDensity, hnum, hden, Set.ncard_coe_finset, Finset.card_range,
    Nat.cast_add, Nat.cast_one, count]

theorem density_le_three_quarters (A : Set ℕ) (h0 : 0 ∉ A) (hA : IsMulCardSet A)
    (δ : ℝ) (hδ : HasDensity A δ) : δ ≤ 3/4 := by
  by_contra h
  have hd : (3/4:ℝ) < δ := lt_of_not_ge h
  -- pick c strictly between 3/4 and δ
  set c : ℝ := (3/4 + δ)/2 with hc
  have hc1 : (3/4:ℝ) < c := by rw [hc]; linarith
  have hc2 : c < δ := by rw [hc]; linarith
  obtain ⟨N0,hN0⟩ := Filter.eventually_atTop.mp ((tendsto_order.mp hδ).1 c hc2)
  apply not_eventually_dense A h0 hA c hc1 N0
  intro N hN
  have hn := hN0 (N+1) (by omega)
  rw [partialDensity_succ A h0 N] at hn
  have hp : (0:ℝ) < N+1 := by positivity
  have := (lt_div_iff₀ hp).mp hn
  have hc0 : (0:ℝ) ≤ c := by linarith
  nlinarith

theorem proof : ∀ (A : Set ℕ) (δ : ℝ), 0 ∉ A → HasDensity A δ → IsMulCardSet A → δ ≤ 3/4 :=
  fun A δ h0 hδ hA => density_le_three_quarters A h0 hA δ hδ

#print axioms proof

end Submissions.Erdos786DistinctDensityLe34.Bonferroni
