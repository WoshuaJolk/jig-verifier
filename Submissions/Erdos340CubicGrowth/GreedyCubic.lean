import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Card
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Push

open Filter Function Set
open scoped Pointwise Real

namespace Submissions.Erdos340CubicGrowth.GreedyCubic

/-- A set whose unordered pairwise sums are unique. -/
def IsSidon (A : Set ℕ) : Prop := ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
  i₁ + i₂ = j₁ + j₂ → (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

namespace Set

theorem IsSidon.insert {A : Set ℕ} {m : ℕ} (hA : IsSidon A) :
    IsSidon (A ∪ {m}) ↔
      (m ∈ A ∨ ∀ᵉ (a ∈ A) (b ∈ A), m + m ≠ a + b ∧ ∀ c ∈ A, m + a ≠ b + c) := by
  by_cases h_mem : m ∈ A
  · exact ⟨fun _ ↦ .inl h_mem, fun _ ↦ by rwa [union_singleton, insert_eq_of_mem h_mem]⟩
  refine ⟨fun h ↦ .inr fun a ha b hb ↦ ⟨fun hc ↦ ?_, fun c hc h_contr ↦ ?_⟩, fun hm ↦ ?_⟩
  · exact h m (by simp) a (by simp [ha]) m (by simp) b (by simp [hb]) hc
      |>.elim (fun _ ↦ by simp_all) (fun _ ↦ by simp_all)
  · exact h m (by simp) b (by simp [hb]) a (by simp [ha]) c (by simp [hc]) h_contr
      |>.elim (fun _ ↦ by simp_all) (fun _ ↦ by simp_all)
  · intro i₁ hi₁
    rcases hi₁ with (hi₁ | hi₁)
    · intro j₁ hj₁
      rcases hj₁ with (hj₁ | hj₁)
      · intro i₂ hi₂
        rcases hi₂ with (hi₂ | hi₂)
        · intro j₂ hj₂
          rcases hj₂ with (hj₂ | hj₂)
          · exact fun h ↦ hA i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ h
          · simp_all
            exact fun h ↦ by
              cases (hm j₁ hj₁ i₁ hi₁).2 i₂ hi₂ (add_comm j₁ m ▸ h.symm)
        · simp_all
          exact fun a ha h ↦ by
            cases (hm i₁ hi₁ j₁ hj₁).2 a ha (add_comm i₁ m ▸ h)
      · simp_all
        refine ⟨fun b hb h ↦ .inr <| by simp_all [add_comm], fun b hb ↦ ⟨fun h ↦ ?_, ?_⟩⟩
        · cases (hm i₁ hi₁ b hb).1 h.symm
        · exact fun c hc h ↦ by cases ((hm c hc i₁ hi₁).2 b hb) h.symm
    · simp_all
      exact fun _ _ _ _ _ ↦ by simp_all [add_comm]

end Set

namespace Finset

instance (A : Finset ℕ) : Decidable (IsSidon (A : Set ℕ)) := by
  refine decidable_of_iff (∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
    i₁ + i₂ = j₁ + j₂ → (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)) ?_
  rfl

theorem IsSidon.insert_ge_max' {A : Finset ℕ} (h : A.Nonempty)
    (hA : IsSidon (A : Set ℕ)) {s : ℕ} (hs : 2 * A.max' h + 1 ≤ s) :
    IsSidon (A ∪ {s}) := by
  have h₁ {a b c : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) :
      a + b < 2 * A.max' h + 1 + c := by
    linarith [A.le_max' _ ha, A.le_max' _ hb]
  have hnot : s ∉ A := by
    exact mt (A.le_max' _) <| not_le.2 <| Finset.max'_lt_iff _ h |>.2 fun a ha ↦ by
      linarith [A.le_max' _ ha]
  exact (Set.IsSidon.insert hA).2 <| by
    simpa [hnot] using fun a ha b hb ↦
      ⟨by linarith [A.le_max' _ ha, A.le_max' _ hb],
        fun c hc ↦ by linarith [h₁ hc hb ha]⟩

theorem IsSidon.exists_insert_ge {A : Finset ℕ} (h : A.Nonempty)
    (hA : IsSidon (A : Set ℕ)) (s : ℕ) :
    ∃ m ≥ s, m ∉ A ∧ IsSidon (A ∪ {m}) := by
  refine ⟨if s ≥ 2 * A.max' h + 1 then s else 2 * A.max' h + 1, ?_, ?_, ?_⟩
  · split_ifs <;> omega
  · split_ifs <;>
    exact mt (A.le_max' _) <| not_le.2 <| Finset.max'_lt_iff _ h |>.2 fun a ha ↦ by
      linarith [A.le_max' _ ha]
  · split_ifs with hs
    · exact insert_ge_max' h hA hs
    · exact insert_ge_max' h hA le_rfl

def greedySidon.go (A : Finset ℕ) (hA : IsSidon (A : Set ℕ)) (m : ℕ) :
    {m' : ℕ // m' ≥ m ∧ m' ∉ A ∧ IsSidon (↑(A ∪ {m'}) : Set ℕ)} :=
  if h : A.Nonempty then
    have hex : ∃ m', m' ≥ m ∧ m' ∉ A ∧ IsSidon (↑(A ∪ {m'}) : Set ℕ) := by
      simpa [and_assoc] using Finset.IsSidon.exists_insert_ge h hA m
    ⟨Nat.find hex, Nat.find_spec hex⟩
  else ⟨m, by simp_all [IsSidon]⟩

def greedySidon.aux (n : ℕ) : ({A : Finset ℕ // IsSidon (A : Set ℕ)} × ℕ) :=
  Nat.rec (⟨{1}, by simp [IsSidon]⟩, 1)
    (fun _ previous =>
      let (A, s) := previous
      let s := if h : A.1.Nonempty then A.1.max' h + 1 else s
      let s' := greedySidon.go A.1 A.2 s
      (⟨A.1 ∪ {s'.1}, s'.2.2.2⟩, s'.1)) n

def greedySidon (n : ℕ) : ℕ :=
  greedySidon.aux n |>.2

end Finset


abbrev initial (n : ℕ) : Finset ℕ := (Finset.greedySidon.aux n).1.1
abbrev seq (n : ℕ) : ℕ := Finset.greedySidon n

theorem go_le {A : Finset ℕ} (hA : IsSidon (A : Set ℕ)) (h : A.Nonempty)
    {m t : ℕ} (ht : m ≤ t) (hnt : t ∉ A) (hst : IsSidon (↑(A ∪ {t}) : Set ℕ)) :
    (Finset.greedySidon.go A hA m).1 ≤ t := by
  unfold Finset.greedySidon.go
  rw [dif_pos h]
  exact Nat.find_min' _ ⟨ht, hnt, hst⟩

theorem prefix_step (n : ℕ) : initial (n+1) = initial n ∪ {seq (n+1)} := by
  rfl

theorem next_eq_go (n : ℕ) (h : (initial n).Nonempty) :
    seq (n+1) = (Finset.greedySidon.go (initial n) (Finset.greedySidon.aux n).1.2
      ((initial n).max' h + 1)).1 := by
  change (Finset.greedySidon.go (initial n) _
    (if hn : (initial n).Nonempty then (initial n).max' hn + 1 else seq n)).1 = _
  rw [dif_pos h]

theorem next_props (n : ℕ) (h : (initial n).Nonempty) :
    (initial n).max' h + 1 ≤ seq (n+1) ∧ seq (n+1) ∉ initial n := by
  have hh := (Finset.greedySidon.go (initial n) (Finset.greedySidon.aux n).1.2
    ((initial n).max' h + 1)).property
  rw [next_eq_go n h]
  exact hh.imp_right (fun x => x.1)

theorem next_le (n : ℕ) (h : (initial n).Nonempty) {t : ℕ}
    (ht : (initial n).max' h + 1 ≤ t) (hnt : t ∉ initial n)
    (hst : IsSidon (↑(initial n ∪ {t}) : Set ℕ)) : seq (n+1) ≤ t := by
  have hh := go_le (Finset.greedySidon.aux n).1.2 h ht hnt hst
  rw [next_eq_go n h]
  exact hh

/-- Each integer up to the current last term is a triple obstruction. -/
def Covered (A : Finset ℕ) (s : ℕ) : Prop :=
  ∀ t, 1 ≤ t → t ≤ s → ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, t + a = b + c

theorem initial_nonempty (n : ℕ) : (initial n).Nonempty := by
  induction n with
  | zero => simp [initial, Finset.greedySidon.aux]
  | succ n ih => rw [prefix_step]; exact ih.mono Finset.subset_union_left

theorem seq_mem (n : ℕ) : seq n ∈ initial n := by
  cases n with
  | zero => simp [initial, seq, Finset.greedySidon, Finset.greedySidon.aux]
  | succ n => rw [prefix_step]; simp

theorem mem_le_seq {n a : ℕ} (ha : a ∈ initial n) : a ≤ seq n := by
  cases n with
  | zero =>
    have heq : a = 1 := by simpa [initial, Finset.greedySidon.aux] using ha
    simp [heq, seq, Finset.greedySidon, Finset.greedySidon.aux]
  | succ n =>
    rw [prefix_step] at ha
    rcases Finset.mem_union.mp ha with ha | ha
    · have hmax := (initial n).le_max' a ha
      have hnext := (next_props n (initial_nonempty n)).1
      omega
    · simpa using (Finset.mem_singleton.mp ha).le

theorem seq_strict : StrictMono seq := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hmax := (initial n).le_max' (seq n) (seq_mem n)
  have hnext := (next_props n (initial_nonempty n)).1
  omega

theorem initial_card (n : ℕ) : (initial n).card = n + 1 := by
  induction n with
  | zero => simp [initial, Finset.greedySidon.aux]
  | succ n ih =>
    rw [prefix_step, Finset.union_singleton,
      Finset.card_insert_of_notMem (next_props n (initial_nonempty n)).2, ih]

theorem one_le_seq (n : ℕ) : 1 ≤ seq n := by
  exact seq_strict.monotone (Nat.zero_le n)

theorem skipped_rep {n t : ℕ} (ht : seq n < t) (hnt : t < seq (n+1)) :
    ∃ a ∈ initial n, ∃ b ∈ initial n, ∃ c ∈ initial n, t + a = b + c := by
  by_contra! hn
  have htmax : (initial n).max' (initial_nonempty n) < t :=
    (Finset.max'_lt_iff _ (initial_nonempty n)).2
      (fun a ha => lt_of_le_of_lt (mem_le_seq ha) ht)
  have hnot : t ∉ initial n := fun hm => (not_le_of_gt ht) (mem_le_seq hm)
  have hnew : IsSidon ((↑(initial n) : Set ℕ) ∪ {t}) := by
    apply (Set.IsSidon.insert (Finset.greedySidon.aux n).1.2).2
    right
    intro a ha b hb
    constructor
    · have ha' := mem_le_seq ha
      have hb' := mem_le_seq hb
      omega
    · intro c hc
      exact hn a ha b hb c hc
  have hle := next_le n (initial_nonempty n) (by omega) hnot
    (by simpa only [Finset.coe_union, Finset.coe_singleton] using hnew)
  omega

theorem covered_initial (n : ℕ) : Covered (initial n) (seq n) := by
  induction n with
  | zero =>
    intro t h1 h2
    change t ≤ 1 at h2
    have ht : t = 1 := by omega
    subst t
    exact ⟨1, by simp [initial, Finset.greedySidon.aux],
      1, by simp [initial, Finset.greedySidon.aux],
      1, by simp [initial, Finset.greedySidon.aux], rfl⟩
  | succ n ih =>
    intro t h1 h2
    by_cases heq : t = seq (n+1)
    · subst t
      exact ⟨seq (n+1), seq_mem _, seq (n+1), seq_mem _, seq (n+1), seq_mem _, rfl⟩
    · have hr : ∃ a ∈ initial n, ∃ b ∈ initial n, ∃ c ∈ initial n, t + a = b + c := by
        by_cases ht : t ≤ seq n
        · exact ih t h1 ht
        · exact skipped_rep (by omega) (by omega)
      obtain ⟨a, ha, b, hb, c, hc, he⟩ := hr
      rw [prefix_step]
      exact ⟨a, Finset.mem_union_left _ ha, b, Finset.mem_union_left _ hb,
        c, Finset.mem_union_left _ hc, he⟩

theorem covered_card_bound {A : Finset ℕ} {N : ℕ} (h : Covered A N) :
    N ≤ A.card ^ 3 := by
  let T := (A ×ˢ (A ×ˢ A)).image (fun p => p.2.1 + p.2.2 - p.1)
  have hsub : Finset.Icc 1 N ⊆ T := by
    intro t ht
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp ht
    obtain ⟨a, ha, b, hb, c, hc, he⟩ := h t h1 h2
    apply Finset.mem_image.mpr
    exact ⟨(a,b,c), by simp only [Finset.mem_product]; exact ⟨ha,hb,hc⟩,
      by dsimp; omega⟩
  have hcount := Finset.card_le_card hsub
  have himage := Finset.card_image_le (s := A ×ˢ (A ×ˢ A))
    (f := fun p : ℕ × ℕ × ℕ => p.2.1 + p.2.2 - p.1)
  simp only [Finset.card_product] at himage
  have hN : (Finset.Icc 1 N).card = N := by simp
  rw [hN] at hcount
  calc N ≤ T.card := hcount
       _ ≤ A.card * (A.card * A.card) := himage
       _ = A.card ^ 3 := by ring

theorem cubic_bound (n : ℕ) : seq n ≤ (n+1)^3 := by
  have h := covered_card_bound (covered_initial n)
  rwa [initial_card] at h

theorem initial_eq_image (n : ℕ) : initial n = (Finset.range (n+1)).image seq := by
  induction n with
  | zero => simp [initial, seq, Finset.greedySidon, Finset.greedySidon.aux]
  | succ n ih =>
    rw [prefix_step, ih, (Finset.range_add_one (n := n+1)), Finset.image_insert,
      Finset.union_singleton]

theorem counting_eq {n N : ℕ} (hn : seq n ≤ N) (hN : N < seq (n+1)) :
    ((Set.range seq ∩ Set.Icc 1 N).ncard : ℕ) = n+1 := by
  have hsets : Set.range seq ∩ Set.Icc 1 N = (↑(initial n) : Set ℕ) := by
    ext a
    constructor
    · rintro ⟨⟨i, rfl⟩, h1, hi⟩
      have hi' : i < n+1 := (seq_strict.lt_iff_lt).mp (lt_of_le_of_lt hi hN)
      rw [initial_eq_image]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi', rfl⟩
    · intro ha
      have ha' : a ∈ (Finset.range (n+1)).image seq := by rwa [initial_eq_image] at ha
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha'
      exact ⟨⟨i, rfl⟩, one_le_seq i, le_trans (mem_le_seq ha) hn⟩
  rw [hsets, Set.ncard_coe_finset, initial_card]

theorem counting_cubic (N : ℕ) :
    N < ((Set.range seq ∩ Set.Icc 1 N).ncard + 1)^3 := by
  have hex : ∃ k, N < seq k :=
    ⟨N+1, lt_of_lt_of_le (Nat.lt_succ_self N) (seq_strict.id_le _)⟩
  have hk := Nat.find_spec hex
  have hmin : ∀ m < Nat.find hex, ¬ N < seq m := fun m hm => Nat.find_min hex hm
  generalize heq : Nat.find hex = k at hk hmin
  cases k with
  | zero =>
    change N < 1 at hk
    have he : N = 0 := by omega
    subst N
    positivity
  | succ n =>
    have hn : seq n ≤ N := Nat.le_of_not_gt (hmin n (by omega))
    rw [counting_eq hn hk]
    exact lt_of_lt_of_le hk (cubic_bound (n+1))

theorem counting_pos {N : ℕ} (hN : 1 ≤ N) :
    1 ≤ (Set.range seq ∩ Set.Icc 1 N).ncard := by
  apply (Set.ncard_pos ((Set.finite_Icc 1 N).subset Set.inter_subset_right)).2
  exact ⟨1, ⟨⟨0, rfl⟩, le_rfl, hN⟩⟩

theorem counting_cuberoot {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) ^ (1/3 : ℝ) ≤ 2 * ((Set.range seq ∩ Set.Icc 1 N).ncard : ℝ) := by
  let c : ℝ := (Set.range seq ∩ Set.Icc 1 N).ncard
  have hc : 1 ≤ c := by dsimp [c]; exact_mod_cast counting_pos hN
  have hcube : (N : ℝ) ≤ (c+1)^3 := by dsimp [c]; exact_mod_cast (counting_cubic N).le
  have hr := Real.rpow_le_rpow (Nat.cast_nonneg N) hcube (by norm_num : (0 : ℝ) ≤ 1/3)
  have heq : ((c+1)^3) ^ (1/3 : ℝ) = c+1 := by
    simpa only [one_div, Nat.cast_ofNat] using Real.pow_rpow_inv_natCast (show 0 ≤ c+1 by linarith)
      (by norm_num : (3 : ℕ) ≠ 0)
  rw [heq] at hr
  change (N : ℝ) ^ (1/3 : ℝ) ≤ 2*c
  linarith

theorem growth_large_epsilon (ε : ℝ) (hε : (1 : ℝ)/6 ≤ ε) :
    (fun N : ℕ => √(N : ℝ) / (N : ℝ)^ε) =O[atTop]
      (fun N : ℕ => ((Set.range seq ∩ Set.Icc 1 N).ncard : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound 2
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hNreal
  have hpow : √(N : ℝ) / (N : ℝ)^ε ≤ (N : ℝ)^(1/3 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hNpos]
    exact Real.rpow_le_rpow_of_exponent_le hNreal (by linarith)
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)), Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg _)]
  exact hpow.trans (counting_cuberoot hN)

-- Positive, negative, and empty controls for the repeated-summand convention.
example : IsSidon (↑({1, 2, 4, 8} : Finset ℕ) : Set ℕ) := by decide
example : ¬ IsSidon (↑({1, 2, 3} : Finset ℕ) : Set ℕ) := by decide
example : ¬ Covered ∅ 1 := by
  intro h
  obtain ⟨a, ha, _⟩ := h 1 le_rfl le_rfl
  simpa using ha
example : seq 0 = 1 := rfl

theorem proof :
    ∀ ε : ℝ, (1 : ℝ)/6 ≤ ε →
      (fun N : ℕ => √(N : ℝ) / (N : ℝ)^ε) =O[atTop]
        (fun N : ℕ => ((Set.range Finset.greedySidon ∩ Set.Icc 1 N).ncard : ℝ)) :=
  growth_large_epsilon

end Submissions.Erdos340CubicGrowth.GreedyCubic
