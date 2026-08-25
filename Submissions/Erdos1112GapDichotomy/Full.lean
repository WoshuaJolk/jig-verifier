import Mathlib


/-! Flattened from Erdos1112. -/
/-
Erdős Problem 1112 — formal statement.

*Reference:* [erdosproblems.com/1112](https://www.erdosproblems.com/1112)

The problem, verbatim from the site:

  "Let $1 \le d_1 < d_2$ and $k \ge 3$. Does there exist an integer $r$ such
  that if $B = \{b_1 < \cdots\}$ is a lacunary sequence of positive integers
  with $b_{i+1} \ge r b_i$ then there exists a sequence of positive integers
  $A = \{a_1 < \cdots\}$ such that $d_1 \le a_{i+1} - a_i \le d_2$ for all
  $i \ge 1$ and $(kA) \cap B = \emptyset$, where $kA$ is the $k$-fold
  sumset?"

Here $kA = \{x_1 + \cdots + x_k : x_1, \ldots, x_k \in A\}$ allows repeated
summands, and $A$, $B$ are infinite sets of positive integers, encoded below
as strictly increasing sequences `ℕ → ℕ` (0-indexed).

Encoding notes (reviewed):
* `IsLacunaryWith` requires `StrictMono b` explicitly, so the class of
  admissible `B` matches the page's `{b₁ < b₂ < ⋯}` notation for *every*
  candidate ratio `r`, not only `r ≥ 2` (where the ratio condition would
  force it anyway).
* `r` is quantified over `ℕ` rather than `ℤ`: the admissible class of `B`
  shrinks as `r` grows, so if any integer ratio works then any larger one
  does; hence the existential questions over `ℤ` and `ℕ` coincide.
* The gap condition is phrased additively (`a i + d₁ ≤ a (i+1)`) to avoid
  truncated natural-number subtraction; with `1 ≤ d₁` it is equivalent to
  `d₁ ≤ a (i+1) − a i ≤ d₂` and forces `A` strictly increasing.

Status: the dichotomy `erdos_1112`, proved in `Erdos1112Proof/Final.lean`
against the definitions in this file, resolves the problem with a complete,
`sorry`-free formal proof. The paper is in `../paper/`.
-/

namespace Erdos1112

/-- `B` (as a strictly increasing enumeration of an infinite set of positive
integers) is *lacunary with ratio `r`*: `b₁ ≥ 1`, `b₁ < b₂ < ⋯`, and
`b_{i+1} ≥ r · b_i` for all `i`. -/
def IsLacunaryWith (r : ℕ) (b : ℕ → ℕ) : Prop :=
  0 < b 0 ∧ StrictMono b ∧ ∀ i, r * b i ≤ b (i + 1)

/-- `A` (as a strictly increasing enumeration of an infinite set of positive
integers) has all consecutive gaps in `[d₁, d₂]`:
`d₁ ≤ a_{i+1} − a_i ≤ d₂` for all `i` (phrased additively; for `1 ≤ d₁`
this forces `A` strictly increasing). -/
def HasGapsIn (d₁ d₂ : ℕ) (a : ℕ → ℕ) : Prop :=
  0 < a 0 ∧ ∀ i, a i + d₁ ≤ a (i + 1) ∧ a (i + 1) ≤ a i + d₂

/-- For `1 ≤ d₁`, the gap condition forces `A` strictly increasing (audit
helper: makes explicit that `A` enumerates an infinite set). -/
lemma HasGapsIn.strictMono {d₁ d₂ : ℕ} {a : ℕ → ℕ} (hd₁ : 1 ≤ d₁)
    (h : HasGapsIn d₁ d₂ a) : StrictMono a :=
  strictMono_nat_of_lt_succ fun i =>
    lt_of_lt_of_le (Nat.lt_add_of_pos_right hd₁) (h.2 i).1

/-- The `k`-fold sumset `kA` of the set enumerated by `a`:
all sums `a_{i₁} + ⋯ + a_{i_k}` (indices arbitrary, repetitions allowed). -/
def kFoldSumset (k : ℕ) (a : ℕ → ℕ) : Set ℕ :=
  { n | ∃ f : Fin k → ℕ, n = ∑ j, a (f j) }

/-- The property asked for by the problem, for given `k`, `d₁`, `d₂` and a
candidate `r`: *every* lacunary sequence `B` with ratio `r` admits a set `A`
with gaps in `[d₁, d₂]` such that `(kA) ∩ B = ∅`. -/
def RatioWorks (k d₁ d₂ r : ℕ) : Prop :=
  ∀ b : ℕ → ℕ, IsLacunaryWith r b →
    ∃ a : ℕ → ℕ, HasGapsIn d₁ d₂ a ∧
      Disjoint (kFoldSumset k a) (Set.range b)

/-- `RatioWorks` is monotone in the ratio: a larger `r` only shrinks the class
of admissible `B`. This machine-checks the reduction from "an integer `r`" to
`r : ℕ` in `Question`: any integer witness may be replaced by any larger
natural one. -/
lemma RatioWorks.mono {k d₁ d₂ r r' : ℕ} (hrr' : r ≤ r')
    (h : RatioWorks k d₁ d₂ r) : RatioWorks k d₁ d₂ r' := by
  intro b hb
  exact h b ⟨hb.1, hb.2.1, fun i => (Nat.mul_le_mul hrr' le_rfl).trans (hb.2.2 i)⟩

/-- **Erdős Problem 1112** (erdosproblems.com/1112), verbatim question:

"Let `1 ≤ d₁ < d₂` and `k ≥ 3`. Does there exist an integer `r` such that if
`B = {b₁ < b₂ < ⋯}` is a lacunary sequence with `b_{i+1} ≥ r·b_i` then there
exists `A = {a₁ < a₂ < ⋯}` with `d₁ ≤ a_{i+1} − a_i ≤ d₂` for all `i` and
`(kA) ∩ B = ∅`?"

I.e., for which `(k, d₁, d₂)` does `∃ r, RatioWorks k d₁ d₂ r` hold?
(Quantifying `r` over `ℕ` is equivalent to quantifying over `ℤ`; see the
header note.) -/
def Question (k d₁ d₂ : ℕ) : Prop :=
  ∃ r : ℕ, RatioWorks k d₁ d₂ r

/-- `B` is lacunary with a *varying* ratio sequence `R`:
`b_{i+1} ≥ R i · b_i` for all `i`. -/
def IsVarLacunaryWith (R : ℕ → ℕ) (b : ℕ → ℕ) : Prop :=
  0 < b 0 ∧ StrictMono b ∧ ∀ i, R i * b i ≤ b (i + 1)

/-- Constant-ratio varying lacunarity is exactly fixed-ratio lacunarity
(audit helper: the bridge used when instantiating the strong non-existence
theorem to refute `RatioWorks` at a constant ratio). -/
lemma isVarLacunaryWith_const_iff {r : ℕ} {b : ℕ → ℕ} :
    IsVarLacunaryWith (fun _ => r) b ↔ IsLacunaryWith r b :=
  Iff.rfl

/-! ### The ℤ-to-ℕ bridge

The problem asks for an *integer* `r`; the development quantifies `r : ℕ`. The two
existence questions are equivalent. Rather than argue this only in prose, we state
the integer form and prove the equivalence. -/

/-- `B` is lacunary with an *integer* ratio `r`: the problem's literal phrasing. -/
def IsLacunaryWithInt (r : ℤ) (b : ℕ → ℕ) : Prop :=
  0 < b 0 ∧ StrictMono b ∧ ∀ i, r * (b i : ℤ) ≤ (b (i + 1) : ℤ)

/-- `RatioWorks` with the ratio quantified over `ℤ`. -/
def RatioWorksInt (k d₁ d₂ : ℕ) (r : ℤ) : Prop :=
  ∀ b : ℕ → ℕ, IsLacunaryWithInt r b →
    ∃ a : ℕ → ℕ, HasGapsIn d₁ d₂ a ∧
      Disjoint (kFoldSumset k a) (Set.range b)

/-- **The problem exactly as posed**: does *some integer* `r` work? -/
def QuestionInt (k d₁ d₂ : ℕ) : Prop :=
  ∃ r : ℤ, RatioWorksInt k d₁ d₂ r

/-- **The ℤ-to-ℕ bridge.** Quantifying the ratio over `ℤ` gives exactly the same
existence question as quantifying it over `ℕ`.

Forward: a natural witness is an integer witness. Backward: given an integer witness
`r`, take `r.toNat`. If `r ≤ 0` the integer ratio condition is vacuous (`B` is
positive), so every `B` admissible at `r.toNat = 0` is admissible at `r`; if `r > 0`
then `(r.toNat : ℤ) = r` and the two conditions coincide. -/
theorem question_iff_questionInt (k d₁ d₂ : ℕ) :
    Question k d₁ d₂ ↔ QuestionInt k d₁ d₂ := by
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨(r : ℤ), fun b hb => hr b ⟨hb.1, hb.2.1, fun i => ?_⟩⟩
    have h := hb.2.2 i
    exact_mod_cast h
  · rintro ⟨r, hr⟩
    refine ⟨r.toNat, fun b hb => hr b ⟨hb.1, hb.2.1, fun i => ?_⟩⟩
    have hb0 : (0 : ℤ) ≤ (b i : ℤ) := Int.natCast_nonneg _
    have hb1 : (0 : ℤ) ≤ (b (i + 1) : ℤ) := Int.natCast_nonneg _
    by_cases h : r ≤ 0
    · nlinarith
    · push_neg at h
      have hrt : (r.toNat : ℤ) = r := Int.toNat_of_nonneg h.le
      have hn : (r.toNat) * b i ≤ b (i + 1) := hb.2.2 i
      have hz : ((r.toNat * b i : ℕ) : ℤ) ≤ ((b (i + 1) : ℕ) : ℤ) := by exact_mod_cast hn
      rw [Nat.cast_mul, hrt] at hz
      exact hz

end Erdos1112


/-! Flattened from Erdos1112Proof.Basic. -/
/-
Bridge lemmas on the frozen definitions of `Erdos1112.lean`.

This file must contain no `sorry`. It provides the working API for
`IsLacunaryWith`, `HasGapsIn`, `kFoldSumset`, `RatioWorks`, `IsVarLacunaryWith`
without ever restating them. (`RatioWorks.mono` already lives, proved, in the
frozen file — we reuse it and do not restate it.)

Convention: API lemmas about a frozen def live in that def's namespace (so dot
notation works); everything else lives in `Erdos1112.Proof`.
-/

namespace Erdos1112

namespace Proof

/-! ### Variable-ratio vs constant-ratio lacunarity -/

/-- A constant ratio sequence specializes `IsVarLacunaryWith` to
`IsLacunaryWith` definitionally. -/
lemma isVarLacunaryWith_const {r : ℕ} {b : ℕ → ℕ} :
    IsVarLacunaryWith (fun _ => r) b ↔ IsLacunaryWith r b :=
  Iff.rfl

/-! ### `kFoldSumset` -/

lemma mem_kFoldSumset {k : ℕ} {a : ℕ → ℕ} {n : ℕ} :
    n ∈ kFoldSumset k a ↔ ∃ f : Fin k → ℕ, n = ∑ j, a (f j) :=
  Iff.rfl

lemma sum_mem_kFoldSumset {k : ℕ} {a : ℕ → ℕ} (f : Fin k → ℕ) :
    (∑ j, a (f j)) ∈ kFoldSumset k a :=
  ⟨f, rfl⟩

/-- The constant configuration: `k · a i ∈ kA`. -/
lemma const_mem_kFoldSumset {k : ℕ} {a : ℕ → ℕ} (i : ℕ) :
    k * a i ∈ kFoldSumset k a := by
  refine ⟨fun _ => i, ?_⟩
  simp [Finset.sum_const]

/-- Disjointness with `Set.range b`, unfolded to the pointwise form used
throughout the non-existence development. -/
lemma disjoint_range_iff {k : ℕ} {a b : ℕ → ℕ} :
    Disjoint (kFoldSumset k a) (Set.range b) ↔
      ∀ n ∈ kFoldSumset k a, ∀ i, n ≠ b i := by
  rw [Set.disjoint_left]
  constructor
  · intro h n hn i hni
    exact h hn ⟨i, hni.symm⟩
  · rintro h n hn ⟨i, rfl⟩
    exact h _ hn i rfl

/-- Failure of disjointness from an explicit hit. -/
lemma not_disjoint_of_mem {k : ℕ} {a b : ℕ → ℕ} {i : ℕ}
    (h : b i ∈ kFoldSumset k a) :
    ¬ Disjoint (kFoldSumset k a) (Set.range b) := by
  rw [disjoint_range_iff]
  push_neg
  exact ⟨b i, h, i, rfl⟩

/-- The gap word of a sequence: `gap a n = a (n+1) − a n`. -/
def gap (a : ℕ → ℕ) (n : ℕ) : ℕ := a (n + 1) - a n

/-- **Generic discrete intermediate-value lemma.** A walk `f : ℕ → ℤ` that
starts at or below `lo`, reaches at or above `hi` by step `N`, and never
increases by more than `σ` per step, lands inside the window `[lo, hi]`
provided the window is at least as wide as one step (`σ ≤ hi − lo + 1`). Used
three times: the sweep crossing (2.7), the Sturmian ladder (2.10 Step 3), and
the Slot Lemma coarse dial (2.12). -/
lemma discrete_ivt {f : ℕ → ℤ} {N : ℕ} {lo hi σ : ℤ}
    (h0 : f 0 ≤ lo) (hN : hi ≤ f N) (hlohi : lo ≤ hi)
    (hstep : ∀ n, n < N → f (n + 1) - f n ≤ σ) (hwidth : σ ≤ hi - lo + 1) :
    ∃ n, n ≤ N ∧ lo ≤ f n ∧ f n ≤ hi := by
  classical
  have hPN : lo ≤ f N := le_trans hlohi hN
  have hex : ∃ n, lo ≤ f n := ⟨N, hPN⟩
  have hm : lo ≤ f (Nat.find hex) := Nat.find_spec hex
  have hmN : Nat.find hex ≤ N := Nat.find_le hPN
  rcases Nat.eq_zero_or_pos (Nat.find hex) with hm0 | hmpos
  · refine ⟨0, Nat.zero_le _, ?_, ?_⟩
    · rw [hm0] at hm; exact hm
    · have : f 0 = lo := le_antisymm h0 (by rw [hm0] at hm; exact hm)
      omega
  · set m := Nat.find hex with hmdef
    have hprev : ¬ lo ≤ f (m - 1) :=
      Nat.find_min hex (show m - 1 < m by omega)
    have hstep' : f m - f (m - 1) ≤ σ := by
      have hlt : m - 1 < N := by omega
      have := hstep (m - 1) hlt
      rwa [Nat.sub_add_cancel hmpos] at this
    exact ⟨m, hmN, hm, by omega⟩

end Proof

/-! ### Consequences of `HasGapsIn` (in its namespace, for dot notation) -/

namespace HasGapsIn

open Proof

variable {d₁ d₂ : ℕ} {a : ℕ → ℕ}

lemma monotone (h : HasGapsIn d₁ d₂ a) : Monotone a :=
  monotone_nat_of_le_succ fun n => le_trans (Nat.le_add_right _ _) (h.2 n).1

-- `HasGapsIn.strictMono` is provided by the frozen statement file.

lemma pos (h : HasGapsIn d₁ d₂ a) (n : ℕ) : 0 < a n :=
  lt_of_lt_of_le h.1 (h.monotone (Nat.zero_le n))

/-- Linear lower bound `a 0 + n·d₁ ≤ a n`. -/
lemma le_apply (h : HasGapsIn d₁ d₂ a) (n : ℕ) :
    a 0 + n * d₁ ≤ a n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h1 := (h.2 n).1
      have h2 : (n + 1) * d₁ = n * d₁ + d₁ := by ring
      omega

/-- Linear upper bound `a n ≤ a 0 + n·d₂`. -/
lemma apply_le (h : HasGapsIn d₁ d₂ a) (n : ℕ) :
    a n ≤ a 0 + n * d₂ := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h1 := (h.2 n).2
      have h2 : (n + 1) * d₂ = n * d₂ + d₂ := by ring
      omega

/-- A gap sequence is unbounded (given `1 ≤ d₁`). -/
lemma exists_gt (hd : 1 ≤ d₁) (h : HasGapsIn d₁ d₂ a) (N : ℕ) :
    ∃ n, N < a n := by
  refine ⟨N + 1, ?_⟩
  have h1 := h.le_apply (N + 1)
  have h2 : N + 1 ≤ (N + 1) * d₁ := Nat.le_mul_of_pos_right (N + 1) hd
  have h3 := h.1
  omega

/-- Tails of gap sequences are gap sequences. -/
lemma tail (h : HasGapsIn d₁ d₂ a) (T : ℕ) :
    HasGapsIn d₁ d₂ (fun n => a (T + n)) :=
  ⟨h.pos T, fun i => h.2 (T + i)⟩

lemma gap_le (h : HasGapsIn d₁ d₂ a) (n : ℕ) : gap a n ≤ d₂ := by
  have := h.2 n; unfold Proof.gap; omega

lemma le_gap (h : HasGapsIn d₁ d₂ a) (n : ℕ) : d₁ ≤ gap a n := by
  have := h.2 n; unfold Proof.gap; omega

lemma succ_eq_add_gap (h : HasGapsIn d₁ d₂ a) (n : ℕ) :
    a (n + 1) = a n + gap a n := by
  have := (h.2 n).1; unfold Proof.gap; omega

/-- `a n = a 0 + ∑_{i<n} gap a i`. -/
lemma eq_add_sum_gaps (h : HasGapsIn d₁ d₂ a) (n : ℕ) :
    a n = a 0 + ∑ i ∈ Finset.range n, gap a i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ← Nat.add_assoc, ← ih, ← h.succ_eq_add_gap]

end HasGapsIn

end Erdos1112


/-! Flattened from Erdos1112Proof.Existence.Beatty. -/
/-
Shifted Beatty sequences, their gaps, cluster containment, and the safety
criterion. Paper: the existence section.
-/

namespace Erdos1112
namespace Proof

/-- The shifted Beatty sequence with real slope `γ` and offset `c`:
`beatty γ c i = c + ⌊(i+1)·γ⌋₊` (indices `i ≥ 0` encode the paper's `i ≥ 1`). -/
noncomputable def beatty (γ : ℝ) (c : ℕ) (i : ℕ) : ℕ :=
  c + (⌊((i : ℝ) + 1) * γ⌋).toNat

/-- Floors of consecutive Beatty terms differ by `d₂ − 1` or `d₂` when the
slope lies in `(d₂ − 1, d₂)`. -/
lemma beatty_floor_gap {d₂ : ℕ} {γ : ℝ} (hγl : (d₂ : ℝ) - 1 < γ)
    (hγu : γ < d₂) (x : ℝ) :
    ⌊x * γ⌋ + ((d₂ : ℤ) - 1) ≤ ⌊(x + 1) * γ⌋ ∧
      ⌊(x + 1) * γ⌋ ≤ ⌊x * γ⌋ + (d₂ : ℤ) := by
  have hx : (x + 1) * γ = x * γ + γ := by ring
  constructor
  · have h1 : x * γ + (((d₂ : ℤ) - 1 : ℤ) : ℝ) ≤ (x + 1) * γ := by
      push_cast
      rw [hx]
      linarith
    calc ⌊x * γ⌋ + ((d₂ : ℤ) - 1)
        = ⌊x * γ + (((d₂ : ℤ) - 1 : ℤ) : ℝ)⌋ := (Int.floor_add_intCast _ _).symm
      _ ≤ ⌊(x + 1) * γ⌋ := Int.floor_le_floor h1
  · have h2 : (x + 1) * γ ≤ x * γ + ((d₂ : ℤ) : ℝ) := by
      push_cast
      rw [hx]
      linarith
    calc ⌊(x + 1) * γ⌋ ≤ ⌊x * γ + ((d₂ : ℤ) : ℝ)⌋ := Int.floor_le_floor h2
      _ = ⌊x * γ⌋ + (d₂ : ℤ) := Int.floor_add_intCast _ _

/-- For slope `γ ∈ (d₂−1, d₂)`, the Beatty gaps lie in `{d₂−1, d₂} ⊆ [d₁, d₂]`,
and the sequence starts positive: it is an admissible `A`. -/
theorem beatty_hasGapsIn {d₁ d₂ c : ℕ} {γ : ℝ}
    (hd₁ : 1 ≤ d₁) (hd : d₁ < d₂)
    (hγl : (d₂ : ℝ) - 1 < γ) (hγu : γ < d₂) :
    HasGapsIn d₁ d₂ (beatty γ c) := by
  have hd₂ : 2 ≤ d₂ := by omega
  have hγ1 : (1 : ℝ) ≤ γ := by
    have h2 : (2 : ℝ) ≤ (d₂ : ℝ) := by exact_mod_cast hd₂
    linarith
  -- floors along the sequence are ≥ 1, so `toNat` is faithful
  have hfloor_ge : ∀ i : ℕ, (1 : ℤ) ≤ ⌊((i : ℝ) + 1) * γ⌋ := by
    intro i
    apply Int.le_floor.mpr
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) i]
  constructor
  · -- positivity of the first term
    have := hfloor_ge 0
    unfold beatty
    omega
  · intro i
    have key := beatty_floor_gap hγl hγu ((i : ℝ) + 1)
    have hA := hfloor_ge i
    have hB := hfloor_ge (i + 1)
    have hcast : ((i + 1 : ℕ) : ℝ) + 1 = ((i : ℝ) + 1) + 1 := by push_cast; ring
    unfold beatty
    rw [hcast]
    constructor
    · have := key.1
      omega
    · have := key.2
      omega

/-- Cluster containment (1.1): every element of `k·A_{γ,c}` lies in
`(k·c + s·γ − k, k·c + s·γ]` for some integer `s ≥ k`. -/
theorem beatty_mem_cluster {k c : ℕ} {γ : ℝ} (hk : 0 < k) (hγ : 0 < γ) {n : ℕ}
    (hn : n ∈ kFoldSumset k (beatty γ c)) :
    ∃ s : ℕ, k ≤ s ∧ (k * c + s * γ - k : ℝ) < n ∧ (n : ℝ) ≤ k * c + s * γ := by
  obtain ⟨f, rfl⟩ := hn
  have hfl : ∀ j : Fin k, (0 : ℤ) ≤ ⌊((f j : ℝ) + 1) * γ⌋ := fun j =>
    Int.floor_nonneg.mpr (by positivity)
  -- the ℤ-level value of each term
  have hterm : ∀ j : Fin k,
      ((beatty γ c (f j) : ℕ) : ℤ) = (c : ℤ) + ⌊((f j : ℝ) + 1) * γ⌋ := by
    intro j
    unfold beatty
    push_cast [Int.toNat_of_nonneg (hfl j)]
    ring
  -- the whole sum, over ℝ
  have hn' : ((∑ j, beatty γ c (f j) : ℕ) : ℝ) =
      k * c + ∑ j, ((⌊((f j : ℝ) + 1) * γ⌋ : ℤ) : ℝ) := by
    have h1 : ((∑ j, beatty γ c (f j) : ℕ) : ℤ) =
        k * c + ∑ j, ⌊((f j : ℝ) + 1) * γ⌋ := by
      push_cast
      rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_add_distrib]
      simp [mul_comm]
    exact_mod_cast h1
  -- the index sum, over ℝ
  have hs : ∑ j, (((f j : ℝ) + 1) * γ) = ((∑ j, (f j + 1) : ℕ) : ℝ) * γ := by
    rw [← Finset.sum_mul]
    push_cast
    ring_nf
  refine ⟨∑ j, (f j + 1), ?_, ?_, ?_⟩
  · calc k = ∑ _j : Fin k, 1 := by simp
      _ ≤ ∑ j, (f j + 1) := Finset.sum_le_sum fun j _ => by omega
  · -- strict lower bound: sum of (x_j − 1 < ⌊x_j⌋)
    have hlt : ∑ j, (((f j : ℝ) + 1) * γ - 1) <
        ∑ j, ((⌊((f j : ℝ) + 1) * γ⌋ : ℤ) : ℝ) := by
      refine Finset.sum_lt_sum_of_nonempty ?_ fun j _ => Int.sub_one_lt_floor _
      exact Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hk)
    have hsub : ∑ j, (((f j : ℝ) + 1) * γ - 1) =
        ((∑ j, (f j + 1) : ℕ) : ℝ) * γ - k := by
      rw [Finset.sum_sub_distrib, hs]
      simp
    rw [hn']
    linarith [hsub ▸ hlt]
  · -- upper bound: sum of (⌊x_j⌋ ≤ x_j)
    have hle : ∑ j, ((⌊((f j : ℝ) + 1) * γ⌋ : ℤ) : ℝ) ≤
        ∑ j, ((f j : ℝ) + 1) * γ :=
      Finset.sum_le_sum fun j _ => Int.floor_le _
    rw [hn']
    linarith [hs ▸ hle]

/-- Safety criterion (1.1): if no integer `s ≥ 1` has `s·γ ∈ [b − k·c, b − k·c + k]`
then `b ∉ k·A_{γ,c}`. -/
theorem beatty_avoids {k c b : ℕ} {γ : ℝ} (hk : 0 < k) (hγ : 0 < γ)
    (hsafe : ∀ s : ℕ, 0 < s →
      (s * γ : ℝ) ∉ Set.Icc ((b : ℝ) - k * c) ((b : ℝ) - k * c + k)) :
    b ∉ kFoldSumset k (beatty γ c) := by
  intro hb
  obtain ⟨s, hsk, hlo, hhi⟩ := beatty_mem_cluster hk hγ hb
  refine hsafe s (lt_of_lt_of_le hk hsk) ⟨?_, ?_⟩
  · linarith
  · linarith

end Proof
end Erdos1112


/-! Flattened from Erdos1112Proof.Existence.FreeGap. -/
/-
The free-gap lemma. Paper: the existence section.

Formalization note (deviation from the paper, safe direction): instead of the
relevance-interval analysis we take `s₁ := ⌈t / hi⌉₊` and exhibit the single
free gap `(gl, w) := ((t+k)/(s₁+1), t/s₁)`:
  * `w ≤ hi` by the ceiling bound; `hi·t ≤ w·t + d₂²` by its minimality;
  * `w − k ≥ 15/32` (from `hi ≥ d₂ − 1/2`, `d₂² ≤ t/32`, `k ≤ d₂ − 1`);
  * the exact identity `(w − gl)·(s₁+1) = w − k` gives the gap length;
  * `(w − gl)·t ≤ d₂²` and `4d₂² ≤ (hi−lo)·t` place the gap inside `[lo, hi]`;
  * safety of any `γ` in the OPEN gap is pure monotonicity in `s`:
    `s ≤ s₁ ⇒ s·γ < s·w ≤ t` and `s ≥ s₁+1 ⇒ s·γ > s·gl ≥ t + k`.
The closed middle third `[gl + (w−gl)/3, w − (w−gl)/3]` has length
`(w−gl)/3 ≥ d₂/(48t)`. All interior reasoning is `t`-scaled (division-free).
-/

namespace Erdos1112
namespace Proof

/-- `γ` is safe for target `t`: no positive multiple `s·γ` lands in `[t, t+k]`. -/
def SafeFor (k : ℕ) (t γ : ℝ) : Prop :=
  ∀ s : ℕ, 0 < s → (s * γ : ℝ) ∉ Set.Icc t (t + k)

set_option maxHeartbeats 1600000 in
/-- **Free-gap lemma** (1.2). Let `t ≥ 32·d₂²` and `[lo, hi] ⊆ [d₂ − 1/2, d₂]`
with `hi − lo ≥ 4·d₂²/t`. Then there is a closed subinterval `[lo', hi']` of
length `≥ d₂/(48·t)` all of whose slopes are safe for `t`. -/
theorem exists_safe_subinterval {k d₂ : ℕ} (hk : 1 ≤ k) (hkd : k + 1 ≤ d₂)
    {t lo hi : ℝ} (ht : 32 * (d₂ : ℝ) ^ 2 ≤ t)
    (hlo : (d₂ : ℝ) - 1 / 2 ≤ lo) (hhi : hi ≤ d₂)
    (hlen : 4 * (d₂ : ℝ) ^ 2 / t ≤ hi - lo) :
    ∃ lo' hi', lo ≤ lo' ∧ hi' ≤ hi ∧ (d₂ : ℝ) / (48 * t) ≤ hi' - lo' ∧
      ∀ γ ∈ Set.Icc lo' hi', SafeFor k t γ := by
  -- ambient facts
  have hd₂2 : (2 : ℝ) ≤ (d₂ : ℝ) := by exact_mod_cast (by omega : 2 ≤ d₂)
  have hkd' : (k : ℝ) + 1 ≤ (d₂ : ℝ) := by exact_mod_cast hkd
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le (by nlinarith) ht
  have hlo32 : (3 : ℝ) / 2 ≤ lo := by linarith
  -- t-scaled interval length: 4d₂² ≤ (hi − lo)·t
  have hlen4 : 4 * (d₂ : ℝ) ^ 2 ≤ (hi - lo) * t := by
    have h := mul_le_mul_of_nonneg_right hlen (le_of_lt ht0)
    rwa [div_mul_cancel₀ _ (ne_of_gt ht0)] at h
  have hlohi : lo < hi := by
    by_contra hcon
    push_neg at hcon
    have h := mul_nonpos_of_nonpos_of_nonneg
      (by linarith : hi - lo ≤ 0) (le_of_lt ht0)
    nlinarith
  have hhi0 : (0 : ℝ) < hi := by linarith
  -- the pivotal index; make it opaque immediately after extracting its bounds
  obtain ⟨s₁, h_le, h_lt⟩ : ∃ s₁ : ℕ, t / hi ≤ (s₁ : ℝ) ∧ (s₁ : ℝ) < t / hi + 1 :=
    ⟨⌈t / hi⌉₊, Nat.le_ceil _, Nat.ceil_lt_add_one (le_of_lt (div_pos ht0 hhi0))⟩
  have hs₁_pos : (0 : ℝ) < (s₁ : ℝ) := lt_of_lt_of_le (div_pos ht0 hhi0) h_le
  have hs₁1_pos : (0 : ℝ) < (s₁ : ℝ) + 1 := by linarith
  -- multiplicative forms of the ceiling bounds
  have hs₁hi_ge : t ≤ (s₁ : ℝ) * hi := by
    rw [div_le_iff₀ hhi0] at h_le; linarith
  have hs₁hi_lt : (s₁ : ℝ) * hi < t + hi := by
    have h := mul_lt_mul_of_pos_right h_lt hhi0
    rwa [add_mul, one_mul, div_mul_cancel₀ t (ne_of_gt hhi0)] at h
  -- size bounds on s₁
  have hs₁d₂ : t ≤ (s₁ : ℝ) * (d₂ : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hhi (le_of_lt hs₁_pos)
    linarith [hs₁hi_ge]
  have hs₁_ub : ((s₁ : ℝ) + 1) * (d₂ : ℝ) ≤ 3 * t := by
    have hhi_lb : (3 / 4 : ℝ) * (d₂ : ℝ) ≤ hi := by nlinarith
    have h1 : (s₁ : ℝ) * ((3 / 4) * (d₂ : ℝ)) ≤ (s₁ : ℝ) * hi :=
      mul_le_mul_of_nonneg_left hhi_lb (le_of_lt hs₁_pos)
    have h2 : 32 * (d₂ : ℝ) ≤ t := by nlinarith
    nlinarith [hs₁hi_lt]
  -- the gap endpoints, as opaque reals with their defining products
  obtain ⟨w, hw_mul⟩ : ∃ w : ℝ, w * (s₁ : ℝ) = t :=
    ⟨t / (s₁ : ℝ), div_mul_cancel₀ t (ne_of_gt hs₁_pos)⟩
  obtain ⟨gl, hgl_mul⟩ : ∃ gl : ℝ, gl * ((s₁ : ℝ) + 1) = t + (k : ℝ) :=
    ⟨(t + (k : ℝ)) / ((s₁ : ℝ) + 1), div_mul_cancel₀ _ (ne_of_gt hs₁1_pos)⟩
  have hw_pos : (0 : ℝ) < w := by
    by_contra hcon
    push_neg at hcon
    have h := mul_nonpos_of_nonpos_of_nonneg hcon (le_of_lt hs₁_pos)
    rw [hw_mul] at h
    linarith
  have hgl_pos : (0 : ℝ) < gl := by
    by_contra hcon
    push_neg at hcon
    have h := mul_nonpos_of_nonpos_of_nonneg hcon (le_of_lt hs₁1_pos)
    rw [hgl_mul] at h
    linarith
  have hw_le_hi : w ≤ hi := by
    by_contra hcon
    push_neg at hcon
    have h := mul_lt_mul_of_pos_right hcon hs₁_pos
    rw [hw_mul] at h
    nlinarith [hs₁hi_ge]
  -- minimality of s₁, t-scaled: hi·t ≤ w·t + d₂²
  have hw_ge : hi * t ≤ w * t + (d₂ : ℝ) ^ 2 := by
    have hkey : (s₁ : ℝ) * hi * w = t * hi := by
      calc (s₁ : ℝ) * hi * w = w * (s₁ : ℝ) * hi := by ring
        _ = t * hi := by rw [hw_mul]
    have h := mul_lt_mul_of_pos_right hs₁hi_lt hw_pos
    rw [hkey] at h
    have hw_d₂ : hi * w ≤ (d₂ : ℝ) ^ 2 := by
      have a1 : hi * w ≤ hi * hi :=
        mul_le_mul_of_nonneg_left hw_le_hi (by linarith)
      have a2 : hi * hi ≤ (d₂ : ℝ) * (d₂ : ℝ) :=
        mul_le_mul hhi hhi (by linarith) (by linarith)
      calc hi * w ≤ hi * hi := a1
        _ ≤ (d₂ : ℝ) * (d₂ : ℝ) := a2
        _ = (d₂ : ℝ) ^ 2 := by ring
    -- h : t·hi < (t + hi)·w  ⇒  hi·t < w·t + hi·w ≤ w·t + d₂²
    have hexp : (t + hi) * w = t * w + hi * w := by ring
    rw [hexp] at h
    have hc1 : t * hi = hi * t := by ring
    have hc2 : t * w = w * t := by ring
    rw [hc1, hc2] at h
    linarith [hw_d₂]
  -- the k-margin: w − k ≥ 15/32
  have hw_k : (15 / 32 : ℝ) ≤ w - (k : ℝ) := by
    by_contra hcon
    push_neg at hcon
    have h1 : w < (d₂ : ℝ) - 17 / 32 := by linarith
    have h2 : w * t < ((d₂ : ℝ) - 17 / 32) * t := mul_lt_mul_of_pos_right h1 ht0
    have h3 : ((d₂ : ℝ) - 1 / 2) * t ≤ hi * t :=
      mul_le_mul_of_nonneg_right (by linarith) (le_of_lt ht0)
    nlinarith [hw_ge]
  -- exact gap-length identity and positivity
  have hlenmul : (w - gl) * ((s₁ : ℝ) + 1) = w - (k : ℝ) := by
    linear_combination hw_mul - hgl_mul
  have hwgl_pos : (0 : ℝ) < w - gl := by
    by_contra hcon
    push_neg at hcon
    have h := mul_nonpos_of_nonpos_of_nonneg hcon (le_of_lt hs₁1_pos)
    rw [hlenmul] at h
    linarith
  -- the gap sits above lo: (w − gl)·t ≤ d₂², then gl·t ≥ lo·t
  have ht_le : t ≤ ((s₁ : ℝ) + 1) * (d₂ : ℝ) := by
    rw [add_mul, one_mul]
    linarith [hs₁d₂]
  have hwgl_t : (w - gl) * t ≤ (d₂ : ℝ) ^ 2 := by
    have step1 : (w - gl) * t ≤ (w - gl) * (((s₁ : ℝ) + 1) * (d₂ : ℝ)) :=
      mul_le_mul_of_nonneg_left ht_le (le_of_lt hwgl_pos)
    have step2 : (w - gl) * (((s₁ : ℝ) + 1) * (d₂ : ℝ)) = (w - (k : ℝ)) * (d₂ : ℝ) := by
      rw [← hlenmul]; ring
    have step3 : (w - (k : ℝ)) * (d₂ : ℝ) ≤ (d₂ : ℝ) * (d₂ : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith [hw_le_hi]) (by linarith)
    calc (w - gl) * t ≤ (w - gl) * (((s₁ : ℝ) + 1) * (d₂ : ℝ)) := step1
      _ = (w - (k : ℝ)) * (d₂ : ℝ) := step2
      _ ≤ (d₂ : ℝ) * (d₂ : ℝ) := step3
      _ = (d₂ : ℝ) ^ 2 := by ring
  have hgl_t : lo * t ≤ gl * t := by
    have e1 : (w - gl) * t = w * t - gl * t := by ring
    have e2 : (hi - lo) * t = hi * t - lo * t := by ring
    rw [e1] at hwgl_t
    rw [e2] at hlen4
    linarith [hw_ge, hwgl_t, hlen4, sq_nonneg ((d₂ : ℝ))]
  have hgl_ge_lo : lo ≤ gl := by
    by_contra hcon
    push_neg at hcon
    have := mul_lt_mul_of_pos_right hcon ht0
    linarith
  -- the middle third and its length
  refine ⟨gl + (w - gl) / 3, w - (w - gl) / 3, by linarith, by linarith [hw_le_hi], ?_, ?_⟩
  · -- d₂/(48t) ≤ (w−gl)/3, i.e. d₂ ≤ 16·t·(w−gl)
    have hgoal16 : (d₂ : ℝ) ≤ 16 * (t * (w - gl)) := by
      have hint1 : ((s₁ : ℝ) + 1) * (d₂ : ℝ) * (w - gl) ≤ 3 * t * (w - gl) :=
        mul_le_mul_of_nonneg_right hs₁_ub (le_of_lt hwgl_pos)
      have hint2 : (w - gl) * ((s₁ : ℝ) + 1) * (d₂ : ℝ) = (w - (k : ℝ)) * (d₂ : ℝ) := by
        rw [hlenmul]
      have hint3 : (15 / 32 : ℝ) * (d₂ : ℝ) ≤ (w - (k : ℝ)) * (d₂ : ℝ) :=
        mul_le_mul_of_nonneg_right hw_k (by linarith)
      have hchain : (15 / 32 : ℝ) * (d₂ : ℝ) ≤ 3 * (t * (w - gl)) := by
        calc (15 / 32 : ℝ) * (d₂ : ℝ) ≤ (w - (k : ℝ)) * (d₂ : ℝ) := hint3
          _ = (w - gl) * ((s₁ : ℝ) + 1) * (d₂ : ℝ) := hint2.symm
          _ = ((s₁ : ℝ) + 1) * (d₂ : ℝ) * (w - gl) := by ring
          _ ≤ 3 * t * (w - gl) := hint1
          _ = 3 * (t * (w - gl)) := by ring
      linarith [hchain, hd₂2]
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 48 * t)]
    have hring : (w - (w - gl) / 3 - (gl + (w - gl) / 3)) * (48 * t) =
        16 * (t * (w - gl)) := by ring
    rw [hring]
    exact hgoal16
  · -- safety of every γ in the closed middle third
    rintro γ ⟨hγl, hγu⟩ s hs
    have hγ_lt_w : γ < w := by linarith [hwgl_pos]
    have hγ_gt_gl : gl < γ := by linarith [hwgl_pos]
    have hs0 : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
    rintro ⟨hmem1, hmem2⟩
    rcases Nat.lt_or_ge s (s₁ + 1) with hss | hss
    · -- s ≤ s₁ ⇒ s·γ < t
      have hss' : (s : ℝ) ≤ (s₁ : ℝ) := by exact_mod_cast Nat.lt_succ_iff.mp hss
      have h11 : (s : ℝ) * γ < (s : ℝ) * w := mul_lt_mul_of_pos_left hγ_lt_w hs0
      have h12 : (s : ℝ) * w ≤ (s₁ : ℝ) * w :=
        mul_le_mul_of_nonneg_right hss' (le_of_lt hw_pos)
      have hcomm : (s₁ : ℝ) * w = t := by linear_combination hw_mul
      linarith [h11, h12, hcomm]
    · -- s ≥ s₁ + 1 ⇒ s·γ > t + k
      have hs' : (s₁ : ℝ) + 1 ≤ (s : ℝ) := by exact_mod_cast hss
      have h14 : ((s₁ : ℝ) + 1) * gl ≤ (s : ℝ) * gl :=
        mul_le_mul_of_nonneg_right hs' (le_of_lt hgl_pos)
      have h15 : (s : ℝ) * gl < (s : ℝ) * γ := mul_lt_mul_of_pos_left hγ_gt_gl hs0
      have hcomm : ((s₁ : ℝ) + 1) * gl = t + (k : ℝ) := by linear_combination hgl_mul
      linarith [h14, h15, hcomm]

end Proof
end Erdos1112


/-! Flattened from Erdos1112Proof.Existence.Nested. -/
/-
Offset choice past the small elements of `B`, nested safe intervals, and
the existence theorem with the explicit ratio `192·d₂`.
Paper: the existence section.

Construction notes:
  * `j₀ := 4·d₂²` — since `b` is strictly monotone on ℕ, `b j₀ ≥ j₀ = 4d₂²`
    directly (no least-index search needed); `c := b j₀ + 1`.
  * shifted targets `t i := b i − k·c` for `i > j₀`; the ratio survives
    additively: `t (i+1) ≥ 192·d₂·t i` from `b (i+1) ≥ 192·d₂·b i`.
  * the interval chain is a plain `Nat.rec` over `ℝ × ℝ` whose step is a
    `dite` on the free-gap existential (`Exists.choose` on the then-branch);
    the invariant and the step relation are recovered by `dif_pos`.
  * `γ* := ⨆ j, lo j`; monotone `lo` / antitone `hi` sandwich it into every
    interval, hence `γ*` is safe for every target simultaneously.
-/

namespace Erdos1112
namespace Proof

set_option maxHeartbeats 3200000 in
/-- **Theorem 1** (existence half, explicit bound): for `d₂ ≥ k + 1` the ratio
`r = 192·d₂` works. Statement identical to the frozen target
`Erdos1112.erdos_1112_existence_bound`. -/
theorem existence_bound (k d₁ d₂ : ℕ) (hk : 3 ≤ k) (hd₁ : 1 ≤ d₁)
    (hd : d₁ < d₂) (h : k + 1 ≤ d₂) :
    RatioWorks k d₁ d₂ (192 * d₂) := by
  classical
  intro b hb
  obtain ⟨hb0, hbmono, hbrat⟩ := hb
  have hd₂2 : 2 ≤ d₂ := by omega
  have hk0 : 0 < k := by omega
  -- (1.3): the offset
  set j₀ : ℕ := 4 * d₂ ^ 2 with hj₀def
  have hbj₀ : 4 * d₂ ^ 2 ≤ b j₀ := le_trans (le_of_eq hj₀def.symm) hbmono.le_apply
  set c : ℕ := b j₀ + 1 with hcdef
  have hd₂bj₀ : d₂ ≤ b j₀ := by nlinarith
  have hkc : k * c ≤ 2 * d₂ * b j₀ := by
    have h1 : k ≤ d₂ := by omega
    have h2 : k * c ≤ d₂ * (b j₀ + 1) := Nat.mul_le_mul h1 (le_refl _)
    nlinarith
  -- every b i with i > j₀ clears k·c with big room
  have hkc_lt : ∀ i, j₀ + 1 ≤ i → k * c + 32 * d₂ ^ 2 ≤ b i := by
    intro i hi
    have h1 : 192 * d₂ * b j₀ ≤ b (j₀ + 1) := hbrat j₀
    have h2 : b (j₀ + 1) ≤ b i := hbmono.monotone hi
    nlinarith
  -- the shifted targets
  set t : ℕ → ℕ := fun i => b i - k * c with htdef
  have ht_cast : ∀ i, j₀ + 1 ≤ i → (t i : ℝ) = (b i : ℝ) - (k : ℝ) * c := by
    intro i hi
    have := hkc_lt i hi
    simp only [htdef]
    push_cast [Nat.cast_sub (by omega : k * c ≤ b i)]
    ring
  set T : ℕ → ℝ := fun m => (t (j₀ + 1 + m) : ℝ) with hTdef
  have hT32 : ∀ m, 32 * (d₂ : ℝ) ^ 2 ≤ T m := by
    intro m
    have h1 := hkc_lt (j₀ + 1 + m) (by omega)
    have h2 : (32 * d₂ ^ 2 : ℕ) ≤ t (j₀ + 1 + m) := by
      simp only [htdef]; omega
    calc 32 * (d₂ : ℝ) ^ 2 = ((32 * d₂ ^ 2 : ℕ) : ℝ) := by push_cast; ring
      _ ≤ T m := by simp only [hTdef]; exact_mod_cast h2
  have hT0 : ∀ m, (0 : ℝ) < T m := by
    intro m
    have h1 := hT32 m
    have h2 : (0 : ℝ) < 32 * (d₂ : ℝ) ^ 2 := by
      have : (2 : ℝ) ≤ (d₂ : ℝ) := by exact_mod_cast hd₂2
      nlinarith
    linarith
  -- one growth step of the targets
  have hTstep' : ∀ m, 192 * (d₂ : ℝ) * T m ≤ T (m + 1) := by
    intro m
    have hi : j₀ + 1 ≤ j₀ + 1 + m := by omega
    have hi' : j₀ + 1 ≤ j₀ + 1 + m + 1 := by omega
    have e1 : T m = (b (j₀ + 1 + m) : ℝ) - (k : ℝ) * c := ht_cast _ hi
    have e2 : T (m + 1) = (b (j₀ + 1 + m + 1) : ℝ) - (k : ℝ) * c := by
      have : j₀ + 1 + (m + 1) = j₀ + 1 + m + 1 := by omega
      simp only [hTdef, this]
      exact ht_cast _ hi'
    have hrat : (192 : ℝ) * d₂ * b (j₀ + 1 + m) ≤ b (j₀ + 1 + m + 1) := by
      exact_mod_cast hbrat (j₀ + 1 + m)
    have hkc0 : (0 : ℝ) ≤ (k : ℝ) * c := by positivity
    have hd₂1 : (1 : ℝ) ≤ 192 * (d₂ : ℝ) := by
      have : (2 : ℝ) ≤ (d₂ : ℝ) := by exact_mod_cast hd₂2
      linarith
    rw [e1, e2]
    nlinarith
  -- the division form used to thread the interval lengths
  have hTstep : ∀ m, 4 * (d₂ : ℝ) ^ 2 / T (m + 1) ≤ (d₂ : ℝ) / (48 * T m) := by
    intro m
    have hd₂R : (2 : ℝ) ≤ (d₂ : ℝ) := by exact_mod_cast hd₂2
    rw [div_le_iff₀ (hT0 (m + 1)), div_mul_eq_mul_div,
      le_div_iff₀ (by nlinarith [hT0 m] : (0 : ℝ) < 48 * T m)]
    have h1 := hTstep' m
    nlinarith [hT0 m, hT0 (m + 1)]
  -- the nested chain of safe intervals
  set Q : ℕ → ℝ × ℝ → ℝ × ℝ → Prop := fun m p p' =>
    p.1 ≤ p'.1 ∧ p'.2 ≤ p.2 ∧ (d₂ : ℝ) / (48 * T m) ≤ p'.2 - p'.1 ∧
      ∀ γ ∈ Set.Icc p'.1 p'.2, SafeFor k (T m) γ with hQdef
  set next : ℕ → ℝ × ℝ → ℝ × ℝ := fun m p =>
    if hE : ∃ p' : ℝ × ℝ, Q m p p' then hE.choose else p with hnextdef
  set chain : ℕ → ℝ × ℝ := fun j =>
    Nat.rec ((d₂ : ℝ) - 1 / 2, (d₂ : ℝ) - 1 / 4) next j with hchaindef
  have hchainS : ∀ j, chain (j + 1) = next j (chain j) := fun _ => rfl
  have hchain0 : chain 0 = ((d₂ : ℝ) - 1 / 2, (d₂ : ℝ) - 1 / 4) := rfl
  have hd₂R : (2 : ℝ) ≤ (d₂ : ℝ) := by exact_mod_cast hd₂2
  -- the invariant, by induction
  have main : ∀ j, ((d₂ : ℝ) - 1 / 2 ≤ (chain j).1) ∧
      ((chain j).2 ≤ (d₂ : ℝ) - 1 / 4) ∧
      (4 * (d₂ : ℝ) ^ 2 / T j ≤ (chain j).2 - (chain j).1) := by
    intro j
    induction j with
    | zero =>
        rw [hchain0]
        refine ⟨le_refl _, le_refl _, ?_⟩
        rw [div_le_iff₀ (hT0 0)]
        have := hT32 0
        nlinarith
    | succ j ih =>
        have hE : ∃ p' : ℝ × ℝ, Q j (chain j) p' := by
          obtain ⟨lo', hi', h1, h2, h3, h4⟩ :=
            exists_safe_subinterval (by omega : 1 ≤ k) h (hT32 j) ih.1
              (by linarith [ih.2.1]) ih.2.2
          exact ⟨(lo', hi'), h1, h2, h3, h4⟩
        have hnext : chain (j + 1) = hE.choose := by
          rw [hchainS j]
          simp only [hnextdef]
          exact dif_pos hE
        have hQ := hE.choose_spec
        rw [← hnext] at hQ
        refine ⟨le_trans ih.1 hQ.1, le_trans hQ.2.1 ih.2.1, ?_⟩
        calc 4 * (d₂ : ℝ) ^ 2 / T (j + 1) ≤ (d₂ : ℝ) / (48 * T j) := hTstep j
          _ ≤ (chain (j + 1)).2 - (chain (j + 1)).1 := hQ.2.2.1
  -- the step relation (recomputed from the invariant)
  have hQstep : ∀ j, Q j (chain j) (chain (j + 1)) := by
    intro j
    have ih := main j
    have hE : ∃ p' : ℝ × ℝ, Q j (chain j) p' := by
      obtain ⟨lo', hi', h1, h2, h3, h4⟩ :=
        exists_safe_subinterval (by omega : 1 ≤ k) h (hT32 j) ih.1
          (by linarith [ih.2.1]) ih.2.2
      exact ⟨(lo', hi'), h1, h2, h3, h4⟩
    have hnext : chain (j + 1) = hE.choose := by
      rw [hchainS j]
      simp only [hnextdef]
      exact dif_pos hE
    rw [hnext]
    exact hE.choose_spec
  -- interval geometry: lo mono, hi anti, lo ≤ hi
  have lo_le_hi : ∀ j, (chain j).1 ≤ (chain j).2 := by
    intro j
    have h1 := (main j).2.2
    have h2 : (0 : ℝ) < 4 * (d₂ : ℝ) ^ 2 / T j := by
      apply div_pos (by nlinarith) (hT0 j)
    linarith
  have lo_mono : Monotone fun j => (chain j).1 :=
    monotone_nat_of_le_succ fun j => (hQstep j).1
  have hi_anti : Antitone fun j => (chain j).2 :=
    antitone_nat_of_succ_le fun j => (hQstep j).2.1
  -- the common slope γ*
  have hbdd : BddAbove (Set.range fun j => (chain j).1) := by
    refine ⟨(d₂ : ℝ) - 1 / 4, ?_⟩
    rintro x ⟨j, rfl⟩
    exact le_trans (lo_le_hi j) (main j).2.1
  set γ' : ℝ := ⨆ j, (chain j).1 with hγdef
  have hγlo : ∀ j, (chain j).1 ≤ γ' := fun j => le_ciSup hbdd j
  have hγhi : ∀ j, γ' ≤ (chain j).2 := by
    intro j
    apply ciSup_le
    intro m
    rcases le_total m j with hmj | hjm
    · exact le_trans (lo_mono hmj) (lo_le_hi j)
    · exact le_trans (lo_le_hi m) (hi_anti hjm)
  have hγ_ge : (d₂ : ℝ) - 1 / 2 ≤ γ' := by
    have := hγlo 0
    rw [hchain0] at this
    exact this
  have hγ_le : γ' ≤ (d₂ : ℝ) - 1 / 4 := by
    have := hγhi 0
    rw [hchain0] at this
    exact this
  have hγl : (d₂ : ℝ) - 1 < γ' := by linarith
  have hγu : γ' < (d₂ : ℝ) := by linarith
  have hγpos : (0 : ℝ) < γ' := by linarith
  -- γ* is safe for every target simultaneously
  have hγsafe : ∀ m, SafeFor k (T m) γ' :=
    fun m => (hQstep m).2.2.2 γ' ⟨hγlo (m + 1), hγhi (m + 1)⟩
  -- assembly
  have hgaps : HasGapsIn d₁ d₂ (beatty γ' c) := beatty_hasGapsIn hd₁ hd hγl hγu
  refine ⟨beatty γ' c, hgaps, disjoint_range_iff.mpr ?_⟩
  intro n hn i
  rcases Nat.lt_or_ge i (j₀ + 1) with hi | hi
  · -- small elements of B sit below min kA
    obtain ⟨f, rfl⟩ := hn
    have ha0 : c + 1 ≤ beatty γ' c 0 := by
      have h1 : (1 : ℤ) ≤ ⌊(((0 : ℕ) : ℝ) + 1) * γ'⌋ := by
        apply Int.le_floor.mpr
        push_cast
        nlinarith
      unfold beatty
      omega
    have hsum : k * beatty γ' c 0 ≤ ∑ j, beatty γ' c (f j) := by
      calc k * beatty γ' c 0 = ∑ _j : Fin k, beatty γ' c 0 := by
            simp [Finset.sum_const]
        _ ≤ ∑ j, beatty γ' c (f j) :=
            Finset.sum_le_sum fun j _ => hgaps.monotone (Nat.zero_le _)
    have hX : beatty γ' c 0 ≤ k * beatty γ' c 0 :=
      Nat.le_mul_of_pos_left _ hk0
    have hbi : b i ≤ b j₀ := hbmono.monotone (by omega)
    omega
  · -- large elements of B are dodged by the safe slope
    intro heq
    set m : ℕ := i - (j₀ + 1) with hmdef
    have him : j₀ + 1 + m = i := by omega
    have hTi : T m = (b i : ℝ) - (k : ℝ) * c := by
      simp only [hTdef, him]
      exact ht_cast i hi
    have hsafe : SafeFor k ((b i : ℝ) - (k : ℝ) * c) γ' := by
      rw [← hTi]; exact hγsafe m
    exact beatty_avoids hk0 hγpos hsafe (heq ▸ hn)

end Proof
end Erdos1112


/-! Flattened from Erdos1112Proof.NonEx.TailCovering. -/
/-
The tail-covering property — `kA` eventually contains a full
congruence class. Paper: the paper's notation subsection and
the paper's non-existence section.
-/

namespace Erdos1112
namespace Proof

/-- `kA` contains a full congruence-class tail: there are `m ≥ 1`, a *reduced*
residue `ρ < m` (so the class is genuinely infinite), and `X₀` with
`{x ≥ X₀ : x ≡ ρ (mod m)} ⊆ kFoldSumset k a`.

The requirement `ρ < m` is essential: without it the degenerate residue
`ρ = m` covers the empty class and makes the property vacuously true, so the
notion would carry no information. -/
def TailCovering (k : ℕ) (a : ℕ → ℕ) : Prop :=
  ∃ m, 0 < m ∧ ∃ ρ, ρ < m ∧ ∃ X₀, ∀ x, X₀ ≤ x → x % m = ρ → x ∈ kFoldSumset k a

/-- Tail-covering with modulus 1 from "contains all large integers". -/
lemma TailCovering.of_cofinite {k : ℕ} {a : ℕ → ℕ}
    (h : ∃ X₀, ∀ x, X₀ ≤ x → x ∈ kFoldSumset k a) : TailCovering k a := by
  obtain ⟨X₀, hX⟩ := h
  exact ⟨1, one_pos, 0, one_pos, X₀, fun x hx _ => hX x hx⟩

end Proof
end Erdos1112


/-! Flattened from Erdos1112Proof.NonEx.Kit. -/
/-
Shared toolkit for the non-existence "easy half" files (`NonEx/Certificate.lean`,
`NonEx/GapWord.lean`, `NonEx/TwoLetter/Core.lean`, `NonEx/SlotLemma.lean`).

`TailCoveringN` is the normalized tail-covering notion (reduced residue
`ρ < m`, so the covered congruence class is genuinely infinite). It is the
form produced by all non-existence case lemmas and consumed by the certificate lemma (the
certificate). It coincides definitionally with `TailCovering`, which also
requires `ρ < m`.
-/

namespace Erdos1112
namespace Proof

/-- Normalized tail-covering: `kA` contains the full congruence-class tail
`{x ≥ X₀ : x ≡ ρ (mod m)}` with a *reduced* residue `ρ < m` (so the class is
genuinely infinite). This is the notion produced by all non-existence case lemmas
and consumed by the certificate lemma. -/
def TailCoveringN (k : ℕ) (a : ℕ → ℕ) : Prop :=
  ∃ m, 0 < m ∧ ∃ ρ, ρ < m ∧ ∃ X₀, ∀ x, X₀ ≤ x → x % m = ρ → x ∈ kFoldSumset k a

/-- Normalized tail-covering coincides with `TailCovering` (both require
`ρ < m`; the two notions are definitionally identical, and this bridge is
the identity repackaging). -/
lemma TailCoveringN.toTailCovering {k : ℕ} {a : ℕ → ℕ} (h : TailCoveringN k a) :
    TailCovering k a := by
  obtain ⟨m, hm, ρ, hρ, X₀, hX⟩ := h
  exact ⟨m, hm, ρ, hρ, X₀, hX⟩

/-! ### `kFoldSumset` composition -/

/-- The empty sum. -/
lemma zero_mem_kFoldSumset_zero {a : ℕ → ℕ} : 0 ∈ kFoldSumset 0 a :=
  ⟨Fin.elim0, by simp⟩

/-- A single summand. -/
lemma single_mem_kFoldSumset {a : ℕ → ℕ} (i : ℕ) : a i ∈ kFoldSumset 1 a :=
  ⟨fun _ => i, by simp⟩

/-- Sums compose: `k₁A + k₂A ⊆ (k₁+k₂)A`. -/
lemma add_mem_kFoldSumset {k₁ k₂ : ℕ} {a : ℕ → ℕ} {u v : ℕ}
    (hu : u ∈ kFoldSumset k₁ a) (hv : v ∈ kFoldSumset k₂ a) :
    u + v ∈ kFoldSumset (k₁ + k₂) a := by
  obtain ⟨f, rfl⟩ := hu
  obtain ⟨g, rfl⟩ := hv
  refine ⟨Fin.append f g, ?_⟩
  rw [Fin.sum_univ_add]
  congr 1
  · exact Finset.sum_congr rfl fun j _ => by rw [Fin.append_left]
  · exact Finset.sum_congr rfl fun j _ => by rw [Fin.append_right]

/-! ### Sums over a one-point update -/

/-- Updating one coordinate of a `Fin k`-indexed sum, additively phrased
(no `ℕ`-subtraction): the per-index summand family `H` may depend on the
index. -/
lemma sum_update_add {k : ℕ} (H : Fin k → ℕ → ℕ) (f : Fin k → ℕ)
    (j₀ : Fin k) (c : ℕ) :
    (∑ j, H j (Function.update f j₀ c j)) + H j₀ (f j₀) =
      H j₀ c + ∑ j, H j (f j) := by
  have h1 : ∀ j, H j (Function.update f j₀ c j) =
      Function.update (fun j => H j (f j)) j₀ (H j₀ c) j :=
    fun j => Function.apply_update (fun i v => H i v) f j₀ c j
  rw [Finset.sum_congr rfl fun j _ => h1 j,
    Finset.sum_update_of_mem (Finset.mem_univ j₀),
    Finset.sdiff_singleton_eq_erase,
    ← Finset.sum_erase_add Finset.univ (fun j => H j (f j))
      (Finset.mem_univ j₀)]
  omega

/-! ### The AP covering constructor -/

/-- If some subsequence of `a` is the arithmetic progression `c + s·j`
(`j ≥ 0`), then `kA ⊇ {k·c + s·j : j ≥ 0}`. -/
lemma kfold_AP_mem {k c s : ℕ} {a : ℕ → ℕ} (hk : 0 < k) (g : ℕ → ℕ)
    (hg : ∀ j, a (g j) = c + s * j) (j : ℕ) :
    k * c + s * j ∈ kFoldSumset k a := by
  refine ⟨Function.update (fun _ => g 0) ⟨0, hk⟩ (g j), ?_⟩
  have h := sum_update_add (fun (_ : Fin k) v => a v) (fun _ => g 0) ⟨0, hk⟩ (g j)
  have hsum : (∑ _t : Fin k, a (g 0)) = k * a (g 0) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have h0 : a (g 0) = c := by have := hg 0; omega
  have hj : a (g j) = c + s * j := hg j
  have hka : k * a (g 0) = k * c := by rw [h0]
  omega

/-- The AP `{k·c + s·j : j ≥ 0} ⊆ kA` (`s ≥ 1`) gives normalized
tail-covering with modulus `s`. -/
lemma tailCoveringN_of_AP {k s c : ℕ} {a : ℕ → ℕ} (hs : 0 < s)
    (hmem : ∀ j, k * c + s * j ∈ kFoldSumset k a) : TailCoveringN k a := by
  refine ⟨s, hs, (k * c) % s, Nat.mod_lt _ hs, k * c, fun x hx hmod => ?_⟩
  have hdvd : s ∣ x - k * c :=
    (Nat.modEq_iff_dvd' hx).mp (show Nat.ModEq s (k * c) x from hmod.symm)
  obtain ⟨j, hj⟩ := hdvd
  have hx' : x = k * c + s * j := by omega
  rw [hx']
  exact hmem j

/-! ### Residue selection in a window (used by the sweep) -/

/-- For coprime `δ, e` (`e ≥ 1`), every window of `e` consecutive integers
contains an `s` with `δ·s ≡ y (mod e)`. -/
lemma exists_mul_mod_eq {δ e : ℕ} (he : 0 < e) (hco : Nat.Coprime δ e)
    (y lo : ℕ) : ∃ s, lo ≤ s ∧ s < lo + e ∧ δ * s % e = y % e := by
  haveI : NeZero e := ⟨he.ne'⟩
  have hu : IsUnit (δ : ZMod e) := (ZMod.isUnit_iff_coprime δ e).mpr hco
  set w : ZMod e := (δ : ZMod e)⁻¹ * (y : ZMod e) with hw
  set t := (w - (lo : ZMod e)).val with ht
  have htlt : t < e := ZMod.val_lt _
  refine ⟨lo + t, Nat.le_add_right _ _, by omega, ?_⟩
  have h1 : ((lo + t : ℕ) : ZMod e) = w := by
    push_cast [ht]
    rw [ZMod.natCast_val, ZMod.cast_id]
    ring
  have h2 : (δ : ZMod e) * w = (y : ZMod e) := by
    rw [hw, ← mul_assoc, ZMod.mul_inv_of_unit _ hu, one_mul]
  have h3 : ((δ * (lo + t) : ℕ) : ZMod e) = ((y : ℕ) : ZMod e) := by
    push_cast
    push_cast at h1
    rw [h1]
    exact_mod_cast h2
  exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp h3

end Proof
end Erdos1112


/-! Flattened from Erdos1112Proof.NonEx.Certificate. -/
/-
The diagonal certificate lemma. Given any ratio sequence `R`,
a single `B` (hitting every congruence class at arbitrarily large heights,
while growing as fast as `R` demands) defeats every tail-covering `A`.
Paper: the non-existence section.

`hall` supplies the normalized covering `TailCoveringN` (reduced residue
`ρ < m`; `NonEx/Kit.lean`), the form exported by every non-existence case lemma.
-/

namespace Erdos1112
namespace Proof

/-! ### The enumeration of congruence classes

`certPair i = (m, ρ)` with `m ≥ 1`, `ρ < m`, hitting every such pair at
arbitrarily large indices `i` (the outer `Nat.pair` coordinate is free). -/

/-- Modulus component of the class enumeration. -/
def certM (i : ℕ) : ℕ := (Nat.unpair (Nat.unpair i).1).1 + 1

/-- Residue component of the class enumeration (reduced mod `certM`). -/
def certR (i : ℕ) : ℕ := (Nat.unpair (Nat.unpair i).1).2 % certM i

lemma certM_pos (i : ℕ) : 0 < certM i := Nat.succ_pos _

lemma certR_lt (i : ℕ) : certR i < certM i := Nat.mod_lt _ (certM_pos i)

/-- Every reduced class `(m, ρ)` recurs at indices beyond any bound. -/
lemma cert_hit (m ρ N : ℕ) (hρ : ρ < m) :
    ∃ i, N ≤ i ∧ certM i = m ∧ certR i = ρ := by
  refine ⟨Nat.pair (Nat.pair (m - 1) ρ) N, Nat.right_le_pair _ _, ?_, ?_⟩
  · show (Nat.unpair (Nat.unpair _).1).1 + 1 = m
    rw [Nat.unpair_pair, Nat.unpair_pair]
    omega
  · show (Nat.unpair (Nat.unpair _).1).2 % _ = ρ
    rw [certM, Nat.unpair_pair, Nat.unpair_pair]
    simp only
    have hm : m - 1 + 1 = m := by omega
    rw [hm, Nat.mod_eq_of_lt hρ]

/-! ### The diagonal sequence `B` -/

/-- Any reduced congruence class contains elements above any threshold. -/
lemma exists_in_class (m ρ t : ℕ) (hρ : ρ < m) :
    ∃ x, t < x ∧ x % m = ρ := by
  refine ⟨ρ + m * (t + 1), ?_, ?_⟩
  · have h1 : t + 1 ≤ m * (t + 1) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hρ]

/-- The certificate sequence: `certB R i` is the least element of the class
`(certM i, certR i)` exceeding `max (R (i-1) · certB R (i-1))
(max (certB R (i-1)) i)` (and exceeding `0` at `i = 0`). -/
def certB (R : ℕ → ℕ) : ℕ → ℕ
  | 0 => Nat.find (exists_in_class (certM 0) (certR 0) 0 (certR_lt 0))
  | i + 1 => Nat.find (exists_in_class (certM (i + 1)) (certR (i + 1))
      (max (R i * certB R i) (max (certB R i) (i + 1))) (certR_lt (i + 1)))

lemma certB_zero_spec (R : ℕ → ℕ) :
    0 < certB R 0 ∧ certB R 0 % certM 0 = certR 0 :=
  Nat.find_spec (exists_in_class (certM 0) (certR 0) 0 (certR_lt 0))

lemma certB_succ_spec (R : ℕ → ℕ) (i : ℕ) :
    max (R i * certB R i) (max (certB R i) (i + 1)) < certB R (i + 1) ∧
      certB R (i + 1) % certM (i + 1) = certR (i + 1) :=
  Nat.find_spec (exists_in_class (certM (i + 1)) (certR (i + 1)) _ (certR_lt (i + 1)))

lemma certB_mod (R : ℕ → ℕ) (i : ℕ) : certB R i % certM i = certR i := by
  cases i with
  | zero => exact (certB_zero_spec R).2
  | succ i => exact (certB_succ_spec R i).2

lemma certB_ge (R : ℕ → ℕ) (i : ℕ) : i ≤ certB R i := by
  cases i with
  | zero => exact Nat.zero_le _
  | succ i =>
      have := (certB_succ_spec R i).1
      omega

lemma certB_lacunary (R : ℕ → ℕ) : IsVarLacunaryWith R (certB R) := by
  refine ⟨(certB_zero_spec R).1, strictMono_nat_of_lt_succ fun i => ?_, fun i => ?_⟩
  · have := (certB_succ_spec R i).1
    omega
  · have := (certB_succ_spec R i).1
    omega

/-- **the corresponding paper lemma (certificate).** If every `(d₁,d₂)`-sequence is tail-covering
(normalized form), then for every ratio sequence `R` there is a single
var-lacunary `B` meeting `kA` for every admissible `A`. The hypothesis uses
the normalized covering `TailCoveringN` (reduced residue `ρ < m`). -/
theorem strong_nonexistence_of_tailCovering (k d₁ d₂ : ℕ) (R : ℕ → ℕ)
    (hall : ∀ a : ℕ → ℕ, HasGapsIn d₁ d₂ a → TailCoveringN k a) :
    ∃ b : ℕ → ℕ, IsVarLacunaryWith R b ∧
      ∀ a : ℕ → ℕ, HasGapsIn d₁ d₂ a →
        ¬ Disjoint (kFoldSumset k a) (Set.range b) := by
  refine ⟨certB R, certB_lacunary R, fun a ha => ?_⟩
  obtain ⟨m, hm, ρ, hρ, X₀, hX⟩ := hall a ha
  obtain ⟨i, hiN, hiM, hiR⟩ := cert_hit m ρ X₀ hρ
  refine not_disjoint_of_mem (i := i) (hX (certB R i) ?_ ?_)
  · have := certB_ge R i
    omega
  · rw [← hiM, ← hiR]
    exact certB_mod R i

end Proof
end Erdos1112


/-! Flattened from Erdos1112Proof.NonEx.GapWord. -/
/-
The non-existence reductions: tail alphabet `G∞`, the tail index,
gcd rescaling, the one-letter case, and the eventually-periodic case.
Paper: the non-existence section.

Interface notes:
* `tailCovering_of_single_letter` and `tailCovering_of_eventually_periodic`
  require `hd₁ : 1 ≤ d₁`. Without it both statements are *false* (with
  `d₁ = 0` the sequence may be eventually constant — e.g. all gaps eventually
  `0` — making `kA` finite, while the hypotheses hold). `NonEx/Main.lean` has
  `hd₁` ambiently available.
* `tailCovering_of_rescaled` uses the additive shape
  `∀ n, a (T + n) = c + g * a' n` for an arbitrary offset `c`, which the
  caller realizes with e.g. `c := a T`, `a' n := (a (T+n) - a T) / g` (or any
  positive-base variant). Phrasing it additively avoids `ℕ`-subtraction
  truncation; no gap or positivity hypotheses on `a'` are needed.
* Each lemma is proved in normalized form (`tailCoveringN_*`, reduced residue
  `ρ < m`; see `NonEx/Kit.lean`) and then weakened to the `TailCovering`
  form under the original name.
-/

namespace Erdos1112
namespace Proof

/-- The tail alphabet of the gap word: values occurring infinitely often. -/
def tailAlphabet (a : ℕ → ℕ) : Set ℕ :=
  {d | ∀ N, ∃ n, N ≤ n ∧ gap a n = d}

section Reductions

variable {k d₁ d₂ : ℕ} {a : ℕ → ℕ}

/-- Tail-alphabet letters obey the gap bounds. -/
lemma mem_tailAlphabet_bounds (h : HasGapsIn d₁ d₂ a) {x : ℕ}
    (hx : x ∈ tailAlphabet a) : d₁ ≤ x ∧ x ≤ d₂ := by
  obtain ⟨n, -, rfl⟩ := hx 0
  exact ⟨h.le_gap n, h.gap_le n⟩

/-- Past some index, every gap value belongs to the tail alphabet
(the tail index; classical, uses finiteness of `[d₁, d₂]`). -/
theorem exists_tail_index (h : HasGapsIn d₁ d₂ a) :
    ∃ T, ∀ n, T ≤ n → gap a n ∈ tailAlphabet a := by
  classical
  have key : ∀ d, d ∉ tailAlphabet a → ∃ N, ∀ n, N ≤ n → gap a n ≠ d := by
    intro d hd
    simp only [tailAlphabet, Set.mem_setOf_eq, not_forall] at hd
    obtain ⟨N, hN⟩ := hd
    push_neg at hN
    exact ⟨N, hN⟩
  set F : ℕ → ℕ := fun d =>
    if hd : d ∈ tailAlphabet a then 0 else (key d hd).choose with hF
  refine ⟨(Finset.Icc d₁ d₂).sup F, fun n hn => ?_⟩
  by_contra hbad
  have hmem : gap a n ∈ Finset.Icc d₁ d₂ :=
    Finset.mem_Icc.mpr ⟨h.le_gap n, h.gap_le n⟩
  have hFn : F (gap a n) ≤ (Finset.Icc d₁ d₂).sup F := Finset.le_sup hmem
  have hFval : F (gap a n) = (key _ hbad).choose := by
    rw [hF]; simp [hbad]
  exact (key _ hbad).choose_spec n (by omega) rfl

/-- **One letter**, normalized form: a single-letter tail
alphabet gives an AP tail, hence tail-covering with `m = δ`. -/
theorem tailCoveringN_of_single_letter (hk : 0 < k) (hd₁ : 1 ≤ d₁)
    (h : HasGapsIn d₁ d₂ a) (hone : ∃ δ, tailAlphabet a = {δ}) :
    TailCoveringN k a := by
  obtain ⟨δ, hδ⟩ := hone
  obtain ⟨T, hT⟩ := exists_tail_index h
  have hgapT : ∀ n, T ≤ n → gap a n = δ := by
    intro n hn
    have := hT n hn
    rwa [hδ, Set.mem_singleton_iff] at this
  have hδpos : 0 < δ := by
    have h1 := hgapT T le_rfl
    have h2 := h.le_gap T
    omega
  have key : ∀ j, a (T + j) = a T + δ * j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        have h3 : T + (j + 1) = T + j + 1 := by omega
        rw [h3, h.succ_eq_add_gap (T + j), hgapT _ (Nat.le_add_right _ _), ih]
        ring
  exact tailCoveringN_of_AP hδpos fun j => kfold_AP_mem hk (fun j => T + j) key j

/-- **Eventually periodic**, normalized form: an eventually
periodic gap word gives tail-covering with `m = ` the period sum
(single-anchor shortcut: `k` copies from one AP). -/
theorem tailCoveringN_of_eventually_periodic (hk : 0 < k) (hd₁ : 1 ≤ d₁)
    (h : HasGapsIn d₁ d₂ a)
    (hper : ∃ p, 0 < p ∧ ∃ T, ∀ n, T ≤ n → gap a (n + p) = gap a n) :
    TailCoveringN k a := by
  obtain ⟨p, hp, T, hT⟩ := hper
  set s := ∑ i ∈ Finset.range p, gap a (T + i) with hs_def
  -- period sum is positive
  have hspos : 0 < s := by
    have h1 : p * d₁ ≤ s := by
      calc p * d₁ = ∑ _i ∈ Finset.range p, d₁ := by
            rw [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_comm]
        _ ≤ s := Finset.sum_le_sum fun i _ => h.le_gap (T + i)
    have h2 := Nat.mul_le_mul hp hd₁
    omega
  -- one-period block advance
  have block : ∀ n, a (n + p) = a n + ∑ i ∈ Finset.range p, gap a (n + i) := by
    intro n
    have h1 := (h.tail n).eq_add_sum_gaps p
    simp only [Nat.add_zero] at h1
    have h2 : ∀ i, gap (fun m => a (n + m)) i = gap a (n + i) := by
      intro i
      show a (n + (i + 1)) - a (n + i) = a (n + i + 1) - a (n + i)
      rw [← Nat.add_assoc]
    rwa [Finset.sum_congr rfl fun i _ => h2 i] at h1
  -- periodicity iterates
  have per_iter : ∀ j i, gap a (T + i + j * p) = gap a (T + i) := by
    intro j
    induction j with
    | zero => intro i; simp
    | succ j ih =>
        intro i
        have h1 : T + i + (j + 1) * p = (T + i + j * p) + p := by
          have : (j + 1) * p = j * p + p := by ring
          omega
        rw [h1, hT _ (by omega), ih i]
  -- the anchored AP
  have key : ∀ j, a (T + j * p) = a T + s * j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        have h1 : T + (j + 1) * p = (T + j * p) + p := by
          have : (j + 1) * p = j * p + p := by ring
          omega
        have h3 : ∑ i ∈ Finset.range p, gap a (T + j * p + i) = s := by
          rw [hs_def]
          refine Finset.sum_congr rfl fun i _ => ?_
          have h4 : T + j * p + i = T + i + j * p := by omega
          rw [h4, per_iter j i]
        rw [h1, block (T + j * p), h3, ih]
        ring
  exact tailCoveringN_of_AP hspos fun j => kfold_AP_mem hk (fun j => T + j * p) key j

/-- **the corresponding paper lemma (rescaling)**, normalized form, redesigned interface: if past
`T` the sequence is an affine image `a (T + n) = c + g · a' n` of some `a'`,
then normalized tail-covering transports from `a'` to `a` (class modulus
`g·m'`). No hypotheses on `a'` beyond the covering are needed. -/
theorem tailCoveringN_of_rescaled {k : ℕ} {a : ℕ → ℕ} (T g c : ℕ)
    (hg : 0 < g) (a' : ℕ → ℕ) (ha' : ∀ n, a (T + n) = c + g * a' n)
    (hcov : TailCoveringN k a') : TailCoveringN k a := by
  obtain ⟨m', hm', ρ', hρ', X₀', hX'⟩ := hcov
  have hgm : 0 < g * m' := Nat.mul_pos hg hm'
  refine ⟨g * m', hgm, (k * c + g * ρ') % (g * m'), Nat.mod_lt _ hgm,
    k * c + g * X₀' + g * ρ', fun x hx hmod => ?_⟩
  -- extract the class parameter
  have hle : k * c + g * ρ' ≤ x := by omega
  have hdvd : g * m' ∣ x - (k * c + g * ρ') :=
    (Nat.modEq_iff_dvd' hle).mp
      (show Nat.ModEq (g * m') (k * c + g * ρ') x from hmod.symm)
  obtain ⟨t, ht⟩ := hdvd
  have hxeq : x = k * c + g * ρ' + g * m' * t := by omega
  -- the rescaled target
  set y := ρ' + m' * t with hy
  have hy_mod : y % m' = ρ' := by
    rw [hy, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hρ']
  have hy_ge : X₀' ≤ y := by
    have h1 : g * X₀' ≤ g * m' * t := by omega
    have h2 : X₀' ≤ m' * t := by
      have h1' : g * X₀' ≤ g * (m' * t) := by rw [← mul_assoc]; exact h1
      exact Nat.le_of_mul_le_mul_left h1' hg
    omega
  obtain ⟨f, hf⟩ := hX' y hy_ge hy_mod
  -- push the witness through the affine map
  refine ⟨fun j => T + f j, ?_⟩
  have h1 : ∀ j : Fin k, a (T + f j) = c + g * a' (f j) := fun j => ha' (f j)
  rw [Finset.sum_congr rfl fun j _ => h1 j, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    ← Finset.mul_sum, ← hf]
  have hgy : g * y = g * ρ' + g * m' * t := by
    rw [hy, Nat.mul_add, ← mul_assoc]
  omega

/-! ### `TailCovering`-form wrappers -/

/-- **One letter**: a single-letter tail alphabet gives an AP
tail, hence tail-covering. (Requires `hd₁`; see the header note.) -/
theorem tailCovering_of_single_letter (hk : 0 < k) (hd₁ : 1 ≤ d₁)
    (h : HasGapsIn d₁ d₂ a) (hone : ∃ δ, tailAlphabet a = {δ}) :
    TailCovering k a :=
  (tailCoveringN_of_single_letter hk hd₁ h hone).toTailCovering

/-- **Eventually periodic**: an eventually periodic gap word
gives tail-covering. (Requires `hd₁`; see the header note.) -/
theorem tailCovering_of_eventually_periodic (hk : 0 < k) (hd₁ : 1 ≤ d₁)
    (h : HasGapsIn d₁ d₂ a)
    (hper : ∃ p, 0 < p ∧ ∃ T, ∀ n, T ≤ n → gap a (n + p) = gap a n) :
    TailCovering k a :=
  (tailCoveringN_of_eventually_periodic hk hd₁ h hper).toTailCovering

/-- **the corresponding paper lemma (rescaling)**: transport of tail-covering along
`a (T + ·) = c + g · a' ·`. (Additive interface; see the header note.) -/
theorem tailCovering_of_rescaled {k : ℕ} {a : ℕ → ℕ} (T g c : ℕ)
    (hg : 0 < g) (a' : ℕ → ℕ) (ha' : ∀ n, a (T + n) = c + g * a' n)
    (hcov : TailCoveringN k a') : TailCovering k a :=
  (tailCoveringN_of_rescaled T g c hg a' ha' hcov).toTailCovering

end Reductions

end Proof
end Erdos1112


/-! Flattened from Erdos1112Proof.SubsetSums. -/
/-
Multiset subset sums, the consecutive-run predicate, and Graham's growth lemma.

`Finset.subsetSum` in Mathlib is for finsets (distinct elements); the paper's
the subset-sum development works with multisets ("x copies of a, Y copies of b, Z copies of M"),
so we define the multiset version and mirror the API.
-/

namespace Erdos1112
namespace Proof

/-- All subset sums of a multiset of naturals (submultiset selections,
repetitions of the underlying elements allowed). -/
def subsetSums (S : Multiset ℕ) : Finset ℕ :=
  (S.powerset.map Multiset.sum).toFinset

lemma mem_subsetSums {S : Multiset ℕ} {n : ℕ} :
    n ∈ subsetSums S ↔ ∃ T ≤ S, T.sum = n := by
  simp [subsetSums, Multiset.mem_powerset, eq_comm]

lemma zero_mem_subsetSums (S : Multiset ℕ) : 0 ∈ subsetSums S :=
  mem_subsetSums.mpr ⟨0, S.zero_le, rfl⟩

lemma sum_mem_subsetSums (S : Multiset ℕ) : S.sum ∈ subsetSums S :=
  mem_subsetSums.mpr ⟨S, le_rfl, rfl⟩

@[simp] lemma subsetSums_zero : subsetSums 0 = {0} := by
  ext n
  simp [mem_subsetSums, eq_comm]

lemma subsetSums_mono {S S' : Multiset ℕ} (h : S ≤ S') :
    subsetSums S ⊆ subsetSums S' := by
  intro n hn
  obtain ⟨T, hT, rfl⟩ := mem_subsetSums.mp hn
  exact mem_subsetSums.mpr ⟨T, hT.trans h, rfl⟩

/-- Cons splits subset sums into "x unused" ∪ "x used". -/
lemma subsetSums_cons (x : ℕ) (S : Multiset ℕ) :
    subsetSums (x ::ₘ S) = subsetSums S ∪ (subsetSums S).image (x + ·) := by
  ext n
  simp only [Finset.mem_union, Finset.mem_image, mem_subsetSums]
  constructor
  · rintro ⟨T, hT, rfl⟩
    by_cases hx : x ∈ T
    · right
      refine ⟨(T.erase x).sum, ⟨T.erase x, ?_, rfl⟩, ?_⟩
      · exact Multiset.erase_le_iff_le_cons.mpr hT
      · rw [← Multiset.sum_cons, Multiset.cons_erase hx]
    · left
      refine ⟨T, ?_, rfl⟩
      rw [Multiset.le_iff_count]
      intro y
      have hy := Multiset.le_iff_count.mp hT y
      rcases eq_or_ne y x with rfl | hyx
      · simp [Multiset.count_eq_zero.mpr hx]
      · simpa [Multiset.count_cons_of_ne hyx] using hy
  · rintro (⟨T, hT, rfl⟩ | ⟨m, ⟨T, hT, rfl⟩, rfl⟩)
    · exact ⟨T, hT.trans (Multiset.le_cons_self S x), rfl⟩
    · exact ⟨x ::ₘ T, Multiset.cons_le_cons x hT, by simp⟩

/-- Sums from disjoint pools add. -/
lemma add_mem_subsetSums_add {S T : Multiset ℕ} {u v : ℕ}
    (hu : u ∈ subsetSums S) (hv : v ∈ subsetSums T) :
    u + v ∈ subsetSums (S + T) := by
  obtain ⟨U, hU, rfl⟩ := mem_subsetSums.mp hu
  obtain ⟨V, hV, rfl⟩ := mem_subsetSums.mp hv
  exact mem_subsetSums.mpr ⟨U + V, add_le_add hU hV, by simp⟩

/-- `T` contains `len` consecutive integers starting somewhere. -/
def HasRun (T : Finset ℕ) (len : ℕ) : Prop :=
  ∃ c, ∀ i < len, c + i ∈ T

lemma HasRun.mono {T T' : Finset ℕ} {len : ℕ} (hTT' : T ⊆ T') (h : HasRun T len) :
    HasRun T' len :=
  h.imp fun _c hc i hi => hTT' (hc i hi)

lemma HasRun.of_le {T : Finset ℕ} {len len' : ℕ} (hle : len' ≤ len)
    (h : HasRun T len) : HasRun T len' :=
  h.imp fun _c hc i hi => hc i (lt_of_lt_of_le hi hle)

/-- **Graham's growth lemma**: a run of length `ℓ` plus one fresh copy of
`g ≤ ℓ` extends to a run of length `ℓ + g`. -/
lemma HasRun.cons_of_le {S : Multiset ℕ} {ℓ g : ℕ} (hgl : g ≤ ℓ)
    (h : HasRun (subsetSums S) ℓ) : HasRun (subsetSums (g ::ₘ S)) (ℓ + g) := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, fun i hi => ?_⟩
  rw [subsetSums_cons]
  rcases lt_or_ge i ℓ with h' | h'
  · exact Finset.mem_union_left _ (hc i h')
  · refine Finset.mem_union_right _ ?_
    have hig : g ≤ i := hgl.trans h'
    have : c + i = g + (c + (i - g)) := by omega
    rw [this]
    exact Finset.mem_image_of_mem _ (hc (i - g) (by omega))

end Proof
end Erdos1112


/-! Flattened from Erdos1112Proof.NonEx.SlotLemmaParts. -/
/-
The slot lemma's `sharp`-independent sub-lemmas.

Split out of `SlotLemma.lean` so these five parts build without importing
`Sharp.Main` (only the final assembly `tailCovering_of_three_letters` needs
`sharp`). Paper: the non-existence section.
-/

namespace Erdos1112
namespace Proof

open scoped Classical

/-- A submultiset of a mapped multiset is the map of a submultiset. -/
private lemma le_map_exists {α β : Type*} {f : α → β} {t : Multiset β}
    {s : Multiset α} (h : t ≤ Multiset.map f s) :
    ∃ u, u ≤ s ∧ Multiset.map f u = t := by
  induction s using Multiset.induction generalizing t with
  | empty =>
      rw [Multiset.map_zero, Multiset.le_zero] at h
      exact ⟨0, le_rfl, by simp [h]⟩
  | cons a s ih =>
      rw [Multiset.map_cons] at h
      by_cases hmem : f a ∈ t
      · obtain ⟨t', rfl⟩ := Multiset.exists_cons_of_mem hmem
        have h' : t' ≤ Multiset.map f s := (Multiset.cons_le_cons_iff (f a)).mp h
        obtain ⟨u, hu, hmap⟩ := ih h'
        exact ⟨a ::ₘ u, Multiset.cons_le_cons a hu, by rw [Multiset.map_cons, hmap]⟩
      · have h' : t ≤ Multiset.map f s := by
          rw [Multiset.le_iff_count] at h ⊢
          intro b
          have hb := h b
          rw [Multiset.count_cons] at hb
          by_cases hbfa : b = f a
          · subst hbfa; rw [Multiset.count_eq_zero.mpr hmem]; exact Nat.zero_le _
          · rw [if_neg hbfa] at hb; exact hb
        obtain ⟨u, hu, hmap⟩ := ih h'
        exact ⟨u, le_trans hu (Multiset.le_cons_self s a), hmap⟩

/-- **Sub-lemma 1: subset sums ↔ index subsets.** A subset sum of the
indexed multiset `{δ t : t ∈ Fin m}` is realized by a Finset of indices. -/
theorem subsetSums_index {m : ℕ} (δ : Fin m → ℕ) {v : ℕ}
    (hv : v ∈ subsetSums (Multiset.map δ Finset.univ.val)) :
    ∃ T : Finset (Fin m), (∑ t ∈ T, δ t) = v := by
  rw [mem_subsetSums] at hv
  obtain ⟨T', hle, hsum⟩ := hv
  obtain ⟨u, hu, hmap⟩ := le_map_exists hle
  have hunod : u.Nodup := by
    rw [Multiset.nodup_iff_count_le_one]
    intro x
    have h1 := Multiset.le_iff_count.mp hu x
    have h2 := (Multiset.nodup_iff_count_le_one.mp Finset.univ.nodup) x
    omega
  refine ⟨u.toFinset, ?_⟩
  have hval : u.toFinset.val = u := by rw [Multiset.toFinset_val]; exact hunod.dedup
  change (Multiset.map δ u.toFinset.val).sum = v
  rw [hval, hmap]; exact hsum

/-- **Sub-lemma 2: slot positions.** Given target gap values each in the
tail alphabet, distinct positions past `N₀` realizing them (`gap a (p t) =
δ t`). Route: greedy selection using infinite occurrence, avoiding the finite
set of already-chosen positions. -/
theorem exists_slot_positions {a : ℕ → ℕ} {m : ℕ} (δ : Fin m → ℕ) (N₀ : ℕ)
    (hδ : ∀ t, δ t ∈ tailAlphabet a) :
    ∃ p : Fin m → ℕ, (∀ t, N₀ ≤ p t) ∧ Function.Injective p ∧
      (∀ t, gap a (p t) = δ t) := by
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    exact ⟨Fin.elim0, fun t => t.elim0, fun t => t.elim0, fun t => t.elim0⟩
  -- extend `δ` to `ℕ` (clamp the index); each value stays in the tail alphabet
  set δ' : ℕ → ℕ := fun t => δ ⟨min t (m - 1), by omega⟩ with hδ'def
  have hδ'tail : ∀ t : ℕ, ∀ B : ℕ, ∃ n, B ≤ n ∧ gap a n = δ' t := fun t B => hδ _ B
  -- greedy strictly-increasing positions `q t` with `gap a (q t) = δ' t`
  set q : ℕ → ℕ := fun t => Nat.rec
    ((hδ'tail 0 N₀).choose)
    (fun t qt => (hδ'tail (t + 1) (qt + 1)).choose) t with hqdef
  have hq0 : N₀ ≤ q 0 ∧ gap a (q 0) = δ' 0 := (hδ'tail 0 N₀).choose_spec
  have hqsucc : ∀ t, q t + 1 ≤ q (t + 1) ∧ gap a (q (t + 1)) = δ' (t + 1) :=
    fun t => (hδ'tail (t + 1) (q t + 1)).choose_spec
  have hqmono : StrictMono q := by
    apply strictMono_nat_of_lt_succ
    intro t; have := (hqsucc t).1; omega
  have hqN₀ : ∀ t, N₀ ≤ q t := by
    intro t
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · exact hq0.1
    · exact le_trans hq0.1 (hqmono.monotone (Nat.zero_le t))
  have hqgap : ∀ t, gap a (q t) = δ' t := by
    intro t
    cases t with
    | zero => exact hq0.2
    | succ t => exact (hqsucc t).2
  refine ⟨fun t => q t.val, fun t => hqN₀ _, ?_, fun t => ?_⟩
  · intro s t hst
    exact Fin.ext (hqmono.injective hst)
  · rw [hqgap]
    simp only [hδ'def, min_eq_left (Nat.le_sub_one_of_lt t.isLt), Fin.eta]

/-- **Sub-lemma 3: slot realization.** The `m` slots at positions `p`
(each toggled off/on = index `p t` / `p t + 1`) realize `∑ a(p t) +
(on-subset sum of the gaps)` as an `m`-fold sum. Route: the direct
`Fin m` config `t ↦ if t ∈ T then p t + 1 else p t`, with `a (p t + 1) =
a (p t) + gap a (p t)`. -/
theorem slot_realize {a : ℕ → ℕ} {m d₁ d₂ : ℕ} (hgaps : HasGapsIn d₁ d₂ a)
    (p : Fin m → ℕ) (T : Finset (Fin m)) :
    (∑ t, a (p t)) + (∑ t ∈ T, gap a (p t)) ∈ kFoldSumset m a := by
  have key : ∀ t : Fin m, a (if t ∈ T then p t + 1 else p t) =
      a (p t) + (if t ∈ T then gap a (p t) else 0) := by
    intro t
    by_cases ht : t ∈ T
    · rw [if_pos ht, if_pos ht, hgaps.succ_eq_add_gap]
    · rw [if_neg ht, if_neg ht, Nat.add_zero]
  refine ⟨fun t => if t ∈ T then p t + 1 else p t, ?_⟩
  symm
  calc ∑ t, a (if t ∈ T then p t + 1 else p t)
      = ∑ t, (a (p t) + if t ∈ T then gap a (p t) else 0) :=
        Finset.sum_congr rfl (fun t _ => key t)
    _ = (∑ t, a (p t)) + ∑ t, (if t ∈ T then gap a (p t) else 0) :=
        Finset.sum_add_distrib
    _ = (∑ t, a (p t)) + ∑ t ∈ T, gap a (p t) := by
        rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- **Sub-lemma 4: coarse dial.** A value family `base + a n + [c, c+M−1]`
(`n ≥ T₀`, all in `kA`) with `a` stepping by `≤ M` covers all large integers.
Route: `discrete_ivt` on `n ↦ a (T₀ + n)` into the window
`[x − base − c − (M−1), x − base − c]`, step `≤ M`, width `M−1`. -/
theorem slot_dial {a : ℕ → ℕ} {k M base c T₀ : ℕ} (hM : 0 < M)
    (hgrow : ∀ n, T₀ ≤ n → a n < a (n + 1))
    (hstep : ∀ n, T₀ ≤ n → a (n + 1) ≤ a n + M)
    (hmem : ∀ n v, T₀ ≤ n → c ≤ v → v ≤ c + (M - 1) →
      base + a n + v ∈ kFoldSumset k a) :
    ∃ X₀, ∀ x, X₀ ≤ x → x ∈ kFoldSumset k a := by
  refine ⟨base + a T₀ + c + M, fun x hx => ?_⟩
  -- lower bound: `a (T₀ + j) ≥ a T₀ + j`
  have hlb : ∀ j, a T₀ + j ≤ a (T₀ + j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        have := hgrow (T₀ + j) (Nat.le_add_right _ _)
        have he : T₀ + (j + 1) = (T₀ + j) + 1 := by omega
        rw [he]; omega
  -- discrete IVT on `f j = a (T₀ + j)` into `[x−base−c−(M−1), x−base−c]`
  have h0 : (a (T₀ + 0) : ℤ) ≤ (x : ℤ) - base - c - (M - 1) := by
    have : (a (T₀ + 0) : ℤ) = (a T₀ : ℤ) := by norm_num
    rw [this]; omega
  have hN : (x : ℤ) - base - c ≤ (a (T₀ + x) : ℤ) := by
    have h1 := hlb x; omega
  have hstep' : ∀ n, n < x → (a (T₀ + (n + 1)) : ℤ) - a (T₀ + n) ≤ M := by
    intro n _
    have he : T₀ + (n + 1) = (T₀ + n) + 1 := by omega
    have := hstep (T₀ + n) (Nat.le_add_right _ _)
    rw [he]; omega
  obtain ⟨j, _, hjlo, hjhi⟩ :=
    discrete_ivt (f := fun j => (a (T₀ + j) : ℤ)) (N := x) h0 hN (by omega)
      hstep' (by omega)
  -- decode: `n := T₀ + j`, `v := x − base − a n`
  set n := T₀ + j with hndef
  have hz1 : (a n : ℤ) ≤ (x : ℤ) - base - c := by simp only [hndef]; linarith
  have hz2 : (x : ℤ) - base - c - (M - 1) ≤ (a n : ℤ) := by simp only [hndef]; linarith
  have hxv : x = base + a n + (x - base - a n) := by omega
  rw [hxv]
  exact hmem n (x - base - a n) (by simp only [hndef]; omega) (by omega) (by omega)

/-- Finset gcd commutes with dividing out a common factor. (Copy of
`Sharp/Graham.lean`'s lemma — this file is Sharp-independent by design.) -/
private lemma gcd_image_div_aux {s : Finset ℕ} {c : ℕ}
    (h : ∀ x ∈ s, c ∣ x) : (s.image (· / c)).gcd id * c = s.gcd id := by
  induction s using Finset.induction with
  | empty => simp
  | insert x s hx ih =>
      rw [Finset.image_insert, Finset.gcd_insert, Finset.gcd_insert]
      have hcx : c ∣ x := h x (Finset.mem_insert_self _ _)
      have ih' := ih fun y hy => h y (Finset.mem_insert_of_mem hy)
      simp only [id_eq]
      rw [← ih']
      show Nat.gcd (x / c) ((Finset.image (· / c) s).gcd id) * c =
        Nat.gcd x ((Finset.image (· / c) s).gcd id * c)
      rw [← Nat.gcd_mul_right, Nat.div_mul_cancel hcx]

/-- **Sub-lemma 5: gcd rescaling.** If the tail alphabet has gcd `g`, the
tail is `a (T+n) = c + g·a' n` for a sequence `a'` whose tail alphabet is the
`/g` rescale (gcd 1), with the same ≥ 3-letter and `≤ d₂` structure. Route:
`a' n := (a (T+n) − a T)/g`; gaps divide by `g` (all tail gaps ≡ 0 mod g);
consumed by `tailCoveringN_of_rescaled`. -/
theorem exists_rescale {a : ℕ → ℕ} {d₁ d₂ : ℕ} (hd₁ : 1 ≤ d₁)
    (hgaps : HasGapsIn d₁ d₂ a)
    (h3 : ∃ x y z : ℕ, x ∈ tailAlphabet a ∧ y ∈ tailAlphabet a ∧
      z ∈ tailAlphabet a ∧ x < y ∧ y < z) :
    ∃ (a' : ℕ → ℕ) (T g c : ℕ), 0 < g ∧ (∀ n, a (T + n) = c + g * a' n) ∧
      (∃ x y z : ℕ, x ∈ tailAlphabet a' ∧ y ∈ tailAlphabet a' ∧
        z ∈ tailAlphabet a' ∧ x < y ∧ y < z) ∧
      ((Finset.Icc 1 d₂).filter (· ∈ tailAlphabet a')).gcd id = 1 := by
  classical
  -- tail index `T` past which every gap is a tail-alphabet letter
  obtain ⟨T, hT⟩ := exists_tail_index hgaps
  -- the tail alphabet as a Finset `G ⊆ [d₁, d₂]`, and `g := gcd G`
  set G : Finset ℕ := (Finset.Icc d₁ d₂).filter (· ∈ tailAlphabet a) with hGdef
  have hmemG : ∀ x, x ∈ tailAlphabet a → x ∈ G := by
    intro x hx
    rw [hGdef, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨mem_tailAlphabet_bounds hgaps hx, hx⟩
  set g : ℕ := G.gcd id with hgdef
  -- `g > 0` (G nonempty via `h3`, elements ≥ d₁ ≥ 1).
  have hg0 : 0 < g := by
    obtain ⟨x, _, _, hx, _, _, _, _⟩ := h3
    have hxd : d₁ ≤ x := (mem_tailAlphabet_bounds hgaps hx).1
    have hgx : g ∣ x := hgdef ▸ Finset.gcd_dvd (hmemG x hx)
    rcases Nat.eq_zero_or_pos g with h0 | h0
    · rw [h0] at hgx; rw [Nat.zero_dvd] at hgx; omega
    · exact h0
  -- every tail gap is divisible by `g`
  have hgdvd : ∀ n, T ≤ n → g ∣ gap a n := by
    intro n hn
    exact hgdef ▸ Finset.gcd_dvd (hmemG _ (hT n hn))
  -- `a (T+n) − a T` is a `g`-multiple (telescoping sum of tail gaps).
  have hdvd_a : ∀ n, g ∣ (a (T + n) - a T) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have he : T + (n + 1) = (T + n) + 1 := by omega
        have hmono : a T ≤ a (T + n) := hgaps.monotone (by omega)
        have hstep : a (T + (n + 1)) - a T = (a (T + n) - a T) + gap a (T + n) := by
          rw [he, hgaps.succ_eq_add_gap]; omega
        rw [hstep]
        exact Nat.dvd_add ih (hgdvd (T + n) (Nat.le_add_right _ _))
  -- the rescaled sequence and offset
  set a' : ℕ → ℕ := fun n => (a (T + n) - a T) / g with ha'def
  set c : ℕ := a T with hcdef
  have haffine : ∀ n, a (T + n) = c + g * a' n := by
    intro n
    have hle : a T ≤ a (T + n) := hgaps.monotone (Nat.le_add_right _ _)
    rw [ha'def, hcdef, Nat.mul_div_cancel' (hdvd_a n)]
    omega
  -- `gap a' n = gap a (T+n) / g`
  have hgap' : ∀ n, gap a' n = gap a (T + n) / g := by
    intro n
    obtain ⟨X', hX'⟩ := hdvd_a (n + 1)
    obtain ⟨Y', hY'⟩ := hdvd_a n
    have hmono2 : a (T + n) ≤ a (T + (n + 1)) := hgaps.monotone (by omega)
    have haX : a' (n + 1) = X' := by
      show (a (T + (n + 1)) - a T) / g = X'
      rw [hX', Nat.mul_div_cancel_left _ hg0]
    have haY : a' n = Y' := by
      show (a (T + n) - a T) / g = Y'
      rw [hY', Nat.mul_div_cancel_left _ hg0]
    have hYX : Y' ≤ X' := Nat.le_of_mul_le_mul_left (by omega) hg0
    have hmono0 : a T ≤ a (T + n) := hgaps.monotone (by omega)
    have hgapval : gap a (T + n) = g * (X' - Y') := by
      show a (T + n + 1) - a (T + n) = g * (X' - Y')
      have h1 : a (T + n + 1) = a (T + (n + 1)) := by rw [Nat.add_assoc]
      rw [Nat.mul_sub, ← hX', ← hY', h1]; omega
    show a' (n + 1) - a' n = gap a (T + n) / g
    rw [haX, haY, hgapval, Nat.mul_div_cancel_left _ hg0]
  -- a-tail letters push forward to a'-tail letters under `/g`
  have htail' : ∀ w, w ∈ tailAlphabet a → w / g ∈ tailAlphabet a' := by
    intro w hw N
    obtain ⟨n, hn, hgn⟩ := hw (N + T)
    refine ⟨n - T, by omega, ?_⟩
    have he : T + (n - T) = n := by omega
    rw [hgap' (n - T), he, hgn]
  -- and pull back: an a'-tail letter `v` has `g·v` an a-tail letter
  have htail_rev : ∀ v, v ∈ tailAlphabet a' → g * v ∈ tailAlphabet a := by
    intro v hv N
    obtain ⟨n, hn, hgn⟩ := hv N
    refine ⟨T + n, by omega, ?_⟩
    have hd := hgdvd (T + n) (Nat.le_add_right _ _)
    have hvv : v = gap a (T + n) / g := by rw [← hgap' n, hgn]
    rw [hvv, Nat.mul_div_cancel' hd]
  refine ⟨a', T, g, c, hg0, haffine, ?_, ?_⟩
  · -- ≥ 3 tail letters of `a'`: the `/g` images of `h3`'s letters
    obtain ⟨x, y, z, hx, hy, hz, hxy, hyz⟩ := h3
    have hgy : g ∣ y := hgdef ▸ Finset.gcd_dvd (hmemG y hy)
    have hgz : g ∣ z := hgdef ▸ Finset.gcd_dvd (hmemG z hz)
    exact ⟨x / g, y / g, z / g, htail' x hx, htail' y hy, htail' z hz,
      Nat.div_lt_div_of_lt_of_dvd hgy hxy, Nat.div_lt_div_of_lt_of_dvd hgz hyz⟩
  · -- gcd of the rescaled alphabet `= gcd G / g = 1`
    have hG'eq : (Finset.Icc 1 d₂).filter (· ∈ tailAlphabet a') = G.image (· / g) := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image, hGdef]
      constructor
      · rintro ⟨-, hvtail⟩
        refine ⟨g * v, ?_, ?_⟩
        · exact ⟨mem_tailAlphabet_bounds hgaps (htail_rev v hvtail), htail_rev v hvtail⟩
        · rw [Nat.mul_div_cancel_left _ hg0]
      · rintro ⟨w, hw, rfl⟩
        obtain ⟨⟨hw1, hw2⟩, hwtail⟩ := hw
        have hgw : g ∣ w := hgdef ▸ Finset.gcd_dvd (hmemG w hwtail)
        refine ⟨⟨?_, ?_⟩, htail' w hwtail⟩
        · exact Nat.one_le_div_iff hg0 |>.mpr (Nat.le_of_dvd (by omega) hgw)
        · exact le_trans (Nat.div_le_self _ _) hw2
    rw [hG'eq]
    have hkey := gcd_image_div_aux (s := G) (c := g) (fun w hw => hgdef ▸ Finset.gcd_dvd hw)
    rw [← hgdef] at hkey
    have h2 : (G.image (· / g)).gcd id * g = 1 * g := by rw [hkey, one_mul]
    exact Nat.eq_of_mul_eq_mul_right hg0 h2

end Proof
end Erdos1112


/-! Flattened from Erdos1112Proof.Sharp.Defs. -/
/-
Statement forms for the bounded subset-sum covering lemma and the hard core.
Paper: the bounded subset-sum covering section.
-/

namespace Erdos1112
namespace Proof

/-- (SHARP) for the triple alphabet `{a, b, M}`: some multiset of at most
`M − 1` elements drawn from `{a,b,M}` has subset sums containing `M`
consecutive integers. -/
def SharpTriple (a b M : ℕ) : Prop :=
  ∃ S : Multiset ℕ, (∀ x ∈ S, x = a ∨ x = b ∨ x = M) ∧
    S.card ≤ M - 1 ∧ HasRun (subsetSums S) M

/-- (SHARP) at maximum `M`, for all alphabets: every finite `G` of at least
three positive integers with `gcd G = 1` and maximum `M` admits a multiset of
at most `M−1` of its elements whose subset sums contain `M` consecutive
integers. (`max` is encoded as `M ∈ G ∧ ∀ g ∈ G, g ≤ M`.) -/
def SharpAt (M : ℕ) : Prop :=
  ∀ G : Finset ℕ, (∀ g ∈ G, 0 < g) → 3 ≤ G.card → G.gcd id = 1 →
    (∀ g ∈ G, g ≤ M) → M ∈ G →
    ∃ S : Multiset ℕ, (∀ x ∈ S, x ∈ G) ∧ S.card ≤ M - 1 ∧
      HasRun (subsetSums S) M

/-- The hard core (paper the subset-sum section, "The hard core"): `G = {a, b, M}` with
`gcd(a,b) = 1` and `δ := a + b − M ≥ 2`. Everything else about the shape
(`3 ≤ a`, `h := M − b ∈ [1, a−2]`, `gcd(a,e) = 1` for `e := b − a`, …)
is derived. -/
def HardCore (a b M : ℕ) : Prop :=
  0 < a ∧ a < b ∧ b < M ∧ Nat.Coprime a b ∧ M + 2 ≤ a + b

namespace HardCore

variable {a b M : ℕ}

/-- In the hard core, `a ≥ 3` (from `M + 2 ≤ a + b` and `b < M` alone). -/
lemma three_le (h : HardCore a b M) : 3 ≤ a := by
  obtain ⟨-, -, hbM, -, hδ⟩ := h
  omega

/-- In the hard core, `h := M − b` satisfies `1 ≤ h ≤ a − 2`. -/
lemma h_bounds (h : HardCore a b M) : 1 ≤ M - b ∧ M - b ≤ a - 2 := by
  obtain ⟨-, -, hbM, -, hδ⟩ := h
  omega

/-- In the hard core, `gcd(a, e) = 1` for the letter difference `e = b − a`. -/
lemma coprime_a_e (h : HardCore a b M) : Nat.Coprime a (b - a) := by
  obtain ⟨-, hab, -, hco, -⟩ := h
  have h1 : Nat.gcd a (b - a) ∣ a := Nat.gcd_dvd_left _ _
  have h2 : Nat.gcd a (b - a) ∣ b - a := Nat.gcd_dvd_right _ _
  have h3 : Nat.gcd a (b - a) ∣ b := by
    have h5 : Nat.gcd a (b - a) ∣ b - a + a := Nat.dvd_add h2 h1
    rwa [Nat.sub_add_cancel (le_of_lt hab)] at h5
  have h4 : Nat.gcd a (b - a) ∣ Nat.gcd a b := Nat.dvd_gcd h1 h3
  rw [hco] at h4
  exact Nat.dvd_one.mp h4

end HardCore

/-- A `SharpTriple` witnesses `SharpAt`-style membership for `G = {a,b,M}`. -/
lemma SharpTriple.mem_insert {a b M : ℕ} (h : SharpTriple a b M) :
    ∃ S : Multiset ℕ, (∀ x ∈ S, x ∈ ({a, b, M} : Finset ℕ)) ∧
      S.card ≤ M - 1 ∧ HasRun (subsetSums S) M := by
  obtain ⟨S, hS, hc, hr⟩ := h
  exact ⟨S, fun x hx => by rcases hS x hx with rfl | rfl | rfl <;> simp, hc, hr⟩

end Proof
end Erdos1112


/-! Flattened from Erdos1112Proof.Sharp.TwoGen. -/
/-
the two-generator lemma: the boxed two-generator interval. Chicken McNugget with
multiplicity bounds. Paper: the bounded subset-sum covering section.

Route: for `α ≥ 2` the base case `y = α − 1` uses Mathlib's
`frobeniusNumber_pair` (classical Chicken McNugget: `n ∉ closure {α,β}` forces
`n ≤ αβ−α−β`, so every `n ≥ C := (α−1)(β−1) = αβ−α−β+1` is representable),
followed by normalizing `j` modulo `α` (moving `β·α`-blocks into `i`), which
forces `i ≤ x` inside the base window. The step `y → y+1` peels one `β` per
the paper. `α = 1` is direct (`j := min y (n/β)`).
-/

namespace Erdos1112
namespace Proof

set_option maxHeartbeats 1600000 in
/-- **the two-generator lemma (two-generator interval).** For coprime `α < β`, `x ≥ β − 1`,
`y ≥ α − 1`: every `n` in `[C, αx + βy − C]` with `C = (α−1)(β−1)` is
`iα + jβ` with `i ≤ x`, `j ≤ y`. -/
theorem twoGen_interval {α β x y : ℕ} (hαβ : α < β) (hα : 0 < α)
    (hco : Nat.Coprime α β) (hx : β - 1 ≤ x) (hy : α - 1 ≤ y) :
    ∀ n, (α - 1) * (β - 1) ≤ n → n + (α - 1) * (β - 1) ≤ α * x + β * y →
      ∃ i j, i ≤ x ∧ j ≤ y ∧ n = i * α + j * β := by
  have hβ0 : 0 < β := lt_trans hα hαβ
  rcases Nat.lt_or_ge α 2 with hα1 | hα2
  · -- α = 1: C = 0; take j := min y (n/β), i := n − jβ
    have hα1' : α = 1 := by omega
    subst hα1'
    intro n _hnlo hnhi
    simp only [Nat.sub_self, Nat.zero_mul, Nat.one_mul, Nat.add_zero] at hnhi
    have hβ1 : β - 1 + 1 = β := by omega
    rcases Nat.lt_or_ge (n / β) (y + 1) with hj | hj
    · -- j := n / β, i := n % β
      refine ⟨n % β, n / β, ?_, by omega, ?_⟩
      · have h1 := Nat.mod_lt n hβ0
        have h2 : n % β ≤ β - 1 := Nat.le_pred_of_lt h1
        linarith
      · calc n = β * (n / β) + n % β := (Nat.div_add_mod n β).symm
          _ = (n % β) * 1 + (n / β) * β := by ring
    · -- j := y, i := n − yβ
      have h4 : (y + 1) * β ≤ (n / β) * β := Nat.mul_le_mul_right β hj
      have h5 : (n / β) * β ≤ n := Nat.div_mul_le_self n β
      have h6 : y * β ≤ n := by
        have hexp : (y + 1) * β = y * β + β := by ring
        linarith
      refine ⟨n - y * β, y, ?_, le_refl y, ?_⟩
      · rw [Nat.sub_le_iff_le_add]
        have hbr : β * y = y * β := Nat.mul_comm _ _
        linarith
      · rw [mul_one, Nat.sub_add_cancel h6]
  · -- α ≥ 2
    have hβ2 : 2 ≤ β := by omega
    -- numeric identities
    have hCval : (α - 1) * (β - 1) + α + β = α * β + 1 := by
      zify [show 1 ≤ α by omega, show 1 ≤ β by omega]
      ring
    have hkey : (α - 1) * (β - 1) + (α - 1) = (α - 1) * β := by
      zify [show 1 ≤ α by omega, show 1 ≤ β by omega]
      ring
    induction y, hy using Nat.le_induction with
    | base =>
        intro n hnlo hnhi
        -- classical Chicken McNugget gives some representation
        have hF := frobeniusNumber_pair hco (by omega : 1 < α) (by omega : 1 < β)
        have hαβ' : α + β ≤ α * β := by
          have hC1 : 1 * 1 ≤ (α - 1) * (β - 1) :=
            Nat.mul_le_mul (by omega) (by omega)
          linarith [hCval]
        have hrep : ∃ i j : ℕ, n = i * α + j * β := by
          by_contra hcon
          push_neg at hcon
          have hnotin : n ∉ AddSubmonoid.closure ({α, β} : Set ℕ) := by
            rw [AddSubmonoid.mem_closure_pair]
            rintro ⟨i, j, hij⟩
            exact hcon i j (by simpa [smul_eq_mul, eq_comm] using hij)
          have hle : n ≤ α * β - α - β := hF.2 hnotin
          have h2 : α * β - α - β + (α + β) = α * β := by
            rw [Nat.sub_sub, Nat.sub_add_cancel hαβ']
          linarith
        obtain ⟨i, j, hij⟩ := hrep
        -- normalize j modulo α
        have hα0 : 0 < α := by omega
        have hjmod : j % α ≤ α - 1 := Nat.le_pred_of_lt (Nat.mod_lt j hα0)
        have heq : n = (i + j / α * β) * α + (j % α) * β := by
          calc n = i * α + j * β := hij
            _ = i * α + (α * (j / α) + j % α) * β := by rw [Nat.div_add_mod]
            _ = (i + j / α * β) * α + (j % α) * β := by ring
        refine ⟨i + j / α * β, j % α, ?_, hjmod, heq⟩
        -- the boxed bound on i′
        have hbr : β * (α - 1) = (α - 1) * β := Nat.mul_comm _ _
        have hn_ub : n ≤ α * x + (α - 1) := by linarith
        have hi'α : (i + j / α * β) * α ≤ n := by
          have : (i + j / α * β) * α ≤ (i + j / α * β) * α + (j % α) * β :=
            Nat.le_add_right _ _
          linarith [heq.symm.le, this]
        have hlt : (i + j / α * β) * α < (x + 1) * α := by
          have hexp : (x + 1) * α = x * α + α := by ring
          have hbr2 : α * x = x * α := Nat.mul_comm _ _
          have hαm : α - 1 + 1 = α := by omega
          linarith
        exact Nat.lt_succ_iff.mp (Nat.lt_of_mul_lt_mul_right hlt)
    | succ y hy ih =>
        intro n hnlo hnhi
        rcases Nat.le_total (n + (α - 1) * (β - 1)) (α * x + β * y) with hcase | hcase
        · obtain ⟨i, j, hix, hjy, heq⟩ := ih n hnlo hcase
          exact ⟨i, j, hix, by omega, heq⟩
        · -- peel one β
          have hwin : 2 * ((α - 1) * (β - 1)) + β ≤ α * x + β * y := by
            have h1 : α * (β - 1) ≤ α * x := Nat.mul_le_mul_left α hx
            have h2 : β * (α - 1) ≤ β * y := Nat.mul_le_mul_left β hy
            have h3 : 2 * ((α - 1) * (β - 1)) + β + (α - 2) =
                α * (β - 1) + β * (α - 1) := by
              zify [show 1 ≤ α by omega, show 1 ≤ β by omega,
                show 2 ≤ α from hα2]
              ring
            linarith
          have hβn : β ≤ n := by
            have hC0 : 0 ≤ (α - 1) * (β - 1) := Nat.zero_le _
            linarith
          have hnlo' : (α - 1) * (β - 1) ≤ n - β :=
            Nat.le_sub_of_add_le (by linarith)
          have hnhi' : (n - β) + (α - 1) * (β - 1) ≤ α * x + β * y := by
            have hexp : β * (y + 1) = β * y + β := by ring
            have h4 : n - β + β = n := Nat.sub_add_cancel hβn
            linarith
          obtain ⟨i, j, hix, hjy, heq⟩ := ih (n - β) hnlo' hnhi'
          refine ⟨i, j + 1, hix, by omega, ?_⟩
          have h5 : n = (n - β) + β := (Nat.sub_add_cancel hβn).symm
          rw [h5, heq]
          ring

/-- Multiset form of the two-generator lemma: the corresponding run of subset sums of
`{x × α, y × β}`. -/
theorem twoGen_hasRun {α β x y : ℕ} (hαβ : α < β) (hα : 0 < α)
    (hco : Nat.Coprime α β) (hx : β - 1 ≤ x) (hy : α - 1 ≤ y) :
    ∀ n, (α - 1) * (β - 1) ≤ n → n + (α - 1) * (β - 1) ≤ α * x + β * y →
      n ∈ subsetSums (Multiset.replicate x α + Multiset.replicate y β) := by
  intro n hnlo hnhi
  obtain ⟨i, j, hix, hjy, heq⟩ := twoGen_interval hαβ hα hco hx hy n hnlo hnhi
  apply mem_subsetSums.mpr
  refine ⟨Multiset.replicate i α + Multiset.replicate j β, ?_, ?_⟩
  · exact add_le_add ((Multiset.replicate_le_replicate α).mpr hix)
      ((Multiset.replicate_le_replicate β).mpr hjy)
  · simp only [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul]
    exact heq.symm

end Proof
end Erdos1112


/-! Flattened from Erdos1112Proof.Sharp.Frame. -/
/-
the frame lemma: the frame lemma — residue representatives mod ν plus
padding copies of ν cover a long run. Paper: the bounded subset-sum covering section.
-/

namespace Erdos1112
namespace Proof

/-- **the frame lemma (frame lemma).** If every residue `ρ mod ν` has a
representative `j·g₁ + k·g₂` inside the box `j ≤ Y, k ≤ Z` of height `≤ S`,
and `L − 1 + S ≤ ν·x`, then the multiset `{Y×g₁, Z×g₂, x×ν}` realizes every
integer of `[S, ν·x] ⊇ [S, S+L−1]` as a subset sum. -/
theorem frame_lemma {ν g₁ g₂ Y Z x S : ℕ} (hν : 0 < ν)
    (hreps : ∀ ρ < ν, ∃ j k, j ≤ Y ∧ k ≤ Z ∧
      (j * g₁ + k * g₂) % ν = ρ ∧ j * g₁ + k * g₂ ≤ S) :
    ∀ n, S ≤ n → n ≤ ν * x →
      n ∈ subsetSums (Multiset.replicate Y g₁ + Multiset.replicate Z g₂ +
        Multiset.replicate x ν) := by
  intro n hSn hnx
  obtain ⟨j, k, hjY, hkZ, hmod, hle⟩ := hreps (n % ν) (Nat.mod_lt _ hν)
  set r : ℕ := j * g₁ + k * g₂ with hrdef
  have hrn : r ≤ n := le_trans hle hSn
  have hdvd : ν ∣ n - r := (Nat.modEq_iff_dvd' hrn).mp hmod
  set q : ℕ := (n - r) / ν with hqdef
  have hqν : q * ν = n - r := Nat.div_mul_cancel hdvd
  have hqx : q ≤ x := by
    have h1 : q * ν ≤ x * ν := by
      rw [hqν]
      calc n - r ≤ n := Nat.sub_le _ _
        _ ≤ ν * x := hnx
        _ = x * ν := Nat.mul_comm _ _
    exact Nat.le_of_mul_le_mul_right h1 hν
  apply mem_subsetSums.mpr
  refine ⟨Multiset.replicate j g₁ + Multiset.replicate k g₂ +
    Multiset.replicate q ν, ?_, ?_⟩
  · exact add_le_add (add_le_add
      ((Multiset.replicate_le_replicate g₁).mpr hjY)
      ((Multiset.replicate_le_replicate g₂).mpr hkZ))
      ((Multiset.replicate_le_replicate ν).mpr hqx)
  · simp only [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul]
    calc j * g₁ + k * g₂ + q * ν = r + (n - r) := by rw [← hrdef, hqν]
      _ = n := by omega

end Proof
end Erdos1112


/-! Flattened from Erdos1112Proof.Sharp.Staircase. -/
/-
the staircase lemma: staircase windows and merges over `G = {a, b, M}`,
including the extended form (d) with the frame-merge condition
`V′ − C′ ≥ a − 1`. The counterexample showing the condition is NOT
removable — `(a,b,M) = (5,7,9)`, multiset `{5,5,5,7}` missing `11` inside
the would-be interval `[10,12]` — is pinned below as a machine-checked
guard.

Notation (paper): `e := b − a`, `μ := M − a`, `g := gcd(e, μ)`, `e′ := e/g`,
`μ′ := μ/g` (coprime, `e′ < μ′`), `C′ := (e′−1)(μ′−1)`, and for the staircase
multiset `(x, y, z)`: `c := y + z`, `V′ := y·e′ + z·μ′ − C′`.

Formalization conventions: `C′, V′` are parameters pinned by ADDITIVE
defining hypotheses (`hV' : V' + C' = e'*y + μ'*z`) to dodge ℕ-subtraction;
the merge condition is `hmerge : a + C' ≤ V' + 1` (⟺ `V′−C′ ≥ a−1`); the
extended form's descent uses the closed form `j* = (u₀ − V' + a − 1)/a`, so
the single-frame-per-class case (`J = 0`) needs no separate treatment.
-/

namespace Erdos1112
namespace Proof

/-- The staircase multiset `(x, y, z)` of copies of `(a, b, M)`. -/
def stair (a b M x y z : ℕ) : Multiset ℕ :=
  Multiset.replicate x a + Multiset.replicate y b + Multiset.replicate z M

/-- `n < (n/d + 1)·d` for `d > 0` (Euclid remainder bound). -/
private lemma lt_div_add_one_mul_self (n : ℕ) {d : ℕ} (hd : 0 < d) :
    n < (n / d + 1) * d := by
  have h1 := Nat.div_add_mod n d
  have h2 := Nat.mod_lt n hd
  have h3 : (n / d + 1) * d = d * (n / d) + d := by ring
  omega

section Staircase

variable {a b M x y z g e' μ' C' V' : ℕ}

/-- Basic facts about the gcd-normalized letters, packaged. -/
structure StairSetup (a b M g e' μ' : ℕ) : Prop where
  hab : a < b
  hbM : b < M
  ha : 0 < a
  hgdef : g = Nat.gcd (b - a) (M - a)
  he' : e' = (b - a) / g
  hμ' : μ' = (M - a) / g

namespace StairSetup

lemma g_pos (S : StairSetup a b M g e' μ') : 0 < g := by
  rw [S.hgdef]
  have hab := S.hab
  exact Nat.gcd_pos_of_pos_left _ (by omega)

lemma g_dvd_e (S : StairSetup a b M g e' μ') : g ∣ b - a :=
  S.hgdef ▸ Nat.gcd_dvd_left _ _

lemma g_dvd_μ (S : StairSetup a b M g e' μ') : g ∣ M - a :=
  S.hgdef ▸ Nat.gcd_dvd_right _ _

lemma e_eq (S : StairSetup a b M g e' μ') : b = a + g * e' := by
  have h := Nat.mul_div_cancel' S.g_dvd_e
  rw [S.he']
  have hab := S.hab
  omega

lemma μ_eq (S : StairSetup a b M g e' μ') : M = a + g * μ' := by
  have h := Nat.mul_div_cancel' S.g_dvd_μ
  rw [S.hμ']
  have hbM := S.hbM
  have hab := S.hab
  omega

lemma e'_pos (S : StairSetup a b M g e' μ') : 0 < e' := by
  rw [S.he']
  have hab := S.hab
  exact Nat.div_pos (Nat.le_of_dvd (by omega) S.g_dvd_e) S.g_pos

lemma e'_lt_μ' (S : StairSetup a b M g e' μ') : e' < μ' := by
  have h1 := S.e_eq
  have h2 := S.μ_eq
  have hbM := S.hbM
  have h3 : g * e' < g * μ' := by omega
  exact Nat.lt_of_mul_lt_mul_left h3

lemma coprime' (S : StairSetup a b M g e' μ') : Nat.Coprime e' μ' := by
  rw [S.he', S.hμ', S.hgdef]
  exact Nat.coprime_div_gcd_div_gcd (S.hgdef ▸ S.g_pos)

end StairSetup

/-- **3.3(a) (level windows).** For `y ≥ μ′−1`, `z ≥ e′−1` and any level
`y + z ≤ t ≤ x`: every `u ∈ [C′, V′]` gives `t·a + g·u` as a subset sum of
the staircase, realized with exactly `t` elements. -/
theorem staircase_level (S : StairSetup a b M g e' μ')
    (hC' : C' = (e' - 1) * (μ' - 1)) (hV' : V' + C' = e' * y + μ' * z)
    (hy : μ' - 1 ≤ y) (hz : e' - 1 ≤ z)
    {t : ℕ} (hct : y + z ≤ t) (htx : t ≤ x)
    {u : ℕ} (hu_lo : C' ≤ u) (hu_hi : u ≤ V') :
    t * a + g * u ∈ subsetSums (stair a b M x y z) := by
  have he'μ' := S.e'_lt_μ'
  have he'0 := S.e'_pos
  have hco' := S.coprime'
  obtain ⟨i, j, hiy, hjz, huij⟩ :=
    twoGen_interval he'μ' he'0 hco' hy hz u (hC' ▸ hu_lo)
      (by rw [← hC']; omega)
  apply mem_subsetSums.mpr
  refine ⟨Multiset.replicate (t - i - j) a + Multiset.replicate i b +
    Multiset.replicate j M, ?_, ?_⟩
  · exact add_le_add (add_le_add
      ((Multiset.replicate_le_replicate a).mpr (by omega))
      ((Multiset.replicate_le_replicate b).mpr hiy))
      ((Multiset.replicate_le_replicate M).mpr hjz)
  · simp only [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul]
    have hijt : t - i - j + i + j = t := by omega
    calc (t - i - j) * a + i * b + j * M
        = (t - i - j) * a + i * (a + g * e') + j * (a + g * μ') := by
          rw [← S.e_eq, ← S.μ_eq]
      _ = (t - i - j + i + j) * a + g * (i * e' + j * μ') := by ring
      _ = t * a + g * u := by rw [hijt, ← huij]

/-- Residue frame: since `gcd(a, g) = 1`, some level in `[c, c+g)` matches
`n`'s residue class modulo `g`. -/
lemma exists_frame (hg : 0 < g) (hag : Nat.Coprime a g) (c n : ℕ) :
    ∃ t₀, c ≤ t₀ ∧ t₀ < c + g ∧ (t₀ * a) % g = n % g := by
  haveI : NeZero g := ⟨hg.ne'⟩
  have hunit : IsUnit (a : ZMod g) := by
    rw [ZMod.isUnit_iff_coprime]
    exact hag
  set v : ZMod g := (((n : ZMod g) - (c : ZMod g) * (a : ZMod g)) * hunit.unit⁻¹) with hvdef
  refine ⟨c + v.val, Nat.le_add_right _ _, by
    have := ZMod.val_lt v
    omega, ?_⟩
  have hcast : (((c + v.val) * a : ℕ) : ZMod g) = ((n : ℕ) : ZMod g) := by
    push_cast
    rw [ZMod.natCast_val, ZMod.cast_id]
    rw [hvdef]
    have hinv : ((n : ZMod g) - (c : ZMod g) * (a : ZMod g)) * ↑hunit.unit⁻¹ * (a : ZMod g)
        = (n : ZMod g) - (c : ZMod g) * (a : ZMod g) := by
      have hu1 : (↑hunit.unit⁻¹ : ZMod g) * (a : ZMod g) = 1 := hunit.val_inv_mul
      calc ((n : ZMod g) - (c : ZMod g) * (a : ZMod g)) * ↑hunit.unit⁻¹ * (a : ZMod g)
          = ((n : ZMod g) - (c : ZMod g) * (a : ZMod g)) * (↑hunit.unit⁻¹ * (a : ZMod g)) := by
            ring
        _ = (n : ZMod g) - (c : ZMod g) * (a : ZMod g) := by rw [hu1, mul_one]
    calc ((c : ZMod g) + ((n : ZMod g) - (c : ZMod g) * (a : ZMod g)) * ↑hunit.unit⁻¹) * (a : ZMod g)
        = (c : ZMod g) * (a : ZMod g) +
          ((n : ZMod g) - (c : ZMod g) * (a : ZMod g)) * ↑hunit.unit⁻¹ * (a : ZMod g) := by
          ring
      _ = (n : ZMod g) := by rw [hinv]; ring
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast

/-- Single-frame landing: a level `t₀ ∈ [c, x]` in `n`'s residue class with
`n` inside its window realizes `n`. -/
theorem staircase_land (S : StairSetup a b M g e' μ')
    (hC' : C' = (e' - 1) * (μ' - 1)) (hV' : V' + C' = e' * y + μ' * z)
    (hy : μ' - 1 ≤ y) (hz : e' - 1 ≤ z)
    {t₀ n : ℕ} (hct : y + z ≤ t₀) (htx : t₀ ≤ x)
    (hres : (t₀ * a) % g = n % g)
    (hlo : t₀ * a + g * C' ≤ n) (hhi : n ≤ t₀ * a + g * V') :
    n ∈ subsetSums (stair a b M x y z) := by
  have hg := S.g_pos
  have hta_n : t₀ * a ≤ n := le_trans (Nat.le_add_right _ _) hlo
  have hdvd : g ∣ n - t₀ * a := (Nat.modEq_iff_dvd' hta_n).mp hres
  set u : ℕ := (n - t₀ * a) / g with hudef
  have hu : g * u = n - t₀ * a := Nat.mul_div_cancel' hdvd
  have hn_eq : n = t₀ * a + g * u := by omega
  have hu_lo : C' ≤ u := by
    have h1 : g * C' ≤ g * u := by omega
    exact Nat.le_of_mul_le_mul_left h1 hg
  have hu_hi : u ≤ V' := by
    have h1 : g * u ≤ g * V' := by omega
    exact Nat.le_of_mul_le_mul_left h1 hg
  rw [hn_eq]
  exact staircase_level S hC' hV' hy hz hct htx hu_lo hu_hi

/-- **the staircase extended/base form (d), base form.** With `x ≥ c + g − 1` (one frame per residue class
available in `[c, c+g)`), the sums cover the solid interval
`[(c+g−1)·a + g·C′, c·a + g·V′]` — no merge hypothesis. -/
theorem staircase_phase_base (S : StairSetup a b M g e' μ')
    (hC' : C' = (e' - 1) * (μ' - 1)) (hV' : V' + C' = e' * y + μ' * z)
    (hag : Nat.Coprime a g)
    (hy : μ' - 1 ≤ y) (hz : e' - 1 ≤ z)
    (hx : y + z + g - 1 ≤ x) :
    ∀ n, (y + z + g - 1) * a + g * C' ≤ n → n ≤ (y + z) * a + g * V' →
      n ∈ subsetSums (stair a b M x y z) := by
  intro n hnlo hnhi
  have hg := S.g_pos
  obtain ⟨t₀, ht₀c, ht₀g, hres⟩ := exists_frame hg hag (y + z) n
  have hta1 : t₀ * a ≤ (y + z + g - 1) * a :=
    Nat.mul_le_mul_right a (by omega)
  have hta2 : (y + z) * a ≤ t₀ * a := Nat.mul_le_mul_right a ht₀c
  exact staircase_land S hC' hV' hy hz ht₀c (by omega) hres
    (by omega) (by omega)

set_option maxHeartbeats 800000 in
/-- **the staircase extended/base form (d), extended form.** With `x ≥ c + g` and the frame-merge
condition `V′ − C′ ≥ a − 1` (here `a + C' ≤ V' + 1`), the frames of each
residue class merge and the sums cover the solid interval
`[(c+g−1)·a + g·C′, (x−g+1)·a + g·V′]`. The merge condition is NOT removable:
see the counterexample below. -/
theorem staircase_phase_extended (S : StairSetup a b M g e' μ')
    (hC' : C' = (e' - 1) * (μ' - 1)) (hV' : V' + C' = e' * y + μ' * z)
    (hag : Nat.Coprime a g)
    (hy : μ' - 1 ≤ y) (hz : e' - 1 ≤ z)
    (hx : y + z + g ≤ x)
    (hmerge : a + C' ≤ V' + 1) :
    ∀ n, (y + z + g - 1) * a + g * C' ≤ n → n ≤ (x - g + 1) * a + g * V' →
      n ∈ subsetSums (stair a b M x y z) := by
  intro n hnlo hnhi
  have hg := S.g_pos
  have ha := S.ha
  obtain ⟨t₀, ht₀c, ht₀g, hres⟩ := exists_frame hg hag (y + z) n
  -- u₀: the offset at the first frame
  have hta1 : t₀ * a ≤ (y + z + g - 1) * a := Nat.mul_le_mul_right a (by omega)
  have hta_n : t₀ * a + g * C' ≤ n := by omega
  have hdvd : g ∣ n - t₀ * a :=
    (Nat.modEq_iff_dvd' (by omega)).mp hres
  set u₀ : ℕ := (n - t₀ * a) / g with hu₀def
  have hu₀ : g * u₀ = n - t₀ * a := Nat.mul_div_cancel' hdvd
  have hn_eq : n = t₀ * a + g * u₀ := by omega
  have hu₀_lo : C' ≤ u₀ := by
    have h1 : g * C' ≤ g * u₀ := by omega
    exact Nat.le_of_mul_le_mul_left h1 hg
  -- the last frame of the class below x: J := ⌊(x − t₀)/g⌋
  have hxt₀ : t₀ ≤ x := by omega
  set J : ℕ := (x - t₀) / g with hJdef
  have hJx : t₀ + J * g ≤ x := by
    have h1 := Nat.div_mul_le_self (x - t₀) g
    rw [← hJdef] at h1
    omega
  have hJmax : x - t₀ < (J + 1) * g := by
    have h1 := lt_div_add_one_mul_self (x - t₀) hg
    rw [← hJdef] at h1
    exact h1
  -- window at the last frame bounds u₀ from above: u₀ ≤ V′ + J·a
  have huJ : u₀ ≤ V' + J * a := by
    have hbr1 : (J + 1) * g = J * g + g := by ring
    have h1 : (x - g + 1) * a ≤ (t₀ + J * g) * a :=
      Nat.mul_le_mul_right a (by omega)
    have h2 : (t₀ + J * g) * a = t₀ * a + J * g * a := by ring
    have h3 : g * (V' + J * a) = g * V' + J * g * a := by ring
    have h4 : g * u₀ ≤ g * (V' + J * a) := by omega
    exact Nat.le_of_mul_le_mul_left h4 hg
  -- the descent index: j* := ⌈(u₀ − V′)/a⌉ (0 if already inside the window)
  set j : ℕ := (u₀ - V' + a - 1) / a with hjdef
  have hj_land_hi : u₀ - j * a ≤ V' := by
    have h1 := lt_div_add_one_mul_self (u₀ - V' + a - 1) ha
    rw [← hjdef] at h1
    have hexp : (j + 1) * a = j * a + a := by ring
    omega
  have hj_land_lo : C' ≤ u₀ - j * a := by
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · rw [hj0, Nat.zero_mul, Nat.sub_zero]
      exact hu₀_lo
    · have h1 : j * a ≤ u₀ - V' + a - 1 := by
        have h2 := Nat.div_mul_le_self (u₀ - V' + a - 1) a
        rw [← hjdef] at h2
        exact h2
      have h3 : a ≤ j * a := Nat.le_mul_of_pos_left a hjpos
      omega
  have hjJ : j ≤ J := by
    have h1 : u₀ - V' + a - 1 < (J + 1) * a := by
      have hexp : (J + 1) * a = J * a + a := by ring
      omega
    have h2 : (u₀ - V' + a - 1) / a < J + 1 :=
      (Nat.div_lt_iff_lt_mul ha).mpr h1
    rw [← hjdef] at h2
    omega
  have ht_le : t₀ + j * g ≤ x := by
    have h1 : j * g ≤ J * g := Nat.mul_le_mul_right g hjJ
    omega
  -- j·a never overshoots u₀ (uses the merge condition via V′ ≥ C′ + a − 1)
  have hja_u₀ : j * a ≤ u₀ := by
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · rw [hj0, Nat.zero_mul]
      exact Nat.zero_le _
    · have h1 : j * a ≤ u₀ - V' + a - 1 := by
        have h2 := Nat.div_mul_le_self (u₀ - V' + a - 1) a
        rw [← hjdef] at h2
        exact h2
      have h3 : a ≤ j * a := Nat.le_mul_of_pos_left a hjpos
      omega
  have hres' : ((t₀ + j * g) * a) % g = n % g := by
    have h1 : (t₀ + j * g) * a = t₀ * a + j * a * g := by ring
    have h2 : (t₀ * a + j * a * g) % g = (t₀ * a) % g := Nat.add_mul_mod_self_right _ _ _
    rw [h1, h2]
    exact hres
  have hgu_sub : g * (u₀ - j * a) = g * u₀ - g * (j * a) := by
    zify [hja_u₀, Nat.mul_le_mul_left g hja_u₀]
    ring
  have hbr4 : g * (j * a) = j * g * a := by ring
  have hgja : g * (j * a) ≤ g * u₀ := Nat.mul_le_mul_left g hja_u₀
  apply staircase_land S hC' hV' hy hz (le_trans ht₀c (Nat.le_add_right _ _)) ht_le hres'
  · -- lower window at the landing frame
    have h1 : (t₀ + j * g) * a = t₀ * a + j * g * a := by ring
    have h3 : g * C' ≤ g * (u₀ - j * a) := Nat.mul_le_mul_left g hj_land_lo
    omega
  · have h1 : (t₀ + j * g) * a = t₀ * a + j * g * a := by ring
    have h3 : g * (u₀ - j * a) ≤ g * V' := Nat.mul_le_mul_left g hj_land_hi
    omega

/-- **the staircase short merge (c) (short two-frame merge, `g = 1`, `x = y + z`).** Level `y+z+1`
exceeds the `a`-budget by one, so it loses exactly the zero offset; with
`V′ ≥ a + max(C′,1) − 1` the two levels still merge and the sums cover
`[(y+z)·a + C′, (y+z+1)·a + V′]`. Needed only for Case L's `a` odd, `g = 1`
branch. -/
theorem staircase_merge_c (S : StairSetup a b M g e' μ')
    (hg1 : g = 1)
    (hC' : C' = (e' - 1) * (μ' - 1)) (hV' : V' + C' = e' * y + μ' * z)
    (hy : μ' - 1 ≤ y) (hz : e' - 1 ≤ z)
    (hx : x = y + z)
    (hmerge : a + max C' 1 ≤ V' + 1) :
    ∀ n, (y + z) * a + C' ≤ n → n ≤ (y + z + 1) * a + V' →
      n ∈ subsetSums (stair a b M x y z) := by
  subst hg1
  subst hx
  have ha := S.ha
  -- level `c = y+z` covers `(y+z)*a + [C', V']`
  have hlevel_c : ∀ u, C' ≤ u → u ≤ V' →
      (y + z) * a + u ∈ subsetSums (stair a b M (y + z) y z) := by
    intro u hu_lo hu_hi
    have h := staircase_level S hC' hV' hy hz (le_refl (y + z)) (le_refl (y + z))
      hu_lo hu_hi
    simpa using h
  -- level `c+1` covers `(y+z+1)*a + [max C' 1, V']` (zero offset excluded)
  have hlevel_c1 : ∀ u, max C' 1 ≤ u → u ≤ V' →
      (y + z + 1) * a + u ∈ subsetSums (stair a b M (y + z) y z) := by
    intro u hu_lo hu_hi
    have hu1 : 1 ≤ u := le_trans (le_max_right _ _) hu_lo
    have huC : C' ≤ u := le_trans (le_max_left _ _) hu_lo
    obtain ⟨i, j, hiy, hjz, huij⟩ :=
      twoGen_interval S.e'_lt_μ' S.e'_pos S.coprime' hy hz u (hC' ▸ huC)
        (by rw [← hC']; omega)
    have hij1 : 1 ≤ i + j := by
      rcases Nat.eq_zero_or_pos (i + j) with h0 | h0
      · exfalso
        obtain ⟨rfl, rfl⟩ : i = 0 ∧ j = 0 := by omega
        simp only [Nat.zero_mul, Nat.add_zero] at huij
        omega
      · exact h0
    apply mem_subsetSums.mpr
    refine ⟨Multiset.replicate (y + z + 1 - i - j) a + Multiset.replicate i b +
      Multiset.replicate j M, ?_, ?_⟩
    · exact add_le_add (add_le_add
        ((Multiset.replicate_le_replicate a).mpr (by omega))
        ((Multiset.replicate_le_replicate b).mpr hiy))
        ((Multiset.replicate_le_replicate M).mpr hjz)
    · simp only [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul]
      have hijt : y + z + 1 - i - j + i + j = y + z + 1 := by omega
      calc (y + z + 1 - i - j) * a + i * b + j * M
          = (y + z + 1 - i - j) * a + i * (a + 1 * e') + j * (a + 1 * μ') := by
            rw [← S.e_eq, ← S.μ_eq]
        _ = (y + z + 1 - i - j + i + j) * a + (i * e' + j * μ') := by ring
        _ = (y + z + 1) * a + u := by rw [hijt, ← huij]
  -- merge the two levels
  intro n hnlo hnhi
  have hab : (y + z + 1) * a = (y + z) * a + a := by ring
  rcases Nat.lt_or_ge n ((y + z) * a + V' + 1) with hcase | hcase
  · -- lands in level c
    have hn : n = (y + z) * a + (n - (y + z) * a) := by omega
    rw [hn]
    exact hlevel_c _ (by omega) (by omega)
  · -- lands in level c+1
    have haV : a ≤ V' + 1 := le_trans (by omega) hmerge
    have hge : (y + z + 1) * a ≤ n := by omega
    have hn : n = (y + z + 1) * a + (n - (y + z + 1) * a) := by omega
    rw [hn]
    refine hlevel_c1 _ ?_ (by omega)
    -- u = n - (y+z+1)*a ≥ V'+1-a ≥ max C' 1
    omega

/-- **The merge condition of the staircase extended/base form (d) is not removable** (counterexample,
machine-checked): for `(a,b,M) = (5,7,9)` with
`(x,y,z) = (3,1,0)` — the multiset `{5,5,5,7}`, which satisfies every
hypothesis of the extended form EXCEPT `V′−C′ ≥ a−1` — the would-be interval
`[10, 12]` is broken: `11` is not a subset sum (while `10` and `12` are).
Any attempt to drop `hmerge` from `staircase_phase_extended` must fail here. -/
example :
    11 ∉ subsetSums (stair 5 7 9 3 1 0) ∧
    10 ∈ subsetSums (stair 5 7 9 3 1 0) ∧
    12 ∈ subsetSums (stair 5 7 9 3 1 0) := by
  decide

end Staircase

end Proof
end Erdos1112


/-! Flattened from Erdos1112Proof.Sharp.Graham. -/
/-
reduction layer: the L1/L2/L3 dispatch lemmas (paper 3.6–3.8) and
the reduction principle packaging Graham's reduction with the minimal-
alphabet analysis (3.5, 3.9, 3.10).

Edge hygiene:
  * L3 is stated WITHOUT assuming `1 < α` — at `α = a/d = 1` (i.e. `a ∣ b`)
    the conductor `(α−1)(β−1)` is 0 and everything still works; the equality
    corner `(α, β) = (1, 2)` is pinned as a decided instance below.
  * L3's `y ≥ α − 1` requirement is the explicit lemma `L3_y_bound`.
-/

namespace Erdos1112
namespace Proof

/-- **L1 (small coprime pair)**: a coprime pair `α, γ` with `α + γ + 1 ≤ M` realizes
an `M`-run within budget `M − 1` using only `α`s and `γ`s. -/
theorem sharp_of_small_coprime_pair {α γ M : ℕ} (hα : 0 < α) (hγ : 0 < γ)
    (hco : Nat.Coprime α γ) (hle : α + γ + 1 ≤ M) :
    ∃ S : Multiset ℕ, (∀ w ∈ S, w = α ∨ w = γ) ∧ S.card ≤ M - 1 ∧
      HasRun (subsetSums S) M := by
  obtain ⟨x, hxM⟩ : ∃ x, x + α = M := ⟨M - α, by omega⟩
  refine ⟨Multiset.replicate (α - 1) γ + Multiset.replicate 0 γ +
    Multiset.replicate x α, ?_, ?_, (α - 1) * γ, ?_⟩
  · intro w hw
    rcases Multiset.mem_add.mp hw with hw | hw
    · rcases Multiset.mem_add.mp hw with hw | hw
      · exact Or.inr (Multiset.eq_of_mem_replicate hw)
      · exact Or.inr (Multiset.eq_of_mem_replicate hw)
    · exact Or.inl (Multiset.eq_of_mem_replicate hw)
  · simp only [Multiset.card_add, Multiset.card_replicate]
    omega
  · intro i hi
    apply frame_lemma hα (S := (α - 1) * γ)
    · intro ρ hρ
      obtain ⟨j, -, hjα, hres⟩ := exists_frame hα hco.symm 0 ρ
      refine ⟨j, 0, by omega, le_refl 0, ?_, ?_⟩
      · rw [Nat.zero_mul, Nat.add_zero, hres, Nat.mod_eq_of_lt hρ]
      · rw [Nat.zero_mul, Nat.add_zero]
        exact Nat.mul_le_mul_right γ (by omega)
    · -- (α−1)·γ ≤ (α−1)·γ + i, trivially
      omega
    · -- (α−1)·γ + i ≤ α·x, from (α−1)(γ+1) ≤ (α−1)x and i ≤ M−1
      have h1 : γ + 1 ≤ x := by omega
      have h2 : (α - 1) * (γ + 1) ≤ (α - 1) * x := Nat.mul_le_mul_left _ h1
      have h3 : (α - 1) * (γ + 1) = (α - 1) * γ + (α - 1) := by ring
      have h4 : α * x = (α - 1) * x + x := by
        have : α = (α - 1) + 1 := by omega
        calc α * x = ((α - 1) + 1) * x := by rw [← this]
          _ = (α - 1) * x + x := by ring
      omega

/-- **L2 (pair at the boundary)**: a coprime pair at the boundary `α + β ∈ {M, M+1}`
(the paper's `t = 0` / `t = 1` split). -/
theorem sharp_of_boundary_pair {α β M : ℕ} (hα : 0 < α) (hαβ : α < β)
    (hco : Nat.Coprime α β) (hb : α + β = M ∨ α + β = M + 1) :
    ∃ S : Multiset ℕ, (∀ w ∈ S, w = α ∨ w = β) ∧ S.card ≤ M - 1 ∧
      HasRun (subsetSums S) M := by
  -- t = 1 for α + β = M, t = 0 for α + β = M + 1
  obtain ⟨t, ht⟩ : ∃ t, (α + β = M ∧ t = 1) ∨ (α + β = M + 1 ∧ t = 0) := by
    rcases hb with hb | hb
    · exact ⟨1, Or.inl ⟨hb, rfl⟩⟩
    · exact ⟨0, Or.inr ⟨hb, rfl⟩⟩
  set x : ℕ := β - 1 with hxdef
  set y : ℕ := α - 1 + t with hydef
  have hCval : (α - 1) * (β - 1) + α + β = α * β + 1 := by
    zify [show 1 ≤ α by omega, show 1 ≤ β by omega]
    ring
  have hgrid : α * x + β * y + α + β = α * β + β * (α - 1 + t) + β := by
    have h1 : α * (β - 1) + α = α * β := by
      zify [show 1 ≤ β by omega]
      ring
    rw [hxdef, hydef]
    omega
  refine ⟨Multiset.replicate x α + Multiset.replicate y β, ?_, ?_, (α - 1) * (β - 1), ?_⟩
  · intro w hw
    rcases Multiset.mem_add.mp hw with hw | hw
    · exact Or.inl (Multiset.eq_of_mem_replicate hw)
    · exact Or.inr (Multiset.eq_of_mem_replicate hw)
  · simp only [Multiset.card_add, Multiset.card_replicate]
    rcases ht with ⟨hM, ht1⟩ | ⟨hM, ht0⟩ <;> omega
  · intro i hi
    apply twoGen_hasRun hαβ hα hco (by omega) (by omega)
    · omega
    · -- (C + i) + C ≤ αx + βy: equality case is t = 0 at i = M−1
      have hββ : β * (α - 1 + t) = β * (α - 1) + β * t := by ring
      rcases ht with ⟨hM, ht1⟩ | ⟨hM, ht0⟩ <;>
        · subst_vars
          have hβα : β * (α - 1) + β = β * α := by
            zify [show 1 ≤ α by omega]
            ring
          have hαβc : α * β = β * α := Nat.mul_comm _ _
          omega

/-- **L3's `y`-requirement, explicit**: with `d ≥ 2`,
`1 ≤ α < β` and `M ≥ d·β + 1`, the count `y = M − d − β + 1` satisfies
`y ≥ α − 1` — via `(d−1)(β−1) ≥ α − 2`. -/
lemma L3_y_bound {d α β M : ℕ} (hd : 2 ≤ d) (h1 : 1 ≤ α) (hαβ : α < β)
    (hM : d * β + 1 ≤ M) : α - 1 ≤ M - d - β + 1 := by
  have h2 : (d - 1) * (β - 1) + d + β = d * β + 1 := by
    zify [show 1 ≤ d by omega, show 1 ≤ β by omega]
    ring
  have h3 : β - 1 ≤ (d - 1) * (β - 1) := Nat.le_mul_of_pos_left _ (by omega)
  omega

/-- **L3 (non-coprime pair)**: `G = {a, b, M}` with `d := gcd(a,b) ≥ 2` (so
`gcd(d, M) = 1` since `gcd(G) = 1`). Stated via `a = d·α`, `b = d·β` with
`α < β` coprime — `α = 1` (i.e. `a ∣ b`) explicitly allowed. -/
theorem sharp_of_noncoprime_pair {d α β M : ℕ} (hd : 2 ≤ d) (hα : 0 < α)
    (hαβ : α < β) (hco : Nat.Coprime α β) (hdM : Nat.Coprime M d)
    (hM : d * β + 1 ≤ M) :
    ∃ S : Multiset ℕ, (∀ w ∈ S, w = d * α ∨ w = d * β ∨ w = M) ∧
      S.card ≤ M - 1 ∧ HasRun (subsetSums S) M := by
  have hβ2 : 2 ≤ β := by omega
  have hdβ_bridge : (d - 1) * (β - 1) + d + β = d * β + 1 := by
    zify [show 1 ≤ d by omega, show 1 ≤ β by omega]
    ring
  have hdβ1 : 1 * 1 ≤ (d - 1) * (β - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hdβM : d + β + 1 ≤ M := by omega
  have hy_ge : α - 1 ≤ M - d - β + 1 := L3_y_bound hd (by omega) hαβ hM
  -- the budget inequality, DIRECT for all M ≥ dβ+1
  have hkey : 2 * ((α - 1) * (β - 1)) + M ≤ α * (β - 1) + β * (M - d - β + 1) + 1 := by
    have hMZ : (d : ℤ) * β + 1 ≤ (M : ℤ) := by exact_mod_cast hM
    zify [show 1 ≤ α by omega, show 1 ≤ β by omega, show d ≤ M by omega,
      show β ≤ M - d by omega]
    nlinarith [mul_nonneg (show (0:ℤ) ≤ (β:ℤ) - 1 by omega)
        (show (0:ℤ) ≤ (M:ℤ) - ((d:ℤ) * β + 1) by linarith),
      mul_nonneg (mul_nonneg (show (0:ℤ) ≤ (d:ℤ) - 2 by omega)
        (show (0:ℤ) ≤ (β:ℤ) by omega)) (show (0:ℤ) ≤ (β:ℤ) - 2 by omega),
      mul_nonneg (show (0:ℤ) ≤ (β:ℤ) - (α:ℤ) - 1 by omega)
        (show (0:ℤ) ≤ (β:ℤ) by omega)]
  refine ⟨Multiset.replicate (β - 1) (d * α) +
    Multiset.replicate (M - d - β + 1) (d * β) + Multiset.replicate (d - 1) M,
    ?_, ?_, d * ((α - 1) * (β - 1)) + (d - 1) * M, ?_⟩
  · intro w hw
    rcases Multiset.mem_add.mp hw with hw | hw
    · rcases Multiset.mem_add.mp hw with hw | hw
      · exact Or.inl (Multiset.eq_of_mem_replicate hw)
      · exact Or.inr (Or.inl (Multiset.eq_of_mem_replicate hw))
    · exact Or.inr (Or.inr (Multiset.eq_of_mem_replicate hw))
  · simp only [Multiset.card_add, Multiset.card_replicate]
    omega
  · intro i hi
    obtain ⟨k, -, hkd, hres⟩ := exists_frame (show 0 < d by omega) hdM 0
      (d * ((α - 1) * (β - 1)) + (d - 1) * M + i)
    set n : ℕ := d * ((α - 1) * (β - 1)) + (d - 1) * M + i with hndef
    have hkd' : k ≤ d - 1 := by omega
    have hkM_le : k * M ≤ (d - 1) * M := Nat.mul_le_mul_right M hkd'
    have hkMn : k * M ≤ n := by omega
    have hdvd : d ∣ n - k * M := (Nat.modEq_iff_dvd' hkMn).mp hres
    set w : ℕ := (n - k * M) / d with hwdef
    have hw : d * w = n - k * M := Nat.mul_div_cancel' hdvd
    have hw_lo : (α - 1) * (β - 1) ≤ w := by
      have h1 : d * ((α - 1) * (β - 1)) ≤ d * w := by omega
      exact Nat.le_of_mul_le_mul_left h1 (by omega)
    have hMd_bridge : (d - 1) * M + M = d * M := by
      zify [show 1 ≤ d by omega]
      ring
    have hdM1 : 1 ≤ d * M := Nat.mul_pos (by omega) (by omega)
    have hw_hi : w + (α - 1) * (β - 1) ≤ α * (β - 1) + β * (M - d - β + 1) := by
      have h1 : d * w ≤ d * ((α - 1) * (β - 1)) + d * M - 1 := by omega
      have h2 : w ≤ (α - 1) * (β - 1) + M - 1 := by
        by_contra hcon
        push_neg at hcon
        have h3 : d * ((α - 1) * (β - 1) + M) ≤ d * w :=
          Nat.mul_le_mul_left d (by omega)
        have h4 : d * ((α - 1) * (β - 1) + M) =
            d * ((α - 1) * (β - 1)) + d * M := by ring
        omega
      omega
    obtain ⟨i', j', hi'x, hj'y, hwij⟩ :=
      twoGen_interval hαβ hα hco (le_refl (β - 1)) hy_ge w hw_lo hw_hi
    refine mem_subsetSums.mpr ⟨Multiset.replicate i' (d * α) +
      Multiset.replicate j' (d * β) + Multiset.replicate k M, ?_, ?_⟩
    · exact add_le_add (add_le_add
        ((Multiset.replicate_le_replicate _).mpr hi'x)
        ((Multiset.replicate_le_replicate _).mpr hj'y))
        ((Multiset.replicate_le_replicate _).mpr hkd')
    · simp only [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul]
      have hexp : i' * (d * α) + j' * (d * β) + k * M =
          d * (i' * α + j' * β) + k * M := by ring
      rw [hexp, ← hwij]
      omega

set_option maxRecDepth 100000 in
/-- The `(α, β) = (1, 2)` equality corner of L3, pinned as a decided
instance: `G = {5, 10, 11}` (`d = 5`, `a ∣ b`), witness
`{5} + 5×{10} + 4×{11}`, budget `10 = M − 1`, covering an 11-run. -/
example : ∀ i < 11, 44 + i ∈ subsetSums
    (Multiset.replicate 1 5 + Multiset.replicate 5 10 + Multiset.replicate 4 11) := by
  decide

/-! ### Reduction-layer interfaces

`sharpAt_of_hardcore`'s assembly will case-split as:
`1 ∈ G` → `sharp_of_one_mem`;  redundant `e ≠ M` → card-recursion;
redundant `e = M` → outer `ih` at `max (G.erase M) < M` + Graham fill
(`HasRun.cons_of_le`);  `|G| = 3` → L1 / L2 / L3 / hard-core `hc`
(with `Coprime M d` derived from `gcd G = 1` at the L3 branch);
`|G| ≥ 4` minimal → `sharp_of_minimal` (which consumes
`minimal_structure`'s `≥ 30` bound; the M ≤ 130 enumeration is NOT expected
to enter). -/

/-- `1 ∈ G` is trivial: `M − 1` copies of `1` cover `[0, M−1]`. -/
theorem sharp_of_one_mem (M : ℕ) :
    ∃ S : Multiset ℕ, (∀ w ∈ S, w = 1) ∧ S.card ≤ M - 1 ∧
      HasRun (subsetSums S) M := by
  refine ⟨Multiset.replicate (M - 1) 1,
    fun w hw => Multiset.eq_of_mem_replicate hw, ?_, 0, ?_⟩
  · simp [Multiset.card_replicate]
  · intro i hi
    refine mem_subsetSums.mpr ⟨Multiset.replicate i 1, ?_, ?_⟩
    · exact (Multiset.replicate_le_replicate 1).mpr (by omega)
    · simp [Multiset.sum_replicate]

/-- The 3.10 descent measure, standalone: rescaling by
`δ ≥ 2` strictly shrinks the maximum. -/
lemma rescaled_max_lt {δ M M' : ℕ} (hδ : 2 ≤ δ) (hM : 0 < M)
    (hδM' : δ * M' ≤ M) : M' < M := by
  have h2 : 2 * M' ≤ δ * M' := Nat.mul_le_mul_right M' hδ
  omega

/-- A prime other than 2 and 3 is at least 5. -/
lemma five_le_of_prime {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3) :
    5 ≤ p := by
  have hp2 := hp.two_le
  rcases Nat.lt_or_ge p 5 with h | h
  · interval_cases p
    · exact absurd rfl h2
    · exact absurd rfl h3
    · exact absurd hp (by decide)
  · exact h

/-- Three pairwise-distinct primes multiply to at least `2·3·5 = 30`. -/
lemma thirty_le_prime_triple {p q r : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hr : r.Prime) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    30 ≤ p * q * r := by
  have h2p := hp.two_le
  have h2q := hq.two_le
  have h2r := hr.two_le
  have h3 : ∀ {x : ℕ}, 2 ≤ x → x ≠ 2 → 3 ≤ x := fun hx h => by omega
  -- helper closing a leaf `30 ≤ a*b*c` from `u ≤ a, v ≤ b, w ≤ c, 30 ≤ u*v*w`
  have leaf : ∀ {a b c u v w : ℕ}, u ≤ a → v ≤ b → w ≤ c → 30 ≤ u * v * w →
      30 ≤ a * b * c := fun ha hb hc h30 =>
    le_trans h30 (Nat.mul_le_mul (Nat.mul_le_mul ha hb) hc)
  by_cases hp2 : p = 2
  · subst hp2
    have hq3' := h3 h2q (Ne.symm hpq)
    have hr3' := h3 h2r (Ne.symm hpr)
    by_cases hq3 : q = 3
    · subst hq3
      have := five_le_of_prime hr (Ne.symm hpr) (Ne.symm hqr)
      exact leaf (le_refl 2) (le_refl 3) this (by norm_num)
    · have := five_le_of_prime hq (Ne.symm hpq) hq3
      exact leaf (le_refl 2) this hr3' (by norm_num)
  · by_cases hq2 : q = 2
    · subst hq2
      have hp3' := h3 h2p hp2
      have hr3' := h3 h2r (Ne.symm hqr)
      by_cases hp3 : p = 3
      · subst hp3
        have := five_le_of_prime hr (Ne.symm hqr) (Ne.symm hpr)
        exact leaf (le_refl 3) (le_refl 2) this (by norm_num)
      · have := five_le_of_prime hp hp2 hp3
        exact leaf this (le_refl 2) hr3' (by norm_num)
    · by_cases hr2 : r = 2
      · subst hr2
        have hp3' := h3 h2p hp2
        have hq3' := h3 h2q hq2
        by_cases hp3 : p = 3
        · subst hp3
          have hq5 := five_le_of_prime hq hq2 (Ne.symm hpq)
          exact leaf (le_refl 3) hq5 (le_refl 2) (by norm_num)
        · have hp5 := five_le_of_prime hp hp2 hp3
          exact leaf hp5 hq3' (le_refl 2) (by norm_num)
      · -- none is 2: all ≥ 3; if one is 3 the others are ≥ 5; 3·5·5 ≥ 30
        have hp3' := h3 h2p hp2
        have hq3' := h3 h2q hq2
        have hr3' := h3 h2r hr2
        by_cases hp3 : p = 3
        · subst hp3
          have hq5 := five_le_of_prime hq hq2 (Ne.symm hpq)
          have hr5 := five_le_of_prime hr hr2 (Ne.symm hpr)
          exact leaf (le_refl 3) hq5 hr5 (by norm_num)
        · have hp5 := five_le_of_prime hp hp2 hp3
          exact leaf hp5 hq3' hr3' (by norm_num)

/-- Three pairwise-coprime naturals ≥ 2 multiply to ≥ 30: coprimality forces
distinct minimal prime factors, which land at ≥ {2,3,5}. -/
lemma thirty_le_mul_coprime {d₁ d₂ d₃ : ℕ} (h1 : 2 ≤ d₁) (h2 : 2 ≤ d₂)
    (h3 : 2 ≤ d₃) (c12 : Nat.Coprime d₁ d₂) (c13 : Nat.Coprime d₁ d₃)
    (c23 : Nat.Coprime d₂ d₃) : 30 ≤ d₁ * d₂ * d₃ := by
  have hp1 := Nat.minFac_prime (show d₁ ≠ 1 by omega)
  have hp2 := Nat.minFac_prime (show d₂ ≠ 1 by omega)
  have hp3 := Nat.minFac_prime (show d₃ ≠ 1 by omega)
  have hne : ∀ {u v : ℕ}, 2 ≤ u → Nat.Coprime u v → u.minFac ≠ v.minFac := by
    intro u v hu huv he
    have hd : u.minFac ∣ Nat.gcd u v :=
      Nat.dvd_gcd (Nat.minFac_dvd u) (he ▸ Nat.minFac_dvd v)
    have h1' := Nat.dvd_one.mp (huv.gcd_eq_one ▸ hd)
    have h2' := (Nat.minFac_prime (show u ≠ 1 by omega)).two_le
    omega
  have h30 := thirty_le_prime_triple hp1 hp2 hp3
    (hne h1 c12) (hne h1 c13) (hne h2 c23)
  calc (30 : ℕ) ≤ d₁.minFac * d₂.minFac * d₃.minFac := h30
    _ ≤ d₁ * d₂ * d₃ :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.minFac_le (by omega))
          (Nat.minFac_le (by omega))) (Nat.minFac_le (by omega))

/-- **3.9 (structure of minimal alphabets)**: if `G` (card ≥ 4, positive,
gcd 1) has every single-element erasure non-coprime, then every element is
divisible by three pairwise-coprime factors ≥ 2, hence `≥ 30`. -/
theorem minimal_structure {G : Finset ℕ} (hpos : ∀ g ∈ G, 0 < g)
    (hcard : 4 ≤ G.card) (hgcd : G.gcd id = 1)
    (hmin : ∀ e ∈ G, (G.erase e).gcd id ≠ 1) :
    ∀ g ∈ G, 30 ≤ g := by
  intro g hg
  have hg0 := hpos g hg
  -- three distinct elements ≠ g
  have hce := Finset.card_erase_of_mem hg
  obtain ⟨g₁, hg₁⟩ := Finset.card_pos.mp (by omega : 0 < (G.erase g).card)
  obtain ⟨hg₁g, hg₁G⟩ := Finset.mem_erase.mp hg₁
  have hce₁ := Finset.card_erase_of_mem hg₁
  obtain ⟨g₂, hg₂⟩ := Finset.card_pos.mp
    (by omega : 0 < ((G.erase g).erase g₁).card)
  obtain ⟨hg₂g₁, hg₂'⟩ := Finset.mem_erase.mp hg₂
  obtain ⟨hg₂g, hg₂G⟩ := Finset.mem_erase.mp hg₂'
  have hce₂ := Finset.card_erase_of_mem hg₂
  obtain ⟨g₃, hg₃⟩ := Finset.card_pos.mp
    (by omega : 0 < (((G.erase g).erase g₁).erase g₂).card)
  obtain ⟨hg₃g₂, hg₃'⟩ := Finset.mem_erase.mp hg₃
  obtain ⟨hg₃g₁, hg₃''⟩ := Finset.mem_erase.mp hg₃'
  obtain ⟨hg₃g, hg₃G⟩ := Finset.mem_erase.mp hg₃''
  -- leave-one-out gcds are pairwise coprime
  have key : ∀ u ∈ G, ∀ v ∈ G, u ≠ v →
      Nat.Coprime ((G.erase u).gcd id) ((G.erase v).gcd id) := by
    intro u hu v hv huv
    have hdvd : Nat.gcd ((G.erase u).gcd id) ((G.erase v).gcd id) ∣ G.gcd id := by
      apply Finset.dvd_gcd
      intro x hx
      by_cases hxu : x = u
      · subst hxu
        exact dvd_trans (Nat.gcd_dvd_right _ _)
          (Finset.gcd_dvd (Finset.mem_erase.mpr ⟨huv, hx⟩))
      · exact dvd_trans (Nat.gcd_dvd_left _ _)
          (Finset.gcd_dvd (Finset.mem_erase.mpr ⟨hxu, hx⟩))
    rw [hgcd] at hdvd
    exact Nat.dvd_one.mp hdvd
  -- they are ≥ 2 and divide g
  have hd2 : ∀ u ∈ G, u ≠ g → 2 ≤ (G.erase u).gcd id := by
    intro u hu hug
    have hne1 := hmin u hu
    have hne0 : (G.erase u).gcd id ≠ 0 := by
      intro h0
      have hz := Finset.gcd_eq_zero_iff.mp h0 g
        (Finset.mem_erase.mpr ⟨Ne.symm hug, hg⟩)
      simp only [id] at hz
      omega
    omega
  have hdvdg : ∀ u ∈ G, u ≠ g → (G.erase u).gcd id ∣ g := fun u _ hug =>
    Finset.gcd_dvd (Finset.mem_erase.mpr ⟨Ne.symm hug, hg⟩)
  -- compose
  have h30 := thirty_le_mul_coprime
    (hd2 g₁ hg₁G hg₁g) (hd2 g₂ hg₂G hg₂g) (hd2 g₃ hg₃G hg₃g)
    (key g₁ hg₁G g₂ hg₂G (Ne.symm hg₂g₁))
    (key g₁ hg₁G g₃ hg₃G (Ne.symm hg₃g₁))
    (key g₂ hg₂G g₃ hg₃G (Ne.symm hg₃g₂))
  have p12 := (key g₁ hg₁G g₂ hg₂G (Ne.symm hg₂g₁)).mul_dvd_of_dvd_of_dvd
    (hdvdg g₁ hg₁G hg₁g) (hdvdg g₂ hg₂G hg₂g)
  have c3 : Nat.Coprime ((G.erase g₁).gcd id * (G.erase g₂).gcd id)
      ((G.erase g₃).gcd id) :=
    Nat.Coprime.mul_left (key g₁ hg₁G g₃ hg₃G (Ne.symm hg₃g₁))
      (key g₂ hg₂G g₃ hg₃G (Ne.symm hg₃g₂))
  have p123 := c3.mul_dvd_of_dvd_of_dvd p12 (hdvdg g₃ hg₃G hg₃g)
  exact le_trans h30 (Nat.le_of_dvd hg0 p123)

/-- Scaling transport for subset sums (needed by 3.10's `G'/δ` recursion). -/
theorem subsetSums_map_mul (c : ℕ) (S : Multiset ℕ) :
    subsetSums (S.map (c * ·)) = (subsetSums S).image (c * ·) := by
  induction S using Multiset.induction with
  | empty => simp
  | cons x S ih =>
      rw [Multiset.map_cons, subsetSums_cons, subsetSums_cons, ih,
        Finset.image_union, Finset.image_image, Finset.image_image]
      congr 1
      have hfun : ((c * ·) ∘ (x + ·)) = ((c * x + ·) ∘ (c * ·)) := by
        funext u
        simp only [Function.comp_apply]
        ring
      rw [hfun]

/-- Finset gcd commutes with dividing out a common factor. -/
lemma finset_gcd_image_div {s : Finset ℕ} {c : ℕ}
    (h : ∀ x ∈ s, c ∣ x) : (s.image (· / c)).gcd id * c = s.gcd id := by
  induction s using Finset.induction with
  | empty => simp
  | insert x s hx ih =>
      rw [Finset.image_insert, Finset.gcd_insert, Finset.gcd_insert]
      have hcx : c ∣ x := h x (Finset.mem_insert_self _ _)
      have ih' := ih fun y hy => h y (Finset.mem_insert_of_mem hy)
      simp only [id_eq]
      rw [← ih']
      show Nat.gcd (x / c) ((Finset.image (· / c) s).gcd id) * c =
        Nat.gcd x ((Finset.image (· / c) s).gcd id * c)
      rw [← Nat.gcd_mul_right, Nat.div_mul_cancel hcx]

/-- **3.10's budget inequality, closed by the `≥ 30` bound alone** — the
`δ = 2` corner needs only `M ≥ 8 ≤ 30`, so the `M ≤ 130` minimal-alphabet
enumeration NEVER enters the formal proof. -/
lemma minimal_budget {δ M : ℕ} (hδ : 2 ≤ δ) (h3δ : 3 * δ ≤ M) (h30 : 30 ≤ M) :
    M / δ + 2 * δ - 1 ≤ M - 1 := by
  rcases Nat.eq_or_lt_of_le hδ with hδ2 | hδ3
  · have hδ2' : δ = 2 := hδ2.symm
    subst hδ2'
    omega
  · have h1 : M / δ ≤ M / 3 := Nat.div_le_div_left hδ3 (by omega)
    have h2 : δ ≤ M / 3 := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
    have h3 : M / 3 * 3 ≤ M := Nat.div_mul_le_self M 3
    omega

/-- Local copy of the Euclid remainder bound (the Staircase one is private). -/
private lemma lt_div_add_one_mul_self' (n : ℕ) {d : ℕ} (hd : 0 < d) :
    n < (n / d + 1) * d := by
  have h1 := Nat.div_add_mod n d
  have h2 := Nat.mod_lt n hd
  have h3 : (n / d + 1) * d = d * (n / d) + d := by ring
  omega

/-- **3.10**: minimal alphabets with `|G| ≥ 4`, by the outer strong induction
(recursing to `max H = M/δ < M` for `H := (G.erase (min G))/δ`), Graham fill
inside `H`, δ-scaling (`subsetSums_map_mul`), and residue bridging with
copies of `min G`; budget closes via `minimal_structure`'s `≥ 30` bound. -/
theorem sharp_of_minimal {M : ℕ} (ih : ∀ M', M' < M → SharpAt M')
    {G : Finset ℕ} (hpos : ∀ g ∈ G, 0 < g) (hcard : 4 ≤ G.card)
    (hgcd : G.gcd id = 1) (hmax : ∀ g ∈ G, g ≤ M) (hM : M ∈ G)
    (hmin : ∀ e ∈ G, (G.erase e).gcd id ≠ 1) :
    ∃ S : Multiset ℕ, (∀ w ∈ S, w ∈ G) ∧ S.card ≤ M - 1 ∧
      HasRun (subsetSums S) M := by
  classical
  have h30 := minimal_structure hpos hcard hgcd hmin
  have hM30 : 30 ≤ M := h30 M hM
  have hM0 : 0 < M := by omega
  -- the minimum a and the rest G'
  have hGne : G.Nonempty := ⟨M, hM⟩
  set a : ℕ := G.min' hGne with hadef
  have haG : a ∈ G := G.min'_mem hGne
  have ha0 : 0 < a := hpos a haG
  have ha_le : ∀ x ∈ G, a ≤ x := fun x hx => G.min'_le x hx
  have ha_lt : ∀ x ∈ G, x ≠ a → a < x := fun x hx hxa =>
    lt_of_le_of_ne (ha_le x hx) (Ne.symm hxa)
  set G' : Finset ℕ := G.erase a with hG'def
  have hG'card : 3 ≤ G'.card := by
    have h := Finset.card_erase_of_mem haG
    rw [← hG'def] at h
    omega
  have hG'sub : ∀ x ∈ G', x ∈ G := fun x hx => Finset.mem_erase.mp hx |>.2
  have hG'ne_a : ∀ x ∈ G', x ≠ a := fun x hx => Finset.mem_erase.mp hx |>.1
  have haM : a < M := by
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < G'.card)
    have hxG := hG'sub x hx
    have h1 := ha_lt x hxG (hG'ne_a x hx)
    have h2 := hmax x hxG
    -- a < x ≤ M, and if a = M then x > M
    rcases Nat.lt_or_ge a M with h | h
    · exact h
    · have := hmax a haG
      omega
  have hMG' : M ∈ G' := Finset.mem_erase.mpr ⟨by omega, hM⟩
  -- δ and the rescaled alphabet H
  set δ : ℕ := G'.gcd id with hδdef
  have hδdvd : ∀ x ∈ G', δ ∣ x := fun x hx => Finset.gcd_dvd hx
  have hδ2 : 2 ≤ δ := by
    have hne1 : δ ≠ 1 := hmin a haG
    have hne0 : δ ≠ 0 := by
      intro h0
      have hz := Finset.gcd_eq_zero_iff.mp h0 M hMG'
      simp only [id_eq] at hz
      omega
    omega
  have hδ0 : 0 < δ := by omega
  set H : Finset ℕ := G'.image (· / δ) with hHdef
  have hHval : ∀ v ∈ H, δ * v ∈ G' := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    rwa [Nat.mul_div_cancel' (hδdvd x hx)]
  have hHgcd : H.gcd id = 1 := by
    have h1 := finset_gcd_image_div hδdvd
    rw [← hδdef] at h1
    have h2 : H.gcd id * δ = δ := by rw [hHdef, h1, hδdef]
    have := Nat.eq_of_mul_eq_mul_right hδ0 (h2.trans (Nat.one_mul δ).symm)
    exact this
  have hHcard : 3 ≤ H.card := by
    have hinj : Set.InjOn (· / δ) G' := by
      intro x hx y hy hxy
      have hxy' : x / δ = y / δ := hxy
      have hx' := Nat.div_mul_cancel (hδdvd x hx)
      have hy' := Nat.div_mul_cancel (hδdvd y hy)
      have hmul := congrArg (· * δ) hxy'
      omega
    rw [hHdef, Finset.card_image_of_injOn hinj]
    omega
  set M' : ℕ := M / δ with hM'def
  have hδM : δ * M' = M := Nat.mul_div_cancel' (hδdvd M hMG')
  have hM'H : M' ∈ H := Finset.mem_image.mpr ⟨M, hMG', rfl⟩
  have hHle : ∀ v ∈ H, v ≤ M' := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    exact Nat.div_le_div_right (hmax x (hG'sub x hx))
  have hHpos : ∀ v ∈ H, 0 < v := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    exact Nat.div_pos (Nat.le_of_dvd (hpos x (hG'sub x hx)) (hδdvd x hx)) hδ0
  have hM'M : M' < M := rescaled_max_lt hδ2 hM0 (le_of_eq hδM)
  have hM'1 : 1 ≤ M' := hHpos M' hM'H
  -- three distinct δ-multiples give 3δ ≤ M
  have h3δ : 3 * δ ≤ M := by
    obtain ⟨x₁, hx₁⟩ := Finset.card_pos.mp (by omega : 0 < H.card)
    obtain ⟨x₂, hx₂⟩ := Finset.card_pos.mp
      (by have := Finset.card_erase_of_mem hx₁; omega : 0 < (H.erase x₁).card)
    obtain ⟨hx₂₁, hx₂H⟩ := Finset.mem_erase.mp hx₂
    obtain ⟨x₃, hx₃⟩ := Finset.card_pos.mp
      (by have := Finset.card_erase_of_mem hx₂
          have := Finset.card_erase_of_mem hx₁
          omega : 0 < ((H.erase x₁).erase x₂).card)
    obtain ⟨hx₃₂, hx₃'⟩ := Finset.mem_erase.mp hx₃
    obtain ⟨hx₃₁, hx₃H⟩ := Finset.mem_erase.mp hx₃'
    have hp1 := hHpos x₁ hx₁
    have hp2 := hHpos x₂ hx₂H
    have hp3 := hHpos x₃ hx₃H
    have hl1 := hHle x₁ hx₁
    have hl2 := hHle x₂ hx₂H
    have hl3 := hHle x₃ hx₃H
    -- among three distinct positives one is ≥ 3
    have hone : 3 ≤ x₁ ∨ 3 ≤ x₂ ∨ 3 ≤ x₃ := by omega
    have hM'3 : 3 ≤ M' := by omega
    calc 3 * δ ≤ M' * δ := Nat.mul_le_mul_right δ hM'3
      _ = M := by rw [Nat.mul_comm]; exact hδM
  -- apply the outer induction at M'
  obtain ⟨SH, hSH_mem, hSH_card, cH, hcH⟩ :=
    ih M' hM'M H hHpos hHcard hHgcd hHle hM'H
  -- fill with copies of a' := min H up to length ℓ
  have hHne : H.Nonempty := ⟨M', hM'H⟩
  set a' : ℕ := H.min' hHne with ha'def
  have ha'H : a' ∈ H := H.min'_mem hHne
  have ha'1 : 1 ≤ a' := hHpos a' ha'H
  have ha'M' : a' ≤ M' := hHle a' ha'H
  have haa' : a + 1 ≤ δ * a' := by
    have h1 := hHval a' ha'H
    have h2 := ha_lt (δ * a') (hG'sub _ h1) (hG'ne_a _ h1)
    omega
  set ℓ : ℕ := (M - 1 + (δ - 1) * a) / δ + 2 with hℓdef
  set t : ℕ := (ℓ - M' + a' - 1) / a' with htdef
  have hfill : HasRun (subsetSums (Multiset.replicate t a' + SH)) (M' + t * a') := by
    clear_value t
    clear htdef
    induction t with
    | zero => simpa using ⟨cH, hcH⟩
    | succ s ihs =>
        have h2 : a' ≤ M' + s * a' := by
          have : 0 ≤ s * a' := Nat.zero_le _
          omega
        have h3 := HasRun.cons_of_le h2 ihs
        have e1 : a' ::ₘ (Multiset.replicate s a' + SH) =
            Multiset.replicate (s + 1) a' + SH := by
          rw [Multiset.replicate_succ, Multiset.cons_add]
        have e2 : M' + s * a' + a' = M' + (s + 1) * a' := by ring
        rwa [e1, e2] at h3
  set L₂ : ℕ := M' + t * a' with hL₂def
  obtain ⟨c₂, hc₂⟩ := hfill
  -- length reached: L₂ ≥ ℓ
  have htℓ : ℓ ≤ L₂ := by
    have h1 := lt_div_add_one_mul_self' (ℓ - M' + a' - 1) ha'1
    rw [← htdef] at h1
    have hexp : (t + 1) * a' = t * a' + a' := by ring
    omega
  -- window arithmetic
  have hwin : M - 1 + (δ - 1) * a + 1 ≤ δ * (L₂ - 1) := by
    have h1 := Nat.div_add_mod (M - 1 + (δ - 1) * a) δ
    have h2 := Nat.mod_lt (M - 1 + (δ - 1) * a) hδ0
    have h3 : δ * (L₂ - 1) = δ * L₂ - δ := by
      have : 1 ≤ L₂ := by omega
      zify [this, show δ ≤ δ * L₂ from Nat.le_mul_of_pos_right δ (by omega)]
      ring
    have h4 : δ * ℓ ≤ δ * L₂ := Nat.mul_le_mul_left δ htℓ
    have h5 : δ * ℓ = δ * ((M - 1 + (δ - 1) * a) / δ) + 2 * δ := by
      rw [hℓdef]; ring
    omega
  -- t is small: t ≤ δ
  have htδ : t ≤ δ := by
    have hdiv : (M - 1 + (δ - 1) * a) / δ < M' + (δ - 1) * a' := by
      rw [Nat.div_lt_iff_lt_mul hδ0]
      have hb1 : (M' + (δ - 1) * a') * δ = M' * δ + (δ - 1) * a' * δ := by ring
      have hb2 : M' * δ = M := by rw [Nat.mul_comm]; exact hδM
      have hb3 : (δ - 1) * a ≤ (δ - 1) * a' * δ - (δ - 1) := by
        have h1 : (δ - 1) * a ≤ (δ - 1) * (δ * a' - 1) :=
          Nat.mul_le_mul_left _ (by omega)
        have h2 : (δ - 1) * (δ * a' - 1) = (δ - 1) * (δ * a') - (δ - 1) := by
          have : 1 ≤ δ * a' := by omega
          zify [this, show (δ-1) ≤ (δ-1) * (δ * a') from
            Nat.le_mul_of_pos_right _ (by omega)]
          ring
        have h3 : (δ - 1) * (δ * a') = (δ - 1) * a' * δ := by ring
        omega
      have hb4 : (δ - 1) ≤ (δ - 1) * a' * δ := by
        calc δ - 1 ≤ (δ - 1) * (a' * δ) :=
              Nat.le_mul_of_pos_right _ (by positivity)
          _ = (δ - 1) * a' * δ := by ring
      omega
    have h1 : ℓ - M' + a' - 1 < (δ + 1) * a' := by
      have hexp : (δ + 1) * a' = δ * a' + a' := by ring
      have h2 : ℓ ≤ M' + (δ - 1) * a' + 1 := by omega
      have h3 : (δ - 1) * a' + a' = δ * a' := by
        have h4 : ((δ - 1) + 1) * a' = (δ - 1) * a' + a' := by ring
        have h5 : (δ - 1) + 1 = δ := by omega
        rw [h5] at h4
        omega
      omega
    have h2 := (Nat.div_lt_iff_lt_mul ha'1).mpr h1
    rw [← htdef] at h2
    omega
  -- coprimality of a and δ
  have hCop : Nat.Coprime a δ := by
    have hdvd : Nat.gcd a δ ∣ G.gcd id := by
      apply Finset.dvd_gcd
      intro x hx
      by_cases hxa : x = a
      · subst hxa
        exact dvd_trans (Nat.gcd_dvd_left _ _) dvd_rfl
      · exact dvd_trans (Nat.gcd_dvd_right _ _)
          (hδdvd x (Finset.mem_erase.mpr ⟨hxa, hx⟩))
    rw [hgcd] at hdvd
    exact Nat.dvd_one.mp hdvd
  -- assemble the witness
  refine ⟨(Multiset.replicate t a' + SH).map (δ * ·) +
    Multiset.replicate (δ - 1) a, ?_, ?_, δ * c₂ + (δ - 1) * a, ?_⟩
  · intro w hw
    rcases Multiset.mem_add.mp hw with hw | hw
    · obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.mp hw
      rcases Multiset.mem_add.mp hv with hv | hv
      · have := Multiset.eq_of_mem_replicate hv
        subst this
        exact hG'sub _ (hHval a' ha'H)
      · exact hG'sub _ (hHval v (hSH_mem v hv))
    · have := Multiset.eq_of_mem_replicate hw
      subst this
      exact haG
  · simp only [Multiset.card_add, Multiset.card_map, Multiset.card_replicate]
    have hbudget := minimal_budget hδ2 h3δ hM30
    rw [← hM'def] at hbudget
    omega
  · intro i hi
    obtain ⟨k, -, hkδ, hres⟩ := exists_frame hδ0 hCop 0
      (δ * c₂ + (δ - 1) * a + i)
    set n : ℕ := δ * c₂ + (δ - 1) * a + i with hndef
    have hkδ' : k ≤ δ - 1 := by omega
    have hka_le : k * a ≤ (δ - 1) * a := Nat.mul_le_mul_right a hkδ'
    have hkan : k * a ≤ n := by omega
    have hdvd : δ ∣ n - k * a := (Nat.modEq_iff_dvd' hkan).mp hres
    set w : ℕ := (n - k * a) / δ with hwdef
    have hw : δ * w = n - k * a := Nat.mul_div_cancel' hdvd
    have hw_lo : c₂ ≤ w := by
      have h1 : δ * c₂ ≤ δ * w := by omega
      exact Nat.le_of_mul_le_mul_left h1 hδ0
    have hw_hi : w < c₂ + L₂ := by
      have h1 : δ * w ≤ δ * c₂ + (δ - 1) * a + M - 1 := by omega
      by_contra hcon
      push_neg at hcon
      have h2 : δ * (c₂ + L₂) ≤ δ * w := Nat.mul_le_mul_left δ hcon
      have h3 : δ * (c₂ + L₂) = δ * c₂ + δ * L₂ := by ring
      have h4 : δ * (L₂ - 1) + δ = δ * L₂ := by
        have : 1 ≤ L₂ := by omega
        zify [this, show δ ≤ δ * L₂ from Nat.le_mul_of_pos_right δ (by omega)]
        ring
      omega
    have hw_mem : w ∈ subsetSums (Multiset.replicate t a' + SH) := by
      have h1 : w = c₂ + (w - c₂) := by omega
      rw [h1]
      exact hc₂ (w - c₂) (by omega)
    have hδw : δ * w ∈ subsetSums ((Multiset.replicate t a' + SH).map (δ * ·)) := by
      rw [subsetSums_map_mul]
      exact Finset.mem_image_of_mem _ hw_mem
    have hka : k * a ∈ subsetSums (Multiset.replicate (δ - 1) a) := by
      apply mem_subsetSums.mpr
      refine ⟨Multiset.replicate k a, (Multiset.replicate_le_replicate a).mpr hkδ', ?_⟩
      simp [Multiset.sum_replicate, smul_eq_mul]
    have := add_mem_subsetSums_add hδw hka
    have heq : δ * w + k * a = n := by omega
    rwa [heq] at this

/-- Graham fill, packaged: a run of length `ℓ ≥ a₀` extends by `t` copies of
`a₀` to length `ℓ + t·a₀`. -/
lemma HasRun.add_replicate {S : Multiset ℕ} {ℓ a₀ : ℕ} (ha : a₀ ≤ ℓ)
    (h : HasRun (subsetSums S) ℓ) (t : ℕ) :
    HasRun (subsetSums (Multiset.replicate t a₀ + S)) (ℓ + t * a₀) := by
  induction t with
  | zero => simpa using h
  | succ s ihs =>
      have h2 : a₀ ≤ ℓ + s * a₀ := by
        have : 0 ≤ s * a₀ := Nat.zero_le _
        omega
      have h3 := HasRun.cons_of_le h2 ihs
      have e1 : a₀ ::ₘ (Multiset.replicate s a₀ + S) =
          Multiset.replicate (s + 1) a₀ + S := by
        rw [Multiset.replicate_succ, Multiset.cons_add]
      have e2 : ℓ + s * a₀ + a₀ = ℓ + (s + 1) * a₀ := by ring
      rwa [e1, e2] at h3

/-- **Reduction principle** (Lemmas 3.5–3.10 packaged): if all hard-core
triples at maximum `M` are sharp, and (SHARP) holds at every smaller
maximum, then (SHARP) holds at `M`. Assembly: `1 ∈ G` triviality; redundant
`e ≠ M` by inner card induction; redundant `e = M` by the outer `ih` at the
new maximum plus Graham fill; `|G| = 3` dispatch through L1/L2/L3/hard-core;
`|G| ≥ 4` minimal through `sharp_of_minimal`. -/
theorem sharpAt_of_hardcore (M : ℕ) (ih : ∀ M', M' < M → SharpAt M')
    (hc : ∀ a b, HardCore a b M → SharpTriple a b M) : SharpAt M := by
  classical
  suffices aux : ∀ n (G : Finset ℕ), G.card ≤ n → (∀ g ∈ G, 0 < g) →
      3 ≤ G.card → G.gcd id = 1 → (∀ g ∈ G, g ≤ M) → M ∈ G →
      ∃ S : Multiset ℕ, (∀ w ∈ S, w ∈ G) ∧ S.card ≤ M - 1 ∧
        HasRun (subsetSums S) M by
    intro G hpos hcard hgcd hle hMG
    exact aux G.card G le_rfl hpos hcard hgcd hle hMG
  intro n
  induction n with
  | zero =>
      intro G hcn _ hcard _ _ _
      exfalso
      omega
  | succ n ihn =>
      intro G hcn hpos hcard hgcd hle hMG
      have hM0 : 0 < M := hpos M hMG
      -- trivial case: 1 ∈ G
      by_cases h1G : 1 ∈ G
      · obtain ⟨S, hS1, hSc, hSr⟩ := sharp_of_one_mem M
        exact ⟨S, fun w hw => (hS1 w hw) ▸ h1G, hSc, hSr⟩
      -- redundant element?
      by_cases hred : ∃ e ∈ G, 4 ≤ G.card ∧ (G.erase e).gcd id = 1
      · obtain ⟨e, heG, hc4, hegcd⟩ := hred
        have hcard' : 3 ≤ (G.erase e).card := by
          have h := Finset.card_erase_of_mem heG
          omega
        by_cases heM : e = M
        · -- e = M removable: outer ih at the new maximum, then Graham fill
          rw [heM] at heG hegcd hcard'
          have hne : (G.erase M).Nonempty := Finset.card_pos.mp (by omega)
          set M₂ : ℕ := (G.erase M).max' hne with hM₂def
          have hM₂mem : M₂ ∈ G.erase M := Finset.max'_mem _ hne
          have hM₂G : M₂ ∈ G := (Finset.mem_erase.mp hM₂mem).2
          have hM₂M : M₂ < M :=
            lt_of_le_of_ne (hle M₂ hM₂G) (Finset.mem_erase.mp hM₂mem).1
          obtain ⟨S, hSmem, hScard, hSrun⟩ :=
            ih M₂ hM₂M (G.erase M)
              (fun g hg => hpos g ((Finset.mem_erase.mp hg).2))
              hcard' hegcd
              (fun g hg => Finset.le_max' _ g hg) hM₂mem
          -- fill with M − M₂ copies of the minimum of G.erase M
          set a₀ : ℕ := (G.erase M).min' hne with ha₀def
          have ha₀mem : a₀ ∈ G.erase M := Finset.min'_mem _ hne
          have ha₀G : a₀ ∈ G := (Finset.mem_erase.mp ha₀mem).2
          have ha₀1 : 1 ≤ a₀ := hpos a₀ ha₀G
          have ha₀M₂ : a₀ ≤ M₂ := Finset.le_max' _ a₀ ha₀mem
          obtain ⟨c₀, hc₀⟩ := hSrun
          have hfilled := HasRun.add_replicate ha₀M₂ ⟨c₀, hc₀⟩ (M - M₂)
          refine ⟨Multiset.replicate (M - M₂) a₀ + S, ?_, ?_, ?_⟩
          · intro w hw
            rcases Multiset.mem_add.mp hw with hw | hw
            · exact (Multiset.eq_of_mem_replicate hw) ▸ ha₀G
            · exact (Finset.mem_erase.mp (Finset.mem_coe.mp
                (Finset.mem_coe.mpr (hSmem w hw)))).2
          · simp only [Multiset.card_add, Multiset.card_replicate]
            have hM₂1 : 1 ≤ M₂ := hpos M₂ hM₂G
            omega
          · apply hfilled.of_le
            have h1 : (M - M₂) * 1 ≤ (M - M₂) * a₀ :=
              Nat.mul_le_mul_left _ ha₀1
            omega
        · -- e ≠ M: recurse on the cardinality
          have hMe : M ∈ G.erase e := Finset.mem_erase.mpr ⟨fun h => heM h.symm, hMG⟩
          have hcn' : (G.erase e).card ≤ n := by
            have h := Finset.card_erase_of_mem heG
            omega
          obtain ⟨S, hSmem, hScard, hSrun⟩ :=
            ihn (G.erase e) hcn'
              (fun g hg => hpos g ((Finset.mem_erase.mp hg).2))
              hcard' hegcd
              (fun g hg => hle g ((Finset.mem_erase.mp hg).2)) hMe
          exact ⟨S, fun w hw => (Finset.mem_erase.mp (hSmem w hw)).2, hScard, hSrun⟩
      · -- no redundant element: |G| = 3 dispatch, or |G| ≥ 4 minimal
        push_neg at hred
        by_cases hcard3 : G.card = 3
        · -- extract the triple a₀ < b₀ < M
          have hne : (G.erase M).Nonempty := by
            apply Finset.card_pos.mp
            have h := Finset.card_erase_of_mem hMG
            omega
          obtain ⟨x₁, hx₁⟩ := hne
          have hce := Finset.card_erase_of_mem hMG
          obtain ⟨x₂, hx₂⟩ := Finset.card_pos.mp
            (by have := Finset.card_erase_of_mem hx₁; omega :
              0 < ((G.erase M).erase x₁).card)
          obtain ⟨hx₂₁, hx₂'⟩ := Finset.mem_erase.mp hx₂
          obtain ⟨hx₁M, hx₁G⟩ := Finset.mem_erase.mp hx₁
          obtain ⟨hx₂M, hx₂G⟩ := Finset.mem_erase.mp hx₂'
          -- order them
          obtain ⟨a₀, b₀, ha₀G, hb₀G, ha₀M, hb₀M, hab⟩ :
              ∃ a₀ b₀, a₀ ∈ G ∧ b₀ ∈ G ∧ a₀ ≠ M ∧ b₀ ≠ M ∧ a₀ < b₀ := by
            rcases Nat.lt_or_ge x₁ x₂ with h | h
            · exact ⟨x₁, x₂, hx₁G, hx₂G, hx₁M, hx₂M, h⟩
            · have hlt : x₂ < x₁ := lt_of_le_of_ne h hx₂₁
              exact ⟨x₂, x₁, hx₂G, hx₁G, hx₂M, hx₁M, hlt⟩
          have ha₀2 : 2 ≤ a₀ := by
            have h1 := hpos a₀ ha₀G
            rcases Nat.lt_or_ge a₀ 2 with h | h
            · interval_cases a₀
              exact absurd ha₀G h1G
            · exact h
          have hb₀M' : b₀ < M := lt_of_le_of_ne (hle b₀ hb₀G) hb₀M
          -- G = {a₀, b₀, M}
          have hGeq : ({a₀, b₀, M} : Finset ℕ) = G := by
            apply Finset.eq_of_subset_of_card_le
            · intro w hw
              simp only [Finset.mem_insert, Finset.mem_singleton] at hw
              rcases hw with rfl | rfl | rfl <;> assumption
            · have h1 : a₀ ∉ ({b₀, M} : Finset ℕ) := by
                simp only [Finset.mem_insert, Finset.mem_singleton]
                push_neg
                exact ⟨by omega, ha₀M⟩
              have h2 : b₀ ∉ ({M} : Finset ℕ) := by
                simp only [Finset.mem_singleton]
                exact hb₀M
              have hcard_ins : ({a₀, b₀, M} : Finset ℕ).card = 3 := by
                rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
                  Finset.card_singleton]
              omega
          set d : ℕ := Nat.gcd a₀ b₀ with hddef
          have hd1 : 1 ≤ d := Nat.gcd_pos_of_pos_left _ (by omega)
          rcases Nat.lt_or_ge d 2 with hd1' | hd2
          · -- coprime pair: L1 / L2 / hard-core
            have hco : Nat.Coprime a₀ b₀ := by
              have : d = 1 := by omega
              rw [hddef] at this
              exact this
            rcases Nat.lt_or_ge (a₀ + b₀) M with hsum | hsum
            · -- a₀ + b₀ + 1 ≤ M: L1
              obtain ⟨S, hSel, hSc, hSr⟩ :=
                sharp_of_small_coprime_pair (M := M) (by omega : 0 < a₀)
                  (by omega : 0 < b₀) hco (by omega)
              exact ⟨S, fun w hw => by
                rcases hSel w hw with rfl | rfl <;> assumption, hSc, hSr⟩
            · rcases Nat.lt_or_ge (M + 1) (a₀ + b₀) with hsum2 | hsum2
              · -- a₀ + b₀ ≥ M + 2: hard core
                have hHC : HardCore a₀ b₀ M :=
                  ⟨by omega, hab, hb₀M', hco, by omega⟩
                obtain ⟨S, hSel, hSc, hSr⟩ := hc a₀ b₀ hHC
                exact ⟨S, fun w hw => by
                  rcases hSel w hw with rfl | rfl | rfl <;> assumption, hSc, hSr⟩
              · -- boundary: L2
                obtain ⟨S, hSel, hSc, hSr⟩ :=
                  sharp_of_boundary_pair (M := M) (by omega : 0 < a₀) hab hco
                    (by omega)
                exact ⟨S, fun w hw => by
                  rcases hSel w hw with rfl | rfl <;> assumption, hSc, hSr⟩
          · -- d ≥ 2: L3
            have hdvda := Nat.gcd_dvd_left a₀ b₀
            have hdvdb := Nat.gcd_dvd_right a₀ b₀
            rw [← hddef] at hdvda hdvdb
            have hd0 : 0 < d := by omega
            have hdM : Nat.Coprime M d := by
              have hdvd : Nat.gcd d M ∣ G.gcd id := by
                apply Finset.dvd_gcd
                intro w hw
                rw [← hGeq] at hw
                simp only [Finset.mem_insert, Finset.mem_singleton] at hw
                rcases hw with rfl | rfl | rfl
                · exact dvd_trans (Nat.gcd_dvd_left _ _) hdvda
                · exact dvd_trans (Nat.gcd_dvd_left _ _) hdvdb
                · exact Nat.gcd_dvd_right _ _
              rw [hgcd] at hdvd
              have := Nat.dvd_one.mp hdvd
              rw [Nat.coprime_comm]
              exact this
            have hα0 : 0 < a₀ / d := Nat.div_pos (Nat.le_of_dvd (by omega) hdvda) hd0
            have hαβ : a₀ / d < b₀ / d :=
              Nat.div_lt_div_of_lt_of_dvd hdvdb hab
            have hco' : Nat.Coprime (a₀ / d) (b₀ / d) := by
              rw [hddef]
              exact Nat.coprime_div_gcd_div_gcd (hddef ▸ hd0)
            have hb₀eq : d * (b₀ / d) = b₀ := Nat.mul_div_cancel' hdvdb
            have ha₀eq : d * (a₀ / d) = a₀ := Nat.mul_div_cancel' hdvda
            obtain ⟨S, hSel, hSc, hSr⟩ :=
              sharp_of_noncoprime_pair hd2 hα0 hαβ hco' hdM
                (by rw [hb₀eq]; omega)
            refine ⟨S, fun w hw => ?_, hSc, hSr⟩
            rcases hSel w hw with rfl | rfl | rfl
            · rw [ha₀eq]; exact ha₀G
            · rw [hb₀eq]; exact hb₀G
            · exact hMG
        · -- |G| ≥ 4 and minimal
          exact sharp_of_minimal ih hpos (by omega) hgcd hle hMG
            (fun e he => hred e he (by omega))

end Proof
end Erdos1112


/-! Flattened from Erdos1112Proof.Sharp.Lift. -/
/-
the lambda-lift lemma: mod-`a` frame certificates and the λ-lift.

`FrameCert a b M x Y Z` is THE certificate notion of the development: it is
stated per-residue (`M − 1 + height ≤ a·x` for some box representative of
every class mod `a`), which makes it
  (i)  kernel-decidable row-by-row (`frameCertOK`, Tables.lean),
  (ii) consumable by `frame_lemma` with `S := a·x − (M−1)`, and
  (iii) EXACTLY transported by the λ-lift: one step `(a,b,M) → (a,b+a,M+a)`
       adds `(j+k)·a ≤ (Y+Z)·a` to each height and `(Y+Z+1)·a` to the budget
       side, so the lift-stability hypothesis is literally the decided table
       property `Y + Z + 1 ≤ a` — no interface gap.
-/

namespace Erdos1112
namespace Proof

/-- A mod-`a` frame certificate: `M` positive (rules out the `M = 0`
degenerate where the ℕ-truncated budget fails to lift), within budget,
lift-stable, and every residue class mod `a` has a box representative whose
height clears the padding window per-residue. -/
def FrameCert (a b M x Y Z : ℕ) : Prop :=
  0 < M ∧ x + Y + Z ≤ M - 1 ∧ Y + Z + 1 ≤ a ∧
  ∀ ρ < a, ∃ j k, j ≤ Y ∧ k ≤ Z ∧ (j * b + k * M) % a = ρ ∧
    M - 1 + (j * b + k * M) ≤ a * x

/-- A frame certificate yields the (SHARP) witness for its triple. -/
theorem FrameCert.sharpTriple {a b M x Y Z : ℕ} (h : FrameCert a b M x Y Z) :
    SharpTriple a b M := by
  obtain ⟨hM, hbudget, hstab, hreps⟩ := h
  have ha : 0 < a := by omega
  have hMax : M - 1 ≤ a * x := by
    obtain ⟨j, k, -, -, -, hh⟩ := hreps 0 ha
    omega
  refine ⟨Multiset.replicate Y b + Multiset.replicate Z M +
    Multiset.replicate x a, ?_, ?_, a * x - (M - 1), ?_⟩
  · intro w hw
    rcases Multiset.mem_add.mp hw with hw | hw
    · rcases Multiset.mem_add.mp hw with hw | hw
      · exact Or.inr (Or.inl (Multiset.eq_of_mem_replicate hw))
      · exact Or.inr (Or.inr (Multiset.eq_of_mem_replicate hw))
    · exact Or.inl (Multiset.eq_of_mem_replicate hw)
  · simp only [Multiset.card_add, Multiset.card_replicate]
    omega
  · intro i hi
    apply frame_lemma ha (S := a * x - (M - 1))
    · intro ρ hρ
      obtain ⟨j, k, hj, hk, hres, hh⟩ := hreps ρ hρ
      exact ⟨j, k, hj, hk, hres, by omega⟩
    · omega
    · omega

/-- **the lambda-lift lemma (λ-lift), one step.** A frame certificate transports from
`(a, b, M)` to `(a, b+a, M+a)`, with padding grown by exactly the decided
stability margin `Y + Z + 1 ≤ a`. -/
theorem FrameCert.lift {a b M x Y Z : ℕ} (h : FrameCert a b M x Y Z) :
    FrameCert a (b + a) (M + a) (x + (Y + Z + 1)) Y Z := by
  obtain ⟨hM, hbudget, hstab, hreps⟩ := h
  refine ⟨by omega, by omega, hstab, ?_⟩
  intro ρ hρ
  obtain ⟨j, k, hj, hk, hres, hh⟩ := hreps ρ hρ
  have h1 : j * (b + a) + k * (M + a) = j * b + k * M + (j + k) * a := by ring
  refine ⟨j, k, hj, hk, ?_, ?_⟩
  · rw [h1, Nat.add_mul_mod_self_right]
    exact hres
  · have h2 : (j + k) * a ≤ (Y + Z) * a := Nat.mul_le_mul_right a (by omega)
    have h3 : a * (x + (Y + Z + 1)) = a * x + (Y + Z + 1) * a := by ring
    have h4 : (Y + Z + 1) * a = (Y + Z) * a + a := by ring
    omega

/-- **the lambda-lift lemma, iterated**: the whole λ-chain above a certified base. -/
theorem FrameCert.lift_iter {a b M x Y Z : ℕ} (h : FrameCert a b M x Y Z) :
    ∀ lam : ℕ, FrameCert a (b + lam * a) (M + lam * a)
      (x + lam * (Y + Z + 1)) Y Z := by
  intro lam
  induction lam with
  | zero => simpa using h
  | succ lam ih =>
      have step := ih.lift
      have e1 : b + lam * a + a = b + (lam + 1) * a := by ring
      have e2 : M + lam * a + a = M + (lam + 1) * a := by ring
      have e3 : x + lam * (Y + Z + 1) + (Y + Z + 1) = x + (lam + 1) * (Y + Z + 1) := by
        ring
      rwa [e1, e2, e3] at step

end Proof
end Erdos1112


/-! Flattened from Erdos1112Proof.Sharp.CaseD. -/
/-
Case D (the Case-D lemma): `a ∣ M` — half-price padding.
Paper: the bounded subset-sum covering section.

Construction: residues mod `a` are covered by `a−1` copies of `b`
(`gcd(a,b) = 1`); padding uses `x = q−1` copies of `a` and `z = xeff/q`
copies of `M = qa` (each `M` worth `q` units of `a` — the "half-price"
trick). Run start `c₀ = (a−1)·b`; for `n ∈ [c₀, c₀+M−1]` pick the residue
rep `j·b`, then `(n − j·b)/a = i + q·k` with `i ≤ q−1`, `k ≤ z`. Budget
`(a−1)+(q−1)+z ≤ M−1` closes because `xeff/q ≤ a−1` and `(q−2)(a−1) ≥ 0`.
-/

namespace Erdos1112
namespace Proof

/-- Coarse coverage: for `q ≥ 1`, every `t ≤ (q−1) + q·z` is `i + q·k` with
`i ≤ q−1`, `k ≤ z` (the `M`-blocks overlap because `x = q−1`). -/
private lemma coarse_cover {q z t : ℕ} (hq : 0 < q) (ht : t ≤ (q - 1) + q * z) :
    ∃ i k, i ≤ q - 1 ∧ k ≤ z ∧ t = i + q * k := by
  have hb : (z + 1) * q = q * z + q := by ring
  have hlt : t < (z + 1) * q := by omega
  have hkz : t / q ≤ z := by
    have := (Nat.div_lt_iff_lt_mul hq).mpr hlt
    omega
  have hmod := Nat.div_add_mod t q
  have hmq := Nat.mod_lt t hq
  exact ⟨t % q, t / q, by omega, hkz, by omega⟩

/-- Budget bound: with `M = a·q`, `a ≥ 3`, `q ≥ 2`, `z ≤ a−1`, the multiset of
size `(a−1)+(q−1)+z` fits within `M−1`. -/
private lemma caseD_budget {a q z M : ℕ} (ha : 3 ≤ a) (hq : 2 ≤ q)
    (hM : M = a * q) (hz : z ≤ a - 1) : (a - 1) + (q - 1) + z ≤ M - 1 := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 3 := ⟨a - 3, by omega⟩
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 2 := ⟨q - 2, by omega⟩
  subst hM
  have hexp : (a' + 3) * (q' + 2) = a' * q' + 2 * a' + 3 * q' + 6 := by ring
  omega

/-- Effective padding fits: `⌈((a−1)b + M − 1)/a⌉` (as a floor `xeff`) is
`≤ M − 1`. -/
private lemma caseD_xeff {a b M : ℕ} (ha : 3 ≤ a) (hb : b + 1 ≤ M) :
    ((a - 1) * b + M - 1) / a ≤ M - 1 := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  have hle : (a' + 1 - 1) * b + M - 1 ≤ (a' + 1) * (M - 1) := by
    have he : a' + 1 - 1 = a' := by omega
    rw [he]
    have hexp : (a' + 1) * (M - 1) = a' * (M - 1) + (M - 1) := by ring
    have hcb : a' * b ≤ a' * (M - 1) := Nat.mul_le_mul_left _ (by omega)
    omega
  calc ((a' + 1 - 1) * b + M - 1) / (a' + 1)
      ≤ ((a' + 1) * (M - 1)) / (a' + 1) := Nat.div_le_div_right hle
    _ = M - 1 := Nat.mul_div_cancel_left _ (by omega)

set_option maxHeartbeats 800000 in
/-- **Case D**: hard-core triple with `a ∣ M`. -/
theorem caseD {a b M : ℕ} (hc : HardCore a b M) (hD : a ∣ M) :
    SharpTriple a b M := by
  have ha3 := hc.three_le
  obtain ⟨ha0, hab, hbM, hco, hδ⟩ := hc
  obtain ⟨q, hq⟩ := hD                    -- `M = a * q`
  have hq2 : 2 ≤ q := by
    rcases Nat.lt_or_ge q 2 with h | h
    · interval_cases q <;> omega
    · exact h
  have hM1 : 1 ≤ M := by omega
  -- effective padding and the split `(x, z)`
  set xeff : ℕ := ((a - 1) * b + M - 1) / a with hxeffdef
  set z : ℕ := xeff / q with hzdef
  -- `xeff ≤ M − 1`
  have hxeff_le : xeff ≤ M - 1 := caseD_xeff ha3 (by omega)
  -- `z ≤ a − 1`
  have hz_lt : z < a := by
    have h1 : z ≤ (M - 1) / q := Nat.div_le_div_right hxeff_le
    have h2 : (M - 1) / q < a := by
      rw [Nat.div_lt_iff_lt_mul (by omega : 0 < q)]
      omega
    omega
  have hz_le : z ≤ a - 1 := by omega
  -- `a * xeff ≤ (a-1)*b + M - 1`  and  `xeff ≤ x + q*z`
  have haxeff : a * xeff ≤ (a - 1) * b + M - 1 := by
    have h := Nat.div_add_mod ((a - 1) * b + M - 1) a
    rw [← hxeffdef] at h
    omega
  have hqz : xeff ≤ (q - 1) + q * z := by
    have h := Nat.div_add_mod xeff q
    rw [← hzdef] at h
    have hmq := Nat.mod_lt xeff (by omega : 0 < q)
    omega
  -- the multiset and its budget
  refine ⟨Multiset.replicate (a - 1) b + Multiset.replicate (q - 1) a +
    Multiset.replicate z M, ?_, ?_, (a - 1) * b, ?_⟩
  · intro w hw
    rcases Multiset.mem_add.mp hw with hw | hw
    · rcases Multiset.mem_add.mp hw with hw | hw
      · exact Or.inr (Or.inl (Multiset.eq_of_mem_replicate hw))
      · exact Or.inl (Multiset.eq_of_mem_replicate hw)
    · exact Or.inr (Or.inr (Multiset.eq_of_mem_replicate hw))
  · simp only [Multiset.card_add, Multiset.card_replicate]
    exact caseD_budget ha3 hq2 hq hz_le
  · -- the run `[(a-1)*b, (a-1)*b + M - 1]`
    intro i hi
    set n : ℕ := (a - 1) * b + i with hndef
    -- residue rep `j * b` with `j ≤ a-1`
    obtain ⟨j, -, hja, hres⟩ := exists_frame ha0 hco.symm 0 n
    have hja' : j ≤ a - 1 := by omega
    have hjb_le : j * b ≤ (a - 1) * b := Nat.mul_le_mul_right b hja'
    have hjbn : j * b ≤ n := by omega
    have hdvd : a ∣ n - j * b := (Nat.modEq_iff_dvd' hjbn).mp hres
    set t : ℕ := (n - j * b) / a with htdef
    have hat : a * t = n - j * b := Nat.mul_div_cancel' hdvd
    -- `t ≤ xeff ≤ x + q*z`
    have htxeff : t ≤ xeff := by
      have h1 : n - j * b ≤ (a - 1) * b + M - 1 := by omega
      exact Nat.div_le_div_right h1
    have htqz : t ≤ (q - 1) + q * z := le_trans htxeff hqz
    obtain ⟨i', k, hi', hk, htik⟩ := coarse_cover (by omega : 0 < q) htqz
    -- assemble the subset sum
    refine mem_subsetSums.mpr ⟨Multiset.replicate j b + Multiset.replicate i' a +
      Multiset.replicate k M, ?_, ?_⟩
    · exact add_le_add (add_le_add
        ((Multiset.replicate_le_replicate b).mpr hja')
        ((Multiset.replicate_le_replicate a).mpr hi'))
        ((Multiset.replicate_le_replicate M).mpr hk)
    · simp only [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul]
      -- `j*b + i'*a + k*M = n`
      have hkM : k * M = a * (q * k) := by rw [hq]; ring
      have hai : i' * a = a * i' := Nat.mul_comm _ _
      have hexp : a * t = a * i' + a * (q * k) := by rw [htik]; ring
      omega

end Proof
end Erdos1112


/-! Flattened from Erdos1112Proof.Sharp.CaseP. -/
/-
Case P (Lemmas 3.12/3.13/3.14 + three explicit certificates):
`a ∣ b + M` — the η = −1 line. Sub-regimes: r = 3 (M < 2a), r = 4
(M = 2a + t), M ≥ 2a + 4, plus the three exceptional triples
(3,7,8), (4,9,11), (5,12,13). Paper: the bounded subset-sum covering section.

Unified route: a *pair-frame* construction covers every
`η = −1` triple at once. Writing `b + M = r·a` (`r ≥ 3`), the multiset
`(x, y, z) = (r−1, ⌈(M−r)/2⌉, ⌊(M−r)/2⌋)` of budget `M − 1` realizes a run
of `M` consecutive integers: a `(b, M)` pair is a residue-free mover worth
`r` grid units of `a`, and `r − 1` copies of `a` supply the fine residue.
`caseP_large` uses the `FrameCert` route where `M ≥ 2a + 4` makes
the budget slack ample; `caseP_r3`/`caseP_r4` and the three certificates all
go through the pair construction `caseP_pair`.
-/

namespace Erdos1112
namespace Proof

/-- the ETAneg lemma (ETAneg; `a ∣ b + M`, `M ≥ 2a + 4`).

`FrameCert` route: with `Y = ⌈(a−1)/2⌉ = a/2`, `Z = ⌊(a−1)/2⌋ = (a−1)/2`
(so `Y + Z = a − 1`) and `x = M − a`, every residue `ρ` mod `a` has a box
representative — either `(w, 0)` (`w ≤ Y`, height `w·b`) or `(0, a−w)`
(height `(a−w)·M`), by the signed cover `j·b + k·M ≡ (j−k)·b (mod a)`. The
budget corner (`Y·b`, `a` even, `b = M−1`) is vacuous because `a ∣ b + M`
with `a` even forces `b + M` even, hence `b ≤ M − 2`. -/
theorem caseP_large {a b M : ℕ} (hc : HardCore a b M) (hP : a ∣ (b + M))
    (hM : 2 * a + 4 ≤ M) : SharpTriple a b M := by
  have ha3 := hc.three_le
  obtain ⟨ha0, hab, hbM, hco, hδ⟩ := hc
  set Y : ℕ := a / 2 with hYdef
  set Z : ℕ := (a - 1) / 2 with hZdef
  have hYZ : Y + Z = a - 1 := by rw [hYdef, hZdef]; omega
  have h2Y_le : 2 * Y ≤ a := by rw [hYdef]; omega
  have h2Y_ge : a ≤ 2 * Y + 1 := by rw [hYdef]; omega
  have h2Z1 : 2 * Z + 1 ≤ a := by rw [hZdef]; omega
  -- budget: `M − 1 + Z·M ≤ a·(M − a)`
  have hZM : M - 1 + Z * M ≤ a * (M - a) := by
    zify [show a ≤ M by omega, show 1 ≤ M by omega]
    have h1 : 2 * (Z : ℤ) + 1 ≤ (a : ℤ) := by exact_mod_cast h2Z1
    nlinarith [mul_nonneg (show (0:ℤ) ≤ (a:ℤ) - 1 by omega)
        (show (0:ℤ) ≤ (M:ℤ) - 2 * a - 2 by omega),
      mul_nonneg (show (0:ℤ) ≤ (a:ℤ) - 1 - 2 * Z by omega)
        (show (0:ℤ) ≤ (M:ℤ) by positivity)]
  -- budget: `M − 1 + Y·b ≤ a·(M − a)` (the corner)
  have hYb : M - 1 + Y * b ≤ a * (M - a) := by
    rcases Nat.lt_or_ge (2 * Y) a with hodd | heven
    · -- `a` odd: `2Y + 1 = a`, use `b ≤ M − 1`
      have h2Y : 2 * Y + 1 = a := by omega
      zify [show a ≤ M by omega, show 1 ≤ M by omega]
      have hc : (2 * Y + 1 : ℤ) = (a : ℤ) := by exact_mod_cast h2Y
      have hYbb : 2 * ((Y : ℤ) * b) = ((a : ℤ) - 1) * b := by linear_combination b * hc
      nlinarith [hYbb, mul_nonneg (show (0:ℤ) ≤ (a:ℤ) - 1 by omega)
          (show (0:ℤ) ≤ (M:ℤ) - 2 * a - 1 by omega),
        mul_le_mul_of_nonneg_left (show (b:ℤ) ≤ (M:ℤ) - 1 by omega)
          (show (0:ℤ) ≤ (a:ℤ) - 1 by omega)]
    · -- `a` even: `2Y = a`, parity forces `b ≤ M − 2`
      have h2Y : 2 * Y = a := by omega
      have h2a : 2 ∣ a := ⟨Y, by omega⟩
      have h2bM : 2 ∣ (b + M) := h2a.trans hP
      have hb2 : b + 2 ≤ M := by omega
      zify [show a ≤ M by omega, show 1 ≤ M by omega]
      have hc : (2 * Y : ℤ) = (a : ℤ) := by exact_mod_cast h2Y
      have hYbb : 2 * ((Y : ℤ) * b) = (a : ℤ) * b := by linear_combination b * hc
      nlinarith [hYbb, mul_nonneg (show (0:ℤ) ≤ (a:ℤ) - 2 by omega)
          (show (0:ℤ) ≤ (M:ℤ) - 2 * a - 2 by omega),
        mul_le_mul_of_nonneg_left (show (b:ℤ) ≤ (M:ℤ) - 2 by omega)
          (show (0:ℤ) ≤ (a:ℤ) by omega)]
  -- the frame certificate
  have hcert : FrameCert a b M (M - a) Y Z := by
    refine ⟨by omega, by omega, by omega, ?_⟩
    intro ρ hρ
    obtain ⟨w0, -, hw0a, hw0res⟩ := exists_frame ha0 hco.symm 0 ρ
    rw [Nat.zero_add] at hw0a
    rw [Nat.mod_eq_of_lt hρ] at hw0res
    by_cases hw0Y : w0 ≤ Y
    · refine ⟨w0, 0, hw0Y, Nat.zero_le _, ?_, ?_⟩
      · simp only [Nat.zero_mul, Nat.add_zero]; exact hw0res
      · have hwb : w0 * b ≤ Y * b := Nat.mul_le_mul_right b hw0Y
        simp only [Nat.zero_mul, Nat.add_zero]
        exact le_trans (by omega : M - 1 + w0 * b ≤ M - 1 + Y * b) hYb
    · have hw0'le : a - w0 ≤ Z := by omega
      refine ⟨0, a - w0, Nat.zero_le _, hw0'le, ?_, ?_⟩
      · -- `((a − w0)·M) % a = ρ` via `(a − w0)·M ≡ w0·b (mod a)`
        simp only [Nat.zero_mul, Nat.zero_add]
        obtain ⟨w0', hw0'sum⟩ : ∃ w', w' + w0 = a := ⟨a - w0, by omega⟩
        rw [show a - w0 = w0' by omega]
        rw [← hw0res]
        have h1 : w0' * M ≡ w0' * M + w0 * (b + M) [MOD a] :=
          (Nat.modEq_iff_dvd' (Nat.le_add_right _ _)).mpr (by
            rw [Nat.add_sub_cancel_left]; exact hP.mul_left w0)
        have h2 : w0' * M + w0 * (b + M) = a * M + w0 * b := by
          rw [← hw0'sum]; ring
        have h3 : a * M + w0 * b ≡ w0 * b [MOD a] := by
          have hz : a * M ≡ 0 [MOD a] := (Nat.modEq_zero_iff_dvd).mpr ⟨M, rfl⟩
          have hz' := hz.add_right (w0 * b)
          rwa [zero_add] at hz'
        calc w0' * M ≡ w0' * M + w0 * (b + M) [MOD a] := h1
          _ = a * M + w0 * b := h2
          _ ≡ w0 * b [MOD a] := h3
      · have hwM : (a - w0) * M ≤ Z * M := Nat.mul_le_mul_right M hw0'le
        simp only [Nat.zero_mul, Nat.zero_add]
        exact le_trans (by omega : M - 1 + (a - w0) * M ≤ M - 1 + Z * M) hZM
  exact hcert.sharpTriple

/-- **The pair-frame construction** (Lemmas 3.12/3.13 template, uniform in `r`).

With `b + M = r·a` (`r ≥ 3`), the multiset `(x, y, z) = (r−1, ⌈(M−r)/2⌉,
⌊(M−r)/2⌋)` realizes a run of `M` consecutive integers starting at
`max(p·b, q·M)` (`p = ⌊a/2⌋`, `q = ⌈a/2⌉−1`). A `(b, M)` pair sums to `r·a`
(a residue-free mover of `r` grid units of `a`); `r−1` copies of `a` give the
fine residue `i`. For a target `n`, pick the signed representative `w`
(`w·b ≡ n mod a`): if `w ≥ 0` spend `w` extra `b`'s, else `−w` extra `M`'s.
The four budget inequalities `E1,E2,F1,F2` (proved per-`r` by the caller)
place `n` inside the covered interval. -/
lemma caseP_pair {a b M r : ℕ}
    (hc : HardCore a b M) (hr : 3 ≤ r) (hP : b + M = r * a)
    (hE1 : (a - 1) * b + M - 1 ≤ a * (r * ((M - r) / 2) + (r - 1)))
    (hE2 : ((a - 1) / 2) * (b + M) + M - 1 ≤ a * (r * ((M - r) / 2) + (r - 1)))
    (hF1 : (a / 2) * (b + M) + M - 1 ≤ a * (r * ((M - r + 1) / 2) + (r - 1)))
    (hF2 : a * M - 1 ≤ a * (r * ((M - r + 1) / 2) + (r - 1))) :
    SharpTriple a b M := by
  have ha3 := hc.three_le
  obtain ⟨ha0, hab, hbM, hco, hδ⟩ := hc
  have hrpos : 0 < r := by omega
  set x : ℕ := r - 1 with hxdef
  set z : ℕ := (M - r) / 2 with hzdef
  set y : ℕ := (M - r + 1) / 2 with hydef
  set p : ℕ := a / 2 with hpdef
  set q : ℕ := (a - 1) / 2 with hqdef
  -- `M ≥ a + r − 1` (from `b < M`, i.e. `ra ≤ 2M − 1`)
  have hMar : a + r - 1 ≤ M := by
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 3 := ⟨r - 3, by omega⟩
    have hexp : (r' + 3) * a = r' * a + 3 * a := by ring
    have h2M : r' * a + 3 * a + 1 ≤ 2 * M := by omega
    have hr'a : 3 * r' ≤ r' * a := by
      have h := Nat.mul_le_mul_left r' ha3; omega
    omega
  have hpq : p + q = a - 1 := by rw [hpdef, hqdef]; omega
  have hyz : y + z = M - r := by rw [hydef, hzdef]; omega
  have hzy : z ≤ y := by rw [hydef, hzdef]; omega
  have hbud : x + y + z = M - 1 := by rw [hxdef]; omega
  have hpy : p ≤ y := by rw [hpdef, hydef]; omega
  have hqz : q ≤ z := by rw [hqdef, hzdef]; omega
  set low : ℕ := max (p * b) (q * M) with hlowdef
  -- `low + M − 1 ≤ a·(r·z + x)` and the `+q·b` variant (rz-group: E1, E2)
  have hpqM : p * M + q * M = (a - 1) * M := by rw [← Nat.add_mul, hpq]
  have hpqb : p * b + q * b = (a - 1) * b := by rw [← Nat.add_mul, hpq]
  have haM : (a - 1) * M + M = a * M := by rw [← Nat.succ_mul]; congr 1; omega
  have hqbM : q * b + q * M = q * (b + M) := by rw [← Nat.mul_add]
  have hpbM : p * b + p * M = p * (b + M) := by rw [← Nat.mul_add]
  have hlow_rz : low + M - 1 ≤ a * (r * z + x) := by
    rw [hlowdef]
    rcases le_total (p * b) (q * M) with h | h
    · rw [max_eq_right h]
      have hle : q * M ≤ q * (b + M) := Nat.mul_le_mul_left q (by omega)
      omega
    · rw [max_eq_left h]
      have hle : p * b ≤ (a - 1) * b := Nat.mul_le_mul_right b (by omega)
      omega
  have hlow_rz_qb : low + M - 1 + q * b ≤ a * (r * z + x) := by
    rw [hlowdef]
    rcases le_total (p * b) (q * M) with h | h
    · rw [max_eq_right h]; omega
    · rw [max_eq_left h]
      have : p * b + q * b = (a - 1) * b := hpqb
      omega
  have hlow_ry_pM : low + M - 1 + p * M ≤ a * (r * y + x) := by
    rw [hlowdef]
    rcases le_total (p * b) (q * M) with h | h
    · rw [max_eq_right h]; omega
    · rw [max_eq_left h]; omega
  -- assemble
  refine ⟨stair a b M x y z, ?_, ?_, low, ?_⟩
  · intro w hw
    simp only [stair, Multiset.mem_add, Multiset.mem_replicate] at hw
    rcases hw with (⟨_, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · simp only [stair, Multiset.card_add, Multiset.card_replicate]; omega
  · intro i hi
    set n : ℕ := low + i with hndef
    obtain ⟨w0, -, hw0a, hw0res⟩ := exists_frame ha0 hco.symm 0 n
    rw [Nat.zero_add] at hw0a
    by_cases hw0p : w0 ≤ p
    · -- `w ≥ 0` branch: `w0` extra `b`'s
      have hw0b_le : w0 * b ≤ n := by
        have h1 : w0 * b ≤ p * b := Nat.mul_le_mul_right b hw0p
        have h2 : p * b ≤ low := le_max_left _ _
        omega
      have hdvd : a ∣ n - w0 * b := (Nat.modEq_iff_dvd' hw0b_le).mp hw0res
      set A : ℕ := (n - w0 * b) / a with hAdef
      have hAa : a * A = n - w0 * b := Nat.mul_div_cancel' hdvd
      have hnA : n = w0 * b + a * A := by omega
      set k' : ℕ := A / r with hk'def
      set i' : ℕ := A % r with hi'def
      have hAik : A = i' + r * k' := by
        rw [hi'def, hk'def, Nat.add_comm]; exact (Nat.div_add_mod A r).symm
      have hi'x : i' ≤ x := by rw [hi'def, hxdef]; have := Nat.mod_lt A hrpos; omega
      -- `A ≤ r·z + x`
      have hAle : a * A ≤ a * (r * z + x) := by
        have : a * A ≤ low + M - 1 := by omega
        omega
      have hC1 : A ≤ r * z + x := Nat.le_of_mul_le_mul_left hAle ha0
      have hk'z : k' ≤ z := by
        rw [hk'def]
        have hlt : A < (z + 1) * r := by
          have : (z + 1) * r = r * z + r := by ring
          omega
        exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hrpos).mpr hlt)
      -- `A + r·w0 ≤ r·y + x`
      have harw : a * r * w0 = w0 * b + w0 * M := by
        rw [show w0 * b + w0 * M = w0 * (b + M) from by ring, hP]; ring
      have hC2mul : a * (A + r * w0) = n + w0 * M := by
        have hexp : a * (A + r * w0) = a * A + a * r * w0 := by ring
        rw [hexp, harw]; omega
      have hC2 : A + r * w0 ≤ r * y + x := by
        apply Nat.le_of_mul_le_mul_left _ ha0
        rw [hC2mul]
        have hw0M : w0 * M ≤ p * M := Nat.mul_le_mul_right M hw0p
        omega
      have hjy : w0 + k' ≤ y := by
        have hrk : k' * r ≤ A := by rw [hk'def]; exact Nat.div_mul_le_self A r
        have hlt : (w0 + k') * r < (y + 1) * r := by
          have e1 : (w0 + k') * r = r * w0 + k' * r := by ring
          have e2 : (y + 1) * r = r * y + r := by ring
          omega
        exact Nat.lt_succ_iff.mp (lt_of_mul_lt_mul_right hlt (Nat.zero_le _))
      refine mem_subsetSums.mpr ⟨Multiset.replicate i' a +
        Multiset.replicate (w0 + k') b + Multiset.replicate k' M, ?_, ?_⟩
      · exact add_le_add (add_le_add
          ((Multiset.replicate_le_replicate a).mpr hi'x)
          ((Multiset.replicate_le_replicate b).mpr hjy))
          ((Multiset.replicate_le_replicate M).mpr hk'z)
      · simp only [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul]
        have hkbM : k' * b + k' * M = k' * (r * a) := by rw [← hP]; ring
        have hstep : i' * a + (w0 + k') * b + k' * M = w0 * b + a * A := by
          have expand : i' * a + (w0 + k') * b + k' * M
              = i' * a + w0 * b + (k' * b + k' * M) := by ring
          rw [expand, hkbM, hAik]; ring
        rw [hstep]; exact hnA.symm
    · -- `w < 0` branch: `v = a − w0` extra `M`'s
      have hw0p' : p < w0 := by omega
      set v : ℕ := a - w0 with hvdef
      have hv1 : 1 ≤ v := by omega
      have hvq : v ≤ q := by omega
      have hvw0 : v + w0 = a := by omega
      -- `v·M ≡ w0·b (mod a)` hence `v·M ≡ n (mod a)`
      have hvM_res : (v * M) % a = n % a := by
        have h1 : v * M ≡ v * M + w0 * (b + M) [MOD a] :=
          (Nat.modEq_iff_dvd' (Nat.le_add_right _ _)).mpr (by
            rw [Nat.add_sub_cancel_left, hP]; exact ⟨w0 * r, by ring⟩)
        have h2 : v * M + w0 * (b + M) = a * M + w0 * b := by
          rw [← hvw0]; ring
        have h3 : a * M + w0 * b ≡ w0 * b [MOD a] := by
          have hz : a * M ≡ 0 [MOD a] := (Nat.modEq_zero_iff_dvd).mpr ⟨M, rfl⟩
          have hz' := hz.add_right (w0 * b)
          rwa [zero_add] at hz'
        have hchain : v * M ≡ w0 * b [MOD a] := by
          calc v * M ≡ v * M + w0 * (b + M) [MOD a] := h1
            _ = a * M + w0 * b := h2
            _ ≡ w0 * b [MOD a] := h3
        exact hchain.trans hw0res
      have hvM_le : v * M ≤ n := by
        have h1 : v * M ≤ q * M := Nat.mul_le_mul_right M hvq
        have h2 : q * M ≤ low := le_max_right _ _
        omega
      have hdvd : a ∣ n - v * M := (Nat.modEq_iff_dvd' hvM_le).mp hvM_res
      set A : ℕ := (n - v * M) / a with hAdef
      have hAa : a * A = n - v * M := Nat.mul_div_cancel' hdvd
      have hnA : n = v * M + a * A := by omega
      set j' : ℕ := A / r with hj'def
      set i' : ℕ := A % r with hi'def
      have hAij : A = i' + r * j' := by
        rw [hi'def, hj'def, Nat.add_comm]; exact (Nat.div_add_mod A r).symm
      have hi'x : i' ≤ x := by rw [hi'def, hxdef]; have := Nat.mod_lt A hrpos; omega
      -- `A ≤ r·y + x` (from rz-group + z ≤ y)
      have hAle : a * A ≤ a * (r * y + x) := by
        have hle1 : a * A ≤ low + M - 1 := by omega
        have hle2 : a * (r * z + x) ≤ a * (r * y + x) :=
          Nat.mul_le_mul_left a (by
            have : r * z ≤ r * y := Nat.mul_le_mul_left r hzy
            omega)
        omega
      have hjy : j' ≤ y := by
        have hAry : A ≤ r * y + x := Nat.le_of_mul_le_mul_left hAle ha0
        rw [hj'def]
        have hlt : A < (y + 1) * r := by
          have : (y + 1) * r = r * y + r := by ring
          omega
        exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hrpos).mpr hlt)
      -- `A + r·v ≤ r·z + x`
      have hbrv : a * r * v = v * b + v * M := by
        rw [show v * b + v * M = v * (b + M) from by ring, hP]; ring
      have hD2mul : a * (A + r * v) = n + v * b := by
        have hexp : a * (A + r * v) = a * A + a * r * v := by ring
        rw [hexp, hbrv]; omega
      have hD2 : A + r * v ≤ r * z + x := by
        apply Nat.le_of_mul_le_mul_left _ ha0
        rw [hD2mul]
        have hvb : v * b ≤ q * b := Nat.mul_le_mul_right b hvq
        omega
      have hk'z : j' + v ≤ z := by
        have hrj : j' * r ≤ A := by rw [hj'def]; exact Nat.div_mul_le_self A r
        have hlt : (j' + v) * r < (z + 1) * r := by
          have e1 : (j' + v) * r = r * v + j' * r := by ring
          have e2 : (z + 1) * r = r * z + r := by ring
          omega
        exact Nat.lt_succ_iff.mp (lt_of_mul_lt_mul_right hlt (Nat.zero_le _))
      refine mem_subsetSums.mpr ⟨Multiset.replicate i' a +
        Multiset.replicate j' b + Multiset.replicate (j' + v) M, ?_, ?_⟩
      · exact add_le_add (add_le_add
          ((Multiset.replicate_le_replicate a).mpr hi'x)
          ((Multiset.replicate_le_replicate b).mpr hjy))
          ((Multiset.replicate_le_replicate M).mpr hk'z)
      · simp only [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul]
        have hjbM : j' * b + j' * M = j' * (r * a) := by rw [← hP]; ring
        have hstep : i' * a + j' * b + (j' + v) * M = v * M + a * A := by
          have expand : i' * a + j' * b + (j' + v) * M
              = i' * a + (j' * b + j' * M) + v * M := by ring
          rw [expand, hjbM, hAij]; ring
        rw [hstep]; exact hnA.symm

set_option maxHeartbeats 1600000 in
/-- the r = 3 pair lemma (G′; `b + M = 3a`, i.e. `M < 2a`) — pair construction, `r = 3`. -/
theorem caseP_r3 {a b M : ℕ} (hc : HardCore a b M) (hP : b + M = 3 * a) :
    SharpTriple a b M := by
  have ha3 := hc.three_le
  have ha0 : 0 < a := hc.1
  have hab : a < b := hc.2.1
  have hbM : b < M := hc.2.2.1
  have hδ : M + 2 ≤ a + b := hc.2.2.2.2
  have hbz : (b : ℤ) + M = 3 * a := by exact_mod_cast hP
  have hbM' : (b : ℤ) < M := by exact_mod_cast hbM
  have hMb : (0 : ℤ) ≤ 2 * (M : ℤ) - 3 * a := by linarith
  have hM2a : (M : ℤ) < 2 * a := by
    have : M < 2 * a := by omega
    exact_mod_cast this
  refine caseP_pair (r := 3) hc (by norm_num) hP ?_ ?_ ?_ ?_
  · -- E1
    rcases Nat.lt_or_ge a 8 with hs | hs
    · interval_cases a <;> omega
    · set z := (M - 3) / 2 with hzd
      have hzz : (M : ℤ) ≤ 2 * z + 4 := by exact_mod_cast (show M ≤ 2 * z + 4 from by omega)
      have haa : (8 : ℤ) ≤ a := by exact_mod_cast hs
      have hbe : (b : ℤ) = 3 * a - M := by linarith
      have hpos : 1 ≤ (a - 1) * b + M := le_trans (by omega) (Nat.le_add_left M _)
      zify [show 1 ≤ a by omega, hpos]
      rw [hbe]
      nlinarith [hzz, haa, hMb, hM2a,
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) (show (0:ℤ) ≤ 2 * (z:ℤ) + 4 - M by linarith),
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) hMb,
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) (show (0:ℤ) ≤ (a:ℤ) - 8 by linarith)]
  · -- E2
    rcases Nat.lt_or_ge a 8 with hs | hs
    · interval_cases a <;> omega
    · set z := (M - 3) / 2 with hzd
      set q := (a - 1) / 2 with hqd
      have hzz : (M : ℤ) ≤ 2 * z + 4 := by exact_mod_cast (show M ≤ 2 * z + 4 from by omega)
      have hqq : (2 : ℤ) * q + 1 ≤ (a : ℤ) := by exact_mod_cast (show 2 * q + 1 ≤ a from by omega)
      have haa : (8 : ℤ) ≤ a := by exact_mod_cast hs
      have hpos : 1 ≤ q * (b + M) + M := le_trans (by omega) (Nat.le_add_left M _)
      zify [hpos]
      rw [hbz]
      nlinarith [hzz, hqq, haa, hMb, hM2a,
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) (show (0:ℤ) ≤ 2 * (z:ℤ) + 4 - M by linarith),
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) (show (0:ℤ) ≤ (a:ℤ) - 1 - 2 * q by linarith),
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) hMb,
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) (show (0:ℤ) ≤ (a:ℤ) - 8 by linarith)]
  · -- F1
    rcases Nat.lt_or_ge a 8 with hs | hs
    · interval_cases a <;> omega
    · set y := (M - 3 + 1) / 2 with hyd
      set p := a / 2 with hpd
      have hyy : (M : ℤ) ≤ 2 * y + 3 := by exact_mod_cast (show M ≤ 2 * y + 3 from by omega)
      have hpp : (2 : ℤ) * p ≤ (a : ℤ) := by exact_mod_cast (show 2 * p ≤ a from by omega)
      have haa : (8 : ℤ) ≤ a := by exact_mod_cast hs
      have hpos : 1 ≤ p * (b + M) + M := le_trans (by omega) (Nat.le_add_left M _)
      zify [hpos]
      rw [hbz]
      nlinarith [hyy, hpp, haa, hMb, hM2a,
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) (show (0:ℤ) ≤ 2 * (y:ℤ) + 3 - M by linarith),
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) (show (0:ℤ) ≤ (a:ℤ) - 2 * p by linarith),
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) hMb,
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) (show (0:ℤ) ≤ (a:ℤ) - 8 by linarith)]
  · -- F2
    rcases Nat.lt_or_ge a 8 with hs | hs
    · interval_cases a <;> omega
    · set y := (M - 3 + 1) / 2 with hyd
      have hyy : (M : ℤ) ≤ 2 * y + 3 := by exact_mod_cast (show M ≤ 2 * y + 3 from by omega)
      have haa : (8 : ℤ) ≤ a := by exact_mod_cast hs
      have hpos : 1 ≤ a * M := Nat.mul_pos ha0 (by omega : 0 < M)
      zify [hpos]
      nlinarith [hyy, haa, hMb, hM2a,
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) (show (0:ℤ) ≤ 2 * (y:ℤ) + 3 - M by linarith),
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) hMb,
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) (show (0:ℤ) ≤ (a:ℤ) - 8 by linarith)]

set_option maxHeartbeats 1600000 in
/-- the r = 4 pair lemma (G; `b + M = 4a`) — pair construction, `r = 4`. -/
theorem caseP_r4 {a b M : ℕ} (hc : HardCore a b M) (hP : b + M = 4 * a) :
    SharpTriple a b M := by
  have ha3 := hc.three_le
  have ha0 : 0 < a := hc.1
  have hab : a < b := hc.2.1
  have hbM : b < M := hc.2.2.1
  have hδ : M + 2 ≤ a + b := hc.2.2.2.2
  have hbz : (b : ℤ) + M = 4 * a := by exact_mod_cast hP
  have hbM' : (b : ℤ) < M := by exact_mod_cast hbM
  have hMb : (0 : ℤ) ≤ 2 * (M : ℤ) - 4 * a := by linarith
  have hM3a : (M : ℤ) < 3 * a := by
    have : M < 3 * a := by omega
    exact_mod_cast this
  refine caseP_pair (r := 4) hc (by norm_num) hP ?_ ?_ ?_ ?_
  · -- E1
    rcases Nat.lt_or_ge a 8 with hs | hs
    · interval_cases a <;> omega
    · set z := (M - 4) / 2 with hzd
      have hzz : (M : ℤ) ≤ 2 * z + 5 := by exact_mod_cast (show M ≤ 2 * z + 5 from by omega)
      have haa : (8 : ℤ) ≤ a := by exact_mod_cast hs
      have hbe : (b : ℤ) = 4 * a - M := by linarith
      have hpos : 1 ≤ (a - 1) * b + M := le_trans (by omega) (Nat.le_add_left M _)
      zify [show 1 ≤ a by omega, hpos]
      rw [hbe]
      nlinarith [hzz, haa, hMb, hM3a,
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) (show (0:ℤ) ≤ 2 * (z:ℤ) + 5 - M by linarith),
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) hMb,
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) (show (0:ℤ) ≤ (a:ℤ) - 8 by linarith)]
  · -- E2
    rcases Nat.lt_or_ge a 8 with hs | hs
    · interval_cases a <;> omega
    · set z := (M - 4) / 2 with hzd
      set q := (a - 1) / 2 with hqd
      have hzz : (M : ℤ) ≤ 2 * z + 5 := by exact_mod_cast (show M ≤ 2 * z + 5 from by omega)
      have hqq : (2 : ℤ) * q + 1 ≤ (a : ℤ) := by exact_mod_cast (show 2 * q + 1 ≤ a from by omega)
      have haa : (8 : ℤ) ≤ a := by exact_mod_cast hs
      have hpos : 1 ≤ q * (b + M) + M := le_trans (by omega) (Nat.le_add_left M _)
      zify [hpos]
      rw [hbz]
      nlinarith [hzz, hqq, haa, hMb, hM3a,
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) (show (0:ℤ) ≤ 2 * (z:ℤ) + 5 - M by linarith),
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) (show (0:ℤ) ≤ (a:ℤ) - 1 - 2 * q by linarith),
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) hMb,
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) (show (0:ℤ) ≤ (a:ℤ) - 8 by linarith)]
  · -- F1
    rcases Nat.lt_or_ge a 8 with hs | hs
    · interval_cases a <;> omega
    · set y := (M - 4 + 1) / 2 with hyd
      set p := a / 2 with hpd
      have hyy : (M : ℤ) ≤ 2 * y + 4 := by exact_mod_cast (show M ≤ 2 * y + 4 from by omega)
      have hpp : (2 : ℤ) * p ≤ (a : ℤ) := by exact_mod_cast (show 2 * p ≤ a from by omega)
      have haa : (8 : ℤ) ≤ a := by exact_mod_cast hs
      have hpos : 1 ≤ p * (b + M) + M := le_trans (by omega) (Nat.le_add_left M _)
      zify [hpos]
      rw [hbz]
      nlinarith [hyy, hpp, haa, hMb, hM3a,
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) (show (0:ℤ) ≤ 2 * (y:ℤ) + 4 - M by linarith),
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) (show (0:ℤ) ≤ (a:ℤ) - 2 * p by linarith),
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) hMb,
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) (show (0:ℤ) ≤ (a:ℤ) - 8 by linarith)]
  · -- F2
    rcases Nat.lt_or_ge a 8 with hs | hs
    · interval_cases a <;> omega
    · set y := (M - 4 + 1) / 2 with hyd
      have hyy : (M : ℤ) ≤ 2 * y + 4 := by exact_mod_cast (show M ≤ 2 * y + 4 from by omega)
      have haa : (8 : ℤ) ≤ a := by exact_mod_cast hs
      have hpos : 1 ≤ a * M := Nat.mul_pos ha0 (by omega : 0 < M)
      zify [hpos]
      nlinarith [hyy, haa, hMb, hM3a,
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) (show (0:ℤ) ≤ 2 * (y:ℤ) + 4 - M by linarith),
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) hMb,
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) (show (0:ℤ) ≤ (a:ℤ) - 8 by linarith)]

/-- **Case P assembled** (Exhaustion of Case P, the subset-sum section): every `η = −1` triple
`b + M = r·a` is covered — `r = 3` (the r = 3 pair lemma), `r = 4` (the r = 4 pair lemma),
`M ≥ 2a + 4` (the ETAneg lemma), and the `r ≥ 5, M < 2a + 4` corner (the three
explicit triples `(3,7,8), (4,9,11), (5,12,13)`) directly by the pair
construction. -/
theorem caseP {a b M : ℕ} (hc : HardCore a b M) (hP : a ∣ (b + M)) :
    SharpTriple a b M := by
  have ha3 := hc.three_le
  have ha0 : 0 < a := hc.1
  have hab : a < b := hc.2.1
  have hbM : b < M := hc.2.2.1
  have hδ : M + 2 ≤ a + b := hc.2.2.2.2
  obtain ⟨r, hr⟩ := hP
  have hr3 : 3 ≤ r := by
    by_contra hcon
    push_neg at hcon
    interval_cases r <;> omega
  rcases Nat.lt_or_ge M (2 * a + 4) with hMs | hMl
  · -- `M < 2a + 4`
    have hM2 : a * r < 4 * a + 8 := by omega
    rcases Nat.lt_or_ge r 5 with hr5 | hr5
    · -- `r = 3` or `r = 4`
      interval_cases r
      · exact caseP_r3 hc (by omega)
      · exact caseP_r4 hc (by omega)
    · -- `r ≥ 5` : `a` bounded, finite corner
      have ha8 : a < 8 := by
        have h5a : 5 * a ≤ a * r := by
          have := Nat.mul_le_mul_left a hr5; omega
        omega
      have hr7 : r ≤ 6 := by
        by_contra hcon
        push_neg at hcon
        have h7a : 7 * a ≤ a * r := by
          have := Nat.mul_le_mul_left a hcon; omega
        omega
      interval_cases r
      · interval_cases a <;>
          exact caseP_pair (r := 5) hc (by norm_num) (by omega) (by omega) (by omega)
            (by omega) (by omega)
      · interval_cases a <;>
          exact caseP_pair (r := 6) hc (by norm_num) (by omega) (by omega) (by omega)
            (by omega) (by omega)
  · -- `M ≥ 2a + 4`
    exact caseP_large hc ⟨r, hr⟩ hMl

end Proof
end Erdos1112


/-! Flattened from Erdos1112Proof.Sharp.CaseL. -/
/-
Case L (the Case-L lemma): scaled consecutive triples
`G = {a, a+g, a+2g}` (i.e. `e = h`). Three sub-cases by parity of `a` and
`g = 1` vs `g ≥ 2`, via the staircase short merge (c) / base form (d). Paper: the bounded subset-sum covering section.

Notation: `g := b − a = M − b`, so `b = a + g`, `M = a + 2g`,
`(e′, μ′) = (1, 2)`, `C′ = 0`, `V′ = 2z + 1`. Multiset `(x, 1, z)` with
`z = ⌈(a−2)/2⌉`, `x = ⌊(a−2)/2⌋ + 2g`, budget `a + 2g − 1 = M − 1`.
The parity split uses `a = 2z + 2` (even) / `a = 2w + 3` (odd) to keep all
arithmetic subtraction-free.
-/

namespace Erdos1112
namespace Proof

/-- Assembly: a covered interval `[lo, hi]` of length `≥ M` with budget
`≤ M − 1` gives `SharpTriple`. -/
private lemma caseL_assemble {a b M x y z lo hi : ℕ}
    (hcov : ∀ n, lo ≤ n → n ≤ hi → n ∈ subsetSums (stair a b M x y z))
    (hlen : lo + M - 1 ≤ hi) (hM : 1 ≤ M) (hbud : x + y + z ≤ M - 1) :
    SharpTriple a b M := by
  refine ⟨stair a b M x y z, ?_, ?_, lo, ?_⟩
  · intro w hw
    simp only [stair, Multiset.mem_add, Multiset.mem_replicate] at hw
    rcases hw with (⟨_, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · simp only [stair, Multiset.card_add, Multiset.card_replicate]; omega
  · intro i hi'
    exact hcov (lo + i) (Nat.le_add_right _ _) (by omega)

set_option maxHeartbeats 1600000 in
/-- **Case L**: hard-core triple with `e = h` (`b − a = M − b`). -/
theorem caseL {a b M : ℕ} (hc : HardCore a b M) (hL : b - a = M - b) :
    SharpTriple a b M := by
  have ha3 := hc.three_le
  have hhb := hc.h_bounds        -- `1 ≤ M − b ≤ a − 2`
  have hcop : Nat.Coprime a (b - a) := hc.coprime_a_e
  obtain ⟨ha0, hab, hbM, hco, hδ⟩ := hc
  set g : ℕ := b - a with hgdef0
  have hba : b - a = g := rfl
  have hg1 : 1 ≤ g := by omega
  have hg_le : g ≤ a - 2 := by omega
  have hb_eq : b = a + g := by omega
  have hM_eq : M = a + 2 * g := by omega
  have hMa : M - a = 2 * g := by omega
  have hM1 : 1 ≤ M := by omega
  -- the shared StairSetup with `(e′, μ′) = (1, 2)`
  have hStair : StairSetup a b M g 1 2 := by
    refine ⟨hab, hbM, ha0, ?_, ?_, ?_⟩
    · rw [hba, hMa]; exact (Nat.gcd_eq_left ⟨2, by ring⟩).symm
    · rw [hba, Nat.div_self (by omega : 0 < g)]
    · rw [hMa, Nat.mul_div_cancel 2 (by omega : 0 < g)]
  have hC' : (0 : ℕ) = (1 - 1) * (2 - 1) := by norm_num
  rcases Nat.even_or_odd a with ⟨r, hr⟩ | ⟨s, hs⟩
  · -- even: reparametrize `a = 2v + 2` (`v ≥ 1`)
    obtain ⟨v, hv⟩ : ∃ v, a = 2 * v + 2 := ⟨r - 1, by omega⟩
    have hv1 : 1 ≤ v := by omega
    -- multiset `(x, 1, z) = (v + 2g, 1, v)`,  `V' = 2v + 1`
    have hVeq : (2 * v + 1) + (0 : ℕ) = 1 * 1 + 2 * v := by omega
    have hcov := staircase_phase_extended (x := v + 2 * g) (y := 1) (z := v)
      (V' := 2 * v + 1) hStair hC' hVeq
      (by rw [← hba] at hcop; exact hcop) (by omega) (by omega)
      (by omega : 1 + v + g ≤ v + 2 * g) (by omega : a + 0 ≤ (2 * v + 1) + 1)
    refine caseL_assemble hcov ?_ hM1 (by omega)
    -- lo = (v+g)*a, hi = (v+g+1)*a + g*(2v+1)
    have hlo : (1 + v + g - 1) * a = (v + g) * a := by congr 1; omega
    have hhi : (v + 2 * g - g + 1) * a = (v + g) * a + a := by
      have : v + 2 * g - g + 1 = (v + g) + 1 := by omega
      rw [this]; ring
    have hprod : g * 3 ≤ g * (2 * v + 1) := Nat.mul_le_mul_left g (by omega)
    rw [hlo, hhi]; omega
  · -- odd: reparametrize `a = 2u + 3` (`u ≥ 0`)
    obtain ⟨u, hu⟩ : ∃ u, a = 2 * u + 3 := ⟨s - 1, by omega⟩
    rcases Nat.lt_or_ge g 2 with hg | hg2
    · -- `g = 1`  →  short merge (3.3c);  `(x, 1, z) = (u+2, 1, u+1)`
      have hgeq : g = 1 := by omega
      have hVeq : (2 * (u + 1) + 1) + (0 : ℕ) = 1 * 1 + 2 * (u + 1) := by omega
      have hcov := staircase_merge_c (x := u + 2) (y := 1) (z := u + 1)
        (V' := 2 * (u + 1) + 1) hStair hgeq hC' hVeq (by omega) (by omega)
        (by omega : u + 2 = 1 + (u + 1))
        (by omega)
      refine caseL_assemble hcov ?_ hM1 (by omega)
      have hcoef : (1 + (u + 1) + 1) * a = (1 + (u + 1)) * a + a := by ring
      rw [hcoef]; omega
    · -- `g ≥ 2`  →  extended form;  `(x, 1, z) = (u + 2g, 1, u+1)`,  `V' = 2u+3`
      have hVeq : (2 * (u + 1) + 1) + (0 : ℕ) = 1 * 1 + 2 * (u + 1) := by omega
      have hcov := staircase_phase_extended (x := u + 2 * g) (y := 1) (z := u + 1)
        (V' := 2 * (u + 1) + 1) hStair hC' hVeq
        (by rw [← hba] at hcop; exact hcop) (by omega) (by omega)
        (by omega : 1 + (u + 1) + g ≤ u + 2 * g)
        (by omega : a + 0 ≤ (2 * (u + 1) + 1) + 1)
      refine caseL_assemble hcov ?_ hM1 (by omega)
      -- lo = (u+1+g)*a, hi = (u+g+1)*a + g*(2u+3);  g*(2u+3) = g*a ≥ M-1
      have hlo : (1 + (u + 1) + g - 1) * a = (u + 1 + g) * a := by congr 1; omega
      have hhi : (u + 2 * g - g + 1) * a = (u + 1 + g) * a := by congr 1; omega
      have hVa : 2 * (u + 1) + 1 = a := by omega
      have h1 : 2 * (2 * u + 1) ≤ g * (2 * u + 1) := Nat.mul_le_mul_right _ (by omega)
      have h2 : g * a = g * (2 * u + 1) + 2 * g := by rw [hu]; ring
      have hga : a + 2 * g - 1 ≤ g * a := by omega
      rw [hlo, hhi, hVa]; omega

end Proof
end Erdos1112


/-! Flattened from Erdos1112Proof.Sharp.CaseE. -/
/-
Case E (the eta-box lemma): the universal η-box for `a ≥ 12`, `μ ≥ 12`
(with `a ∤ M`, `a ∤ b+M`). This branch carries the bulk of the hard core
(71,421 of the 83,251 triples with M ≤ 120). Paper: the bounded subset-sum covering section.

Route (mirrors the paper): with `η := M·b⁻¹ mod a` (`b` is a unit mod `a`
by `gcd(a,b) = 1`), the side hypotheses pin `η ∈ [2, a−2]`:
  * `η ≠ 0`  ⟺ `a ∤ M`,
  * `η ≠ a−1` ⟺ `a ∤ b+M`  (`b + M ≡ b(1+η)`),
  * `η ≠ 1`  from `h = M − b ∈ [1, a−2]` (hard core).
Set `t := min(η, a−η) ∈ [2, a/2]` and `(Y, Z) := (t−1, ⌊(a−1)/t⌋)`
(`⌊(a−1)/t⌋ = ⌈(a−t)/t⌉`). The box offsets `j·b + k·M ≡ b·(j + k·η) (mod a)`
sweep a complete residue system: `{j + k·t}` is `[0, t(Z+1)−1] ⊇ [0, a−1]`
when `t = η` (division algorithm), and `{j + k·(a−t)} ≡ {j − k·t}` covers
the mirrored interval when `t = a−η` (`eta_box_steps`). Hence
`(a, b, M, x, Y, Z)` with `x := ⌈(M−1+Y·b+Z·M)/a⌉` is a `FrameCert`; the
quadratic endpoint bound `2·(t+Z) ≤ a+4` (from `(t−2)(a−2t) ≥ 0`) plus
`M ≥ a+12` close the budget `x+Y+Z ≤ M−1` per the paper's threshold algebra
`a·σ ≤ (a−σ)·M`.
-/

namespace Erdos1112
namespace Proof

/-- Box coverage of `ℤ/a` by steps of `η`: every `w < a` is congruent to
`j + k·η (mod a)` with `j ≤ t−1`, `k ≤ ⌊(a−1)/t⌋` for `t := min(η, a−η)`.
For `t = η` this is the division algorithm `w = j + k·t`; for `t = a−η`
the step acts as `−t`, and `k := ⌈(a−w)/t⌉`, `j := k·t − (a−w)` gives
`j + k·η = (k−1)·a + w`. -/
private lemma eta_box_steps {a η w : ℕ} (hη1 : 1 ≤ η) (hηa : η + 1 ≤ a)
    (hw : w < a) :
    ∃ j k, j + 1 ≤ min η (a - η) ∧ k ≤ (a - 1) / min η (a - η) ∧
      (j + k * η) % a = w % a := by
  set t := min η (a - η) with htdef
  have ht1 : 1 ≤ t := by omega
  rcases le_total η (a - η) with hcase | hcase
  · -- `t = η`: division algorithm.
    have htη : t = η := by omega
    refine ⟨w % t, w / t, ?_, Nat.div_le_div_right (by omega), ?_⟩
    · have := Nat.mod_lt w (show 0 < t by omega)
      omega
    · rw [← htη, Nat.mod_add_div' w t]
  · -- `t = a − η`: the step `η = a − t` acts as `−t` mod `a`.
    have hηt : η + t = a := by omega
    rcases Nat.lt_or_ge w t with hwt | hwt
    · exact ⟨w, 0, by omega, Nat.zero_le _, by rw [Nat.zero_mul, Nat.add_zero]⟩
    · have hd1 := Nat.div_add_mod (a - w + t - 1) t
      have hd2 := Nat.mod_lt (a - w + t - 1) (show 0 < t by omega)
      have hd3 := Nat.div_mul_le_self (a - w + t - 1) t
      set k := (a - w + t - 1) / t with hkdef
      have hcomm : t * k = k * t := Nat.mul_comm t k
      have hklo : a - w ≤ k * t := by omega
      have hkhi : k * t ≤ a - w + t - 1 := hd3
      have hk1 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with hk0 | hk
        · rw [hk0, Nat.zero_mul] at hklo
          omega
        · exact hk
      refine ⟨k * t - (a - w), k, by omega, Nat.div_le_div_right (by omega), ?_⟩
      have hbr : k * η + k * t = k * a := by
        rw [← Nat.mul_add, hηt]
      have hone : (k - 1) * a + a = k * a := by
        have h : k - 1 + 1 = k := by omega
        calc (k - 1) * a + a = (k - 1 + 1) * a := by ring
          _ = k * a := by rw [h]
      have hjk : k * t - (a - w) + k * η = (k - 1) * a + w := by omega
      rw [hjk, Nat.add_comm, Nat.add_mul_mod_self_right]

/-- Ceiling-padding bounds: if `n ≤ a·B` then `x := ⌈n/a⌉ = (n+a−1)/a`
satisfies both `n ≤ a·x` and `x ≤ B`. -/
private lemma ceil_pad {a n B : ℕ} (ha : 0 < a) (hnB : n ≤ a * B) :
    n ≤ a * ((n + a - 1) / a) ∧ (n + a - 1) / a ≤ B := by
  constructor
  · have h1 := Nat.div_add_mod (n + a - 1) a
    have h2 := Nat.mod_lt (n + a - 1) ha
    omega
  · have h3 : n + a - 1 < (B + 1) * a := by
      have hexp : (B + 1) * a = a * B + a := by ring
      omega
    have h4 := (Nat.div_lt_iff_lt_mul ha).mpr h3
    omega

set_option maxHeartbeats 800000 in
/-- **Case E (η-box)**: `a ∤ M`, `a ∤ b + M`, `a ≥ 12`, `μ = M − a ≥ 12`. -/
theorem caseE {a b M : ℕ} (hc : HardCore a b M)
    (hnD : ¬ a ∣ M) (hnP : ¬ a ∣ (b + M))
    (ha : 12 ≤ a) (hμ : 12 ≤ M - a) : SharpTriple a b M := by
  obtain ⟨ha0, hab, hbM, hco, hδ⟩ := hc
  haveI : NeZero a := ⟨by omega⟩
  -- `b` is a unit mod `a`; `η := M·b⁻¹`.
  have hunit : IsUnit (b : ZMod a) := (ZMod.isUnit_iff_coprime b a).mpr hco.symm
  have hbmul : (b : ZMod a) * ↑hunit.unit⁻¹ = 1 := hunit.mul_val_inv
  set η : ℕ := ((M : ZMod a) * ↑hunit.unit⁻¹).val with hηdef
  have hηlt : η < a := ZMod.val_lt _
  have hηcast : (η : ZMod a) = (M : ZMod a) * ↑hunit.unit⁻¹ := by
    rw [hηdef, ZMod.natCast_val, ZMod.cast_id]
  have hbη : (b : ZMod a) * (η : ZMod a) = (M : ZMod a) := by
    rw [hηcast]
    calc (b : ZMod a) * ((M : ZMod a) * ↑hunit.unit⁻¹)
        = (M : ZMod a) * ((b : ZMod a) * ↑hunit.unit⁻¹) := by ring
      _ = (M : ZMod a) := by rw [hbmul, mul_one]
  -- η ∉ {0, 1, a−1}: the three excluded residue lines.
  have hη0 : η ≠ 0 := by
    intro h0
    apply hnD
    have hM0 : (M : ZMod a) = ((0 : ℕ) : ZMod a) := by
      rw [← hbη, h0]
      push_cast
      ring
    exact Nat.modEq_zero_iff_dvd.mp ((ZMod.natCast_eq_natCast_iff _ _ _).mp hM0)
  have hη1 : η ≠ 1 := by
    intro h1
    have hMb : (M : ZMod a) = ((b : ℕ) : ZMod a) := by
      rw [← hbη, h1]
      push_cast
      ring
    have hmb := (ZMod.natCast_eq_natCast_iff _ _ _).mp hMb
    have hdvd : a ∣ M - b := (Nat.modEq_iff_dvd' (le_of_lt hbM)).mp hmb.symm
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have hηa1 : η ≠ a - 1 := by
    intro he
    apply hnP
    have hm1 : ((a - 1 : ℕ) : ZMod a) = -1 := by
      have hself := ZMod.natCast_self a
      rw [Nat.cast_sub (by omega : 1 ≤ a), hself]
      push_cast
      ring
    have hsum : ((b + M : ℕ) : ZMod a) = ((0 : ℕ) : ZMod a) := by
      push_cast
      rw [← hbη, he, hm1]
      ring
    exact Nat.modEq_zero_iff_dvd.mp ((ZMod.natCast_eq_natCast_iff _ _ _).mp hsum)
  -- the box parameters
  set t : ℕ := min η (a - η) with htdef
  have ht2 : 2 ≤ t := by omega
  have h2t : 2 * t ≤ a := by omega
  set Z : ℕ := (a - 1) / t with hZdef
  have hZt : Z * t ≤ a - 1 := by
    rw [hZdef]
    exact Nat.div_mul_le_self _ _
  -- quadratic endpoint bound: 2·(t+Z) ≤ a+4 via (t−2)(a−2t) ≥ 0
  have hσ : 2 * (t + Z) ≤ a + 4 := by
    have h1 : (Z : ℤ) * t ≤ (a : ℤ) - 1 := by
      have h := hZt
      zify [show 1 ≤ a by omega] at h
      exact h
    have h2 : (2 : ℤ) ≤ (t : ℤ) := by exact_mod_cast ht2
    have h3 : 2 * (t : ℤ) ≤ (a : ℤ) := by exact_mod_cast h2t
    have hkeyZ : (t : ℤ) * (2 * ((t : ℤ) + (Z : ℤ))) ≤ (t : ℤ) * ((a : ℤ) + 4) := by
      nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ (t : ℤ) - 2)
        (by omega : (0 : ℤ) ≤ (a : ℤ) - 2 * (t : ℤ)), h1]
    have hkey : t * (2 * (t + Z)) ≤ t * (a + 4) := by exact_mod_cast hkeyZ
    exact Nat.le_of_mul_le_mul_left hkey (by omega)
  have htZM : t + Z ≤ M := by omega
  -- the budget inequality (paper: a·σ ≤ (a−σ)·M for σ = t+Z, M ≥ a+12)
  have hKey : M - 1 + ((t - 1) * b + Z * M) ≤ a * (M - (t + Z)) := by
    zify [show 1 ≤ t by omega, show 1 ≤ M by omega, htZM]
    have hσ' : 2 * ((t : ℤ) + (Z : ℤ)) ≤ (a : ℤ) + 4 := by exact_mod_cast hσ
    have haM : (a : ℤ) + 12 ≤ (M : ℤ) := by omega
    have ha12 : (12 : ℤ) ≤ (a : ℤ) := by exact_mod_cast ha
    have hbM' : (b : ℤ) ≤ (M : ℤ) - 1 := by omega
    have ht1' : (1 : ℤ) ≤ (t : ℤ) := by omega
    nlinarith [mul_le_mul_of_nonneg_left hbM' (by omega : (0 : ℤ) ≤ (t : ℤ) - 1),
      mul_nonneg (by omega : (0 : ℤ) ≤ (a : ℤ) - 4)
        (by omega : (0 : ℤ) ≤ (M : ℤ) - (a : ℤ) - 12),
      mul_nonneg (by omega : (0 : ℤ) ≤ (M : ℤ))
        (by omega : (0 : ℤ) ≤ (a : ℤ) + 4 - 2 * ((t : ℤ) + (Z : ℤ))),
      mul_nonneg (by omega : (0 : ℤ) ≤ (a : ℤ))
        (by omega : (0 : ℤ) ≤ (a : ℤ) + 4 - 2 * ((t : ℤ) + (Z : ℤ)))]
  obtain ⟨hax, hxB⟩ := ceil_pad (show 0 < a by omega) hKey
  set x : ℕ := (M - 1 + ((t - 1) * b + Z * M) + a - 1) / a with hxdef
  -- assemble the frame certificate
  have hcert : FrameCert a b M x (t - 1) Z := by
    refine ⟨by omega, by omega, by omega, ?_⟩
    intro ρ hρ
    set w : ℕ := ((ρ : ZMod a) * ↑hunit.unit⁻¹).val with hwdef
    have hwlt : w < a := ZMod.val_lt _
    have hwcast : (w : ZMod a) = (ρ : ZMod a) * ↑hunit.unit⁻¹ := by
      rw [hwdef, ZMod.natCast_val, ZMod.cast_id]
    have hbw : (b : ZMod a) * (w : ZMod a) = (ρ : ZMod a) := by
      rw [hwcast]
      calc (b : ZMod a) * ((ρ : ZMod a) * ↑hunit.unit⁻¹)
          = (ρ : ZMod a) * ((b : ZMod a) * ↑hunit.unit⁻¹) := by ring
        _ = (ρ : ZMod a) := by rw [hbmul, mul_one]
    obtain ⟨j, k, hjt, hkZ, hmod⟩ :=
      eta_box_steps (show 1 ≤ η by omega) (show η + 1 ≤ a by omega) hwlt
    rw [← htdef] at hjt hkZ
    rw [← hZdef] at hkZ
    refine ⟨j, k, by omega, hkZ, ?_, ?_⟩
    · -- residue class: j·b + k·M ≡ b·(j + k·η) ≡ b·w ≡ ρ (mod a)
      have hjkw : ((j + k * η : ℕ) : ZMod a) = ((w : ℕ) : ZMod a) :=
        (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
      have expand : ((j * b + k * M : ℕ) : ZMod a)
          = (b : ZMod a) * ((j + k * η : ℕ) : ZMod a) := by
        push_cast
        rw [← hbη]
        ring
      have hcast : ((j * b + k * M : ℕ) : ZMod a) = ((ρ : ℕ) : ZMod a) := by
        rw [expand, hjkw]
        exact hbw
      have hmodeq := (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
      rw [Nat.ModEq, Nat.mod_eq_of_lt hρ] at hmodeq
      exact hmodeq
    · -- height: the corner (t−1)·b + Z·M dominates, and x was chosen for it
      have hj' : j * b ≤ (t - 1) * b := Nat.mul_le_mul_right b (by omega)
      have hk' : k * M ≤ Z * M := Nat.mul_le_mul_right M hkZ
      omega
  exact hcert.sharpTriple

end Proof
end Erdos1112


/-! Flattened from Erdos1112Proof.Sharp.Tables. -/
/-
the subset-sum development certificate layer: the kernel-decidable frame-certificate checker
and its soundness theorem. Certificate DATA lives in `Sharp/TablesData.lean`
(6-tuples `(a, b, M, x, Y, Z)`, split into Table A and Table B).

All 360 table rows satisfy the per-residue frame condition
(`FrameCert`/`frameCertOK`), which is what the λ-lift transports, so one
certificate notion serves validity, lift-stability, and (SHARP)-witnessing
at once. Kernel `decide` only.
-/

namespace Erdos1112
namespace Proof

/-- Boolean checker for `FrameCert`, kernel-`decide`-friendly. -/
def frameCertOK : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ → Bool
  | (a, b, M, x, Y, Z) =>
    decide (0 < M) && decide (x + Y + Z ≤ M - 1) && decide (Y + Z + 1 ≤ a) &&
    ((List.range a).all fun ρ =>
      (List.range (Y + 1)).any fun j =>
        (List.range (Z + 1)).any fun k =>
          decide ((j * b + k * M) % a = ρ) &&
          decide (M - 1 + (j * b + k * M) ≤ a * x))

/-- **Checker soundness**: a passing row is a genuine frame certificate. -/
theorem frameCertOK_sound {a b M x Y Z : ℕ}
    (h : frameCertOK (a, b, M, x, Y, Z) = true) : FrameCert a b M x Y Z := by
  rw [frameCertOK] at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
    List.mem_range, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  refine ⟨h0, h1, h2, ?_⟩
  intro ρ hρ
  obtain ⟨j, hj, k, hk, hres, hht⟩ := h3 ρ hρ
  exact ⟨j, k, by omega, by omega, hres, hht⟩

/-- Convenience: a passing row yields its (SHARP) witness. -/
theorem frameCertOK_sharpTriple {a b M x Y Z : ℕ}
    (h : frameCertOK (a, b, M, x, Y, Z) = true) : SharpTriple a b M :=
  (frameCertOK_sound h).sharpTriple

end Proof
end Erdos1112


/-! Flattened from Erdos1112Proof.Sharp.TablesData. -/
/-
Certificate data for the bounded subset-sum covering lemma, as 6-tuples
`(a, b, M, x, Y, Z)`:
  * `certTableA` — the 158 Case-T exceptions certified directly here; with
    the 14-row `tSuppT` supplement (CaseTCore.lean) these form the paper's
    172-row Table A, each row used at exactly its own triple;
  * `certTableB` — the 178 Case-B class-base rows (the paper's Table B),
    each the root of a λ-lift chain (the paper's λ-lift lemma).
Every row is kernel-decided against `frameCertOK` — validity, budget and
lift-stability (`Y+Z+1 ≤ a`) in one decided property (no native_decide).
-/

namespace Erdos1112
namespace Proof

def certTableA : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (4, 9, 10, 7, 1, 1),
  (4, 13, 14, 10, 1, 1),
  (5, 8, 9, 5, 2, 1),
  (5, 9, 12, 7, 2, 1),
  (5, 11, 12, 7, 1, 2),
  (5, 11, 13, 8, 2, 1),
  (5, 12, 14, 9, 1, 2),
  (5, 13, 14, 8, 2, 1),
  (5, 13, 16, 10, 1, 2),
  (6, 11, 14, 9, 1, 2),
  (6, 11, 15, 9, 2, 1),
  (6, 13, 14, 9, 1, 2),
  (6, 13, 15, 10, 2, 1),
  (6, 13, 16, 10, 1, 2),
  (7, 10, 12, 7, 3, 1),
  (7, 10, 15, 8, 2, 2),
  (7, 11, 12, 7, 2, 2),
  (7, 11, 13, 7, 2, 2),
  (7, 11, 16, 8, 3, 1),
  (7, 12, 13, 7, 3, 1),
  (7, 12, 15, 8, 2, 2),
  (7, 13, 17, 9, 3, 1),
  (7, 13, 18, 9, 2, 2),
  (7, 15, 16, 9, 1, 3),
  (7, 15, 17, 9, 2, 2),
  (7, 15, 18, 10, 3, 1),
  (7, 16, 17, 10, 2, 2),
  (7, 16, 18, 11, 1, 3),
  (8, 11, 12, 7, 3, 1),
  (8, 11, 15, 9, 2, 2),
  (8, 13, 14, 7, 3, 2),
  (8, 13, 15, 8, 2, 2),
  (8, 13, 17, 10, 2, 2),
  (8, 15, 18, 9, 3, 2),
  (8, 15, 19, 11, 2, 2),
  (8, 17, 18, 11, 1, 3),
  (8, 17, 19, 10, 2, 2),
  (9, 13, 16, 8, 3, 2),
  (9, 13, 20, 9, 4, 1),
  (9, 14, 15, 8, 2, 2),
  (9, 14, 16, 9, 4, 1),
  (9, 14, 17, 9, 2, 3),
  (9, 14, 20, 9, 3, 2),
  (9, 16, 17, 9, 4, 1),
  (9, 16, 19, 10, 3, 2),
  (9, 17, 20, 11, 2, 3),
  (9, 19, 20, 11, 1, 4),
  (10, 13, 18, 10, 3, 2),
  (10, 13, 21, 9, 3, 2),
  (10, 17, 18, 9, 3, 2),
  (10, 17, 19, 9, 3, 2),
  (10, 17, 21, 10, 2, 3),
  (11, 14, 18, 9, 5, 1),
  (11, 14, 21, 10, 3, 2),
  (11, 15, 16, 7, 3, 2),
  (11, 15, 20, 9, 4, 2),
  (11, 16, 18, 8, 4, 2),
  (11, 16, 19, 10, 5, 1),
  (11, 16, 20, 9, 3, 2),
  (11, 17, 18, 8, 2, 3),
  (11, 18, 19, 9, 4, 3),
  (11, 18, 20, 11, 5, 1),
  (11, 18, 21, 10, 2, 3),
  (11, 19, 20, 9, 4, 2),
  (11, 20, 21, 11, 5, 1),
  (12, 17, 18, 10, 5, 1),
  (12, 17, 20, 10, 3, 2),
  (12, 17, 21, 10, 2, 3),
  (12, 17, 23, 12, 4, 2),
  (12, 19, 20, 10, 3, 2),
  (12, 19, 21, 11, 2, 3),
  (12, 19, 22, 11, 3, 4),
  (12, 19, 23, 11, 4, 2),
  (13, 16, 24, 11, 2, 4),
  (13, 17, 20, 9, 4, 2),
  (13, 17, 24, 10, 4, 4),
  (13, 18, 19, 9, 4, 2),
  (13, 18, 20, 9, 3, 3),
  (13, 18, 22, 11, 6, 1),
  (13, 18, 24, 11, 3, 3),
  (13, 19, 24, 10, 3, 3),
  (13, 20, 21, 10, 2, 4),
  (13, 20, 22, 10, 4, 2),
  (13, 20, 23, 12, 6, 1),
  (13, 20, 24, 11, 4, 2),
  (13, 21, 22, 10, 4, 4),
  (13, 21, 24, 11, 2, 4),
  (13, 22, 23, 11, 3, 3),
  (13, 22, 24, 13, 6, 1),
  (13, 23, 24, 11, 4, 2),
  (14, 17, 24, 12, 5, 2),
  (14, 19, 20, 9, 3, 3),
  (14, 19, 21, 12, 6, 1),
  (14, 19, 22, 9, 5, 2),
  (14, 19, 25, 10, 4, 2),
  (14, 23, 24, 12, 3, 5),
  (14, 23, 25, 11, 3, 4),
  (15, 19, 24, 11, 2, 4),
  (15, 22, 24, 11, 2, 4),
  (15, 22, 25, 11, 4, 2),
  (15, 22, 26, 13, 7, 1),
  (15, 23, 24, 11, 2, 4),
  (15, 23, 26, 12, 5, 4),
  (16, 21, 24, 13, 7, 1),
  (16, 21, 25, 10, 4, 3),
  (16, 23, 24, 13, 7, 1),
  (16, 23, 26, 11, 5, 2),
  (16, 23, 27, 12, 3, 4),
  (16, 25, 26, 10, 3, 4),
  (16, 25, 27, 12, 2, 5),
  (17, 21, 28, 11, 3, 4),
  (17, 22, 26, 10, 6, 2),
  (17, 22, 28, 13, 8, 1),
  (17, 23, 24, 10, 3, 4),
  (17, 24, 25, 10, 5, 2),
  (17, 24, 26, 11, 4, 4),
  (17, 24, 28, 11, 3, 4),
  (17, 25, 28, 11, 6, 2),
  (17, 26, 27, 11, 2, 5),
  (17, 26, 28, 11, 4, 3),
  (17, 27, 28, 12, 4, 3),
  (18, 23, 29, 12, 4, 3),
  (18, 25, 26, 10, 5, 3),
  (18, 25, 27, 15, 8, 1),
  (18, 25, 28, 11, 3, 4),
  (19, 24, 30, 11, 5, 3),
  (19, 25, 30, 11, 4, 3),
  (19, 26, 27, 10, 4, 4),
  (19, 26, 28, 11, 3, 4),
  (19, 26, 29, 12, 3, 4),
  (19, 26, 30, 12, 6, 2),
  (19, 27, 28, 12, 6, 2),
  (19, 28, 30, 13, 3, 5),
  (19, 29, 30, 13, 2, 6),
  (20, 27, 28, 11, 3, 4),
  (20, 27, 29, 12, 6, 2),
  (20, 27, 30, 16, 9, 1),
  (20, 27, 31, 12, 5, 4),
  (20, 29, 30, 16, 9, 1),
  (21, 29, 30, 10, 5, 4),
  (21, 29, 32, 12, 3, 5),
  (22, 29, 32, 11, 5, 4),
  (22, 29, 33, 17, 10, 1),
  (22, 31, 32, 12, 5, 3),
  (22, 31, 33, 18, 10, 1),
  (23, 30, 34, 13, 4, 4),
  (23, 31, 32, 11, 3, 5),
  (23, 31, 34, 11, 6, 4),
  (23, 32, 33, 13, 3, 5),
  (23, 32, 34, 12, 4, 4),
  (23, 33, 34, 13, 7, 2),
  (25, 33, 36, 14, 8, 2),
  (25, 34, 35, 13, 4, 4),
  (25, 34, 36, 13, 3, 6),
  (26, 35, 36, 13, 3, 6),
  (26, 35, 37, 13, 6, 3),
  (27, 37, 38, 14, 6, 3),
  (29, 39, 40, 14, 3, 7)]

def certTableB : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (4, 17, 18, 13, 1, 1),
  (5, 16, 17, 10, 1, 2),
  (5, 16, 18, 11, 2, 1),
  (5, 17, 19, 12, 1, 2),
  (5, 18, 19, 11, 2, 1),
  (5, 18, 21, 13, 1, 2),
  (5, 14, 17, 10, 2, 1),
  (6, 19, 20, 13, 1, 2),
  (6, 19, 21, 14, 2, 1),
  (6, 19, 22, 14, 1, 2),
  (6, 17, 20, 13, 1, 2),
  (6, 17, 21, 13, 2, 1),
  (7, 22, 23, 13, 1, 3),
  (7, 22, 24, 13, 2, 2),
  (7, 22, 25, 14, 3, 1),
  (7, 15, 19, 11, 2, 2),
  (7, 23, 24, 14, 2, 2),
  (7, 23, 25, 15, 1, 3),
  (7, 16, 20, 11, 2, 2),
  (7, 17, 19, 11, 3, 1),
  (7, 17, 20, 12, 1, 3),
  (7, 17, 22, 12, 2, 2),
  (7, 18, 19, 11, 2, 2),
  (7, 18, 20, 11, 2, 2),
  (7, 18, 22, 13, 1, 3),
  (7, 18, 23, 12, 3, 1),
  (7, 19, 20, 11, 3, 1),
  (7, 19, 22, 12, 2, 2),
  (7, 19, 24, 14, 1, 3),
  (7, 20, 23, 13, 2, 2),
  (7, 20, 24, 13, 3, 1),
  (7, 20, 25, 13, 2, 2),
  (8, 25, 26, 16, 1, 3),
  (8, 25, 27, 14, 2, 2),
  (8, 17, 20, 12, 3, 1),
  (8, 17, 21, 12, 2, 2),
  (8, 17, 22, 11, 3, 2),
  (8, 19, 20, 12, 3, 1),
  (8, 19, 22, 14, 1, 3),
  (8, 19, 23, 14, 2, 2),
  (8, 19, 25, 12, 2, 2),
  (8, 21, 22, 11, 3, 2),
  (8, 21, 23, 12, 2, 2),
  (8, 21, 25, 15, 2, 2),
  (8, 21, 26, 16, 1, 3),
  (8, 23, 26, 13, 3, 2),
  (8, 23, 27, 16, 2, 2),
  (8, 15, 20, 11, 3, 1),
  (8, 15, 21, 10, 2, 2),
  (9, 28, 29, 16, 1, 4),
  (9, 19, 21, 12, 2, 2),
  (9, 19, 22, 12, 3, 2),
  (9, 19, 23, 12, 4, 1),
  (9, 19, 24, 13, 2, 2),
  (9, 19, 25, 12, 4, 2),
  (9, 20, 21, 12, 2, 2),
  (9, 20, 22, 13, 1, 4),
  (9, 20, 23, 13, 2, 3),
  (9, 20, 24, 13, 2, 2),
  (9, 20, 26, 13, 3, 2),
  (9, 22, 24, 13, 2, 2),
  (9, 22, 25, 13, 3, 2),
  (9, 22, 26, 15, 1, 4),
  (9, 22, 28, 13, 4, 2),
  (9, 22, 29, 14, 4, 1),
  (9, 23, 24, 13, 2, 2),
  (9, 23, 25, 14, 4, 1),
  (9, 23, 26, 14, 2, 3),
  (9, 23, 28, 16, 1, 4),
  (9, 23, 29, 14, 3, 2),
  (9, 14, 21, 10, 2, 2),
  (9, 25, 26, 14, 4, 1),
  (9, 25, 28, 15, 3, 2),
  (9, 16, 21, 11, 2, 2),
  (9, 16, 22, 10, 4, 2),
  (9, 26, 29, 16, 2, 3),
  (9, 17, 21, 11, 2, 2),
  (9, 17, 22, 11, 4, 1),
  (9, 17, 23, 11, 3, 2),
  (9, 17, 24, 12, 2, 2),
  (10, 21, 22, 13, 1, 4),
  (10, 21, 23, 11, 2, 3),
  (10, 21, 24, 11, 3, 2),
  (10, 21, 25, 14, 4, 1),
  (10, 21, 26, 14, 3, 2),
  (10, 21, 27, 13, 3, 2),
  (10, 21, 28, 14, 3, 3),
  (10, 23, 24, 12, 3, 3),
  (10, 23, 25, 15, 4, 1),
  (10, 23, 26, 16, 1, 4),
  (10, 23, 28, 16, 3, 2),
  (10, 23, 29, 14, 2, 3),
  (10, 23, 31, 14, 3, 2),
  (10, 27, 28, 14, 3, 2),
  (10, 27, 29, 14, 3, 2),
  (10, 27, 31, 15, 2, 3),
  (10, 17, 22, 12, 3, 2),
  (10, 17, 25, 12, 4, 1),
  (10, 19, 22, 11, 3, 3),
  (10, 19, 23, 11, 3, 2),
  (10, 19, 24, 13, 3, 2),
  (10, 19, 25, 13, 4, 1),
  (10, 19, 26, 11, 3, 2),
  (10, 19, 27, 12, 2, 3),
  (11, 23, 24, 13, 1, 5),
  (11, 23, 25, 12, 2, 3),
  (11, 23, 26, 12, 3, 2),
  (11, 23, 27, 13, 3, 4),
  (11, 23, 28, 14, 5, 1),
  (11, 23, 29, 14, 2, 4),
  (11, 23, 30, 13, 4, 2),
  (11, 23, 31, 14, 4, 3),
  (11, 24, 25, 12, 2, 4),
  (11, 24, 26, 15, 1, 5),
  (11, 24, 27, 12, 4, 2),
  (11, 24, 28, 13, 2, 3),
  (11, 24, 29, 13, 4, 3),
  (11, 24, 30, 13, 3, 2),
  (11, 24, 32, 15, 4, 2),
  (11, 25, 26, 12, 3, 4),
  (11, 25, 27, 12, 4, 3),
  (11, 25, 28, 16, 1, 5),
  (11, 25, 29, 15, 5, 1),
  (11, 25, 31, 14, 2, 3),
  (11, 25, 32, 15, 2, 4),
  (11, 14, 23, 9, 3, 2),
  (11, 26, 27, 12, 3, 2),
  (11, 26, 28, 13, 2, 4),
  (11, 26, 30, 17, 1, 5),
  (11, 26, 31, 14, 3, 4),
  (11, 26, 32, 14, 4, 2),
  (11, 15, 23, 10, 2, 3),
  (11, 15, 24, 10, 5, 1),
  (11, 27, 29, 13, 4, 2),
  (11, 27, 30, 16, 5, 1),
  (11, 27, 31, 14, 3, 2),
  (11, 27, 32, 18, 1, 5),
  (11, 16, 23, 10, 4, 3),
  (11, 16, 24, 11, 3, 2),
  (11, 16, 25, 11, 4, 2),
  (11, 28, 29, 13, 2, 3),
  (11, 28, 30, 14, 3, 4),
  (11, 28, 31, 14, 2, 4),
  (11, 28, 32, 15, 4, 3),
  (11, 17, 24, 10, 3, 2),
  (11, 17, 25, 11, 5, 1),
  (11, 17, 26, 11, 4, 2),
  (11, 29, 30, 14, 4, 3),
  (11, 29, 31, 17, 5, 1),
  (11, 29, 32, 15, 2, 3),
  (11, 18, 23, 10, 4, 2),
  (11, 18, 24, 11, 4, 2),
  (11, 18, 27, 13, 3, 2),
  (11, 30, 31, 14, 4, 2),
  (11, 30, 32, 15, 3, 2),
  (11, 19, 23, 11, 2, 4),
  (11, 19, 24, 11, 2, 3),
  (11, 19, 26, 12, 5, 1),
  (11, 19, 28, 12, 4, 3),
  (11, 31, 32, 17, 5, 1),
  (11, 20, 23, 11, 3, 4),
  (11, 20, 25, 11, 3, 2),
  (11, 20, 26, 12, 4, 3),
  (11, 20, 27, 12, 2, 3),
  (11, 20, 28, 12, 4, 2),
  (11, 21, 24, 11, 4, 3),
  (11, 21, 25, 11, 4, 2),
  (11, 21, 26, 12, 2, 4),
  (11, 21, 27, 13, 5, 1),
  (11, 21, 28, 13, 4, 2),
  (11, 21, 29, 12, 3, 2),
  (11, 21, 30, 13, 2, 3),
  (9, 25, 32, 18, 1, 4),
  (10, 27, 34, 20, 1, 4),
  (11, 28, 34, 19, 1, 5),
  (11, 29, 36, 20, 1, 5),
  (11, 30, 38, 21, 1, 5),
  (11, 31, 40, 22, 1, 5)
]

set_option maxRecDepth 1000000 in
theorem certTableA_ok : certTableA.all frameCertOK = true := by decide

set_option maxRecDepth 1000000 in
theorem certTableB_ok : certTableB.all frameCertOK = true := by decide

/-- Every Table-A row yields its (SHARP) witness. -/
theorem certTableA_sharp :
    ∀ e ∈ certTableA, SharpTriple e.1 e.2.1 e.2.2.1 := by
  intro e he
  obtain ⟨a, b, M, x, Y, Z⟩ := e
  exact frameCertOK_sharpTriple (List.all_eq_true.mp certTableA_ok _ he)

/-- Every Table-B row is a frame certificate (the root of its λ-chain). -/
theorem certTableB_frame :
    ∀ e ∈ certTableB, FrameCert e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2 := by
  intro e he
  obtain ⟨a, b, M, x, Y, Z⟩ := e
  exact frameCertOK_sound (List.all_eq_true.mp certTableB_ok _ he)

end Proof
end Erdos1112


/-! Flattened from Erdos1112Proof.Sharp.CaseTCore. -/
/-
Case T of the bounded subset-sum covering lemma: the per-`a` decidable
T-line check `TlineGo`, its soundness, and the generic linear tail
(`a > 3000`).

Design note: an earlier draft's Case-T lemma used three staircase variants
(A: two-frame merge, `x = c+1`; B: the short merge, staircase part (c),
`x = c`; and the base form, part (d), `x = c+g`). Variant B rests on
`staircase_merge_c` (proved in Staircase.lean); `TlineBudget` checks only
variant A (`g = 1`) and the base form (`g ≥ 2`) — the paper's two
merge-robust variants — and the **14** triples where only variant B's budget
fits (all with `a ≤ 29`) are instead certified by explicit kernel-checked
frame certificates (`tSuppT` below, same `frameCertOK` checker as the
Appendix-B tables). The scan invariant `TlineGo e h a = true` for all lines
and `a ≤ 3000` was verified against this exact ℕ-truncated formula set:
budget failures = 158 (= `certTableA`) + 14 (= `tSuppT`) — together the
paper's 172-row Table A — none unexplained.

For `a > 3000` the base form alone fits on every line (`T_tail`): with
`μ' ≥ 3` (from `e ≠ h`), `z ≤ (a + 201)/3`, so the budget `2(y+z) + g + 1`
has slope `2/3 < 1` against `M = a + μ` — part (ii) of the paper's T-tail
proposition, with crude constants.
-/

namespace Erdos1112
namespace Proof

/-! ### Ceiling division -/

/-- Ceiling division `⌈n/m⌉` as `(n + m − 1)/m`. -/
def cdiv (n m : ℕ) : ℕ := (n + m - 1) / m

/-- `⌈n/m⌉·m ≥ n` (for `m > 0`). -/
lemma le_mul_cdiv {m : ℕ} (hm : 0 < m) (n : ℕ) : n ≤ m * cdiv n m := by
  unfold cdiv
  have h1 := Nat.div_add_mod (n + m - 1) m
  have h2 := Nat.mod_lt (n + m - 1) hm
  omega

/-- `⌈n/m⌉·m ≤ n + m − 1`. -/
lemma cdiv_mul_le {m : ℕ} (_hm : 0 < m) (n : ℕ) : cdiv n m * m ≤ n + m - 1 := by
  unfold cdiv
  exact Nat.div_mul_le_self _ _

/-! ### The supplementary certificate table (variant-B replacements) -/

/-- The 14 T-line triples whose minimal draft budget was achieved only by
the short merge (part (c) of the paper's staircase lemma); certified here
directly by mod-`a` frame boxes so that Case T does not depend on
`staircase_merge_c`. Format `(a,b,M,x,Y,Z)`, same checker as Tables A/B. -/
def tSuppT : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (10, 13, 15, 9, 4, 1),
  (11, 14, 15, 7, 3, 4),
  (13, 16, 21, 10, 6, 1),
  (16, 19, 27, 13, 6, 2),
  (16, 21, 23, 10, 5, 2),
  (17, 22, 23, 10, 5, 6),
  (17, 22, 25, 10, 4, 3),
  (18, 23, 27, 14, 8, 1),
  (22, 29, 31, 11, 6, 3),
  (23, 30, 31, 13, 7, 8),
  (23, 30, 33, 13, 7, 2),
  (24, 31, 35, 12, 4, 4),
  (28, 37, 39, 14, 4, 5),
  (29, 38, 39, 15, 9, 10)]

set_option maxRecDepth 100000 in
theorem tSuppT_ok : tSuppT.all frameCertOK = true := by decide

/-- Every supplementary row yields its (SHARP) witness. -/
theorem tSuppT_sharp : ∀ r ∈ tSuppT, SharpTriple r.1 r.2.1 r.2.2.1 := by
  intro r hr
  obtain ⟨a, b, M, x, Y, Z⟩ := r
  exact frameCertOK_sharpTriple (List.all_eq_true.mp tSuppT_ok _ hr)

/-! ### The decidable per-`a` T-line check -/

/-- Side conditions of the T-scan at line `(e,h)`, position `a`: the
specialization of the Case-T routing hypotheses to `b = a+e`, `M = a+e+h`
(`h + 2 ≤ a` from the hard core's `δ ≥ 2`; `gcd(a,e) = 1` from
`gcd(a,b) = 1`; `a ∤ μ` ⟺ `a ∤ M`; `a ∤ 2e+h` ⟺ `a ∤ b+M`). -/
def TlineSide (e h a : ℕ) : Bool :=
  decide (h + 2 ≤ a) && decide (Nat.gcd a e = 1) &&
  decide ((e + h) % a ≠ 0) && decide ((2 * e + h) % a ≠ 0)

/-- Budget check for the two formalized Case-T variants, with the line
constants passed explicitly: variant A (`g = 1`, `x = c+1`, extended form)
and the base form (`g ≥ 2`, `x = c+g`). `μ` is the second argument. -/
def TlineBudgetCore (a μ g e' μ' C y : ℕ) : Bool :=
  if g = 1 then
    decide (2 * (y + max (e' - 1) (cdiv (max a μ - 1 + 2 * C - e' * y) μ')) + 1
      ≤ a + μ - 1)
  else
    decide (2 * (y + max (e' - 1) (cdiv (a + cdiv (μ - 1) g + 2 * C - e' * y) μ')) + g
      ≤ a + μ - 1)

/-- Budget check at line `(e,h)`, position `a`. -/
def TlineBudget (e h a : ℕ) : Bool :=
  TlineBudgetCore a (e + h) (Nat.gcd e (e + h)) (e / Nat.gcd e (e + h))
    ((e + h) / Nat.gcd e (e + h))
    ((e / Nat.gcd e (e + h) - 1) * ((e + h) / Nat.gcd e (e + h) - 1))
    ((e + h) / Nat.gcd e (e + h) - 1)

/-- Exception lookup: `(a, a+e, a+e+h)` is a row of Table A or of the
supplementary table. -/
def TlineTable (e h a : ℕ) : Bool :=
  (certTableA.any fun r => decide (r.1 = a ∧ r.2.1 = a + e ∧ r.2.2.1 = a + e + h)) ||
  (tSuppT.any fun r => decide (r.1 = a ∧ r.2.1 = a + e ∧ r.2.2.1 = a + e + h))

/-- The full per-`a` check: side conditions imply budget-or-table. -/
def TlineGo (e h a : ℕ) : Bool :=
  !TlineSide e h a || TlineBudget e h a || TlineTable e h a

/-! ### Soundness of the two variants -/

/-- Generic base-form soundness (any `g ≥ 1`): a staircase `(x, y, z)` with
one frame per phase class and run-length/budget inequalities yields the
(SHARP) witness. `hrun` is the additive form of
`g·(V′−C′) ≥ (g−1)·a + M − 1`. -/
lemma T_base {a b M g e' μ' C' y z x : ℕ} (S : StairSetup a b M g e' μ')
    (hC' : C' = (e' - 1) * (μ' - 1))
    (hy : μ' - 1 ≤ y) (hz : e' - 1 ≤ z)
    (hag : Nat.Coprime a g)
    (hx : y + z + g - 1 ≤ x)
    (hrun : (g - 1) * a + M + 2 * (g * C') ≤ g * (e' * y + μ' * z) + 1)
    (hbud : x + y + z + 1 ≤ M) : SharpTriple a b M := by
  have hg1 : 1 ≤ g := S.g_pos
  have hCW : C' ≤ e' * y + μ' * z := by
    have h1 : (e' - 1) * (μ' - 1) ≤ e' * y := Nat.mul_le_mul (Nat.sub_le e' 1) hy
    omega
  set V' := e' * y + μ' * z - C' with hV'def
  have hV' : V' + C' = e' * y + μ' * z := by omega
  have run := staircase_phase_base S hC' hV' hag hy hz hx
  refine ⟨stair a b M x y z, ?_, ?_, (y + z + g - 1) * a + g * C', ?_⟩
  · intro w hw
    simp only [stair] at hw
    rcases Multiset.mem_add.mp hw with hw | hw
    · rcases Multiset.mem_add.mp hw with hw | hw
      · exact Or.inl (Multiset.eq_of_mem_replicate hw)
      · exact Or.inr (Or.inl (Multiset.eq_of_mem_replicate hw))
    · exact Or.inr (Or.inr (Multiset.eq_of_mem_replicate hw))
  · simp only [stair, Multiset.card_add, Multiset.card_replicate]
    omega
  · intro i hi
    apply run
    · exact Nat.le_add_right _ _
    · have hsplit : (y + z + g - 1) * a = (y + z) * a + (g - 1) * a := by
        have hb : y + z + g - 1 = (y + z) + (g - 1) := by omega
        rw [hb, Nat.add_mul]
      have hgV : g * V' + g * C' = g * (e' * y + μ' * z) := by
        rw [← Nat.mul_add, hV']
      omega

/-- Variant-A soundness (`g = 1`, `x = c + 1`, extended form
the staircase extended/base form (d)): merge and run-length inequalities in additive `W`-form
(`W := e′·y + μ′·z = V′ + C′`), budget `2c + 2 ≤ M`. -/
lemma T_variantA {a b M e' μ' C' y z : ℕ} (S : StairSetup a b M 1 e' μ')
    (hC' : C' = (e' - 1) * (μ' - 1))
    (hy : μ' - 1 ≤ y) (hz : e' - 1 ≤ z)
    (hmerge : a + 2 * C' ≤ e' * y + μ' * z + 1)
    (hlen : M + 2 * C' ≤ a + (e' * y + μ' * z) + 1)
    (hbud : 2 * (y + z) + 2 ≤ M) : SharpTriple a b M := by
  have hCW : C' ≤ e' * y + μ' * z := by
    have h1 : (e' - 1) * (μ' - 1) ≤ e' * y := Nat.mul_le_mul (Nat.sub_le e' 1) hy
    omega
  set V' := e' * y + μ' * z - C' with hV'def
  have hV' : V' + C' = e' * y + μ' * z := by omega
  have run := staircase_phase_extended S hC' hV' (Nat.coprime_one_right a) hy hz
    (le_refl (y + z + 1)) (by omega)
  refine ⟨stair a b M (y + z + 1) y z, ?_, ?_, (y + z) * a + C', ?_⟩
  · intro w hw
    simp only [stair] at hw
    rcases Multiset.mem_add.mp hw with hw | hw
    · rcases Multiset.mem_add.mp hw with hw | hw
      · exact Or.inl (Multiset.eq_of_mem_replicate hw)
      · exact Or.inr (Or.inl (Multiset.eq_of_mem_replicate hw))
    · exact Or.inr (Or.inr (Multiset.eq_of_mem_replicate hw))
  · simp only [stair, Multiset.card_add, Multiset.card_replicate]
    omega
  · intro i hi
    apply run
    · rw [show y + z + 1 - 1 = y + z from by omega, Nat.one_mul]
      omega
    · rw [show y + z + 1 - 1 + 1 = y + z + 1 from by omega, Nat.one_mul]
      have hb2 : (y + z + 1) * a = (y + z) * a + a := by ring
      omega

/-! ### Soundness of the decided check -/

/-- Soundness of `TlineBudgetCore` at a T-line point, with the line
constants pinned by defining equations (all discharged by `rfl` at the
call site). -/
lemma TlineBudgetCore_sound {a e h g e' μ' C y : ℕ}
    (he : 1 ≤ e) (hh : 1 ≤ h) (ha : 0 < a) (hcop : Nat.Coprime a e)
    (hg : g = Nat.gcd e (e + h)) (he' : e' = e / g) (hμ' : μ' = (e + h) / g)
    (hC : C = (e' - 1) * (μ' - 1)) (hy : y = μ' - 1)
    (hbud : TlineBudgetCore a (e + h) g e' μ' C y = true) :
    SharpTriple a (a + e) (a + e + h) := by
  have S : StairSetup a (a + e) (a + e + h) g e' μ' := by
    refine ⟨by omega, by omega, ha, ?_, ?_, ?_⟩
    · rw [show a + e - a = e from by omega, show a + e + h - a = e + h from by omega]
      exact hg
    · rw [show a + e - a = e from by omega]
      exact he'
    · rw [show a + e + h - a = e + h from by omega]
      exact hμ'
  have he'0 : 0 < e' := S.e'_pos
  have hμ'0 : 0 < μ' := lt_trans he'0 S.e'_lt_μ'
  rw [TlineBudgetCore] at hbud
  by_cases hg1 : g = 1
  · -- variant A
    rw [if_pos hg1, decide_eq_true_eq] at hbud
    set z := max (e' - 1) (cdiv (max a (e + h) - 1 + 2 * C - e' * y) μ') with hzdef
    have hz1 : e' - 1 ≤ z := hzdef ▸ le_max_left _ _
    have hz2 : cdiv (max a (e + h) - 1 + 2 * C - e' * y) μ' ≤ z :=
      hzdef ▸ le_max_right _ _
    have hW : max a (e + h) - 1 + 2 * C ≤ e' * y + μ' * z := by
      have h1 : max a (e + h) - 1 + 2 * C - e' * y
          ≤ μ' * cdiv (max a (e + h) - 1 + 2 * C - e' * y) μ' := le_mul_cdiv hμ'0 _
      have h2 : μ' * cdiv (max a (e + h) - 1 + 2 * C - e' * y) μ' ≤ μ' * z :=
        Nat.mul_le_mul_left μ' hz2
      omega
    have S1 : StairSetup a (a + e) (a + e + h) 1 e' μ' := hg1 ▸ S
    exact T_variantA (y := y) (z := z) S1 hC (by omega) hz1 (by omega) (by omega)
      (by omega)
  · -- base form
    rw [if_neg hg1, decide_eq_true_eq] at hbud
    set z := max (e' - 1) (cdiv (a + cdiv (e + h - 1) g + 2 * C - e' * y) μ') with hzdef
    have hz1 : e' - 1 ≤ z := hzdef ▸ le_max_left _ _
    have hz2 : cdiv (a + cdiv (e + h - 1) g + 2 * C - e' * y) μ' ≤ z :=
      hzdef ▸ le_max_right _ _
    have hg0 : 0 < g := S.g_pos
    have hW : a + cdiv (e + h - 1) g + 2 * C ≤ e' * y + μ' * z := by
      have h1 : a + cdiv (e + h - 1) g + 2 * C - e' * y
          ≤ μ' * cdiv (a + cdiv (e + h - 1) g + 2 * C - e' * y) μ' := le_mul_cdiv hμ'0 _
      have h2 : μ' * cdiv (a + cdiv (e + h - 1) g + 2 * C - e' * y) μ' ≤ μ' * z :=
        Nat.mul_le_mul_left μ' hz2
      omega
    have hgdvde : g ∣ e := hg ▸ Nat.gcd_dvd_left _ _
    have hagg : Nat.Coprime a g := hcop.coprime_dvd_right hgdvde
    apply T_base (x := y + z + g) (y := y) (z := z) S hC (by omega) hz1 hagg
      (by omega)
    · -- hrun
      have h3 : e + h - 1 ≤ g * cdiv (e + h - 1) g := le_mul_cdiv hg0 _
      have h4 : g * (a + cdiv (e + h - 1) g + 2 * C) ≤ g * (e' * y + μ' * z) :=
        Nat.mul_le_mul_left g hW
      have h5 : g * (a + cdiv (e + h - 1) g + 2 * C)
          = g * a + g * cdiv (e + h - 1) g + 2 * (g * C) := by ring
      have h6 : (g - 1) * a + a = g * a := by
        have hb : g - 1 + 1 = g := by omega
        calc (g - 1) * a + a = (g - 1 + 1) * a := by ring
          _ = g * a := by rw [hb]
      omega
    · -- hbud
      omega

/-- Soundness of the full per-`a` check: at a genuine Case-T point
(specialized side hypotheses), `TlineGo e h a = true` yields the (SHARP)
witness — by variant A / base form when the budget fits, and by the
Table A / supplementary certificates otherwise. -/
lemma TlineGo_sound {e h a : ℕ} (he : 1 ≤ e) (hh : 1 ≤ h)
    (h2a : h + 2 ≤ a) (hcop : Nat.Coprime a e)
    (hnd1 : ¬ a ∣ (e + h)) (hnd2 : ¬ a ∣ (2 * e + h))
    (hgo : TlineGo e h a = true) : SharpTriple a (a + e) (a + e + h) := by
  have ha : 0 < a := by omega
  have hside : TlineSide e h a = true := by
    simp only [TlineSide, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨h2a, hcop⟩, fun hz => hnd1 (Nat.dvd_of_mod_eq_zero hz)⟩,
      fun hz => hnd2 (Nat.dvd_of_mod_eq_zero hz)⟩
  simp only [TlineGo, hside, Bool.not_true, Bool.false_or, Bool.or_eq_true] at hgo
  rcases hgo with hbud | htab
  · -- budget branch
    simp only [TlineBudget] at hbud
    exact TlineBudgetCore_sound he hh ha hcop rfl rfl rfl rfl rfl hbud
  · -- table branch
    simp only [TlineTable, Bool.or_eq_true, List.any_eq_true,
      decide_eq_true_eq] at htab
    rcases htab with ⟨r, hrmem, hr1, hr2, hr3⟩ | ⟨r, hrmem, hr1, hr2, hr3⟩
    · have hs := certTableA_sharp r hrmem
      rw [hr1, hr2, hr3] at hs
      exact hs
    · have hs := tSuppT_sharp r hrmem
      rw [hr1, hr2, hr3] at hs
      exact hs

/-! ### The linear tail `a > 3000` (T-tail, part (ii)) -/

/-- Tail at line level: for `a ≥ 3001` the base form alone fits on every
line. Crude constants (`e', y, g ≤ 10`, `μ' ≤ 11`, `C ≤ 90`) give
`3·z ≤ a + 201`, whence the budget `2(y+z) + g + 1` is under
`M = a + e + h` with room `≥ (a − 495)/3`. Needs `μ' ≥ 3`, i.e. `e ≠ h`. -/
lemma T_tail_line {a e h : ℕ} (he : 1 ≤ e) (hh : 1 ≤ h) (hμ : e + h ≤ 11)
    (hne : e ≠ h) (hcop : Nat.Coprime a e) (ha : 3001 ≤ a) :
    SharpTriple a (a + e) (a + e + h) := by
  set g := Nat.gcd e (e + h) with hgdef
  set e' := e / g with he'def
  set μ' := (e + h) / g with hμ'def
  set C := (e' - 1) * (μ' - 1) with hCdef
  set y := μ' - 1 with hydef
  have S : StairSetup a (a + e) (a + e + h) g e' μ' := by
    refine ⟨by omega, by omega, by omega, ?_, ?_, ?_⟩
    · rw [show a + e - a = e from by omega, show a + e + h - a = e + h from by omega]
    · rw [show a + e - a = e from by omega]
    · rw [show a + e + h - a = e + h from by omega]
  have hg0 : 0 < g := S.g_pos
  have hgdvde : g ∣ e := hgdef ▸ Nat.gcd_dvd_left _ _
  have hge : g ≤ e := Nat.le_of_dvd (by omega) hgdvde
  have he'e : e' ≤ e := he'def ▸ Nat.div_le_self e g
  have hμ'μ : μ' ≤ e + h := hμ'def ▸ Nat.div_le_self _ _
  have he'0 : 0 < e' := S.e'_pos
  have he'μ' : e' < μ' := S.e'_lt_μ'
  have hμ'0 : 0 < μ' := by omega
  -- `μ' ≥ 3`: `μ' ≤ 2` forces `(e', μ') = (1, 2)`, i.e. `h = g = e`.
  have hμ'3 : 3 ≤ μ' := by
    by_contra hlt
    push_neg at hlt
    have hμ'2 : μ' = 2 := by omega
    have he'1 : e' = 1 := by omega
    have hbe := S.e_eq
    have hMe := S.μ_eq
    rw [he'1, Nat.mul_one] at hbe
    rw [hμ'2] at hMe
    exact hne (by omega)
  have hC90 : C ≤ 90 := by
    rw [hCdef]
    calc (e' - 1) * (μ' - 1) ≤ 9 * 10 := Nat.mul_le_mul (by omega) (by omega)
      _ = 90 := by norm_num
  have he'y : e' * y ≤ 100 := by
    calc e' * y ≤ 10 * 10 := Nat.mul_le_mul (by omega) (by omega)
      _ = 100 := by norm_num
  set N := a + (e + h) + 2 * C - e' * y with hNdef
  set z := max (e' - 1) (cdiv N μ') with hzdef
  have hz1 : e' - 1 ≤ z := hzdef ▸ le_max_left _ _
  have hz2 : cdiv N μ' ≤ z := hzdef ▸ le_max_right _ _
  have hWlo : a + (e + h) + 2 * C ≤ e' * y + μ' * z := by
    have h1 : N ≤ μ' * cdiv N μ' := le_mul_cdiv hμ'0 N
    have h2 : μ' * cdiv N μ' ≤ μ' * z := Nat.mul_le_mul_left μ' hz2
    omega
  have hz3 : 3 * z ≤ a + 201 := by
    have h1 : cdiv N μ' * μ' ≤ N + μ' - 1 := cdiv_mul_le hμ'0 N
    have h2 : cdiv N μ' * 3 ≤ cdiv N μ' * μ' := Nat.mul_le_mul_left _ hμ'3
    have h4 : 3 * cdiv N μ' = cdiv N μ' * 3 := Nat.mul_comm _ _
    omega
  have hagg : Nat.Coprime a g := hcop.coprime_dvd_right hgdvde
  apply T_base (x := y + z + g) (y := y) (z := z) S hCdef (by omega) hz1 hagg
    (by omega)
  · -- hrun: `g·W ≥ g·a + g·μ + 2·g·C ≥ (g−1)·a + M + 2·g·C − 1`
    have h4 : g * (a + (e + h) + 2 * C) ≤ g * (e' * y + μ' * z) :=
      Nat.mul_le_mul_left g hWlo
    have h5 : g * (a + (e + h) + 2 * C) = g * a + g * (e + h) + 2 * (g * C) := by
      ring
    have h6 : (g - 1) * a + a = g * a := by
      have hb : g - 1 + 1 = g := by omega
      calc (g - 1) * a + a = (g - 1 + 1) * a := by ring
        _ = g * a := by rw [hb]
    have h7 : e + h ≤ g * (e + h) := Nat.le_mul_of_pos_left _ hg0
    omega
  · -- budget: `2(y+z) + g + 1 ≤ a + e + h`, from `3z ≤ a + 201`, `a ≥ 3001`
    omega

/-- **T-tail (ii), packaged**: the Case-T tail `a ≥ 3001`. -/
lemma T_tail {a b M : ℕ} (hc : HardCore a b M) (hL : b - a ≠ M - b)
    (hμ : M - a ≤ 11) (ha : 3001 ≤ a) : SharpTriple a b M := by
  have hcop := hc.coprime_a_e
  obtain ⟨ha0, hab, hbM, hco, hδ⟩ := hc
  set e := b - a with hedef
  set h := M - b with hhdef
  have hbe : b = a + e := by omega
  have hMe : M = a + e + h := by omega
  rw [hbe, hMe]
  exact T_tail_line (by omega) (by omega) (by omega) hL hcop ha

end Proof
end Erdos1112


/-! Flattened from Erdos1112Proof.Sharp.CaseTScanE1. -/
/-
Case T scan blocks (T-tail, part (i)), lines `e = 1`:
kernel-decided verification of `TlineGo 1 h a` for `a ≤ 3000`, chunked in
three per-line blocks of ≤ 1001 values each (cacheable, failure-localizing).
-/

namespace Erdos1112
namespace Proof

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_1_2_b0 : ∀ a : ℕ, a < 1000 → TlineGo 1 2 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_1_2_b1 : ∀ d : ℕ, d < 1000 → TlineGo 1 2 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_1_2_b2 : ∀ d : ℕ, d < 1001 → TlineGo 1 2 (2000 + d) = true := by decide

/-- Line `(e,h) = (1,2)`: the full scan `a ≤ 3000`. -/
theorem T_scan_1_2 : ∀ a : ℕ, a ≤ 3000 → TlineGo 1 2 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_1_2_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_1_2_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_1_2_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_1_3_b0 : ∀ a : ℕ, a < 1000 → TlineGo 1 3 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_1_3_b1 : ∀ d : ℕ, d < 1000 → TlineGo 1 3 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_1_3_b2 : ∀ d : ℕ, d < 1001 → TlineGo 1 3 (2000 + d) = true := by decide

/-- Line `(e,h) = (1,3)`: the full scan `a ≤ 3000`. -/
theorem T_scan_1_3 : ∀ a : ℕ, a ≤ 3000 → TlineGo 1 3 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_1_3_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_1_3_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_1_3_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_1_4_b0 : ∀ a : ℕ, a < 1000 → TlineGo 1 4 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_1_4_b1 : ∀ d : ℕ, d < 1000 → TlineGo 1 4 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_1_4_b2 : ∀ d : ℕ, d < 1001 → TlineGo 1 4 (2000 + d) = true := by decide

/-- Line `(e,h) = (1,4)`: the full scan `a ≤ 3000`. -/
theorem T_scan_1_4 : ∀ a : ℕ, a ≤ 3000 → TlineGo 1 4 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_1_4_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_1_4_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_1_4_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_1_5_b0 : ∀ a : ℕ, a < 1000 → TlineGo 1 5 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_1_5_b1 : ∀ d : ℕ, d < 1000 → TlineGo 1 5 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_1_5_b2 : ∀ d : ℕ, d < 1001 → TlineGo 1 5 (2000 + d) = true := by decide

/-- Line `(e,h) = (1,5)`: the full scan `a ≤ 3000`. -/
theorem T_scan_1_5 : ∀ a : ℕ, a ≤ 3000 → TlineGo 1 5 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_1_5_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_1_5_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_1_5_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_1_6_b0 : ∀ a : ℕ, a < 1000 → TlineGo 1 6 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_1_6_b1 : ∀ d : ℕ, d < 1000 → TlineGo 1 6 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_1_6_b2 : ∀ d : ℕ, d < 1001 → TlineGo 1 6 (2000 + d) = true := by decide

/-- Line `(e,h) = (1,6)`: the full scan `a ≤ 3000`. -/
theorem T_scan_1_6 : ∀ a : ℕ, a ≤ 3000 → TlineGo 1 6 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_1_6_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_1_6_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_1_6_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_1_7_b0 : ∀ a : ℕ, a < 1000 → TlineGo 1 7 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_1_7_b1 : ∀ d : ℕ, d < 1000 → TlineGo 1 7 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_1_7_b2 : ∀ d : ℕ, d < 1001 → TlineGo 1 7 (2000 + d) = true := by decide

/-- Line `(e,h) = (1,7)`: the full scan `a ≤ 3000`. -/
theorem T_scan_1_7 : ∀ a : ℕ, a ≤ 3000 → TlineGo 1 7 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_1_7_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_1_7_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_1_7_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_1_8_b0 : ∀ a : ℕ, a < 1000 → TlineGo 1 8 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_1_8_b1 : ∀ d : ℕ, d < 1000 → TlineGo 1 8 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_1_8_b2 : ∀ d : ℕ, d < 1001 → TlineGo 1 8 (2000 + d) = true := by decide

/-- Line `(e,h) = (1,8)`: the full scan `a ≤ 3000`. -/
theorem T_scan_1_8 : ∀ a : ℕ, a ≤ 3000 → TlineGo 1 8 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_1_8_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_1_8_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_1_8_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_1_9_b0 : ∀ a : ℕ, a < 1000 → TlineGo 1 9 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_1_9_b1 : ∀ d : ℕ, d < 1000 → TlineGo 1 9 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_1_9_b2 : ∀ d : ℕ, d < 1001 → TlineGo 1 9 (2000 + d) = true := by decide

/-- Line `(e,h) = (1,9)`: the full scan `a ≤ 3000`. -/
theorem T_scan_1_9 : ∀ a : ℕ, a ≤ 3000 → TlineGo 1 9 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_1_9_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_1_9_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_1_9_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_1_10_b0 : ∀ a : ℕ, a < 1000 → TlineGo 1 10 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_1_10_b1 : ∀ d : ℕ, d < 1000 → TlineGo 1 10 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_1_10_b2 : ∀ d : ℕ, d < 1001 → TlineGo 1 10 (2000 + d) = true := by decide

/-- Line `(e,h) = (1,10)`: the full scan `a ≤ 3000`. -/
theorem T_scan_1_10 : ∀ a : ℕ, a ≤ 3000 → TlineGo 1 10 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_1_10_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_1_10_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_1_10_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

end Proof
end Erdos1112


/-! Flattened from Erdos1112Proof.Sharp.CaseTScanE2. -/
/-
Case T scan blocks (T-tail, part (i)), lines `e = 2`:
kernel-decided verification of `TlineGo 2 h a` for `a ≤ 3000`, chunked in
three per-line blocks of ≤ 1001 values each (cacheable, failure-localizing).
-/

namespace Erdos1112
namespace Proof

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_2_1_b0 : ∀ a : ℕ, a < 1000 → TlineGo 2 1 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_2_1_b1 : ∀ d : ℕ, d < 1000 → TlineGo 2 1 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_2_1_b2 : ∀ d : ℕ, d < 1001 → TlineGo 2 1 (2000 + d) = true := by decide

/-- Line `(e,h) = (2,1)`: the full scan `a ≤ 3000`. -/
theorem T_scan_2_1 : ∀ a : ℕ, a ≤ 3000 → TlineGo 2 1 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_2_1_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_2_1_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_2_1_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_2_3_b0 : ∀ a : ℕ, a < 1000 → TlineGo 2 3 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_2_3_b1 : ∀ d : ℕ, d < 1000 → TlineGo 2 3 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_2_3_b2 : ∀ d : ℕ, d < 1001 → TlineGo 2 3 (2000 + d) = true := by decide

/-- Line `(e,h) = (2,3)`: the full scan `a ≤ 3000`. -/
theorem T_scan_2_3 : ∀ a : ℕ, a ≤ 3000 → TlineGo 2 3 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_2_3_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_2_3_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_2_3_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_2_4_b0 : ∀ a : ℕ, a < 1000 → TlineGo 2 4 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_2_4_b1 : ∀ d : ℕ, d < 1000 → TlineGo 2 4 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_2_4_b2 : ∀ d : ℕ, d < 1001 → TlineGo 2 4 (2000 + d) = true := by decide

/-- Line `(e,h) = (2,4)`: the full scan `a ≤ 3000`. -/
theorem T_scan_2_4 : ∀ a : ℕ, a ≤ 3000 → TlineGo 2 4 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_2_4_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_2_4_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_2_4_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_2_5_b0 : ∀ a : ℕ, a < 1000 → TlineGo 2 5 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_2_5_b1 : ∀ d : ℕ, d < 1000 → TlineGo 2 5 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_2_5_b2 : ∀ d : ℕ, d < 1001 → TlineGo 2 5 (2000 + d) = true := by decide

/-- Line `(e,h) = (2,5)`: the full scan `a ≤ 3000`. -/
theorem T_scan_2_5 : ∀ a : ℕ, a ≤ 3000 → TlineGo 2 5 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_2_5_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_2_5_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_2_5_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_2_6_b0 : ∀ a : ℕ, a < 1000 → TlineGo 2 6 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_2_6_b1 : ∀ d : ℕ, d < 1000 → TlineGo 2 6 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_2_6_b2 : ∀ d : ℕ, d < 1001 → TlineGo 2 6 (2000 + d) = true := by decide

/-- Line `(e,h) = (2,6)`: the full scan `a ≤ 3000`. -/
theorem T_scan_2_6 : ∀ a : ℕ, a ≤ 3000 → TlineGo 2 6 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_2_6_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_2_6_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_2_6_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_2_7_b0 : ∀ a : ℕ, a < 1000 → TlineGo 2 7 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_2_7_b1 : ∀ d : ℕ, d < 1000 → TlineGo 2 7 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_2_7_b2 : ∀ d : ℕ, d < 1001 → TlineGo 2 7 (2000 + d) = true := by decide

/-- Line `(e,h) = (2,7)`: the full scan `a ≤ 3000`. -/
theorem T_scan_2_7 : ∀ a : ℕ, a ≤ 3000 → TlineGo 2 7 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_2_7_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_2_7_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_2_7_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_2_8_b0 : ∀ a : ℕ, a < 1000 → TlineGo 2 8 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_2_8_b1 : ∀ d : ℕ, d < 1000 → TlineGo 2 8 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_2_8_b2 : ∀ d : ℕ, d < 1001 → TlineGo 2 8 (2000 + d) = true := by decide

/-- Line `(e,h) = (2,8)`: the full scan `a ≤ 3000`. -/
theorem T_scan_2_8 : ∀ a : ℕ, a ≤ 3000 → TlineGo 2 8 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_2_8_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_2_8_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_2_8_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_2_9_b0 : ∀ a : ℕ, a < 1000 → TlineGo 2 9 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_2_9_b1 : ∀ d : ℕ, d < 1000 → TlineGo 2 9 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_2_9_b2 : ∀ d : ℕ, d < 1001 → TlineGo 2 9 (2000 + d) = true := by decide

/-- Line `(e,h) = (2,9)`: the full scan `a ≤ 3000`. -/
theorem T_scan_2_9 : ∀ a : ℕ, a ≤ 3000 → TlineGo 2 9 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_2_9_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_2_9_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_2_9_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

end Proof
end Erdos1112


/-! Flattened from Erdos1112Proof.Sharp.CaseTScanE3. -/
/-
Case T scan blocks (T-tail, part (i)), lines `e = 3`:
kernel-decided verification of `TlineGo 3 h a` for `a ≤ 3000`, chunked in
three per-line blocks of ≤ 1001 values each (cacheable, failure-localizing).
-/

namespace Erdos1112
namespace Proof

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_3_1_b0 : ∀ a : ℕ, a < 1000 → TlineGo 3 1 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_3_1_b1 : ∀ d : ℕ, d < 1000 → TlineGo 3 1 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_3_1_b2 : ∀ d : ℕ, d < 1001 → TlineGo 3 1 (2000 + d) = true := by decide

/-- Line `(e,h) = (3,1)`: the full scan `a ≤ 3000`. -/
theorem T_scan_3_1 : ∀ a : ℕ, a ≤ 3000 → TlineGo 3 1 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_3_1_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_3_1_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_3_1_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_3_2_b0 : ∀ a : ℕ, a < 1000 → TlineGo 3 2 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_3_2_b1 : ∀ d : ℕ, d < 1000 → TlineGo 3 2 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_3_2_b2 : ∀ d : ℕ, d < 1001 → TlineGo 3 2 (2000 + d) = true := by decide

/-- Line `(e,h) = (3,2)`: the full scan `a ≤ 3000`. -/
theorem T_scan_3_2 : ∀ a : ℕ, a ≤ 3000 → TlineGo 3 2 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_3_2_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_3_2_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_3_2_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_3_4_b0 : ∀ a : ℕ, a < 1000 → TlineGo 3 4 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_3_4_b1 : ∀ d : ℕ, d < 1000 → TlineGo 3 4 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_3_4_b2 : ∀ d : ℕ, d < 1001 → TlineGo 3 4 (2000 + d) = true := by decide

/-- Line `(e,h) = (3,4)`: the full scan `a ≤ 3000`. -/
theorem T_scan_3_4 : ∀ a : ℕ, a ≤ 3000 → TlineGo 3 4 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_3_4_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_3_4_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_3_4_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_3_5_b0 : ∀ a : ℕ, a < 1000 → TlineGo 3 5 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_3_5_b1 : ∀ d : ℕ, d < 1000 → TlineGo 3 5 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_3_5_b2 : ∀ d : ℕ, d < 1001 → TlineGo 3 5 (2000 + d) = true := by decide

/-- Line `(e,h) = (3,5)`: the full scan `a ≤ 3000`. -/
theorem T_scan_3_5 : ∀ a : ℕ, a ≤ 3000 → TlineGo 3 5 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_3_5_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_3_5_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_3_5_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_3_6_b0 : ∀ a : ℕ, a < 1000 → TlineGo 3 6 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_3_6_b1 : ∀ d : ℕ, d < 1000 → TlineGo 3 6 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_3_6_b2 : ∀ d : ℕ, d < 1001 → TlineGo 3 6 (2000 + d) = true := by decide

/-- Line `(e,h) = (3,6)`: the full scan `a ≤ 3000`. -/
theorem T_scan_3_6 : ∀ a : ℕ, a ≤ 3000 → TlineGo 3 6 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_3_6_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_3_6_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_3_6_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_3_7_b0 : ∀ a : ℕ, a < 1000 → TlineGo 3 7 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_3_7_b1 : ∀ d : ℕ, d < 1000 → TlineGo 3 7 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_3_7_b2 : ∀ d : ℕ, d < 1001 → TlineGo 3 7 (2000 + d) = true := by decide

/-- Line `(e,h) = (3,7)`: the full scan `a ≤ 3000`. -/
theorem T_scan_3_7 : ∀ a : ℕ, a ≤ 3000 → TlineGo 3 7 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_3_7_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_3_7_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_3_7_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_3_8_b0 : ∀ a : ℕ, a < 1000 → TlineGo 3 8 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_3_8_b1 : ∀ d : ℕ, d < 1000 → TlineGo 3 8 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_3_8_b2 : ∀ d : ℕ, d < 1001 → TlineGo 3 8 (2000 + d) = true := by decide

/-- Line `(e,h) = (3,8)`: the full scan `a ≤ 3000`. -/
theorem T_scan_3_8 : ∀ a : ℕ, a ≤ 3000 → TlineGo 3 8 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_3_8_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_3_8_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_3_8_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

end Proof
end Erdos1112


/-! Flattened from Erdos1112Proof.Sharp.CaseTScanE4. -/
/-
Case T scan blocks (T-tail, part (i)), lines `e = 4`:
kernel-decided verification of `TlineGo 4 h a` for `a ≤ 3000`, chunked in
three per-line blocks of ≤ 1001 values each (cacheable, failure-localizing).
-/

namespace Erdos1112
namespace Proof

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_4_1_b0 : ∀ a : ℕ, a < 1000 → TlineGo 4 1 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_4_1_b1 : ∀ d : ℕ, d < 1000 → TlineGo 4 1 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_4_1_b2 : ∀ d : ℕ, d < 1001 → TlineGo 4 1 (2000 + d) = true := by decide

/-- Line `(e,h) = (4,1)`: the full scan `a ≤ 3000`. -/
theorem T_scan_4_1 : ∀ a : ℕ, a ≤ 3000 → TlineGo 4 1 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_4_1_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_4_1_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_4_1_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_4_2_b0 : ∀ a : ℕ, a < 1000 → TlineGo 4 2 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_4_2_b1 : ∀ d : ℕ, d < 1000 → TlineGo 4 2 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_4_2_b2 : ∀ d : ℕ, d < 1001 → TlineGo 4 2 (2000 + d) = true := by decide

/-- Line `(e,h) = (4,2)`: the full scan `a ≤ 3000`. -/
theorem T_scan_4_2 : ∀ a : ℕ, a ≤ 3000 → TlineGo 4 2 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_4_2_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_4_2_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_4_2_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_4_3_b0 : ∀ a : ℕ, a < 1000 → TlineGo 4 3 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_4_3_b1 : ∀ d : ℕ, d < 1000 → TlineGo 4 3 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_4_3_b2 : ∀ d : ℕ, d < 1001 → TlineGo 4 3 (2000 + d) = true := by decide

/-- Line `(e,h) = (4,3)`: the full scan `a ≤ 3000`. -/
theorem T_scan_4_3 : ∀ a : ℕ, a ≤ 3000 → TlineGo 4 3 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_4_3_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_4_3_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_4_3_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_4_5_b0 : ∀ a : ℕ, a < 1000 → TlineGo 4 5 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_4_5_b1 : ∀ d : ℕ, d < 1000 → TlineGo 4 5 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_4_5_b2 : ∀ d : ℕ, d < 1001 → TlineGo 4 5 (2000 + d) = true := by decide

/-- Line `(e,h) = (4,5)`: the full scan `a ≤ 3000`. -/
theorem T_scan_4_5 : ∀ a : ℕ, a ≤ 3000 → TlineGo 4 5 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_4_5_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_4_5_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_4_5_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_4_6_b0 : ∀ a : ℕ, a < 1000 → TlineGo 4 6 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_4_6_b1 : ∀ d : ℕ, d < 1000 → TlineGo 4 6 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_4_6_b2 : ∀ d : ℕ, d < 1001 → TlineGo 4 6 (2000 + d) = true := by decide

/-- Line `(e,h) = (4,6)`: the full scan `a ≤ 3000`. -/
theorem T_scan_4_6 : ∀ a : ℕ, a ≤ 3000 → TlineGo 4 6 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_4_6_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_4_6_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_4_6_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_4_7_b0 : ∀ a : ℕ, a < 1000 → TlineGo 4 7 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_4_7_b1 : ∀ d : ℕ, d < 1000 → TlineGo 4 7 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_4_7_b2 : ∀ d : ℕ, d < 1001 → TlineGo 4 7 (2000 + d) = true := by decide

/-- Line `(e,h) = (4,7)`: the full scan `a ≤ 3000`. -/
theorem T_scan_4_7 : ∀ a : ℕ, a ≤ 3000 → TlineGo 4 7 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_4_7_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_4_7_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_4_7_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

end Proof
end Erdos1112


/-! Flattened from Erdos1112Proof.Sharp.CaseTScanE5. -/
/-
Case T scan blocks (T-tail, part (i)), lines `e = 5`:
kernel-decided verification of `TlineGo 5 h a` for `a ≤ 3000`, chunked in
three per-line blocks of ≤ 1001 values each (cacheable, failure-localizing).
-/

namespace Erdos1112
namespace Proof

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_5_1_b0 : ∀ a : ℕ, a < 1000 → TlineGo 5 1 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_5_1_b1 : ∀ d : ℕ, d < 1000 → TlineGo 5 1 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_5_1_b2 : ∀ d : ℕ, d < 1001 → TlineGo 5 1 (2000 + d) = true := by decide

/-- Line `(e,h) = (5,1)`: the full scan `a ≤ 3000`. -/
theorem T_scan_5_1 : ∀ a : ℕ, a ≤ 3000 → TlineGo 5 1 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_5_1_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_5_1_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_5_1_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_5_2_b0 : ∀ a : ℕ, a < 1000 → TlineGo 5 2 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_5_2_b1 : ∀ d : ℕ, d < 1000 → TlineGo 5 2 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_5_2_b2 : ∀ d : ℕ, d < 1001 → TlineGo 5 2 (2000 + d) = true := by decide

/-- Line `(e,h) = (5,2)`: the full scan `a ≤ 3000`. -/
theorem T_scan_5_2 : ∀ a : ℕ, a ≤ 3000 → TlineGo 5 2 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_5_2_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_5_2_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_5_2_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_5_3_b0 : ∀ a : ℕ, a < 1000 → TlineGo 5 3 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_5_3_b1 : ∀ d : ℕ, d < 1000 → TlineGo 5 3 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_5_3_b2 : ∀ d : ℕ, d < 1001 → TlineGo 5 3 (2000 + d) = true := by decide

/-- Line `(e,h) = (5,3)`: the full scan `a ≤ 3000`. -/
theorem T_scan_5_3 : ∀ a : ℕ, a ≤ 3000 → TlineGo 5 3 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_5_3_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_5_3_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_5_3_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_5_4_b0 : ∀ a : ℕ, a < 1000 → TlineGo 5 4 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_5_4_b1 : ∀ d : ℕ, d < 1000 → TlineGo 5 4 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_5_4_b2 : ∀ d : ℕ, d < 1001 → TlineGo 5 4 (2000 + d) = true := by decide

/-- Line `(e,h) = (5,4)`: the full scan `a ≤ 3000`. -/
theorem T_scan_5_4 : ∀ a : ℕ, a ≤ 3000 → TlineGo 5 4 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_5_4_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_5_4_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_5_4_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_5_6_b0 : ∀ a : ℕ, a < 1000 → TlineGo 5 6 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_5_6_b1 : ∀ d : ℕ, d < 1000 → TlineGo 5 6 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_5_6_b2 : ∀ d : ℕ, d < 1001 → TlineGo 5 6 (2000 + d) = true := by decide

/-- Line `(e,h) = (5,6)`: the full scan `a ≤ 3000`. -/
theorem T_scan_5_6 : ∀ a : ℕ, a ≤ 3000 → TlineGo 5 6 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_5_6_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_5_6_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_5_6_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

end Proof
end Erdos1112


/-! Flattened from Erdos1112Proof.Sharp.CaseTScanE6. -/
/-
Case T scan blocks (T-tail, part (i)), lines `e = 6`:
kernel-decided verification of `TlineGo 6 h a` for `a ≤ 3000`, chunked in
three per-line blocks of ≤ 1001 values each (cacheable, failure-localizing).
-/

namespace Erdos1112
namespace Proof

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_6_1_b0 : ∀ a : ℕ, a < 1000 → TlineGo 6 1 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_6_1_b1 : ∀ d : ℕ, d < 1000 → TlineGo 6 1 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_6_1_b2 : ∀ d : ℕ, d < 1001 → TlineGo 6 1 (2000 + d) = true := by decide

/-- Line `(e,h) = (6,1)`: the full scan `a ≤ 3000`. -/
theorem T_scan_6_1 : ∀ a : ℕ, a ≤ 3000 → TlineGo 6 1 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_6_1_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_6_1_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_6_1_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_6_2_b0 : ∀ a : ℕ, a < 1000 → TlineGo 6 2 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_6_2_b1 : ∀ d : ℕ, d < 1000 → TlineGo 6 2 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_6_2_b2 : ∀ d : ℕ, d < 1001 → TlineGo 6 2 (2000 + d) = true := by decide

/-- Line `(e,h) = (6,2)`: the full scan `a ≤ 3000`. -/
theorem T_scan_6_2 : ∀ a : ℕ, a ≤ 3000 → TlineGo 6 2 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_6_2_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_6_2_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_6_2_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_6_3_b0 : ∀ a : ℕ, a < 1000 → TlineGo 6 3 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_6_3_b1 : ∀ d : ℕ, d < 1000 → TlineGo 6 3 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_6_3_b2 : ∀ d : ℕ, d < 1001 → TlineGo 6 3 (2000 + d) = true := by decide

/-- Line `(e,h) = (6,3)`: the full scan `a ≤ 3000`. -/
theorem T_scan_6_3 : ∀ a : ℕ, a ≤ 3000 → TlineGo 6 3 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_6_3_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_6_3_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_6_3_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_6_4_b0 : ∀ a : ℕ, a < 1000 → TlineGo 6 4 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_6_4_b1 : ∀ d : ℕ, d < 1000 → TlineGo 6 4 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_6_4_b2 : ∀ d : ℕ, d < 1001 → TlineGo 6 4 (2000 + d) = true := by decide

/-- Line `(e,h) = (6,4)`: the full scan `a ≤ 3000`. -/
theorem T_scan_6_4 : ∀ a : ℕ, a ≤ 3000 → TlineGo 6 4 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_6_4_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_6_4_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_6_4_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_6_5_b0 : ∀ a : ℕ, a < 1000 → TlineGo 6 5 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_6_5_b1 : ∀ d : ℕ, d < 1000 → TlineGo 6 5 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_6_5_b2 : ∀ d : ℕ, d < 1001 → TlineGo 6 5 (2000 + d) = true := by decide

/-- Line `(e,h) = (6,5)`: the full scan `a ≤ 3000`. -/
theorem T_scan_6_5 : ∀ a : ℕ, a ≤ 3000 → TlineGo 6 5 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_6_5_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_6_5_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_6_5_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

end Proof
end Erdos1112


/-! Flattened from Erdos1112Proof.Sharp.CaseTScanE7. -/
/-
Case T scan blocks (T-tail, part (i)), lines `e = 7`:
kernel-decided verification of `TlineGo 7 h a` for `a ≤ 3000`, chunked in
three per-line blocks of ≤ 1001 values each (cacheable, failure-localizing).
-/

namespace Erdos1112
namespace Proof

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_7_1_b0 : ∀ a : ℕ, a < 1000 → TlineGo 7 1 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_7_1_b1 : ∀ d : ℕ, d < 1000 → TlineGo 7 1 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_7_1_b2 : ∀ d : ℕ, d < 1001 → TlineGo 7 1 (2000 + d) = true := by decide

/-- Line `(e,h) = (7,1)`: the full scan `a ≤ 3000`. -/
theorem T_scan_7_1 : ∀ a : ℕ, a ≤ 3000 → TlineGo 7 1 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_7_1_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_7_1_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_7_1_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_7_2_b0 : ∀ a : ℕ, a < 1000 → TlineGo 7 2 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_7_2_b1 : ∀ d : ℕ, d < 1000 → TlineGo 7 2 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_7_2_b2 : ∀ d : ℕ, d < 1001 → TlineGo 7 2 (2000 + d) = true := by decide

/-- Line `(e,h) = (7,2)`: the full scan `a ≤ 3000`. -/
theorem T_scan_7_2 : ∀ a : ℕ, a ≤ 3000 → TlineGo 7 2 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_7_2_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_7_2_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_7_2_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_7_3_b0 : ∀ a : ℕ, a < 1000 → TlineGo 7 3 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_7_3_b1 : ∀ d : ℕ, d < 1000 → TlineGo 7 3 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_7_3_b2 : ∀ d : ℕ, d < 1001 → TlineGo 7 3 (2000 + d) = true := by decide

/-- Line `(e,h) = (7,3)`: the full scan `a ≤ 3000`. -/
theorem T_scan_7_3 : ∀ a : ℕ, a ≤ 3000 → TlineGo 7 3 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_7_3_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_7_3_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_7_3_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_7_4_b0 : ∀ a : ℕ, a < 1000 → TlineGo 7 4 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_7_4_b1 : ∀ d : ℕ, d < 1000 → TlineGo 7 4 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_7_4_b2 : ∀ d : ℕ, d < 1001 → TlineGo 7 4 (2000 + d) = true := by decide

/-- Line `(e,h) = (7,4)`: the full scan `a ≤ 3000`. -/
theorem T_scan_7_4 : ∀ a : ℕ, a ≤ 3000 → TlineGo 7 4 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_7_4_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_7_4_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_7_4_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

end Proof
end Erdos1112


/-! Flattened from Erdos1112Proof.Sharp.CaseTScanE8. -/
/-
Case T scan blocks (T-tail, part (i)), lines `e = 8`:
kernel-decided verification of `TlineGo 8 h a` for `a ≤ 3000`, chunked in
three per-line blocks of ≤ 1001 values each (cacheable, failure-localizing).
-/

namespace Erdos1112
namespace Proof

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_8_1_b0 : ∀ a : ℕ, a < 1000 → TlineGo 8 1 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_8_1_b1 : ∀ d : ℕ, d < 1000 → TlineGo 8 1 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_8_1_b2 : ∀ d : ℕ, d < 1001 → TlineGo 8 1 (2000 + d) = true := by decide

/-- Line `(e,h) = (8,1)`: the full scan `a ≤ 3000`. -/
theorem T_scan_8_1 : ∀ a : ℕ, a ≤ 3000 → TlineGo 8 1 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_8_1_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_8_1_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_8_1_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_8_2_b0 : ∀ a : ℕ, a < 1000 → TlineGo 8 2 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_8_2_b1 : ∀ d : ℕ, d < 1000 → TlineGo 8 2 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_8_2_b2 : ∀ d : ℕ, d < 1001 → TlineGo 8 2 (2000 + d) = true := by decide

/-- Line `(e,h) = (8,2)`: the full scan `a ≤ 3000`. -/
theorem T_scan_8_2 : ∀ a : ℕ, a ≤ 3000 → TlineGo 8 2 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_8_2_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_8_2_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_8_2_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_8_3_b0 : ∀ a : ℕ, a < 1000 → TlineGo 8 3 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_8_3_b1 : ∀ d : ℕ, d < 1000 → TlineGo 8 3 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_8_3_b2 : ∀ d : ℕ, d < 1001 → TlineGo 8 3 (2000 + d) = true := by decide

/-- Line `(e,h) = (8,3)`: the full scan `a ≤ 3000`. -/
theorem T_scan_8_3 : ∀ a : ℕ, a ≤ 3000 → TlineGo 8 3 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_8_3_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_8_3_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_8_3_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

end Proof
end Erdos1112


/-! Flattened from Erdos1112Proof.Sharp.CaseTScanE9. -/
/-
Case T scan blocks (T-tail, part (i)), lines `e = 9`:
kernel-decided verification of `TlineGo 9 h a` for `a ≤ 3000`, chunked in
three per-line blocks of ≤ 1001 values each (cacheable, failure-localizing).
-/

namespace Erdos1112
namespace Proof

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_9_1_b0 : ∀ a : ℕ, a < 1000 → TlineGo 9 1 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_9_1_b1 : ∀ d : ℕ, d < 1000 → TlineGo 9 1 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_9_1_b2 : ∀ d : ℕ, d < 1001 → TlineGo 9 1 (2000 + d) = true := by decide

/-- Line `(e,h) = (9,1)`: the full scan `a ≤ 3000`. -/
theorem T_scan_9_1 : ∀ a : ℕ, a ≤ 3000 → TlineGo 9 1 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_9_1_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_9_1_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_9_1_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_9_2_b0 : ∀ a : ℕ, a < 1000 → TlineGo 9 2 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_9_2_b1 : ∀ d : ℕ, d < 1000 → TlineGo 9 2 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_9_2_b2 : ∀ d : ℕ, d < 1001 → TlineGo 9 2 (2000 + d) = true := by decide

/-- Line `(e,h) = (9,2)`: the full scan `a ≤ 3000`. -/
theorem T_scan_9_2 : ∀ a : ℕ, a ≤ 3000 → TlineGo 9 2 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_9_2_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_9_2_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_9_2_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

end Proof
end Erdos1112


/-! Flattened from Erdos1112Proof.Sharp.CaseTScanE10. -/
/-
Case T scan blocks (T-tail, part (i)), lines `e = 10`:
kernel-decided verification of `TlineGo 10 h a` for `a ≤ 3000`, chunked in
three per-line blocks of ≤ 1001 values each (cacheable, failure-localizing).
-/

namespace Erdos1112
namespace Proof

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_10_1_b0 : ∀ a : ℕ, a < 1000 → TlineGo 10 1 a = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_10_1_b1 : ∀ d : ℕ, d < 1000 → TlineGo 10 1 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem T_go_10_1_b2 : ∀ d : ℕ, d < 1001 → TlineGo 10 1 (2000 + d) = true := by decide

/-- Line `(e,h) = (10,1)`: the full scan `a ≤ 3000`. -/
theorem T_scan_10_1 : ∀ a : ℕ, a ≤ 3000 → TlineGo 10 1 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_10_1_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_10_1_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_10_1_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

end Proof
end Erdos1112


/-! Flattened from Erdos1112Proof.Sharp.CaseTScan. -/
/-
Case T scan dispatch (T-tail, part (i)): the 50 per-line scans
assembled into one statement over the line parameters. GENERATED FILE.
-/

namespace Erdos1112
namespace Proof

set_option maxHeartbeats 4000000 in
/-- **T-tail, part (i)**, decided: on every T-line (`1 ≤ e, h`, `e+h ≤ 11`,
`e ≠ h`) and every `a ≤ 3000`, side conditions imply budget-or-table. -/
theorem T_scan_all {e h a : ℕ} (he : 1 ≤ e) (hh : 1 ≤ h)
    (hμ : e + h ≤ 11) (hne : e ≠ h) (ha : a ≤ 3000) :
    TlineGo e h a = true := by
  have he10 : e ≤ 10 := by omega
  have hh10 : h ≤ 10 := by omega
  interval_cases e <;> interval_cases h <;>
    first
      | exact absurd rfl hne
      | exact T_scan_1_2 a ha
      | exact T_scan_1_3 a ha
      | exact T_scan_1_4 a ha
      | exact T_scan_1_5 a ha
      | exact T_scan_1_6 a ha
      | exact T_scan_1_7 a ha
      | exact T_scan_1_8 a ha
      | exact T_scan_1_9 a ha
      | exact T_scan_1_10 a ha
      | exact T_scan_2_1 a ha
      | exact T_scan_2_3 a ha
      | exact T_scan_2_4 a ha
      | exact T_scan_2_5 a ha
      | exact T_scan_2_6 a ha
      | exact T_scan_2_7 a ha
      | exact T_scan_2_8 a ha
      | exact T_scan_2_9 a ha
      | exact T_scan_3_1 a ha
      | exact T_scan_3_2 a ha
      | exact T_scan_3_4 a ha
      | exact T_scan_3_5 a ha
      | exact T_scan_3_6 a ha
      | exact T_scan_3_7 a ha
      | exact T_scan_3_8 a ha
      | exact T_scan_4_1 a ha
      | exact T_scan_4_2 a ha
      | exact T_scan_4_3 a ha
      | exact T_scan_4_5 a ha
      | exact T_scan_4_6 a ha
      | exact T_scan_4_7 a ha
      | exact T_scan_5_1 a ha
      | exact T_scan_5_2 a ha
      | exact T_scan_5_3 a ha
      | exact T_scan_5_4 a ha
      | exact T_scan_5_6 a ha
      | exact T_scan_6_1 a ha
      | exact T_scan_6_2 a ha
      | exact T_scan_6_3 a ha
      | exact T_scan_6_4 a ha
      | exact T_scan_6_5 a ha
      | exact T_scan_7_1 a ha
      | exact T_scan_7_2 a ha
      | exact T_scan_7_3 a ha
      | exact T_scan_7_4 a ha
      | exact T_scan_8_1 a ha
      | exact T_scan_8_2 a ha
      | exact T_scan_8_3 a ha
      | exact T_scan_9_1 a ha
      | exact T_scan_9_2 a ha
      | exact T_scan_10_1 a ha
      | exact absurd hμ (by decide)

end Proof
end Erdos1112


/-! Flattened from Erdos1112Proof.Sharp.CaseT. -/
/-
Case T (the Case-T lemma and the T-tail proposition): the finitely many staircase lines
`μ = e + h ≤ 11`, `e ≠ h`. Assembly:
  * `a ≤ 3000`: the kernel-decided per-line/per-block scan `T_scan_all`
    (CaseTScan, T-tail part (i)) plus its soundness `TlineGo_sound`
    (CaseTCore) — variant A / base-form staircase constructions, with the
    158 Table-A rows and the 14 supplementary rows (`tSuppT`, replacing the
    paper's variant B) discharged by frame certificates;
  * `a > 3000`: the generic linear tail `T_tail` (CaseTCore,
    T-tail part (ii)) — base form only, slope `2/μ' ≤ 2/3 < 1`.
Paper: the bounded subset-sum covering section.
-/

namespace Erdos1112
namespace Proof

/-- **Case T**: hard-core, `a ∤ M`, `a ∤ b+M`, `e ≠ h`, `μ = M − a ≤ 11`. -/
theorem caseT {a b M : ℕ} (hc : HardCore a b M)
    (hnD : ¬ a ∣ M) (hnP : ¬ a ∣ (b + M))
    (hL : b - a ≠ M - b) (hμ : M - a ≤ 11) : SharpTriple a b M := by
  rcases Nat.lt_or_ge 3000 a with ha3000 | ha3000
  · exact T_tail hc hL hμ (by omega)
  · -- `a ≤ 3000`: specialize to the line `(e, h) = (b − a, M − b)`.
    have hcop := hc.coprime_a_e
    obtain ⟨ha0, hab, hbM, hco, hδ⟩ := hc
    set e := b - a with hedef
    set h := M - b with hhdef
    have hbe : b = a + e := by omega
    have hMe : M = a + e + h := by omega
    have hnd1 : ¬ a ∣ (e + h) := by
      intro hd
      exact hnD (hMe ▸ (by rw [Nat.add_assoc]; exact Nat.dvd_add (dvd_refl a) hd))
    have hnd2 : ¬ a ∣ (2 * e + h) := by
      intro hd
      apply hnP
      have hbm : b + M = a + a + (2 * e + h) := by omega
      rw [hbm]
      exact Nat.dvd_add (Nat.dvd_add (dvd_refl a) (dvd_refl a)) hd
    have hgo : TlineGo e h a = true :=
      T_scan_all (by omega) (by omega) (by omega) hL ha3000
    have hs := TlineGo_sound (by omega) (by omega) (by omega) hcop hnd1 hnd2 hgo
    rw [hbe, hMe]
    exact hs

end Proof
end Erdos1112


/-! Flattened from Erdos1112Proof.Sharp.CaseBClasses. -/
/-
Case B support: completeness of the Table-B class table.

A Case-B target `(a, b, M)` (hard core, `a ∤ M`, `a ∤ b+M`, `e ≠ h`,
`a ≤ 11`, `μ = M−a ≥ 12`) determines the data `(a, h, b)` with `h := M − b`;
its class is `(a, b % a, h)`. `caseBGuard` records exactly the conditions on
`(a, h, b)` that follow from the Case-B hypotheses. The decided sweep
`caseBComplete` checks, for every guard-passing `(a, h, b)` with `b ≤ 53`,
that some row of `certTableB` is a λ-chain base for it: same `a`, same `h`
(`M₀ = b₀ + h`), same class mod `a` and `b₀ ≤ b` (`(b − b₀) % a = 0` with
`b₀ ≤ b`). Window arithmetic: every table row has `b₀ ≤ 31`, and the window
`[43, 53]` spans a full residue system mod `a` for every `a ≤ 11`, so for
`b ≥ 54` the guard descends along `b ↦ b − a` (`rowFor`); the λ-lift
(the lambda-lift lemma, `FrameCert.lift_iter`) then transports the base certificate to
the target (`sharpTriple_of_base`). Kernel `decide` only.
-/

namespace Erdos1112
namespace Proof

/-- The `(a, h, b)`-conditions satisfied by every Case-B target with
`h := M − b` (Boolean form, for the decided sweep): hard-core shape
(`3 ≤ a`, `1 ≤ h ≤ a−2`, `a < b`, `gcd(a,b) = 1`), the branch conditions
`a ∤ M = b + h` and `a ∤ b + M = 2b + h`, `e = b − a ≠ h`, and
`μ = b − a + h ≥ 12`, together with the Case-B size bound `a ≤ 11`. -/
def caseBGuard (a h b : ℕ) : Bool :=
  decide (3 ≤ a) && decide (a ≤ 11) && decide (1 ≤ h) && decide (h + 2 ≤ a) &&
  decide (a < b) && decide (Nat.gcd a b = 1) &&
  decide ((b + h) % a ≠ 0) && decide ((2 * b + h) % a ≠ 0) &&
  decide (b - a ≠ h) && decide (12 ≤ b - a + h)

/-- Row `(a₀, b₀, M₀, x, Y, Z)` is a usable λ-chain base for the target
data `(a, h, b)`: `a₀ = a`, `b₀ ≤ b`, `b ≡ b₀ (mod a)`, `M₀ = b₀ + h`. -/
def caseBRowMatch (a h b : ℕ) (row : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) : Bool :=
  decide (row.1 = a) && decide (row.2.1 ≤ b) &&
  decide ((b - row.2.1) % a = 0) && decide (row.2.2.1 = row.2.1 + h)

/-- The bounded completeness sweep: every guard-passing `(a, h, b)` with
`a ≤ 11`, `h ≤ 9`, `b ≤ 53` has a base row in `certTableB`. -/
def caseBComplete : Bool :=
  (List.range 12).all fun a =>
    (List.range 10).all fun h =>
      (List.range 54).all fun b =>
        !(caseBGuard a h b) || certTableB.any (caseBRowMatch a h b)

set_option maxRecDepth 1000000 in
theorem caseBComplete_true : caseBComplete = true := by decide

theorem caseBGuard_eq_true_iff {a h b : ℕ} :
    caseBGuard a h b = true ↔
      3 ≤ a ∧ a ≤ 11 ∧ 1 ≤ h ∧ h + 2 ≤ a ∧ a < b ∧ Nat.gcd a b = 1 ∧
      (b + h) % a ≠ 0 ∧ (2 * b + h) % a ≠ 0 ∧ b - a ≠ h ∧ 12 ≤ b - a + h := by
  simp only [caseBGuard, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

theorem caseBRowMatch_eq_true_iff {a h b : ℕ} {row : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ} :
    caseBRowMatch a h b row = true ↔
      row.1 = a ∧ row.2.1 ≤ b ∧ (b - row.2.1) % a = 0 ∧
      row.2.2.1 = row.2.1 + h := by
  simp only [caseBRowMatch, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

/-- Coprimality descends along `b ↦ b − a` (cf. `HardCore.coprime_a_e`). -/
theorem gcd_sub_self_right {a b : ℕ} (hab : a ≤ b) (h : Nat.gcd a b = 1) :
    Nat.gcd a (b - a) = 1 := by
  have h1 : Nat.gcd a (b - a) ∣ a := Nat.gcd_dvd_left _ _
  have h2 : Nat.gcd a (b - a) ∣ b - a := Nat.gcd_dvd_right _ _
  have h3 : Nat.gcd a (b - a) ∣ b := by
    have h5 : Nat.gcd a (b - a) ∣ b - a + a := Nat.dvd_add h2 h1
    rwa [Nat.sub_add_cancel hab] at h5
  have h4 : Nat.gcd a (b - a) ∣ Nat.gcd a b := Nat.dvd_gcd h1 h3
  rw [h] at h4
  exact Nat.dvd_one.mp h4

/-- Sweep soundness inside the decided window. -/
theorem rowFor_small {a h b : ℕ} (hb : b < 54) (hg : caseBGuard a h b = true) :
    ∃ row ∈ certTableB, caseBRowMatch a h b row = true := by
  obtain ⟨-, ha11, -, hh2a, -⟩ := caseBGuard_eq_true_iff.mp hg
  have hall := caseBComplete_true
  simp only [caseBComplete, List.all_eq_true, List.mem_range] at hall
  have hpt := hall a (by omega) h (by omega) b hb
  rw [hg] at hpt
  simp only [Bool.not_true, Bool.false_or] at hpt
  exact List.any_eq_true.mp hpt

/-- **Completeness for all `b`**: every guard-passing target datum has a
base row in `certTableB`, by descent `b ↦ b − a` into the decided window
(the window `[43, 53]` is a full residue system mod `a`, and all guard
conditions are mod-`a`-stable or slack for `b ≥ 54`). -/
theorem rowFor {a h : ℕ} :
    ∀ b, caseBGuard a h b = true →
      ∃ row ∈ certTableB, caseBRowMatch a h b row = true := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro hg
    by_cases hb : b < 54
    · exact rowFor_small hb hg
    · obtain ⟨h3a, ha11, h1h, hh2a, hab, hgcd, hmod1, hmod2, -, -⟩ :=
        caseBGuard_eq_true_iff.mp hg
      have hab' : a ≤ b := Nat.le_of_lt hab
      -- the guard holds at `b - a`
      have hg' : caseBGuard a h (b - a) = true := by
        rw [caseBGuard_eq_true_iff]
        refine ⟨h3a, ha11, h1h, hh2a, by omega, gcd_sub_self_right hab' hgcd,
          ?_, ?_, by omega, by omega⟩
        · intro hcon
          apply hmod1
          have e1 : b + h = b - a + h + a := by omega
          rw [e1, Nat.add_mod_right]
          exact hcon
        · intro hcon
          apply hmod2
          have e2 : 2 * b + h = 2 * (b - a) + h + a + a := by omega
          rw [e2, Nat.add_mod_right, Nat.add_mod_right]
          exact hcon
      obtain ⟨row, hrow, hmatch⟩ := ih (b - a) (by omega) hg'
      obtain ⟨hra, hrb, hrm, hrM⟩ := caseBRowMatch_eq_true_iff.mp hmatch
      refine ⟨row, hrow, caseBRowMatch_eq_true_iff.mpr ⟨hra, by omega, ?_, hrM⟩⟩
      have hstep : b - row.2.1 = b - a - row.2.1 + a := by omega
      rw [hstep, Nat.add_mod_right]
      exact hrm

/-- A matching base row certifies the target triple: the λ-lift
(`FrameCert.lift_iter` at `lam` with `lam * a = b − b₀`) transports the
row's frame certificate to `(a, b, M)`, which then yields (SHARP). -/
theorem sharpTriple_of_base {a b M : ℕ} {row : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ}
    (hrow : row ∈ certTableB) (hra : row.1 = a) (hrb : row.2.1 ≤ b)
    (hrm : (b - row.2.1) % a = 0) (hrM : row.2.2.1 = row.2.1 + (M - b))
    (hbM : b ≤ M) : SharpTriple a b M := by
  have hframe := certTableB_frame row hrow
  rw [hra] at hframe
  obtain ⟨lam, hlam⟩ := Nat.dvd_of_mod_eq_zero hrm
  have hcomm : lam * a = a * lam := Nat.mul_comm lam a
  have hb' : row.2.1 + lam * a = b := by omega
  have hM' : row.2.2.1 + lam * a = M := by omega
  have hlift := hframe.lift_iter lam
  rw [hb', hM'] at hlift
  exact hlift.sharpTriple

end Proof
end Erdos1112


/-! Flattened from Erdos1112Proof.Sharp.CaseB. -/
/-
Case B: `a ≤ 11`, `μ ≥ 12` — Table B base certificates
(one per class `(a, ē, h)`, 178 classes, kernel-decided) extended to every
larger member of the class by the λ-lift (the lambda-lift lemma). Completeness of the
class table is a decidable sweep over the finite class space. Paper: the bounded subset-sum covering section.
-/

namespace Erdos1112
namespace Proof

/-- **Case B**: hard-core, `a ∤ M`, `a ∤ b+M`, `e ≠ h`, `a ≤ 11`,
`μ = M − a ≥ 12`. The hypotheses give the guard on `(a, h, b)` with
`h := M − b`; `rowFor` (decided sweep + descent) produces a Table-B base
row of the class `(a, b % a, h)` at or below `b`, and the λ-lift
(`sharpTriple_of_base`) transports its frame certificate to `(a, b, M)`. -/
theorem caseB {a b M : ℕ} (hc : HardCore a b M)
    (hnD : ¬ a ∣ M) (hnP : ¬ a ∣ (b + M))
    (hL : b - a ≠ M - b) (ha : a ≤ 11) (hμ : 12 ≤ M - a) :
    SharpTriple a b M := by
  have h3a := hc.three_le
  have hhb := hc.h_bounds
  obtain ⟨ha0, hab, hbM, hco, hδ⟩ := hc
  have hg : caseBGuard a (M - b) b = true := by
    rw [caseBGuard_eq_true_iff]
    refine ⟨h3a, ha, hhb.1, by omega, hab, hco, ?_, ?_, hL, by omega⟩
    · have e : b + (M - b) = M := by omega
      rw [e]
      exact fun hmod => hnD (Nat.dvd_of_mod_eq_zero hmod)
    · have e : 2 * b + (M - b) = b + M := by omega
      rw [e]
      exact fun hmod => hnP (Nat.dvd_of_mod_eq_zero hmod)
  obtain ⟨row, hrow, hmatch⟩ := rowFor b hg
  obtain ⟨hra, hrb, hrm, hrM⟩ := caseBRowMatch_eq_true_iff.mp hmatch
  exact sharpTriple_of_base hrow hra hrb hrm hrM (Nat.le_of_lt hbM)

end Proof
end Erdos1112


/-! Flattened from Erdos1112Proof.Sharp.Main. -/
/-
Theorem 3 (SHARP), assembled: strong induction on the maximum M,
reduction to the hard core, and the six-case decision-tree routing
(D / P / L / E / T / B — exhaustive by arithmetic). Paper: the bounded subset-sum covering section.
-/

namespace Erdos1112
namespace Proof

/-- Hard-core routing: the six cases exhaust the hard core. -/
theorem hardcore_cases {a b M : ℕ} (hc : HardCore a b M) :
    SharpTriple a b M := by
  by_cases hD : a ∣ M
  · exact caseD hc hD
  by_cases hP : a ∣ (b + M)
  · exact caseP hc hP
  by_cases hL : b - a = M - b
  · exact caseL hc hL
  by_cases hμ : M - a ≤ 11
  · exact caseT hc hD hP hL hμ
  by_cases ha : 12 ≤ a
  · exact caseE hc hD hP ha (by omega)
  · exact caseB hc hD hP hL (by omega) (by omega)

/-- **Theorem 3 (SHARP)**, by strong induction on the maximum. -/
theorem sharp (M : ℕ) : SharpAt M := by
  induction M using Nat.strong_induction_on with
  | _ M ih => exact sharpAt_of_hardcore M ih (fun a b hc => hardcore_cases hc)

end Proof
end Erdos1112


/-! Flattened from Erdos1112Proof.NonEx.SlotLemma. -/
/-
The slot lemma: alphabets with ≥ 3 letters reduce to the
finite subset-sum lemma (SHARP): if `k − 1 ≥ m(G∞)` then `kA` is
tail-covering — fine slots realize an M-run of subset sums, the k-th summand
is the coarse dial. Consumes Theorem 3 (SHARP) from the Sharp/ layer.
Paper: the non-existence section.

The `sharp`-independent sub-lemmas live in `SlotLemmaParts.lean`; this file
holds only the final assembly, the sole part that imports `Sharp.Main`.
-/

namespace Erdos1112
namespace Proof

open scoped Classical

/-- **Slot core (gcd 1)**: the Slot Lemma when the tail alphabet already has
gcd 1. The slot construction: build `G∞'` as a Finset with
`max = M ≤ d₂`, apply `sharp M` to get a multiset `S` with an `M`-run of
subset sums, place its `|S| ≤ M−1 ≤ k−1` letters at non-adjacent tail
positions (`exists_slot_positions`), realize `base + subsetSums S` via
`slot_realize` + `subsetSums_index`, park the remaining summands, and sweep
the last summand as the coarse dial (`slot_dial`). -/
theorem slot_core_gcd_one {k d₁ d₂ : ℕ} {a : ℕ → ℕ}
    (hk : 3 ≤ k) (hd₁ : 1 ≤ d₁) (hgaps : HasGapsIn d₁ d₂ a) (hd : d₂ ≤ k)
    (h3 : ∃ x y z : ℕ, x ∈ tailAlphabet a ∧ y ∈ tailAlphabet a ∧
      z ∈ tailAlphabet a ∧ x < y ∧ y < z)
    (hgcd1 : ((Finset.Icc 1 d₂).filter (· ∈ tailAlphabet a)).gcd id = 1) :
    ∃ X₀, ∀ x, X₀ ≤ x → x ∈ kFoldSumset k a := by
  classical
  set G : Finset ℕ := (Finset.Icc 1 d₂).filter (· ∈ tailAlphabet a) with hGdef
  obtain ⟨x, y, z, hx, hy, hz, hxy, hyz⟩ := h3
  have hmemG : ∀ w, w ∈ tailAlphabet a → w ∈ G := by
    intro w hw
    rw [hGdef, Finset.mem_filter, Finset.mem_Icc]
    have hb := mem_tailAlphabet_bounds hgaps hw
    exact ⟨⟨by omega, hb.2⟩, hw⟩
  have hxG := hmemG x hx; have hyG := hmemG y hy; have hzG := hmemG z hz
  have hGne : G.Nonempty := ⟨x, hxG⟩
  set M := G.max' hGne with hMdef
  have hMG : M ∈ G := Finset.max'_mem _ hGne
  have hpos : ∀ w ∈ G, 0 < w := by
    intro w hw; rw [hGdef, Finset.mem_filter, Finset.mem_Icc] at hw; omega
  have hleM : ∀ w ∈ G, w ≤ M := fun w hw => Finset.le_max' _ w hw
  have hcard3 : 3 ≤ G.card := by
    have hsub : ({x, y, z} : Finset ℕ) ⊆ G := by
      intro w hw
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl <;> assumption
    have h3c : ({x, y, z} : Finset ℕ).card = 3 := by
      rw [Finset.card_insert_of_notMem (by
            simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
        Finset.card_insert_of_notMem (by
            simp only [Finset.mem_singleton]; omega), Finset.card_singleton]
    exact h3c ▸ Finset.card_le_card hsub
  -- the slot-lemma ↔ subset-sum seam: SharpAt hands `|S| ≤ M − 1`, and `M ≤ d₂ ≤ k`
  -- gives `|S| ≤ k − 1`, with the binding corner `k = d₂ = M`.
  obtain ⟨S, hSmem, hScard, hSrun⟩ := sharp M G hpos hcard3 hgcd1 hleM hMG
  have hMd2 : M ≤ d₂ := (Finset.mem_Icc.mp (Finset.mem_filter.mp (hGdef ▸ hMG)).1).2
  have hSk : S.card ≤ k - 1 := le_trans hScard (by omega)
  obtain ⟨c, hc⟩ := hSrun
  -- tail index (for the dial step bound)
  obtain ⟨T, hT⟩ := exists_tail_index hgaps
  -- enumerate `S` as `δ : Fin S.card → ℕ`
  have hlen : S.toList.length = S.card := Multiset.length_toList S
  set δ : Fin S.card → ℕ := fun t => S.toList.get (t.cast hlen.symm) with hδdef
  have hδmem : ∀ t, δ t ∈ S := fun t => (Multiset.mem_toList).mp (List.get_mem _ _)
  have hδtail : ∀ t, δ t ∈ tailAlphabet a := fun t =>
    (Finset.mem_filter.mp (hGdef ▸ hSmem _ (hδmem t))).2
  have hδS : Multiset.map δ Finset.univ.val = S := by
    have hlist : List.ofFn δ = S.toList := by
      apply List.ext_getElem
      · simp [hlen]
      · intro i h1 h2
        simp only [hδdef, List.getElem_ofFn, List.get_eq_getElem, Fin.val_cast]
    rw [Fin.univ_val_map, hlist, Multiset.coe_toList]
  -- non-adjacent positions realizing each letter as a gap
  obtain ⟨p, -, -, hpgap⟩ := exists_slot_positions δ 0 hδtail
  have hM0 : 0 < M := hpos M hMG
  -- dial data: `a` is strictly increasing, and steps by `≤ M` in the tail
  have hgrow : ∀ n, T ≤ n → a n < a (n + 1) := by
    intro n _; have := hgaps.le_gap n; rw [hgaps.succ_eq_add_gap]; omega
  have hstep : ∀ n, T ≤ n → a (n + 1) ≤ a n + M := by
    intro n hn
    have hgm : gap a n ≤ M := hleM _ (hmemG _ (hT n hn))
    rw [hgaps.succ_eq_add_gap]; omega
  -- base = slot bases + parked summands; the dial sweeps
  set base : ℕ := (∑ t, a (p t)) + (k - 1 - S.card) * a 0 with hbasedef
  have hmem : ∀ n v, T ≤ n → c ≤ v → v ≤ c + (M - 1) →
      base + a n + v ∈ kFoldSumset k a := by
    intro n v _ hcv hvc
    have hvrun : v ∈ subsetSums S := by
      have hveq : v = c + (v - c) := by omega
      rw [hveq]; exact hc (v - c) (by omega)
    rw [← hδS] at hvrun
    obtain ⟨Tset, hTsum⟩ := subsetSums_index δ hvrun
    have hgapsum : (∑ t ∈ Tset, gap a (p t)) = v := by
      rw [Finset.sum_congr rfl (fun t _ => hpgap t)]; exact hTsum
    have hslot := slot_realize hgaps p Tset
    rw [hgapsum] at hslot
    have hpark : (k - 1 - S.card) * a 0 ∈ kFoldSumset (k - 1 - S.card) a := by
      refine ⟨fun _ => 0, ?_⟩
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    have hcomb := add_mem_kFoldSumset (add_mem_kFoldSumset hslot hpark)
      (single_mem_kFoldSumset (a := a) n)
    have hkeq : S.card + (k - 1 - S.card) + 1 = k := by omega
    rw [hkeq] at hcomb
    have hval : (∑ t, a (p t)) + v + (k - 1 - S.card) * a 0 + a n
        = base + a n + v := by rw [hbasedef]; ring
    rwa [hval] at hcomb
  exact slot_dial hM0 hgrow hstep hmem

/-- **the corresponding paper lemma + (SHARP)**: a tail alphabet with at least 3 letters is
tail-covering for every `k ≥ d₂`. Rescales to gcd 1 (`exists_rescale`), runs
the slot core, and lifts back (`tailCoveringN_of_rescaled`). -/
theorem tailCovering_of_three_letters {k d₁ d₂ : ℕ} {a : ℕ → ℕ}
    (hk : 3 ≤ k) (hd₁ : 1 ≤ d₁) (hgaps : HasGapsIn d₁ d₂ a) (hd : d₂ ≤ k)
    (h3 : ∃ x y z : ℕ, x ∈ tailAlphabet a ∧ y ∈ tailAlphabet a ∧
      z ∈ tailAlphabet a ∧ x < y ∧ y < z) :
    TailCoveringN k a := by
  -- rescale to a gcd-1 tail alphabet
  obtain ⟨a', T, g, c, hg0, haffine, h3', hgcd1⟩ := exists_rescale hd₁ hgaps h3
  -- the rescaled sequence has the same gap-band structure (gaps of `a'` divide
  -- those of `a`, so lie in `[1, d₂]`); the slot core applies, then lift.
  suffices hcov' : TailCoveringN k a' by
    exact tailCoveringN_of_rescaled T g c hg0 a' haffine hcov'
  -- `HasGapsIn` requires `0 < a 0` (the problem's `A` is a set of positive
  -- integers). This is unneeded by the internal slot construction, which the
  -- gcd-rescaled `a' n = (a T − a T)/g` (with `a' 0 = 0`) exposes. Handle it at
  -- the interface: run the slot core on `a'' := a' + 1` (`a'' 0 = 1`, same gaps
  -- ⇒ same gcd-1 tail alphabet, so `HasGapsIn 1 d₂ a''` holds), then shift
  -- `a'' → a'` (the `k`-fold sums differ by exactly `k`).
  set a'' : ℕ → ℕ := fun n => a' n + 1 with ha''def
  have hmono' : ∀ n, a' n ≤ a' (n + 1) := by
    intro n
    have h1 := haffine n; have h2 := haffine (n + 1)
    have hm : a (T + n) ≤ a (T + (n + 1)) := hgaps.monotone (by omega)
    rw [h1, h2] at hm
    exact Nat.le_of_mul_le_mul_left (le_of_add_le_add_left hm) hg0
  have hband' : ∀ n, a' n + 1 ≤ a' (n + 1) ∧ a' (n + 1) ≤ a' n + d₂ := by
    intro n
    have h1 := haffine n; have h2 := haffine (n + 1)
    have he : T + (n + 1) = (T + n) + 1 := by omega
    have hga : a (T + (n + 1)) = a (T + n) + gap a (T + n) := by
      rw [he, hgaps.succ_eq_add_gap]
    have hle : 1 ≤ gap a (T + n) := le_trans hd₁ (hgaps.le_gap _)
    have hge : gap a (T + n) ≤ d₂ := hgaps.gap_le _
    have hd2g : d₂ ≤ g * d₂ := Nat.le_mul_of_pos_left d₂ hg0
    rw [h1, h2, Nat.add_assoc] at hga
    have hkey : g * a' (n + 1) = g * a' n + gap a (T + n) := Nat.add_left_cancel hga
    refine ⟨?_, ?_⟩
    · have hlt : g * a' n < g * a' (n + 1) := by omega
      have := Nat.lt_of_mul_lt_mul_left hlt; omega
    · have hle2 : g * a' (n + 1) ≤ g * (a' n + d₂) := by rw [Nat.mul_add]; omega
      have := Nat.le_of_mul_le_mul_left hle2 hg0; omega
  have hgaps'' : HasGapsIn 1 d₂ a'' := by
    refine ⟨Nat.succ_pos _, fun i => ⟨?_, ?_⟩⟩
    · have := (hband' i).1; simp only [ha''def]; omega
    · have := (hband' i).2; simp only [ha''def]; omega
  have hgapeq : ∀ n, gap a'' n = gap a' n := by
    intro n; simp only [gap, ha''def]; have := hmono' n; omega
  have htail_eq : tailAlphabet a'' = tailAlphabet a' := by
    ext d; simp only [tailAlphabet, Set.mem_setOf_eq, hgapeq]
  have h3'' : ∃ x y z : ℕ, x ∈ tailAlphabet a'' ∧ y ∈ tailAlphabet a'' ∧
      z ∈ tailAlphabet a'' ∧ x < y ∧ y < z := htail_eq ▸ h3'
  have hgcd1'' : ((Finset.Icc 1 d₂).filter (· ∈ tailAlphabet a'')).gcd id = 1 := by
    simp only [htail_eq]; exact hgcd1
  obtain ⟨X₀, hX₀⟩ := slot_core_gcd_one hk (le_refl 1) hgaps'' hd h3'' hgcd1''
  -- shift: `y ∈ kA'` ⇐ `y + k ∈ kA''`
  refine ⟨1, one_pos, 0, one_pos, X₀, fun y hy _ => ?_⟩
  obtain ⟨f, hf⟩ := hX₀ (y + k) (by omega)
  refine ⟨f, ?_⟩
  simp only [ha''def, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one] at hf
  omega

end Proof
end Erdos1112


/-! Flattened from Erdos1112Proof.NonEx.TwoLetter.Core. -/
/-
The two-letter combinatorial core: the interval property, the sweep, the
width dichotomy, and the boundary width (palindrome–border–period).

Setting: tail gaps `g_n = δ + e·h_n`, `h_n ∈ {0,1}`, `gcd(δ, δ+e) = 1`,
`q_n = h_1 + ⋯ + h_n`, `W_s = {∑ q_{i_t} : ∑ i_t = s}` (k summands,
repetitions allowed), `W₂(σ) = max−min of q_i + q_j on i+j = σ`.

Interface note: `Wset` does not constrain `1 ≤ f j`. Index `0`
(contributing `qCount h 0 = 0`) matches the paper's tail convention
`a_{1+i}, i ≥ 0` (`x ∈ kA − k·a₁` uses `i_t ≥ 0`), is required for
the antidiagonal pair placements of the width lemmas (`WidthTwoAt` pairs may
use index 0), and is harmless in the sweep.
-/

namespace Erdos1112
namespace Proof

/-- Prefix-count of a binary word `h : ℕ → Bool` (1-indexed positions,
`q h 0 = 0`). -/
def qCount (h : ℕ → Bool) (n : ℕ) : ℕ :=
  (Finset.range n).sum fun i => if h (i + 1) then 1 else 0

lemma qCount_succ (h : ℕ → Bool) (n : ℕ) :
    qCount h (n + 1) = qCount h n + (if h (n + 1) then 1 else 0) :=
  Finset.sum_range_succ _ n

lemma qCount_le (h : ℕ → Bool) (n : ℕ) : qCount h n ≤ n := by
  calc qCount h n ≤ ∑ _i ∈ Finset.range n, 1 :=
        Finset.sum_le_sum fun i _ => by split <;> omega
    _ = n := by simp

/-- The `k`-summand antidiagonal value set
`W_s = {∑_t q_{i_t} : i_t ≥ 0, ∑_t i_t = s}`. -/
def Wset (h : ℕ → Bool) (k s : ℕ) : Set ℕ :=
  {w | ∃ f : Fin k → ℕ, (∑ j, f j) = s ∧ (∑ j, qCount h (f j)) = w}

/-- Two-index antidiagonal width `W₂(σ) ≥ 2` witnessed by two pairs. -/
def WidthTwoAt (h : ℕ → Bool) (σ : ℕ) : Prop :=
  ∃ i j i' j', i + j = σ ∧ i' + j' = σ ∧
    qCount h i + qCount h j + 2 ≤ qCount h i' + qCount h j'

/-! ### `Wset` algebra -/

/-- Transport of `Wset` membership along index/antidiagonal equalities
(placement arithmetic). -/
lemma Wset.congr_mem {h : ℕ → Bool} {k k' s s' w : ℕ} (hk : k = k')
    (hs : s = s') (hw : w ∈ Wset h k s) : w ∈ Wset h k' s' := hk ▸ hs ▸ hw

lemma Wset.single (h : ℕ → Bool) (i : ℕ) : qCount h i ∈ Wset h 1 i :=
  ⟨fun _ => i, by simp, by simp⟩

lemma Wset.add {h : ℕ → Bool} {k₁ k₂ s₁ s₂ w₁ w₂ : ℕ}
    (h₁ : w₁ ∈ Wset h k₁ s₁) (h₂ : w₂ ∈ Wset h k₂ s₂) :
    w₁ + w₂ ∈ Wset h (k₁ + k₂) (s₁ + s₂) := by
  obtain ⟨f, hfs, hfw⟩ := h₁
  obtain ⟨g, hgs, hgw⟩ := h₂
  refine ⟨Fin.append f g, ?_, ?_⟩
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [hfs, hgs]
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [hfw, hgw]

lemma Wset.pair (h : ℕ → Bool) (i j : ℕ) :
    qCount h i + qCount h j ∈ Wset h 2 (i + j) :=
  Wset.add (Wset.single h i) (Wset.single h j)

lemma Wset.nsmul {h : ℕ → Bool} {k s w : ℕ} (m : ℕ) (hw : w ∈ Wset h k s) :
    m * w ∈ Wset h (m * k) (m * s) := by
  induction m with
  | zero =>
      simp only [Nat.zero_mul]
      exact ⟨Fin.elim0, by simp, by simp⟩
  | succ m ih =>
      have h1 := Wset.add ih hw
      simp only [Nat.succ_mul]
      exact h1

lemma Wset.le_sum {h : ℕ → Bool} {k s w : ℕ} (hw : w ∈ Wset h k s) : w ≤ s := by
  obtain ⟨f, hfs, hfw⟩ := hw
  calc w = ∑ j, qCount h (f j) := hfw.symm
    _ ≤ ∑ j, f j := Finset.sum_le_sum fun j _ => qCount_le h (f j)
    _ = s := hfs

lemma Wset.nonempty {h : ℕ → Bool} {k : ℕ} (hk : 0 < k) (s : ℕ) :
    ∃ w, w ∈ Wset h k s := by
  have h1 : qCount h s ∈ Wset h 1 s := Wset.single h s
  have h2 : (0 : ℕ) ∈ Wset h (k - 1) 0 :=
    ⟨fun _ => 0, by simp, by simp [qCount]⟩
  have h3 := Wset.add h1 h2
  have hk' : 1 + (k - 1) = k := by omega
  have hs' : s + 0 = s := by omega
  exact ⟨qCount h s + 0, Wset.congr_mem hk' hs' h3⟩

/-! ### Window endpoints -/

/-- Left endpoint of the antidiagonal window. -/
noncomputable def wmin (h : ℕ → Bool) (k s : ℕ) : ℕ := sInf (Wset h k s)

/-- Right endpoint of the antidiagonal window. -/
noncomputable def wmax (h : ℕ → Bool) (k s : ℕ) : ℕ := sSup (Wset h k s)

lemma bddAbove_Wset (h : ℕ → Bool) (k s : ℕ) : BddAbove (Wset h k s) :=
  ⟨s, fun _ hw => Wset.le_sum hw⟩

lemma wmin_mem {h : ℕ → Bool} {k : ℕ} (hk : 0 < k) (s : ℕ) :
    wmin h k s ∈ Wset h k s :=
  Nat.sInf_mem (Wset.nonempty hk s)

lemma wmax_mem {h : ℕ → Bool} {k : ℕ} (hk : 0 < k) (s : ℕ) :
    wmax h k s ∈ Wset h k s :=
  Nat.sSup_mem (Wset.nonempty hk s) (bddAbove_Wset h k s)

lemma wmin_le {h : ℕ → Bool} {k s w : ℕ} (hw : w ∈ Wset h k s) :
    wmin h k s ≤ w :=
  Nat.sInf_le hw

lemma le_wmax {h : ℕ → Bool} {k s w : ℕ} (hw : w ∈ Wset h k s) :
    w ≤ wmax h k s :=
  le_csSup (bddAbove_Wset h k s) hw

lemma wmax_le_sum {h : ℕ → Bool} {k : ℕ} (hk : 0 < k) (s : ℕ) :
    wmax h k s ≤ s :=
  Wset.le_sum (wmax_mem hk s)

/-- One up-step of a configuration: bump one index; the value moves by
`0` or `1`. -/
lemma Wset.step_up {h : ℕ → Bool} {k s w : ℕ} (hk : 0 < k)
    (hw : w ∈ Wset h k s) :
    ∃ v ∈ Wset h k (s + 1), w ≤ v ∧ v ≤ w + 1 := by
  obtain ⟨f, hfs, hfw⟩ := hw
  refine ⟨∑ j, qCount h (Function.update f ⟨0, hk⟩ (f ⟨0, hk⟩ + 1) j),
    ⟨Function.update f ⟨0, hk⟩ (f ⟨0, hk⟩ + 1), ?_, rfl⟩, ?_, ?_⟩
  all_goals
    have e1 := sum_update_add (fun (_ : Fin k) v => v) f ⟨0, hk⟩ (f ⟨0, hk⟩ + 1)
    have e2 := sum_update_add (fun (_ : Fin k) v => qCount h v) f ⟨0, hk⟩
      (f ⟨0, hk⟩ + 1)
    have q1 := qCount_succ h (f ⟨0, hk⟩)
    have hq : (if h (f ⟨0, hk⟩ + 1) then 1 else 0) ≤ 1 := by split <;> omega
    omega

/-- One down-step of a configuration: shrink one nonzero index; the value
drops by `0` or `1`. -/
lemma Wset.step_down {h : ℕ → Bool} {k s w : ℕ} (hw : w ∈ Wset h k (s + 1)) :
    ∃ v ∈ Wset h k s, w ≤ v + 1 := by
  obtain ⟨f, hfs, hfw⟩ := hw
  have hj : ∃ j₀ : Fin k, 1 ≤ f j₀ := by
    by_contra hn
    push_neg at hn
    have : ∑ j, f j = 0 := Finset.sum_eq_zero fun j _ => by have := hn j; omega
    omega
  obtain ⟨j₀, hj₀⟩ := hj
  have hfj : f j₀ - 1 + 1 = f j₀ := by omega
  refine ⟨∑ j, qCount h (Function.update f j₀ (f j₀ - 1) j),
    ⟨Function.update f j₀ (f j₀ - 1), ?_, rfl⟩, ?_⟩
  all_goals
    have e1 := sum_update_add (fun (_ : Fin k) v => v) f j₀ (f j₀ - 1)
    have e2 := sum_update_add (fun (_ : Fin k) v => qCount h v) f j₀ (f j₀ - 1)
    have q1 : qCount h (f j₀) = qCount h (f j₀ - 1) + (if h (f j₀) then 1 else 0) := by
      have := qCount_succ h (f j₀ - 1); rwa [hfj] at this
    have hq : (if h (f j₀) then 1 else 0) ≤ 1 := by split <;> omega
    omega

/-- `wmax(s+1) ≤ wmax(s) + 1`: the sweep's step bound. -/
lemma wmax_succ_le (h : ℕ → Bool) {k : ℕ} (hk : 0 < k) (s : ℕ) :
    wmax h k (s + 1) ≤ wmax h k s + 1 := by
  obtain ⟨v, hv, hv2⟩ := Wset.step_down (wmax_mem hk (s + 1))
  exact le_trans hv2 (Nat.add_le_add_right (le_wmax hv) 1)

/-- `wmax(s+t) ≤ wmax(s) + t` (iterated step bound). -/
lemma wmax_add_le (h : ℕ → Bool) {k : ℕ} (hk : 0 < k) (s t : ℕ) :
    wmax h k (s + t) ≤ wmax h k s + t := by
  induction t with
  | zero => simp
  | succ t ih =>
      have h1 := wmax_succ_le h hk (s + t)
      have he1 : s + (t + 1) = s + t + 1 := by omega
      rw [he1]
      omega

lemma wmin_succ_le (h : ℕ → Bool) {k : ℕ} (hk : 0 < k) (s : ℕ) :
    wmin h k (s + 1) ≤ wmin h k s + 1 := by
  obtain ⟨v, hv, _, hv2⟩ := Wset.step_up hk (wmin_mem hk s)
  exact le_trans (wmin_le hv) hv2

lemma wmin_add_le (h : ℕ → Bool) {k : ℕ} (hk : 0 < k) (s e : ℕ) :
    wmin h k (s + e) ≤ wmin h k s + e := by
  induction e with
  | zero => simp
  | succ e ih =>
      have h1 : s + (e + 1) = (s + e) + 1 := by omega
      rw [h1]
      have h2 := wmin_succ_le h hk (s + e)
      omega

/-! ### the corresponding paper lemma -/

/-- Connectivity walk: two configurations on the same antidiagonal are
joined by single-index moves changing the value by at most 1; any value
between their values is attained. Strong induction on the `ℓ¹` distance. -/
private lemma connect_aux (h : ℕ → Bool) (k s : ℕ) :
    ∀ D : ℕ, ∀ f f' : Fin k → ℕ, (∑ j, f j) = s → (∑ j, f' j) = s →
      (∑ j, ((f j : ℤ) - f' j).natAbs) = D →
      ∀ u, (∑ j, qCount h (f j)) ≤ u → u ≤ (∑ j, qCount h (f' j)) →
      u ∈ Wset h k s := by
  intro D
  induction D using Nat.strong_induction_on with
  | _ D ih =>
    intro f f' hfs hfs' hD u hu hu'
    rcases eq_or_lt_of_le hu with heq | hlt
    · exact ⟨f, hfs, heq⟩
    by_cases hff' : f = f'
    · subst hff'
      exact absurd (hlt.trans_le hu') (lt_irrefl _)
    -- find a descent coordinate and an ascent coordinate
    have hex_a : ∃ a, f' a < f a := by
      by_contra hno
      push_neg at hno
      apply hff'
      funext j
      by_contra hj
      have hjlt : f j < f' j := lt_of_le_of_ne (hno j) hj
      have hsum : (∑ j, f j) < ∑ j, f' j :=
        Finset.sum_lt_sum (fun i _ => hno i) ⟨j, Finset.mem_univ j, hjlt⟩
      omega
    have hex_b : ∃ b, f b < f' b := by
      by_contra hno
      push_neg at hno
      apply hff'
      funext j
      by_contra hj
      have hjlt : f' j < f j := lt_of_le_of_ne (hno j) (Ne.symm hj)
      have hsum : (∑ j, f' j) < ∑ j, f j :=
        Finset.sum_lt_sum (fun i _ => hno i) ⟨j, Finset.mem_univ j, hjlt⟩
      omega
    obtain ⟨a, ha⟩ := hex_a
    obtain ⟨b, hb⟩ := hex_b
    have hab : a ≠ b := fun hh => by rw [hh] at ha; omega
    -- the move f → g: pull 1 from coordinate a, push 1 onto coordinate b
    set F1 := Function.update f a (f a - 1) with hF1def
    set g := Function.update F1 b (f b + 1) with hgdef
    have hF1a : F1 a = f a - 1 := by rw [hF1def, Function.update_self]
    have hF1b : F1 b = f b := by rw [hF1def, Function.update_of_ne (Ne.symm hab)]
    -- index sums
    have e1 : (∑ j, g j) + F1 b = (f b + 1) + ∑ j, F1 j := by
      rw [hgdef]; exact sum_update_add (fun _ v => v) F1 b (f b + 1)
    have e2 : (∑ j, F1 j) + f a = (f a - 1) + ∑ j, f j := by
      rw [hF1def]; exact sum_update_add (fun _ v => v) f a (f a - 1)
    have hgs : (∑ j, g j) = s := by omega
    -- values
    have e3 : (∑ j, qCount h (g j)) + qCount h (F1 b) =
        qCount h (f b + 1) + ∑ j, qCount h (F1 j) := by
      rw [hgdef]; exact sum_update_add (fun _ v => qCount h v) F1 b (f b + 1)
    have e4 : (∑ j, qCount h (F1 j)) + qCount h (f a) =
        qCount h (f a - 1) + ∑ j, qCount h (f j) := by
      rw [hF1def]; exact sum_update_add (fun _ v => qCount h v) f a (f a - 1)
    have q1 := qCount_succ h (f b)
    have q2 : qCount h (f a) = qCount h (f a - 1) + (if h (f a) then 1 else 0) := by
      have hfa : f a - 1 + 1 = f a := by omega
      have := qCount_succ h (f a - 1)
      rw [hfa] at this
      exact this
    have hqb : (if h (f b + 1) then 1 else 0) ≤ 1 := by split <;> omega
    have hqa : (if h (f a) then 1 else 0) ≤ 1 := by split <;> omega
    have hF1bq : qCount h (F1 b) = qCount h (f b) := by rw [hF1b]
    -- distances
    have e5 : (∑ j, ((g j : ℤ) - f' j).natAbs) + ((F1 b : ℤ) - f' b).natAbs =
        (((f b + 1 : ℕ) : ℤ) - f' b).natAbs + ∑ j, ((F1 j : ℤ) - f' j).natAbs := by
      rw [hgdef]
      exact sum_update_add (fun j v => ((v : ℤ) - f' j).natAbs) F1 b (f b + 1)
    have e6 : (∑ j, ((F1 j : ℤ) - f' j).natAbs) + ((f a : ℤ) - f' a).natAbs =
        (((f a - 1 : ℕ) : ℤ) - f' a).natAbs + ∑ j, ((f j : ℤ) - f' j).natAbs := by
      rw [hF1def]
      exact sum_update_add (fun j v => ((v : ℤ) - f' j).natAbs) f a (f a - 1)
    have hpair : ((f a : ℤ) - f' a).natAbs + ((f b : ℤ) - f' b).natAbs ≤
        ∑ j, ((f j : ℤ) - f' j).natAbs := by
      have hps : ∑ j ∈ ({a, b} : Finset (Fin k)), ((f j : ℤ) - f' j).natAbs =
          ((f a : ℤ) - f' a).natAbs + ((f b : ℤ) - f' b).natAbs :=
        Finset.sum_pair hab
      have hle : ∑ j ∈ ({a, b} : Finset (Fin k)), ((f j : ℤ) - f' j).natAbs ≤
          ∑ j, ((f j : ℤ) - f' j).natAbs :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      omega
    have hF1bd : ((F1 b : ℤ) - f' b).natAbs = ((f b : ℤ) - f' b).natAbs := by
      rw [hF1b]
    -- the two moved coordinates each shed exactly one unit of distance
    have hNAb1 : (((f b + 1 : ℕ) : ℤ) - f' b).natAbs =
        ((f b : ℤ) - f' b).natAbs - 1 := by omega
    have hNAa1 : (((f a - 1 : ℕ) : ℤ) - f' a).natAbs =
        ((f a : ℤ) - f' a).natAbs - 1 := by omega
    have hNAa_pos : 1 ≤ ((f a : ℤ) - f' a).natAbs := by omega
    have hNAb_pos : 1 ≤ ((f b : ℤ) - f' b).natAbs := by omega
    -- recurse at distance D - 2
    have hgD : (∑ j, ((g j : ℤ) - f' j).natAbs) = D - 2 := by omega
    have hDlt : D - 2 < D := by omega
    have hgV : (∑ j, qCount h (g j)) ≤ u := by omega
    exact ih (D - 2) hDlt g f' hgs hfs' hgD u hgV hu'

/-- **the corresponding paper lemma (interval property)**: `W_s` is a full integer interval. -/
theorem Wset_interval (h : ℕ → Bool) (k s : ℕ) (_hk : 0 < k)
    {w w' u : ℕ} (hw : w ∈ Wset h k s) (hw' : w' ∈ Wset h k s)
    (hu : w ≤ u) (hu' : u ≤ w') : u ∈ Wset h k s := by
  obtain ⟨f, hfs, hfw⟩ := hw
  obtain ⟨f', hfs', hfw'⟩ := hw'
  exact connect_aux h k s _ f f' hfs hfs' rfl u (by omega) (by omega)

/-! ### Bridges between the ambient sequence and `Wset` (used by sweep and
the Sturmian ladder). -/

/-- The two-letter ambient identity: `a n = a 0 + δ·n + e·q_n`. -/
lemma sweep_a_eq {d₁ d₂ : ℕ} {a : ℕ → ℕ} (hgaps : HasGapsIn d₁ d₂ a)
    (h : ℕ → Bool) (δ e : ℕ)
    (hgap : ∀ n, gap a n = δ + e * (if h (n + 1) then 1 else 0)) (n : ℕ) :
    a n = a 0 + δ * n + e * qCount h n := by
  induction n with
  | zero => simp [qCount]
  | succ n ih =>
      rw [hgaps.succ_eq_add_gap n, hgap n, ih, qCount_succ]
      ring

/-- Config bridge: every `w ∈ W_s` realizes `k·a₀ + δ·s + e·w ∈ kA`. -/
lemma mem_kFold_of_Wset {k d₁ d₂ : ℕ} {a : ℕ → ℕ} (hgaps : HasGapsIn d₁ d₂ a)
    (h : ℕ → Bool) (δ e : ℕ)
    (hgap : ∀ n, gap a n = δ + e * (if h (n + 1) then 1 else 0))
    {s w : ℕ} (hw : w ∈ Wset h k s) :
    k * a 0 + δ * s + e * w ∈ kFoldSumset k a := by
  obtain ⟨f, hfs, hfw⟩ := hw
  refine ⟨f, ?_⟩
  have hbridge : ∀ j : Fin k, a (f j) = a 0 + δ * f j + e * qCount h (f j) :=
    fun j => sweep_a_eq hgaps h δ e hgap (f j)
  have e1 : (∑ j, a (f j)) =
      (∑ _j : Fin k, a 0) + δ * (∑ j, f j) + e * (∑ j, qCount h (f j)) := by
    rw [Finset.sum_congr rfl (fun j _ => hbridge j), Finset.sum_add_distrib,
      Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  rw [e1, hfs, hfw, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul]

set_option maxHeartbeats 2400000 in
/-- **the corresponding paper lemma (sweep)**: if the windows have width `≥ d₂ − 1` for all
large `s`, the two-letter tail's `kA` contains all large integers.
(Interface in terms of the ambient sequence.) -/
theorem sweep {k d₁ d₂ : ℕ} {a : ℕ → ℕ} (hk : 3 ≤ k)
    (hgaps : HasGapsIn d₁ d₂ a) (_hd : d₂ ≤ k)
    (h : ℕ → Bool) (δ e : ℕ) (hδ : 0 < δ) (he : 0 < e)
    (hco : Nat.Coprime δ (δ + e)) (hd₂ : d₂ = δ + e)
    (hgap : ∀ n, gap a n = δ + e * (if h (n + 1) then 1 else 0))
    (S₀ : ℕ)
    (hwidth : ∀ s, S₀ ≤ s → ∃ w w', w ∈ Wset h k s ∧ w' ∈ Wset h k s ∧
      w + (d₂ - 1) ≤ w') :
    TailCovering k a := by
  have hk0 : 0 < k := by omega
  have hd2pos : 0 < d₂ := by omega
  have hδe : Nat.Coprime δ e := by
    have h' : δ.Coprime (e + δ) := by rwa [Nat.add_comm] at hco
    exact (Nat.coprime_add_self_right).mp h'
  refine ⟨1, one_pos, 0, one_pos, k * a 0 + d₂ * (S₀ + e) + 1, fun x hx _ => ?_⟩
  -- reduced target `x' = x − k·a₀`
  set x' : ℕ := x - k * a 0 with hx'def
  have hx'ge : d₂ * (S₀ + e) + 1 ≤ x' := by omega
  have hxx' : x = k * a 0 + x' := by omega
  -- an admissible level `s₀ ∈ [S₀, S₀+e)` with `δ·s₀ ≡ x' (mod e)`
  obtain ⟨s₀, hs₀lo, hs₀hi, hs₀mod⟩ := exists_mul_mod_eq he hδe x' S₀
  -- `w₀ := (x' − δ·s₀)/e` (one exact division)
  have hwm₀ : wmax h k s₀ ≤ s₀ := wmax_le_sum hk0 s₀
  have hδs₀ : δ * s₀ + e * wmax h k s₀ ≤ x' := by
    have h1 : e * wmax h k s₀ ≤ e * s₀ := Nat.mul_le_mul_left e hwm₀
    have h2 : δ * s₀ + e * s₀ = d₂ * s₀ := by rw [hd₂]; ring
    have h3 : d₂ * s₀ ≤ d₂ * (S₀ + e) := Nat.mul_le_mul_left d₂ (by omega)
    omega
  have hle₀ : δ * s₀ ≤ x' := by omega
  have hdvd : e ∣ x' - δ * s₀ := (Nat.modEq_iff_dvd' hle₀).mp hs₀mod
  set w₀ : ℕ := (x' - δ * s₀) / e with hw₀def
  have hew₀ : e * w₀ = x' - δ * s₀ := Nat.mul_div_cancel' hdvd
  have hw₀ge : wmax h k s₀ ≤ w₀ := by
    have : e * wmax h k s₀ ≤ e * w₀ := by omega
    exact Nat.le_of_mul_le_mul_left this he
  -- the ℤ walk `g j = wmax(s₀+j·e) − w₀ + δ·j`, window `[0, d₂−1]`, step `≤ d₂`
  set g : ℕ → ℤ := fun j => (wmax h k (s₀ + j * e) : ℤ) - w₀ + δ * j with hgdef
  set N : ℕ := w₀ + d₂ with hNdef
  have hg0 : g 0 ≤ 0 := by
    have he0 : g 0 = (wmax h k s₀ : ℤ) - w₀ := by simp [hgdef]
    rw [he0]; omega
  have hgN : (d₂ : ℤ) - 1 ≤ g N := by
    have heN : g N = (wmax h k (s₀ + N * e) : ℤ) - w₀ + δ * N := by simp [hgdef]
    rw [heN, hNdef]
    have hwpos : (0 : ℤ) ≤ (wmax h k (s₀ + (w₀ + d₂) * e) : ℤ) := by positivity
    have hδ1 : (1 : ℤ) ≤ δ := by exact_mod_cast hδ
    have hmul : (w₀ : ℤ) + d₂ ≤ (δ : ℤ) * (w₀ + d₂) := by
      have hnn : (0 : ℤ) ≤ (w₀ : ℤ) + d₂ := by positivity
      calc (w₀ : ℤ) + d₂ = 1 * ((w₀ : ℤ) + d₂) := by ring
        _ ≤ (δ : ℤ) * ((w₀ : ℤ) + d₂) := by
            apply mul_le_mul_of_nonneg_right hδ1 hnn
    have hNe : ((w₀ + d₂ : ℕ) : ℤ) = (w₀ : ℤ) + d₂ := by push_cast; ring
    rw [hNe]
    linarith [hwpos, hmul]
  have hstep : ∀ j, j < N → g (j + 1) - g j ≤ d₂ := by
    intro j _
    have hΔ : wmax h k (s₀ + (j + 1) * e) ≤ wmax h k (s₀ + j * e) + e := by
      have he1 : s₀ + (j + 1) * e = (s₀ + j * e) + e := by ring
      rw [he1]; exact wmax_add_le h hk0 _ e
    have hcast : ((wmax h k (s₀ + (j + 1) * e) : ℤ)) ≤ (wmax h k (s₀ + j * e) : ℤ) + e := by
      exact_mod_cast hΔ
    have hstepeq : g (j + 1) - g j =
        (wmax h k (s₀ + (j + 1) * e) : ℤ) - (wmax h k (s₀ + j * e) : ℤ) + δ := by
      simp only [hgdef]; push_cast; ring
    have hd2e : (d₂ : ℤ) = δ + e := by rw [hd₂]; push_cast; ring
    rw [hstepeq, hd2e]; linarith [hcast]
  have hlohi : (0 : ℤ) ≤ (d₂ : ℤ) - 1 := by
    have h1 : (1 : ℤ) ≤ (d₂ : ℤ) := by exact_mod_cast hd2pos
    omega
  obtain ⟨j, hjN, hjlo, hjhi⟩ :=
    discrete_ivt hg0 hgN hlohi hstep (by omega)
  -- decode: `w_j := wmax(s_j) − g j` lies in the window `W_{s_j}`
  set sj : ℕ := s₀ + j * e with hsjdef
  have hwj_le : (w₀ : ℤ) - δ * j ≤ wmax h k sj := by
    simp only [hgdef, ← hsjdef] at hjlo; linarith
  have hwj_ge : wmin h k sj ≤ (w₀ : ℤ) - δ * j := by
    obtain ⟨wa, wb, hwa, hwb, hwab⟩ := hwidth sj (by simp only [hsjdef]; omega)
    have hmn := wmin_le hwa
    have hmx := le_wmax hwb
    simp only [hgdef, ← hsjdef] at hjhi
    have hd2m1 : (d₂ : ℤ) - 1 ≤ (wmax h k sj : ℤ) - (wmin h k sj : ℤ) := by
      have : (wmin h k sj) + (d₂ - 1) ≤ wmax h k sj := by omega
      have hcast : ((wmin h k sj : ℤ)) + ((d₂ : ℤ) - 1) ≤ (wmax h k sj : ℤ) := by
        have h1 : ((wmin h k sj : ℤ)) + ((d₂ : ℤ) - 1) = ((wmin h k sj + (d₂ - 1) : ℕ) : ℤ) := by
          push_cast; omega
        rw [h1]; exact_mod_cast this
      linarith
    linarith
  -- `w_j : ℕ` with `x' = δ·sj + e·w_j`
  set wj : ℕ := w₀ - δ * j with hwjdef
  have hwjnn : δ * j ≤ w₀ := by
    have : (0 : ℤ) ≤ (w₀ : ℤ) - δ * j := le_trans (by positivity) hwj_ge
    have : (δ * j : ℤ) ≤ w₀ := by linarith
    exact_mod_cast this
  have hwjcast : ((wj : ℤ)) = (w₀ : ℤ) - δ * j := by simp only [hwjdef]; push_cast [hwjnn]; ring
  have hwj_mem : wj ∈ Wset h k sj := by
    apply Wset_interval h k sj hk0 (wmin_mem hk0 sj) (wmax_mem hk0 sj)
    · rw [← Nat.cast_le (α := ℤ), hwjcast]; exact hwj_ge
    · rw [← Nat.cast_le (α := ℤ), hwjcast]; exact hwj_le
  have hx'eq : x' = δ * sj + e * wj := by
    have h1 : (x' : ℤ) = δ * sj + e * wj := by
      have hesj : (e : ℤ) * w₀ = x' - δ * s₀ := by
        rw [← Nat.cast_mul, hew₀]; push_cast [hle₀]; ring
      rw [hwjcast]
      simp only [hsjdef]
      push_cast
      push_cast at hesj
      ring_nf
      ring_nf at hesj
      linarith
    exact_mod_cast h1
  -- conclude `x ∈ kA`
  rw [hxx', hx'eq, ← Nat.add_assoc]
  exact mem_kFold_of_Wset hgaps h δ e hgap hwj_mem

/-- A **palindromic prefix** `h[1..τ]`: `h (i+1) = h (τ - i)` for every interior
position `i < τ`. This is exactly the `W₂(τ) = 0` shape (the corresponding paper lemma). -/
def IsPalindromePrefix (h : ℕ → Bool) (τ : ℕ) : Prop :=
  ∀ i, i < τ → h (i + 1) = h (τ - i)

/-- **2.9 border step 1** (`W₂(τ) = 0 ⟹ palindrome`). If the antidiagonal sum
`qCount i + qCount (τ - i)` is constant in `i` — given in adjacent-difference
form — then `h[1..τ]` is a palindromic prefix. Pure `qCount_succ` bit algebra. -/
theorem palindrome_of_qCount_const {h : ℕ → Bool} {τ : ℕ}
    (hconst : ∀ i, i < τ →
      qCount h (i + 1) + qCount h (τ - (i + 1)) = qCount h i + qCount h (τ - i)) :
    IsPalindromePrefix h τ := by
  intro i hi
  have hc := hconst i hi
  have hq1 := qCount_succ h i
  have hq2 := qCount_succ h (τ - (i + 1))
  rw [show τ - (i + 1) + 1 = τ - i from by omega] at hq2
  have hbit : (if h (i + 1) then (1 : ℕ) else 0) = (if h (τ - i) then 1 else 0) := by
    omega
  cases hb1 : h (i + 1) <;> cases hb2 : h (τ - i) <;> simp_all

/-- **2.9 border step 2** (`border ⟹ period`). Two palindromic prefixes, at
`τ` and `τ - Δ`, force period `Δ` on the window `(Δ, τ]`: `h m = h (m - Δ)`.
(Classical border–period duality, done by index chasing with `i := τ - m`.) -/
theorem period_of_two_palindromes {h : ℕ → Bool} {τ Δ : ℕ}
    (hΔ : 0 < Δ) (hΔτ : Δ ≤ τ)
    (hτ : IsPalindromePrefix h τ) (hτΔ : IsPalindromePrefix h (τ - Δ)) :
    ∀ m, Δ < m → m ≤ τ → h m = h (m - Δ) := by
  intro m hm1 hm2
  have e1 := hτ (τ - m) (by omega)
  have e2 := hτΔ (τ - m) (by omega)
  rw [show τ - (τ - m) = m from by omega] at e1
  rw [show τ - Δ - (τ - m) = m - Δ from by omega] at e2
  rw [← e1]; exact e2

/-- **2.9 border step 3** (`period windows ⟹ eventual periodicity`).
Arbitrarily long period-`Δ` windows (from an unbounded family of palindromes)
make `h` eventually periodic with period `Δ` — the shape refuted by `hnp`. -/
theorem eventuallyPeriodic_of_period_windows {h : ℕ → Bool} {Δ : ℕ} (hΔ : 0 < Δ)
    (hwin : ∀ N, ∃ τ, N ≤ τ ∧ ∀ m, Δ < m → m ≤ τ → h m = h (m - Δ)) :
    ∃ p, 0 < p ∧ ∃ T, ∀ n, T ≤ n → h (n + p) = h n := by
  refine ⟨Δ, hΔ, 1, fun n hn => ?_⟩
  obtain ⟨τ, hτN, hτp⟩ := hwin (n + Δ)
  have hstep := hτp (n + Δ) (by omega) (by omega)
  rwa [show n + Δ - Δ = n from by omega] at hstep

/-- **the corresponding paper lemma (even boundary `d₂ = k`)**: when the repetition trick falls one
short (`2⌊(k-1)/2⌋ = k-2 < d₂-1`), the width bound still holds for large `s`.
Proof by contradiction: if it fails at unboundedly many `s`, the two config
families (config (1) `(k/2-1)` extremal pairs + free pair at `τ`, config (2)
with one pair shifted to `σ₁`, free pair at `τ-Δ`) force `W₂(τ)=W₂(τ-Δ)=0`,
hence palindromic prefixes at `τ, τ-Δ` (`palindrome_of_qCount_const`), hence
period `Δ` on `(Δ, τ]` (`period_of_two_palindromes`); `τ(s) → ∞` gives eventual
periodicity (`eventuallyPeriodic_of_period_windows`), contradicting `hnp`. -/
theorem width_even_boundary {k d₂ : ℕ} (h : ℕ → Bool) (hk : 3 ≤ k)
    (hd : d₂ ≤ k) (hbdry : 2 * ((k - 1) / 2) < d₂ - 1)
    (σ₀ : ℕ) (hσ₀ : WidthTwoAt h σ₀)
    (hnp : ¬ ∃ p, 0 < p ∧ ∃ T, ∀ n, T ≤ n → h (n + p) = h n)
    (hunbal : ∀ T, ∃ σ, T ≤ σ ∧ WidthTwoAt h σ) :
    ∃ S₀, ∀ s, S₀ ≤ s → ∃ w w', w ∈ Wset h k s ∧ w' ∈ Wset h k s ∧
      w + (d₂ - 1) ≤ w' := by
  obtain ⟨i, j, i', j', hij, hij', hwidth⟩ := hσ₀
  obtain ⟨σ₁, hσ₁ge, i₁, j₁, i₁', j₁', hij1, hij1', hwidth1⟩ := hunbal (σ₀ + 1)
  set L := qCount h i + qCount h j with hL
  set H := qCount h i' + qCount h j' with hH
  set L₁ := qCount h i₁ + qCount h j₁ with hL1
  set H₁ := qCount h i₁' + qCount h j₁' with hH1
  set Δ := σ₁ - σ₀ with hΔdef
  have hΔ : 0 < Δ := by omega
  -- the boundary hypothesis forces `k` even and `d₂ = k`
  have hkev : k % 2 = 0 := by omega
  have hd2k : d₂ = k := by omega
  have hLmem : L ∈ Wset h 2 σ₀ := hij ▸ Wset.pair h i j
  have hHmem : H ∈ Wset h 2 σ₀ := hij' ▸ Wset.pair h i' j'
  have hL1mem : L₁ ∈ Wset h 2 σ₁ := hij1 ▸ Wset.pair h i₁ j₁
  have hH1mem : H₁ ∈ Wset h 2 σ₁ := hij1' ▸ Wset.pair h i₁' j₁'
  by_contra hcon
  push_neg at hcon
  apply hnp
  apply eventuallyPeriodic_of_period_windows hΔ
  intro N
  obtain ⟨s, hsge, hsnar⟩ := hcon (N + (k / 2 - 1) * σ₀ + σ₁ + Δ)
  set τ := s - (k / 2 - 1) * σ₀ with hτdef
  refine ⟨τ, by omega, ?_⟩
  -- **The core** : with the width `≤ k-2`, any base config with a `(k-2)`-spread
  -- plus a free pair on antidiagonal `τ'` forces that antidiagonal constant,
  -- i.e. `h[1..τ']` palindromic.
  have key : ∀ blo bhi B τ' : ℕ, blo ∈ Wset h (k - 2) B → bhi ∈ Wset h (k - 2) B →
      blo + (k - 2) ≤ bhi → B + τ' = s → IsPalindromePrefix h τ' := by
    intro blo bhi B τ' hblo hbhi hspread hBs
    apply palindrome_of_qCount_const
    intro x hx
    have mk : ∀ z, z ≤ τ' → ∀ b, b ∈ Wset h (k - 2) B →
        b + (qCount h z + qCount h (τ' - z)) ∈ Wset h k s := by
      intro z hz b hb
      have hpz : qCount h z + qCount h (τ' - z) ∈ Wset h 2 τ' :=
        Wset.congr_mem rfl (show z + (τ' - z) = τ' from by omega) (Wset.pair h z (τ' - z))
      exact Wset.congr_mem (show k - 2 + 2 = k from by omega) hBs (Wset.add hb hpz)
    have h1 := hsnar _ _ (mk x (by omega) blo hblo) (mk (x + 1) (by omega) bhi hbhi)
    have h2 := hsnar _ _ (mk (x + 1) (by omega) blo hblo) (mk x (by omega) bhi hbhi)
    omega
  -- config family (1) at `τ` : `(k/2-1)` pairs at `σ₀`
  have hcoef : (k / 2 - 1) * σ₀ = (k / 2 - 2) * σ₀ + σ₀ := by
    rw [show k / 2 - 1 = (k / 2 - 2) + 1 from by omega, Nat.succ_mul]
  have hspread1 : ∀ x y : ℕ, x + 2 ≤ y → (k / 2 - 1) * x + (k - 2) ≤ (k / 2 - 1) * y := by
    intro x y hxy
    have hm := Nat.mul_le_mul_left (k / 2 - 1) hxy
    have he : (k / 2 - 1) * (x + 2) = (k / 2 - 1) * x + (k / 2 - 1) * 2 := by ring
    have h2 : (k / 2 - 1) * 2 = k - 2 := by omega
    omega
  have hpalτ : IsPalindromePrefix h τ :=
    key ((k / 2 - 1) * L) ((k / 2 - 1) * H) ((k / 2 - 1) * σ₀) τ
      (Wset.congr_mem (show (k / 2 - 1) * 2 = k - 2 from by omega) rfl
        (Wset.nsmul (k / 2 - 1) hLmem))
      (Wset.congr_mem (show (k / 2 - 1) * 2 = k - 2 from by omega) rfl
        (Wset.nsmul (k / 2 - 1) hHmem))
      (hspread1 L H hwidth) (by omega)
  -- config family (2) at `τ - Δ` : `(k/2-2)` pairs at `σ₀` + one pair at `σ₁`
  have hbaseLo : (k / 2 - 2) * L + L₁ ∈ Wset h (k - 2) ((k / 2 - 2) * σ₀ + σ₁) :=
    Wset.congr_mem (show (k / 2 - 2) * 2 + 2 = k - 2 from by omega) rfl
      (Wset.add (Wset.nsmul (k / 2 - 2) hLmem) hL1mem)
  have hbaseHi : (k / 2 - 2) * H + H₁ ∈ Wset h (k - 2) ((k / 2 - 2) * σ₀ + σ₁) :=
    Wset.congr_mem (show (k / 2 - 2) * 2 + 2 = k - 2 from by omega) rfl
      (Wset.add (Wset.nsmul (k / 2 - 2) hHmem) hH1mem)
  have hspread2 : (k / 2 - 2) * L + L₁ + (k - 2) ≤ (k / 2 - 2) * H + H₁ := by
    have hm := Nat.mul_le_mul_left (k / 2 - 2) hwidth
    have he : (k / 2 - 2) * (L + 2) = (k / 2 - 2) * L + (k / 2 - 2) * 2 := by ring
    have h2 : (k / 2 - 2) * 2 = k - 4 := by omega
    omega
  have hpalτΔ : IsPalindromePrefix h (τ - Δ) :=
    key ((k / 2 - 2) * L + L₁) ((k / 2 - 2) * H + H₁) ((k / 2 - 2) * σ₀ + σ₁) (τ - Δ)
      hbaseLo hbaseHi hspread2 (by omega)
  exact period_of_two_palindromes hΔ (by omega) hpalτ hpalτΔ

/-- **the corresponding paper lemma(a) + 2.9**: width production. If some antidiagonal has
`W₂(σ₀) ≥ 2` then (odd `k`, or even `k` with `d₂ ≤ k−1`, or even `k` at the
boundary `d₂ = k` given every tail unbalanced and non-periodicity — Lemma
2.9's palindrome/border/period argument) the sweep hypothesis holds. -/
theorem width_of_unbalanced {k d₂ : ℕ} (h : ℕ → Bool) (hk : 3 ≤ k)
    (hd : d₂ ≤ k) (σ₀ : ℕ) (hσ₀ : WidthTwoAt h σ₀)
    (hnp : ¬ ∃ p, 0 < p ∧ ∃ T, ∀ n, T ≤ n → h (n + p) = h n)
    (hunbal : ∀ T, ∃ σ, T ≤ σ ∧ WidthTwoAt h σ) :
    ∃ S₀, ∀ s, S₀ ≤ s → ∃ w w', w ∈ Wset h k s ∧ w' ∈ Wset h k s ∧
      w + (d₂ - 1) ≤ w' := by
  obtain ⟨i, j, i', j', hij, hij', hwidth⟩ := hσ₀
  set p := (k - 1) / 2 with hp
  set L := qCount h i + qCount h j with hL
  set H := qCount h i' + qCount h j' with hH
  rcases Nat.lt_or_ge (d₂ - 1) (2 * p + 1) with hcov | hbdry
  · -- **2.8(a) repetition**: `p` low/high pairs at `σ₀` + a free block absorbing `s`.
    refine ⟨p * σ₀, fun s hs => ?_⟩
    obtain ⟨F, hF⟩ := Wset.nonempty (show 0 < k - 2 * p by omega) (s - p * σ₀)
    have hLmem : L ∈ Wset h 2 σ₀ := hij ▸ Wset.pair h i j
    have hHmem : H ∈ Wset h 2 σ₀ := hij' ▸ Wset.pair h i' j'
    have hcount : p * 2 + (k - 2 * p) = k := by omega
    have hsum : p * σ₀ + (s - p * σ₀) = s := by omega
    refine ⟨p * L + F, p * H + F,
      Wset.congr_mem hcount hsum (Wset.add (Wset.nsmul p hLmem) hF),
      Wset.congr_mem hcount hsum (Wset.add (Wset.nsmul p hHmem) hF), ?_⟩
    -- `p·H ≥ p·(L+2) = p·L + 2p ≥ p·L + (d₂-1)`
    have : p * L + 2 * p ≤ p * H := by
      have := Nat.mul_le_mul_left p hwidth; ring_nf at this ⊢; omega
    omega
  · -- **2.9 boundary** (`even k`, `d₂ = k`): repetition falls one short.
    exact width_even_boundary h hk hd (by omega) σ₀
      ⟨i, j, i', j', hij, hij', hwidth⟩ hnp hunbal

end Proof
end Erdos1112


/-! Flattened from Erdos1112Proof.NonEx.TwoLetter.MH.Slope. -/
/-
Morse–Hedlund, stage 1: the balance calculus and the slope of a balanced word.

Everything here consumes the balance hypothesis in its unfolded Pi form
(`hbal : ∀ i j n, (q(i+n) − q i : ℤ) − (q(j+n) − q j : ℤ) ≤ 1`), so that this
file needs only `Core` and can be imported by `Balanced.lean` without cycles.

Design: the slope is obtained as
`sSup {(q n − 1)/n : n ≥ 1}` directly — no Fekete, no limits.  The two-sided
uniform bound `|q n − n·α| ≤ 1` (n ≥ 1) comes from the multiplicative chain
`t·q n − (t−1) ≤ q(t·n) ≤ t·q n + (t−1)` and the cross bound
`n·q m − n ≤ m·q n + m`, which shows every `(q m − 1)/m` is ≤ every
`(q n + 1)/n`.
-/

namespace Erdos1112
namespace Proof
namespace MH

theorem qCount_zero (h : ℕ → Bool) : qCount h 0 = 0 := by
  simp [qCount]

theorem qCount_succ (h : ℕ → Bool) (n : ℕ) :
    qCount h (n + 1) = qCount h n + (if h (n + 1) then 1 else 0) := by
  rw [qCount, Finset.sum_range_succ]; rfl

theorem qCount_le (h : ℕ → Bool) (n : ℕ) : qCount h n ≤ n := by
  rw [qCount]
  calc (Finset.range n).sum (fun i => if h (i + 1) then 1 else 0)
      ≤ (Finset.range n).sum (fun _ => 1) :=
        Finset.sum_le_sum (fun i _ => by split <;> omega)
    _ = n := by simp

/-- The unfolded balance hypothesis used throughout this stream. -/
def BalancedHyp (h : ℕ → Bool) : Prop :=
  ∀ i j n : ℕ,
    ((qCount h (i + n) : ℤ) - (qCount h i : ℤ)) -
      ((qCount h (j + n) : ℤ) - (qCount h j : ℤ)) ≤ 1

section Balance

variable {h : ℕ → Bool}

/-- Window subadditivity: `q(m+n) ≤ q m + q n + 1`.
Route: `hbal m 0 n`, `qCount_zero`, `omega`. -/
theorem window_le (hbal : BalancedHyp h) (m n : ℕ) :
    (qCount h (m + n) : ℤ) ≤ qCount h m + qCount h n + 1 := by
  have := hbal m 0 n
  have h0 : qCount h 0 = 0 := qCount_zero h
  rw [Nat.zero_add] at this
  omega

/-- Window superadditivity: `q m + q n ≤ q(m+n) + 1`.
Route: `hbal 0 m n`, `qCount_zero`, `omega`. -/
theorem le_window (hbal : BalancedHyp h) (m n : ℕ) :
    (qCount h m : ℤ) + qCount h n ≤ qCount h (m + n) + 1 := by
  have := hbal 0 m n
  have h0 : qCount h 0 = 0 := qCount_zero h
  rw [Nat.zero_add] at this
  omega

/-- Multiplicative upper chain `q(t·n) ≤ t·q n + (t − 1)` for `t ≥ 1`.
Route: `Nat.le_induction` on `t`; `window_le` at `(t·n, n)`; `push_cast`; `omega`. -/
theorem window_mul_le (hbal : BalancedHyp h) (n : ℕ) : ∀ t : ℕ, 1 ≤ t →
    (qCount h (t * n) : ℤ) ≤ t * qCount h n + (t - 1) := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => simp
  | succ t ht ih =>
      have h2 := window_le hbal (t * n) n
      have heq : (t + 1) * n = t * n + n := by ring
      rw [heq]
      push_cast
      push_cast at ih
      linarith

/-- Multiplicative lower chain `t·q n − (t − 1) ≤ q(t·n)` for `t ≥ 1`.
Route: mirror of `window_mul_le` via `le_window`. -/
theorem le_window_mul (hbal : BalancedHyp h) (n : ℕ) : ∀ t : ℕ, 1 ≤ t →
    (t : ℤ) * qCount h n - (t - 1) ≤ qCount h (t * n) := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => simp
  | succ t ht ih =>
      have h2 := le_window hbal (t * n) n
      have heq : (t + 1) * n = t * n + n := by ring
      rw [heq]
      push_cast
      push_cast at ih
      linarith

/-- Cross bound `n·q m − n ≤ m·q n + m` (`m, n ≥ 1`): both chains at `m·n`.
Route: `le_window_mul n m` (value `n·m`), `window_mul_le m n` — instances
`q(n·m) ≥ n·q m − (n−1)` and `q(m·n) ≤ m·q n + (m−1)`, `Nat.mul_comm`, `omega`. -/
theorem cross_bound (hbal : BalancedHyp h) (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (n : ℤ) * qCount h m - n ≤ m * qCount h n + m := by
  have h1 := le_window_mul hbal m n hn
  have h2 := window_mul_le hbal n m hm
  rw [Nat.mul_comm n m] at h1
  linarith

end Balance

/-- The slope of a binary word: `sSup {(q n − 1)/n : n ≥ 1}` (no limits). -/
noncomputable def slope (h : ℕ → Bool) : ℝ :=
  sSup {x : ℝ | ∃ n : ℕ, 1 ≤ n ∧ x = ((qCount h n : ℝ) - 1) / n}

section SlopeBounds

variable {h : ℕ → Bool}

/-- `q n − 1 ≤ n·slope` for `n ≥ 1`.  Route: `le_csSup`; `BddAbove` from
`cross_bound` at `n := 1` (`div_le_div_iff` cross-multiplication). -/
theorem le_slope (n : ℕ) (hn : 1 ≤ n) :
    (qCount h n : ℝ) - 1 ≤ n * slope h := by
  have hbdd : BddAbove {x : ℝ | ∃ m : ℕ, 1 ≤ m ∧ x = ((qCount h m : ℝ) - 1) / m} := by
    refine ⟨1, fun x hx => ?_⟩
    obtain ⟨m, hm, rfl⟩ := hx
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    rw [div_le_one hm0]
    have hq : (qCount h m : ℝ) ≤ m := by exact_mod_cast qCount_le h m
    linarith
  have hle : ((qCount h n : ℝ) - 1) / n ≤ slope h :=
    le_csSup hbdd ⟨n, hn, rfl⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  calc (qCount h n : ℝ) - 1 = ((qCount h n : ℝ) - 1) / n * n := by field_simp
    _ ≤ slope h * n := mul_le_mul_of_nonneg_right hle hn0.le
    _ = n * slope h := mul_comm _ _

/-- `n·slope ≤ q n + 1` for `n ≥ 1`.  Route: `csSup_le` (nonempty via `n = 1`);
each element `(q m − 1)/m ≤ (q n + 1)/n` by `cross_bound` + `div_le_div_iff`. -/
theorem slope_le (hbal : BalancedHyp h) (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * slope h ≤ qCount h n + 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hne : {x : ℝ | ∃ m : ℕ, 1 ≤ m ∧ x = ((qCount h m : ℝ) - 1) / m}.Nonempty :=
    ⟨((qCount h 1 : ℝ) - 1) / ((1 : ℕ) : ℝ), ⟨1, le_refl 1, rfl⟩⟩
  have hup : slope h ≤ ((qCount h n : ℝ) + 1) / n := by
    apply csSup_le hne
    rintro x ⟨m, hm, rfl⟩
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    rw [div_le_div_iff₀ hm0 hn0]
    have hc : ((n : ℤ) * qCount h m - n : ℝ) ≤ ((m : ℤ) * qCount h n + m : ℝ) := by
      exact_mod_cast cross_bound hbal m n hm hn
    push_cast at hc
    nlinarith
  calc (n : ℝ) * slope h ≤ n * (((qCount h n : ℝ) + 1) / n) :=
        mul_le_mul_of_nonneg_left hup hn0.le
    _ = qCount h n + 1 := by field_simp

/-- `0 ≤ slope h`.  Route: `by_contra`; `exists_nat_gt` picks `n` with
`1/n < −slope`; then `(q n − 1)/n ≤ slope < −1/n` forces `q n < 0`. -/
theorem slope_nonneg : 0 ≤ slope h := by
  by_contra hneg
  push_neg at hneg
  have hs : 0 < -slope h := by linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / (-slope h))
  have hn0 : (0 : ℝ) < n := lt_trans (div_pos one_pos hs) hn
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | hp
    · simp at hn0
    · exact hp
  have h1 := le_slope (h := h) n hn1
  have hq : (0 : ℝ) ≤ qCount h n := Nat.cast_nonneg _
  have h2 : 1 < (n : ℝ) * (-slope h) := by
    have := (div_lt_iff₀ hs).mp hn
    linarith
  nlinarith

/-- `slope h ≤ 1`.  Route: `csSup_le`; `(q m − 1)/m ≤ 1` since `q m ≤ m`
(`qCount` sums `m` indicator terms; `Finset.sum_le_card_nsmul`). -/
theorem slope_le_one : slope h ≤ 1 := by
  have hne : {x : ℝ | ∃ m : ℕ, 1 ≤ m ∧ x = ((qCount h m : ℝ) - 1) / m}.Nonempty :=
    ⟨((qCount h 1 : ℝ) - 1) / ((1 : ℕ) : ℝ), ⟨1, le_refl 1, rfl⟩⟩
  apply csSup_le hne
  rintro x ⟨m, hm, rfl⟩
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  rw [div_le_one hm0]
  have hq : (qCount h m : ℝ) ≤ m := by exact_mod_cast qCount_le h m
  linarith

end SlopeBounds

end MH
end Proof
end Erdos1112


/-! Flattened from Erdos1112Proof.NonEx.TwoLetter.MH.RationalCase. -/
/-
Morse–Hedlund, stage 2: rational slope ⇒ the word is eventually periodic.

Design (Coven–Hedlund-style but fully integer-domain): with
`α = P/Q` the scaled discrepancy `E n := Q·q n − P·n ∈ ℤ` is bounded
(`|E n| ≤ Q`), and the length-`Q` window sums `w n := q(n+Q) − q n` have
oscillation ≤ 1 (balance), hence take at most two adjacent values.  The block
potential `Φ N := ∑_{r<Q} E(N·Q + r)` is bounded and moves by
`Q·∑_r (w(N·Q+r) − P)` per step; excluding the divergent sign patterns leaves
`w − P ∈ {0,1}` (or `{−1,0}`), so `Φ` is monotone and bounded, hence (integer
valued) eventually constant, forcing `w n = P` for all large `n`; the window
recursion `q(n+1) − q(n) = [h(n+1)]` then yields period `Q`.  No reals, no
density, no compactness.
-/

namespace Erdos1112
namespace Proof
namespace MH

/-- A weakly decreasing ℕ-sequence is eventually constant.
Route: `WellFounded.has_min wellFounded_lt (Set.range f)` picks the attained
minimum; `antitone_nat_of_succ_le` gives the other inequality past it. -/
theorem antitone_eventually_constant (f : ℕ → ℕ) (hf : ∀ n, f (n + 1) ≤ f n) :
    ∃ S, ∀ n, S ≤ n → f n = f S := by
  have hanti : Antitone f := antitone_nat_of_succ_le hf
  obtain ⟨m, ⟨S, hSm⟩, hmin⟩ :=
    WellFounded.has_min wellFounded_lt (Set.range f) (Set.range_nonempty f)
  refine ⟨S, fun n hn => ?_⟩
  have h1 : f n ≤ f S := hanti hn
  have h2 : ¬ f n < m := hmin (f n) ⟨n, rfl⟩
  rw [← hSm] at h2
  omega

/-- Generalized telescoping: a shift-`Q` difference sum reindexes to a length-`Q`
window of shift-`N` differences. -/
private theorem sum_shift_diff (f : ℕ → ℤ) (Q N : ℕ) :
    ∑ n ∈ Finset.range N, (f (n + Q) - f n)
      = ∑ j ∈ Finset.range Q, (f (N + j) - f j) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      have hstep : (∑ j ∈ Finset.range Q, (f (N + 1 + j) - f j))
          - (∑ j ∈ Finset.range Q, (f (N + j) - f j)) = f (N + Q) - f N := by
        rw [← Finset.sum_sub_distrib]
        rw [Finset.sum_congr rfl (fun j _ => by
          show (f (N + 1 + j) - f j) - (f (N + j) - f j) = f (N + j + 1) - f (N + j)
          rw [show N + 1 + j = N + j + 1 from by ring]; ring)]
        exact Finset.sum_range_sub (fun j => f (N + j)) Q
      linarith [hstep]

theorem eventuallyPeriodic_of_rational (h : ℕ → Bool)
    (hbal : BalancedHyp h)
    (P : ℤ) (Q : ℕ) (hQ : 0 < Q)
    (hE : ∀ n : ℕ, |(Q : ℤ) * qCount h n - P * n| ≤ Q) :
    ∃ p, 0 < p ∧ ∃ T, ∀ n, T ≤ n → h (n + p) = h n := by
  have hQ0 : (0 : ℤ) < Q := by exact_mod_cast hQ
  set E : ℕ → ℤ := fun n => (Q : ℤ) * qCount h n - P * n with hE_def
  set w : ℕ → ℤ := fun n => (qCount h (n + Q) : ℤ) - qCount h n with hw_def
  have hQw : ∀ n, (Q : ℤ) * (w n - P) = E (n + Q) - E n := by
    intro n; simp only [hE_def, hw_def]; push_cast; ring
  have hosc : ∀ a b, w a - w b ≤ 1 := by
    intro a b; have := hbal a b Q; simp only [hw_def]; linarith
  set S : ℕ → ℤ := fun N => ∑ n ∈ Finset.range N, (w n - P) with hS_def
  have hQS : ∀ N, (Q : ℤ) * S N = ∑ j ∈ Finset.range Q, (E (N + j) - E j) := by
    intro N
    have h1 : (Q : ℤ) * S N = ∑ n ∈ Finset.range N, (E (n + Q) - E n) := by
      simp only [hS_def, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun n _ => hQw n)
    rw [h1, sum_shift_diff]
  have hSbd : ∀ N, |S N| ≤ 2 * Q := by
    intro N
    have hb : |(Q : ℤ) * S N| ≤ 2 * Q * Q := by
      rw [hQS]
      calc |∑ j ∈ Finset.range Q, (E (N + j) - E j)|
            ≤ ∑ j ∈ Finset.range Q, |E (N + j) - E j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j ∈ Finset.range Q, (2 * Q : ℤ) := by
            refine Finset.sum_le_sum (fun j _ => ?_)
            have h1 := hE (N + j); have h2 := hE j
            simp only [hE_def]
            rw [abs_le] at h1 h2 ⊢; omega
        _ = 2 * Q * Q := by rw [Finset.sum_const, Finset.card_range]; ring
    rw [abs_mul, abs_of_pos hQ0] at hb
    nlinarith [hb, abs_nonneg (S N), hQ0]
  -- monotone dichotomy from oscillation ≤ 1
  have hdich : (∀ n, P ≤ w n) ∨ (∀ n, w n ≤ P) := by
    by_contra hc; push_neg at hc
    obtain ⟨⟨n₁, hn₁⟩, ⟨n₂, hn₂⟩⟩ := hc
    have := hosc n₂ n₁; omega
  -- in either case `S` is monotone and bounded, so eventually constant, forcing `w = P`
  have hwP : ∃ T, ∀ n, T ≤ n → w n = P := by
    rcases hdich with hge | hle
    · have hSmono : ∀ N, S N ≤ S (N + 1) := by
        intro N; simp only [hS_def, Finset.sum_range_succ]; linarith [hge N]
      set g : ℕ → ℕ := fun N => (2 * Q - S N).toNat with hg_def
      have hgle : ∀ N, g (N + 1) ≤ g N := by
        intro N; simp only [hg_def]
        have := hSmono N; have := hSbd N; have := hSbd (N + 1)
        rw [abs_le] at *; omega
      obtain ⟨T, hT⟩ := antitone_eventually_constant g hgle
      refine ⟨T, fun n hn => ?_⟩
      have e1 : S n = S (n + 1) := by
        have ha := hT n hn; have hb := hT (n + 1) (by omega)
        simp only [hg_def] at ha hb
        have b1 := hSbd n; have b2 := hSbd (n + 1); have b3 := hSbd T
        rw [abs_le] at b1 b2 b3; omega
      simp only [hS_def, Finset.sum_range_succ] at e1; linarith
    · have hSmono : ∀ N, S (N + 1) ≤ S N := by
        intro N; simp only [hS_def, Finset.sum_range_succ]; linarith [hle N]
      set g : ℕ → ℕ := fun N => (S N + 2 * Q).toNat with hg_def
      have hgle : ∀ N, g (N + 1) ≤ g N := by
        intro N; simp only [hg_def]
        have := hSmono N; have := hSbd N; have := hSbd (N + 1)
        rw [abs_le] at *; omega
      obtain ⟨T, hT⟩ := antitone_eventually_constant g hgle
      refine ⟨T, fun n hn => ?_⟩
      have e1 : S n = S (n + 1) := by
        have ha := hT n hn; have hb := hT (n + 1) (by omega)
        simp only [hg_def] at ha hb
        have b3 := hSbd T; rw [abs_le] at b3
        have b1 := hSbd n; have b2 := hSbd (n + 1)
        rw [abs_le] at b1 b2; omega
      simp only [hS_def, Finset.sum_range_succ] at e1; linarith
  -- `w = P` on a tail ⇒ period `Q`
  obtain ⟨T, hwPT⟩ := hwP
  refine ⟨Q, hQ, T + 1, fun n hn => ?_⟩
  have hw1 := hwPT (n - 1) (by omega)
  have hw2 := hwPT n (by omega)
  simp only [hw_def] at hw1 hw2
  have hq1 := qCount_succ h (n - 1)
  have hq2 := qCount_succ h (n - 1 + Q)
  rw [show n - 1 + 1 = n from by omega] at hq1
  rw [show n - 1 + Q + 1 = n + Q from by omega] at hq2
  have hbit : (if h n then (1 : ℕ) else 0) = (if h (n + Q) then 1 else 0) := by omega
  cases hb1 : h n <;> cases hb2 : h (n + Q) <;> simp_all

end MH
end Proof
end Erdos1112


/-! Flattened from Erdos1112Proof.NonEx.TwoLetter.MH.IrrationalCase. -/
/-
Morse–Hedlund, stage 3: irrational slope ⇒ some tail of the counting function
is exactly mechanical.

Threshold separation, density-free route: with the discrepancy
`D n := q n − n·α ∈ [−1, 1]`, a *bad pair* (`ε m = 1`, `ε n = 0`,
`{mα} < {nα}`) is **exactly** a pair with `D m − D n > 1` (since
`D i = ε i − {iα}`).  Balance transfers to increments: for `t := m − n > 0`
and every base `i`,
  `D(i+t) − D(i) ≥ (D(n+t) − D(n)) − 1 = (D m − D n) − 1 > 0`,
and iterating along `0, t, 2t, …` drives `D(r·t) → ∞`, contradicting
`|D| ≤ 1` (mirror case for `m < n`).  So the separation needs NO density, NO
three-distance, NO arc amplification — `exists_nat_gt` is the only analytic
input.  The threshold `c := sSup ({0} ∪ {fract(nα) : ε n = 0})` then defines
the mechanical intercept, with at most ONE boundary index (fract-injectivity
from irrationality), removed by passing to a tail.
-/

namespace Erdos1112
namespace Proof
namespace MH

/-- Discrepancy of the counting word against slope `α`. -/
noncomputable def disc (h : ℕ → Bool) (α : ℝ) (n : ℕ) : ℝ :=
  (qCount h n : ℝ) - n * α

/-- **Separation core.**  Balance + `|D| ≤ 1` force the discrepancy
oscillation ≤ 1.  Route (see header): if
`D m − D n > 1`, iterate the balance-transferred increment along the
arithmetic progression with difference `t = |m − n|`; contradiction with
boundedness after `r > 2/(D m − D n − 1)` steps (`exists_nat_gt`).
No irrationality needed here. -/
theorem disc_osc_le_one (h : ℕ → Bool) (hbal : BalancedHyp h)
    {α : ℝ} (hD : ∀ n : ℕ, |disc h α n| ≤ 1) :
    ∀ m n : ℕ, disc h α m - disc h α n ≤ 1 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨m, n, hgap⟩ := hcon
  have hmn : m ≠ n := by rintro rfl; linarith
  -- increments over a fixed shift t: the n·α terms cancel
  have key : ∀ t i j : ℕ,
      disc h α (i + t) - disc h α i - (disc h α (j + t) - disc h α j) =
        ((qCount h (i + t) : ℝ) - qCount h i) -
          ((qCount h (j + t) : ℝ) - qCount h j) := by
    intro t i j
    simp only [disc]
    push_cast
    ring
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · -- m < n : descending ladder with step t := n − m
    set t := n - m with ht_def
    have htm : m + t = n := by omega
    have hstep : ∀ i : ℕ,
        disc h α (i + t) ≤ disc h α i + (disc h α n - disc h α m + 1) := by
      intro i
      have hb := hbal i m t
      have hbR : ((qCount h (i + t) : ℝ) - qCount h i) -
          ((qCount h (m + t) : ℝ) - qCount h m) ≤ 1 := by exact_mod_cast hb
      have hk := key t i m
      rw [htm] at hk hbR
      linarith
    have hiter : ∀ r : ℕ,
        disc h α (r * t) ≤ disc h α 0 + r * (disc h α n - disc h α m + 1) := by
      intro r
      induction r with
      | zero => simp
      | succ r ih =>
          have hs := hstep (r * t)
          have heq : (r + 1) * t = r * t + t := by ring
          rw [heq]
          push_cast
          linarith
    have hx : 0 < -(disc h α n - disc h α m + 1) := by linarith
    obtain ⟨r, hr⟩ := exists_nat_gt (2 / (-(disc h α n - disc h α m + 1)))
    have h1 := hiter r
    have h2 := hD (r * t)
    have h3 := hD 0
    rw [abs_le] at h2 h3
    have h4 : 2 < (r : ℝ) * (-(disc h α n - disc h α m + 1)) := by
      have := (div_lt_iff₀ hx).mp hr
      linarith
    nlinarith [h1, h2.1, h3.2]
  · -- m > n : ascending ladder with step t := m − n
    set t := m - n with ht_def
    have htn : n + t = m := by omega
    have hstep : ∀ i : ℕ,
        disc h α i + (disc h α m - disc h α n - 1) ≤ disc h α (i + t) := by
      intro i
      have hb := hbal n i t
      have hbR : ((qCount h (n + t) : ℝ) - qCount h n) -
          ((qCount h (i + t) : ℝ) - qCount h i) ≤ 1 := by exact_mod_cast hb
      have hk := key t n i
      rw [htn] at hk hbR
      linarith
    have hiter : ∀ r : ℕ,
        disc h α 0 + r * (disc h α m - disc h α n - 1) ≤ disc h α (r * t) := by
      intro r
      induction r with
      | zero => simp
      | succ r ih =>
          have hs := hstep (r * t)
          have heq : (r + 1) * t = r * t + t := by ring
          rw [heq]
          push_cast
          linarith
    have hx : 0 < disc h α m - disc h α n - 1 := by linarith
    obtain ⟨r, hr⟩ := exists_nat_gt (2 / (disc h α m - disc h α n - 1))
    have h1 := hiter r
    have h2 := hD (r * t)
    have h3 := hD 0
    rw [abs_le] at h2 h3
    have h4 : 2 < (r : ℝ) * (disc h α m - disc h α n - 1) := by
      have := (div_lt_iff₀ hx).mp hr
      linarith
    nlinarith [h1, h2.2, h3.1]

/-- For irrational `α` and `n ≥ 1`, `q n ∈ {⌊nα⌋, ⌊nα⌋ + 1}`.
Route: `|D n| ≤ 1`; the endpoint `q n = nα − 1` is excluded by
`(hα.natCast_mul).ne_int`-style rationality, giving the strict inequality
that `Int.le_floor` / `Int.floor_le_iff` convert. -/
theorem eps_mem (h : ℕ → Bool) {α : ℝ} (hα : Irrational α)
    (hD : ∀ n : ℕ, |disc h α n| ≤ 1) (n : ℕ) (hn : 1 ≤ n) :
    (qCount h n : ℤ) = ⌊(n : ℝ) * α⌋ ∨ (qCount h n : ℤ) = ⌊(n : ℝ) * α⌋ + 1 := by
  have hDn := hD n
  rw [disc, abs_le] at hDn
  have hup : (qCount h n : ℤ) ≤ ⌊(n : ℝ) * α⌋ + 1 := by
    have h1 : (qCount h n : ℤ) ≤ ⌊(n : ℝ) * α + ((1 : ℤ) : ℝ)⌋ :=
      Int.le_floor.mpr (by push_cast; linarith [hDn.2])
    rwa [Int.floor_add_intCast] at h1
  have hstrict : (n : ℝ) * α - 1 < qCount h n := by
    rcases lt_or_eq_of_le hDn.1 with hlt | heq
    · linarith
    · exfalso
      have hirr : Irrational ((n : ℝ) * α) := by
        have hn0 : n ≠ 0 := by omega
        exact_mod_cast hα.natCast_mul hn0
      exact hirr.ne_int ((qCount h n : ℤ) + 1) (by push_cast; linarith)
  have hlow : ⌊(n : ℝ) * α⌋ ≤ (qCount h n : ℤ) := by
    rw [Int.floor_le_iff]
    push_cast
    linarith
  omega

/-- `n ↦ Int.fract (n·α)` is injective on `n ≥ 1` for irrational `α`.
Route: equal fracts ⇒ `(m − n)·α ∈ ℤ` ⇒ `m = n` via `hα.intCast_mul` +
`Irrational.ne_int`. -/
theorem fract_injective {α : ℝ} (hα : Irrational α) {m n : ℕ}
    (_hm : 1 ≤ m) (_hn : 1 ≤ n)
    (hf : Int.fract ((m : ℝ) * α) = Int.fract ((n : ℝ) * α)) : m = n := by
  by_contra hne
  have h1 : (m : ℝ) * α - ⌊(m : ℝ) * α⌋ = (n : ℝ) * α - ⌊(n : ℝ) * α⌋ := by
    rw [Int.self_sub_floor, Int.self_sub_floor]
    exact hf
  have hmn : (m : ℤ) - n ≠ 0 := by omega
  have hirr : Irrational ((((m : ℤ) - n : ℤ) : ℝ) * α) := hα.intCast_mul hmn
  exact hirr.ne_int (⌊(m : ℝ) * α⌋ - ⌊(n : ℝ) * α⌋) (by push_cast; linarith)

/-- **Mechanical tail** for irrational slope.  Route: `disc_osc_le_one` +
`eps_mem`; threshold `c := sSup ({0} ∪ {Int.fract (nα) : ε n = 0})`;
`ε n = 1 ⇒ c ≤ fract(nα)` (upper-bound check unpacks a would-be bad pair),
`ε n = 0 ⇒ fract(nα) ≤ c` (`le_csSup`); at most one index attains `c`
(`fract_injective`), tail `T₀` past it; floor identity
`⌊nα + (1 − c)⌋ = ⌊nα⌋ + ind(fract(nα) ≥ c)` (`Int.floor_intCast_add`);
finally the tail shift `β := Int.fract (T·α + (1 − c))` via
`Int.floor_add_intCast`. -/
theorem mechanical_tail (h : ℕ → Bool) (hbal : BalancedHyp h)
    {α : ℝ} (hα : Irrational α) (hD : ∀ n : ℕ, |disc h α n| ≤ 1) :
    ∃ (β : ℝ) (T : ℕ), ∀ n : ℕ,
      (qCount h (T + n) : ℤ) - qCount h T = ⌊(n : ℝ) * α + β⌋ := by
  classical
  have hosc : ∀ m n, disc h α m - disc h α n ≤ 1 := disc_osc_le_one h hbal hD
  set ev : ℕ → ℤ := fun n => (qCount h n : ℤ) - ⌊(n : ℝ) * α⌋ with hev_def
  have hev01 : ∀ n, 1 ≤ n → ev n = 0 ∨ ev n = 1 := by
    intro n hn
    simp only [hev_def]
    rcases eps_mem h hα hD n hn with h0 | h1
    · left; rw [h0]; ring
    · right; rw [h1]; ring
  have hDeq : ∀ n, disc h α n = (ev n : ℝ) - Int.fract ((n : ℝ) * α) := by
    intro n
    have hf : Int.fract ((n : ℝ) * α) = (n : ℝ) * α - ⌊(n : ℝ) * α⌋ :=
      (Int.self_sub_floor _).symm
    rw [disc, hf]; simp only [hev_def]; push_cast; ring
  have hsep : ∀ m n, 1 ≤ m → 1 ≤ n → ev m = 1 → ev n = 0 →
      Int.fract ((n : ℝ) * α) ≤ Int.fract ((m : ℝ) * α) := by
    intro m n _ _ hem hen
    have := hosc m n; rw [hDeq, hDeq, hem, hen] at this; push_cast at this; linarith
  set S : Set ℝ := insert 0 {r | ∃ n, 1 ≤ n ∧ ev n = 0 ∧ Int.fract ((n : ℝ) * α) = r}
    with hS_def
  have hSbdd : BddAbove S := by
    refine ⟨1, fun r hr => ?_⟩
    rcases hr with h0 | ⟨n, _, _, hrn⟩
    · exact h0 ▸ zero_le_one
    · exact hrn ▸ le_of_lt (Int.fract_lt_one _)
  have hSne : S.Nonempty := ⟨0, Set.mem_insert 0 _⟩
  set c := sSup S with hc_def
  have hc0 : 0 ≤ c := le_csSup hSbdd (Set.mem_insert 0 _)
  have hc1 : c ≤ 1 := csSup_le hSne (fun r hr => by
    rcases hr with h0 | ⟨n, _, _, hrn⟩
    · exact h0 ▸ zero_le_one
    · exact hrn ▸ le_of_lt (Int.fract_lt_one _))
  have hle_c : ∀ n, 1 ≤ n → ev n = 0 → Int.fract ((n : ℝ) * α) ≤ c :=
    fun n hn hen => le_csSup hSbdd (Or.inr ⟨n, hn, hen, rfl⟩)
  have hge_c : ∀ m, 1 ≤ m → ev m = 1 → c ≤ Int.fract ((m : ℝ) * α) :=
    fun m hm hem => csSup_le hSne (fun r hr => by
      rcases hr with h0 | ⟨n, hn, hen, hrn⟩
      · exact h0 ▸ Int.fract_nonneg _
      · exact hrn ▸ hsep m n hm hn hem hen)
  -- tail `T` past the at-most-one boundary index `fract = c`
  obtain ⟨T, hT1, hTbdry⟩ :
      ∃ T : ℕ, 1 ≤ T ∧ ∀ m : ℕ, T ≤ m → Int.fract ((m : ℝ) * α) ≠ c := by
    by_cases hb : ∃ n₀ : ℕ, 1 ≤ n₀ ∧ Int.fract ((n₀ : ℝ) * α) = c
    · obtain ⟨n₀, hn₀1, hn₀c⟩ := hb
      refine ⟨n₀ + 1, by omega, fun m hm hmc => ?_⟩
      have hm1 : 1 ≤ m := by omega
      have hmeq : m = n₀ := fract_injective hα hm1 hn₀1 (by rw [hmc, hn₀c])
      omega
    · push_neg at hb; exact ⟨1, le_refl 1, fun m hm hmc => hb m hm hmc⟩
  have hqm : ∀ m, T ≤ m → (qCount h m : ℤ) = ⌊(m : ℝ) * α + (1 - c)⌋ := by
    intro m hm
    have hm1 : 1 ≤ m := le_trans hT1 hm
    have hne := hTbdry m hm
    have hqeps : (qCount h m : ℤ) = ⌊(m : ℝ) * α⌋ + ev m := by rw [hev_def]; ring
    rw [hqeps]; symm; rw [Int.floor_eq_iff]
    have hfe : (m : ℝ) * α = ⌊(m : ℝ) * α⌋ + Int.fract ((m : ℝ) * α) :=
      (Int.floor_add_fract _).symm
    rcases hev01 m hm1 with h0 | h1
    · have hfc : Int.fract ((m : ℝ) * α) < c := lt_of_le_of_ne (hle_c m hm1 h0) hne
      rw [h0]; push_cast; constructor <;> linarith [hfe, hfc, hc1, Int.fract_nonneg ((m:ℝ)*α)]
    · have hgc : c < Int.fract ((m : ℝ) * α) := lt_of_le_of_ne (hge_c m hm1 h1) (Ne.symm hne)
      rw [h1]; push_cast; constructor <;> linarith [hfe, hgc, hc0, Int.fract_lt_one ((m:ℝ)*α)]
  refine ⟨(T : ℝ) * α + (1 - c) - (qCount h T : ℝ), T, fun n => ?_⟩
  rw [hqm (T + n) (by omega)]
  rw [show (n : ℝ) * α + ((T : ℝ) * α + (1 - c) - (qCount h T : ℝ))
      = (((T + n : ℕ) : ℝ) * α + (1 - c)) - ((qCount h T : ℤ) : ℝ) from by push_cast; ring]
  rw [Int.floor_sub_intCast]

end MH
end Proof
end Erdos1112


/-! Flattened from Erdos1112Proof.NonEx.TwoLetter.Balanced. -/
/-
The Morse–Hedlund classification of balanced one-sided binary words.
Design: slope via sSup, rational ⇒ ultimately periodic, irrational ⇒
threshold separation ⇒ exact tail mechanicity.

`balanced_classification` is assembled here from the staged lemmas in
`MH/Slope.lean`, `MH/RationalCase.lean`, `MH/IrrationalCase.lean`. The
density-free route (threshold separation via discrepancy-oscillation
iteration; no density, equidistribution, or three-distance) is in
`MH/IrrationalCase.lean`.
-/

namespace Erdos1112
namespace Proof

/-- Balancedness of the counting function: any two equal-length windows
carry 1-counts differing by at most 1. -/
def BalancedQ (h : ℕ → Bool) : Prop :=
  ∀ i j n : ℕ, (qCount h (i + n) - qCount h i : ℤ) -
    (qCount h (j + n) - qCount h j : ℤ) ≤ 1

/-- Eventual periodicity of a word. -/
def EventuallyPeriodicW (h : ℕ → Bool) : Prop :=
  ∃ p, 0 < p ∧ ∃ T, ∀ n, T ≤ n → h (n + p) = h n

/-- **Morse–Hedlund (one-sided, minimized form)**: a balanced binary word is
ultimately periodic, or some tail of its counting function is exactly
mechanical with irrational slope: `q(T+n) − q(T) = ⌊n·α + β⌋` for all `n`. -/
theorem balanced_classification (h : ℕ → Bool) (bal : BalancedQ h) :
    EventuallyPeriodicW h ∨
      ∃ (α β : ℝ) (T : ℕ), Irrational α ∧ α ∈ Set.Ioo (0 : ℝ) 1 ∧
        ∀ n : ℕ, (qCount h (T + n) : ℤ) - qCount h T = ⌊(n : ℝ) * α + β⌋ := by
  have hbal : MH.BalancedHyp h := bal
  set α := MH.slope h with hα_def
  -- the uniform discrepancy bound |q n − n·α| ≤ 1 (n = 0 gives 0)
  have hD : ∀ n : ℕ, |MH.disc h α n| ≤ 1 := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [MH.disc, MH.qCount_zero]
    · have h1 := MH.le_slope (h := h) n hn
      have h2 := MH.slope_le (h := h) (hbal := hbal) n hn
      rw [MH.disc, abs_le]
      constructor <;> linarith
  by_cases hirr : Irrational α
  · -- irrational slope: mechanical tail
    right
    obtain ⟨β, T, hmech⟩ := MH.mechanical_tail h hbal hirr hD
    refine ⟨α, β, T, hirr, ⟨?_, ?_⟩, hmech⟩
    · -- 0 < α : slope_nonneg plus irrationality excludes 0
      rcases eq_or_lt_of_le (MH.slope_nonneg (h := h)) with h0 | h0
      · exact absurd h0.symm (by simpa using hirr.ne_int 0)
      · exact h0
    · -- α < 1 : slope_le_one plus irrationality excludes 1
      rcases eq_or_lt_of_le (MH.slope_le_one (h := h)) with h1 | h1
      · exact absurd h1 (by simpa using hirr.ne_int 1)
      · exact h1
  · -- rational slope: eventually periodic
    left
    obtain ⟨r, hr⟩ : α ∈ Set.range ((↑) : ℚ → ℝ) := not_not.mp hirr
    -- clear denominators: |r.den · q n − r.num · n| ≤ r.den
    have hden : ((r.den : ℝ)) * α = (r.num : ℝ) := by
      rw [← hr, Rat.cast_def]
      field_simp
    have hE : ∀ n : ℕ, |(r.den : ℤ) * qCount h n - r.num * n| ≤ r.den := by
      intro n
      have hDn := hD n
      rw [MH.disc] at hDn
      have hpos : (0 : ℝ) < (r.den : ℝ) := by exact_mod_cast r.pos
      have key : |((r.den : ℝ)) * qCount h n - (r.num : ℝ) * n| ≤ (r.den : ℝ) := by
        have expand : ((r.den : ℝ)) * qCount h n - (r.num : ℝ) * n =
            (r.den : ℝ) * ((qCount h n : ℝ) - n * α) := by
          rw [mul_sub]
          have hswap : (r.den : ℝ) * ((n : ℝ) * α) = (n : ℝ) * ((r.den : ℝ) * α) := by
            ring
          rw [hswap, hden]
          ring
        calc |((r.den : ℝ)) * qCount h n - (r.num : ℝ) * n|
            = (r.den : ℝ) * |(qCount h n : ℝ) - n * α| := by
              rw [expand, abs_mul, abs_of_pos hpos]
          _ ≤ (r.den : ℝ) * 1 := mul_le_mul_of_nonneg_left hDn hpos.le
          _ = (r.den : ℝ) := mul_one _
      exact_mod_cast (by push_cast; exact key :
        |((r.den : ℤ) : ℝ) * qCount h n - (r.num : ℝ) * n| ≤ ((r.den : ℤ) : ℝ))
    exact MH.eventuallyPeriodic_of_rational h hbal r.num r.den r.pos hE

/-- Balancedness follows from `W₂ ≤ 1` everywhere (paper 2.8(b) derivation). -/
theorem balancedQ_of_no_widthTwo (h : ℕ → Bool)
    (hno : ∀ σ, ¬ WidthTwoAt h σ) : BalancedQ h := by
  intro i j n
  by_contra hcon
  push_neg at hcon
  -- a violation exhibits two pairs on the antidiagonal σ = i + j + n
  refine hno (i + (j + n)) ⟨i, j + n, i + n, j, rfl, by omega, ?_⟩
  omega

end Proof
end Erdos1112


/-! Flattened from Erdos1112Proof.NonEx.TwoLetter.MH.Walk. -/
/-
Morse–Hedlund, stage 4: quantitative syndeticity input for the uniform-hitting lemma
— Dirichlet step + circle walk.

Design (replaces compactness/ε-net bookkeeping by a walk): Dirichlet
(`Real.exists_int_int_abs_mul_sub_le`) supplies `j ≥ 1`, `K` with
`0 < |jα − K| < b`; if the sign is negative, the multiple
`j' := ⌊1/|θ|⌋₊ · j` flips it (`⌊1/|θ|⌋₊·θ + 1 ∈ (0, |θ|)`, nonzero by
irrationality).  With a positive step `θ < ε/2` the fract-walk
`x_{m+1} = fract(x_m + θ)` enters any arc `(u, u+ε) ⊆ [0,1]` within
`M = 2⌈1/θ⌉₊ + 2` steps: from below `u` it climbs by exact `+θ` (no wrap
possible) and the first crossing lands in `(u, u+θ]`; from above `u` it must
wrap within `⌈1/θ⌉₊` steps, and the wrap successor lies in `[0, θ)` — a hit
if `> u`, otherwise the climb applies.  All uniform in the start point,
hence in the phase `β` and the block position `N`.
-/

namespace Erdos1112
namespace Proof
namespace MH

/-- Positive Dirichlet step below `b` for irrational `α`.
Route: `exists_nat_gt (1/b)`; `Real.exists_int_int_abs_mul_sub_le`;
nonzeroness via `(hα.natCast_mul _).ne_int`; sign flip via `⌊1/(−θ)⌋₊`
multiple as in the module docstring. -/
theorem exists_pos_step {α : ℝ} (hα : Irrational α) {b : ℝ}
    (hb0 : 0 < b) (hb : b ≤ 1 / 2) :
    ∃ (j : ℕ) (K : ℤ), 1 ≤ j ∧ 0 < (j : ℝ) * α - K ∧ (j : ℝ) * α - K < b := by
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (1 / b)
  have hn₀pos : 0 < n₀ := by
    rcases Nat.eq_zero_or_pos n₀ with h | h
    · exfalso; rw [h] at hn₀; simp only [Nat.cast_zero] at hn₀
      have : (0 : ℝ) < 1 / b := by positivity
      linarith
    · exact h
  obtain ⟨j₀, k₀, hk₀pos, hk₀n, habs⟩ := Real.exists_int_int_abs_mul_sub_le α hn₀pos
  have hk₀ne : k₀ ≠ 0 := by omega
  have hb' : (1 : ℝ) / (n₀ + 1) < b := by
    rw [div_lt_iff₀ (by positivity)]
    have h1 : 1 < n₀ * b := (div_lt_iff₀ hb0).mp hn₀
    nlinarith [h1, hb0]
  have hθb : |(k₀ : ℝ) * α - j₀| < b := lt_of_le_of_lt habs hb'
  have hθne : (k₀ : ℝ) * α - j₀ ≠ 0 := sub_ne_zero.mpr ((hα.intCast_mul hk₀ne).ne_int j₀)
  have hcastk : ((k₀.toNat : ℕ) : ℝ) = (k₀ : ℝ) := by
    have := Int.toNat_of_nonneg (le_of_lt hk₀pos); exact_mod_cast this
  rcases lt_or_gt_of_ne hθne with hneg | hpos
  · -- θ < 0: flip via `M = ⌊1/(-θ)⌋₊`
    set θ' : ℝ := -((k₀ : ℝ) * α - j₀) with hθ'
    have hθ'0 : 0 < θ' := by rw [hθ']; linarith
    have hθ'b : θ' < b := by rw [hθ']; rw [abs_lt] at hθb; linarith
    set M : ℕ := ⌊1 / θ'⌋₊ with hM_def
    have hinv1 : 1 < 1 / θ' := by rw [lt_div_iff₀ hθ'0]; linarith
    have hM1 : 1 ≤ M := by
      rw [hM_def]; exact Nat.le_floor (by exact_mod_cast le_of_lt hinv1)
    have hMle : (M : ℝ) * θ' ≤ 1 := by
      have hfl : (M : ℝ) ≤ 1 / θ' := by
        rw [hM_def]; exact Nat.floor_le (le_of_lt (div_pos one_pos hθ'0))
      calc (M : ℝ) * θ' ≤ (1 / θ') * θ' := mul_le_mul_of_nonneg_right hfl (le_of_lt hθ'0)
        _ = 1 := by field_simp
    have hMgt : 1 < ((M : ℝ) + 1) * θ' := by
      have hlt : 1 / θ' < (M : ℝ) + 1 := by rw [hM_def]; exact Nat.lt_floor_add_one _
      have hh : (1 / θ') * θ' < ((M : ℝ) + 1) * θ' := mul_lt_mul_of_pos_right hlt hθ'0
      rwa [one_div_mul_cancel (ne_of_gt hθ'0)] at hh
    have hjpos : 1 ≤ M * k₀.toNat := by
      have h1 : 1 ≤ k₀.toNat := by omega
      calc 1 = 1 * 1 := by ring
        _ ≤ M * k₀.toNat := Nat.mul_le_mul hM1 h1
    have hval : (↑(M * k₀.toNat) : ℝ) * α - (↑((M : ℤ) * j₀ - 1) : ℝ) = 1 - M * θ' := by
      push_cast [hcastk]; rw [hθ']; ring
    refine ⟨M * k₀.toNat, (M : ℤ) * j₀ - 1, hjpos, ?_, ?_⟩
    · rw [hval]
      have hne0 : (↑(M * k₀.toNat) : ℝ) * α - (↑((M : ℤ) * j₀ - 1) : ℝ) ≠ 0 :=
        sub_ne_zero.mpr ((hα.natCast_mul (by omega : M * k₀.toNat ≠ 0)).ne_int _)
      rw [hval] at hne0
      rcases lt_or_gt_of_ne (Ne.symm hne0) with h | h
      · exact h
      · linarith
    · rw [hval]
      have hexp : ((M : ℝ) + 1) * θ' = M * θ' + θ' := by ring
      linarith [hMgt, hθ'b, hexp]
  · -- θ > 0: direct
    refine ⟨k₀.toNat, j₀, by omega, ?_, ?_⟩
    · rw [hcastk]; exact hpos
    · rw [hcastk]; rw [abs_lt] at hθb; linarith

/-- The fract-walk with positive step `θ` (with `2θ < ε`) enters every arc
`(u, u+ε) ⊆ [0,1]` within a bounded number of steps, uniformly in the start.
Route: `T := ⌈1/θ⌉₊`, `M := 2T + 2`; step lemmas via `Int.fract_eq_self` /
`Int.fract_sub_intCast`; exact-climb by induction; first crossing by
`Nat.find`; wrap analysis as in the module docstring. -/
theorem walk_enters {θ ε : ℝ} (hθ0 : 0 < θ) (hθε : 2 * θ < ε) :
    ∃ M : ℕ, ∀ x : ℕ → ℝ, (∀ m, x (m + 1) = Int.fract (x m + θ)) →
      0 ≤ x 0 → x 0 < 1 → ∀ u : ℝ, 0 ≤ u → u + ε ≤ 1 →
      ∃ m, m ≤ M ∧ x m ∈ Set.Ioo u (u + ε) := by
  classical
  refine ⟨⌊2 / θ⌋₊ + 2, fun x hx hx0 hx1 u hu hue => ?_⟩
  set M₀ : ℕ := ⌊2 / θ⌋₊ + 2 with hM₀
  have hMθ : 2 < (M₀ : ℝ) * θ := by
    have h1 : 2 / θ < (⌊2 / θ⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one (2 / θ)
    have h2 : (2 / θ) * θ = 2 := by field_simp
    have h3 := mul_lt_mul_of_pos_right h1 hθ0
    rw [hM₀]; push_cast; nlinarith [h3, h2, hθ0]
  -- unwrap: `y m = x 0 + m θ`, so `x m = fract (y m)`
  set y : ℕ → ℝ := fun m => x 0 + m * θ with hy_def
  have hkey : ∀ z : ℝ, Int.fract (Int.fract z + θ) = Int.fract (z + θ) := by
    intro z
    have harg : Int.fract z + θ = (z + θ) - ((⌊z⌋ : ℤ) : ℝ) := by
      rw [← Int.self_sub_floor]; ring
    rw [harg, Int.fract_sub_intCast]
  have hxy : ∀ m, x m = Int.fract (y m) := by
    intro m
    induction m with
    | zero =>
        simp only [hy_def, Nat.cast_zero, zero_mul, add_zero]
        exact (Int.fract_eq_self.mpr ⟨hx0, hx1⟩).symm
    | succ m ih =>
        rw [hx m, ih, hkey]
        congr 1
        simp only [hy_def]; push_cast; ring
  -- first crossing of `u + 1`
  have hcrossM : u + 1 < y M₀ := by
    simp only [hy_def]; nlinarith [hMθ, hx0, hue, hθε, hθ0]
  have hcross : ∃ m, u + 1 < y m := ⟨M₀, hcrossM⟩
  set m := Nat.find hcross with hm_def
  have hm_spec : u + 1 < y m := Nat.find_spec hcross
  have hm_le : m ≤ M₀ := Nat.find_le hcrossM
  have hm_pos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exfalso; rw [h] at hm_spec
      simp only [hy_def, Nat.cast_zero, zero_mul, add_zero] at hm_spec
      linarith
    · exact h
  have hm_prev : ¬ (u + 1 < y (m - 1)) := Nat.find_min hcross (by omega)
  have hyu1 : y (m - 1) ≤ u + 1 := not_lt.mp hm_prev
  have hymrec : y m = y (m - 1) + θ := by
    simp only [hy_def]; rw [Nat.cast_sub hm_pos]; push_cast; ring
  have hym_hi : y m < u + 1 + ε := by rw [hymrec]; linarith [hyu1, hθε, hθ0]
  -- `y m ∈ (u+1, 2)`, so `fract (y m) = y m - 1`
  have hfloor : ⌊y m⌋ = 1 := by
    rw [Int.floor_eq_iff]
    constructor <;> push_cast <;> [linarith [hm_spec, hu]; linarith [hym_hi, hue]]
  have hxm : x m = y m - 1 := by
    rw [hxy m, ← Int.self_sub_floor, hfloor]; push_cast; ring
  exact ⟨m, hm_le, by rw [hxm]; linarith [hm_spec], by rw [hxm]; linarith [hym_hi]⟩

end MH
end Proof
end Erdos1112


/-! Flattened from Erdos1112Proof.NonEx.TwoLetter.MH.Subwindow. -/
/-
Morse–Hedlund, stage 5: paper the corresponding paper lemma Steps 0+2
(the sub-window claim), with Step 1 (uniform syndeticity) taken as a
hypothesis to avoid an import cycle with `Sturmian.lean` (dependency
inversion; `Sturmian.lean` instantiates `hsyn` with `uniform_syndeticity`).

Follows (2.10.1)–(2.10.6) literally: for `s ≥ S₀ := 2k²L + 1` and any integer
`w` at depth `θ := sα + kβ − w ∈ [η, k−η]`, pick `κ := η/4`, the interval
`I := (max 0 (θ−1) + κ, min (k−1) θ − κ)` (nonempty of length ≥ η/2 in each
of the three θ-regimes), its midpoint `T*`, the arc
`J := ((T*−κ)/(k−1), (T*+κ)/(k−1)) ⊆ (0,1)` of length `η/(2(k−1))`; one free
index per block `(jL, (j+1)L]` via `hsyn`, forced last index
`i_k := s − ∑`; the fractional sum `Θ` lies in `(θ−1, θ+1) ∩ (θ+ℤ) = {θ}`
(the mod-1 pinning), which converts to `∑ q(i_t) = w` by the exact
mechanical form.
-/

namespace Erdos1112
namespace Proof
namespace MH

/-- **Sub-window claim** (paper 2.10 Step 2).  Route:
choice over blocks via `choose`; sum splitting via `Fin.snoc`,
`Fin.sum_univ_castSucc`; pinning via "integer in `(−1,1)` is `0`". -/
theorem subwindow (h : ℕ → Bool) {α β : ℝ}
    (hmech : ∀ n : ℕ, (qCount h n : ℤ) = ⌊(n : ℝ) * α + β⌋)
    {k : ℕ} (hk : 3 ≤ k) {η : ℝ} (hη0 : 0 < η) (hη8 : η ≤ 1 / 8)
    (L : ℕ) (_hL : 0 < L)
    (hsyn : ∀ (u : ℝ) (N : ℕ), u + η / (2 * ((k : ℝ) - 1)) ≤ 1 → 0 ≤ u →
      ∃ n, N < n ∧ n ≤ N + L ∧
        Int.fract ((n : ℝ) * α + β) ∈ Set.Ioo u (u + η / (2 * ((k : ℝ) - 1)))) :
    ∃ S₀ : ℕ, ∀ s : ℕ, S₀ ≤ s → ∀ w : ℤ,
      η ≤ (s : ℝ) * α + k * β - w → (s : ℝ) * α + k * β - w ≤ k - η →
      ∃ f : Fin k → ℕ, (∀ j, 1 ≤ f j) ∧ (∑ j, f j) = s ∧
        (∑ j, (qCount h (f j) : ℤ)) = w := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hm2 : 2 ≤ m := by omega
  have hmR2 : (2 : ℝ) ≤ m := by exact_mod_cast hm2
  have hmRpos : (0 : ℝ) < m := by linarith
  have hmp1 : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  set κ : ℝ := η / 4 with hκ
  have hκ0 : 0 < κ := by rw [hκ]; linarith
  set W : ℝ := η / (2 * (((m + 1 : ℕ) : ℝ) - 1)) with hW
  have hWeq : W = η / (2 * (m : ℝ)) := by rw [hW, hmp1]; ring_nf
  have hW0 : 0 < W := by rw [hWeq]; positivity
  have hmW : (m : ℝ) * W = 2 * κ := by rw [hWeq, hκ]; field_simp; ring
  refine ⟨(m + 1) * (m + 1) * L + 1, fun s hs w hθlo hθhi => ?_⟩
  set θ : ℝ := (s : ℝ) * α + ((m + 1 : ℕ) : ℝ) * β - w with hθ
  have hθlo' : η ≤ θ := hθlo
  have hθhi' : θ ≤ (m : ℝ) + 1 - η := by rw [hmp1] at hθhi; exact hθhi
  -- the interval `(max 0 (θ-1)+κ, min m θ − κ)` is nonempty
  have hnonempty : max 0 (θ - 1) + κ < min (m : ℝ) θ - κ := by
    have hlt_θ : max 0 (θ - 1) < θ - 2 * κ :=
      max_lt (by rw [hκ]; linarith) (by rw [hκ]; linarith)
    have hlt_mR : max 0 (θ - 1) < (m : ℝ) - 2 * κ :=
      max_lt (by rw [hκ]; linarith) (by rw [hκ]; linarith)
    have : max 0 (θ - 1) + 2 * κ < min (m : ℝ) θ := lt_min (by linarith) (by linarith)
    linarith
  obtain ⟨Tstar, hTlo, hThi⟩ := exists_between hnonempty
  have hTκ0 : 0 ≤ Tstar - κ := by have := le_max_left 0 (θ - 1); linarith
  have hTκmR : Tstar + κ ≤ (m : ℝ) := by have := min_le_left (m : ℝ) θ; linarith
  set u : ℝ := (Tstar - κ) / m with hu
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have huW : u + W ≤ 1 := by
    rw [hu, hWeq, div_add_div _ _ (ne_of_gt hmRpos) (by positivity),
      div_le_one (by positivity)]
    nlinarith [hTκmR, hmRpos]
  -- choose one index per disjoint length-`L` block, fract in the arc `(u, u+W)`
  have hchoose : ∀ j : Fin m, ∃ n, j.val * L < n ∧ n ≤ j.val * L + L ∧
      Int.fract ((n : ℝ) * α + β) ∈ Set.Ioo u (u + W) :=
    fun j => hsyn u (j.val * L) huW hu0
  choose idx hidxlo hidxhi hidxfr using hchoose
  have hidxbd : ∀ j : Fin m, idx j ≤ m * L := by
    intro j
    have h1 := hidxhi j
    have h2 : j.val * L + L ≤ m * L := by
      have h3 : (j.val + 1) * L ≤ m * L := by gcongr; omega
      have h4 : (j.val + 1) * L = j.val * L + L := by ring
      omega
    omega
  have hsum_le : (∑ j, idx j) ≤ m * (m * L) := by
    calc (∑ j : Fin m, idx j) ≤ ∑ _j : Fin m, m * L := Finset.sum_le_sum (fun j _ => hidxbd j)
      _ = m * (m * L) := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
  have hbd : m * (m * L) ≤ (m + 1) * (m + 1) * L := by
    rw [show m * (m * L) = m * m * L from by ring]; gcongr <;> omega
  set ik : ℕ := s - ∑ j, idx j with hik
  have hik1 : 1 ≤ ik := by rw [hik]; omega
  set f : Fin (m + 1) → ℕ := Fin.snoc idx ik with hf
  refine ⟨f, ?_, ?_, ?_⟩
  · -- each index ≥ 1
    intro t
    refine Fin.lastCases ?_ ?_ t
    · rw [hf, Fin.snoc_last]; exact hik1
    · intro j; rw [hf, Fin.snoc_castSucc]; have := hidxlo j; omega
  · -- sum = s
    rw [hf, Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    rw [hik]; omega
  · -- `∑ q = w`, by fract-sum pinning
    set x : Fin (m + 1) → ℝ := fun t => (f t : ℝ) * α + β with hx
    have hfsum : (∑ t, f t) = s := by
      rw [hf, Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]; rw [hik]; omega
    have hfr_j : ∀ j : Fin m, x (Fin.castSucc j) = (idx j : ℝ) * α + β := by
      intro j; simp only [hx, hf, Fin.snoc_castSucc]
    have hne : (Finset.univ : Finset (Fin m)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
    have hmu : (m : ℝ) * u = Tstar - κ := by rw [hu]; field_simp
    have hmuW : (m : ℝ) * (u + W) = Tstar + κ := by rw [mul_add, hmu, hmW]; ring
    have hΘsplit : (∑ t, Int.fract (x t))
        = (∑ j, Int.fract (x (Fin.castSucc j))) + Int.fract (x (Fin.last m)) :=
      Fin.sum_univ_castSucc _
    have hfr_lo : (m : ℝ) * u < ∑ j, Int.fract (x (Fin.castSucc j)) := by
      calc (m : ℝ) * u = ∑ _j : Fin m, u := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ < ∑ j, Int.fract (x (Fin.castSucc j)) :=
              Finset.sum_lt_sum_of_nonempty hne (fun j _ => by rw [hfr_j]; exact (hidxfr j).1)
    have hfr_hi : (∑ j, Int.fract (x (Fin.castSucc j))) < (m : ℝ) * (u + W) := by
      calc (∑ j, Int.fract (x (Fin.castSucc j)))
            < ∑ _j : Fin m, (u + W) :=
              Finset.sum_lt_sum_of_nonempty hne (fun j _ => by rw [hfr_j]; exact (hidxfr j).2)
        _ = (m : ℝ) * (u + W) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hik_fr0 : 0 ≤ Int.fract (x (Fin.last m)) := Int.fract_nonneg _
    have hik_fr1 : Int.fract (x (Fin.last m)) < 1 := Int.fract_lt_one _
    have hΘlo : θ - 1 < ∑ t, Int.fract (x t) := by
      rw [hΘsplit]; linarith [hfr_lo, hmu, hik_fr0, hTlo, le_max_right (0 : ℝ) (θ - 1)]
    have hΘhi : (∑ t, Int.fract (x t)) < θ + 1 := by
      rw [hΘsplit]; linarith [hfr_hi, hmuW, hik_fr1, hThi, min_le_right (m : ℝ) θ]
    have hxsum : (∑ t, x t) = θ + w := by
      simp only [hx]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      rw [show (∑ t, (f t : ℝ)) = ((s : ℕ) : ℝ) from by rw [← Nat.cast_sum, hfsum]]
      rw [hθ]; push_cast; ring
    have hfloorsum : ((∑ t, ⌊x t⌋ : ℤ) : ℝ) = θ + w - ∑ t, Int.fract (x t) := by
      rw [Int.cast_sum,
        Finset.sum_congr rfl (fun t _ => by
          show ((⌊x t⌋ : ℤ) : ℝ) = x t - Int.fract (x t)
          linarith [Int.floor_add_fract (x t)]),
        Finset.sum_sub_distrib, hxsum]
    have hq_eq : (∑ t, (qCount h (f t) : ℤ)) = ∑ t, ⌊x t⌋ :=
      Finset.sum_congr rfl (fun t _ => by rw [hmech])
    rw [hq_eq]
    have hint : (((∑ t, ⌊x t⌋) - w : ℤ) : ℝ) = θ - ∑ t, Int.fract (x t) := by
      rw [Int.cast_sub, hfloorsum]; ring
    have hlt1 : |(((∑ t, ⌊x t⌋) - w : ℤ) : ℝ)| < 1 := by
      rw [hint, abs_lt]; exact ⟨by linarith [hΘhi], by linarith [hΘlo]⟩
    have hz : (∑ t, ⌊x t⌋) - w = 0 := by
      by_contra hne'
      have h1 : (1 : ℝ) ≤ |(((∑ t, ⌊x t⌋) - w : ℤ) : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hne'
      linarith
    omega

end MH
end Proof
end Erdos1112


/-! Flattened from Erdos1112Proof.NonEx.TwoLetter.Sturmian. -/
/-
The Sturmian ladder: a two-letter tail with exactly
mechanical counting function (irrational slope) is tail-covering with m = 1.
Steps: (0) window bookkeeping, (1) uniform syndeticity from a Dirichlet-step
fract-walk (`MH/Walk.lean`; no three-gap needed), (2) exact fractional-sum
completion via the mod-1 pinning (`MH/Subwindow.lean`), (3) the ladder lands.
Paper: the paper's non-existence section, (2.10.1)–(2.10.11), followed literally.
-/

namespace Erdos1112
namespace Proof

/-- **Step 1 (uniform syndeticity).** For irrational `α` and any arc length
`ε > 0` there is `L` such that every `L`-block of consecutive integers
contains an `n` with `Int.fract (n·α + β)` in any prescribed arc of length
`ε` — uniformly in the arc position and in `β`. -/
theorem uniform_syndeticity {α : ℝ} (hα : Irrational α) {ε : ℝ} (hε : 0 < ε) :
    ∃ L, 0 < L ∧ ∀ (β u : ℝ) (N : ℕ), u + ε ≤ 1 → 0 ≤ u →
      ∃ n, N < n ∧ n ≤ N + L ∧ Int.fract ((n : ℝ) * α + β) ∈ Set.Ioo u (u + ε) := by
  -- Dirichlet step, made positive, strictly below min(ε/2, 1/2)
  have hb0 : 0 < min (ε / 2) (1 / 2) := lt_min (half_pos hε) (by norm_num)
  obtain ⟨j, K, hj1, hθ0, hθb⟩ := MH.exists_pos_step hα hb0 (min_le_right _ _)
  set θ : ℝ := (j : ℝ) * α - K with hθ_def
  have hθε : 2 * θ < ε := by
    have h1 : θ < ε / 2 := lt_of_lt_of_le hθb (min_le_left _ _)
    linarith
  obtain ⟨M, hM⟩ := MH.walk_enters hθ0 hθε
  refine ⟨M * j + 1, Nat.succ_pos _, fun β u N hu1 hu0 => ?_⟩
  -- the fract-walk sampled along the AP n = N + 1 + m·j
  set x : ℕ → ℝ := fun m => Int.fract (((N + 1 + m * j : ℕ) : ℝ) * α + β) with hx_def
  have key : ∀ y : ℝ, Int.fract (Int.fract y + θ) = Int.fract (y + θ) := by
    intro y
    have harg : Int.fract y + θ = (y + θ) - ((⌊y⌋ : ℤ) : ℝ) := by
      rw [← Int.self_sub_floor]; ring
    rw [harg, Int.fract_sub_intCast]
  have hrec : ∀ m, x (m + 1) = Int.fract (x m + θ) := by
    intro m
    simp only [hx_def]
    rw [key]
    have harg : (((N + 1 + m * j : ℕ) : ℝ) * α + β) + θ =
        (((N + 1 + (m + 1) * j : ℕ) : ℝ) * α + β) - ((K : ℤ) : ℝ) := by
      rw [hθ_def]; push_cast; ring
    rw [harg, Int.fract_sub_intCast]
  obtain ⟨m, hmM, hmem⟩ := hM x hrec (Int.fract_nonneg _) (Int.fract_lt_one _)
    u hu0 hu1
  refine ⟨N + 1 + m * j, by omega, ?_, ?_⟩
  · have : m * j ≤ M * j := Nat.mul_le_mul_right j hmM
    omega
  · simpa only [hx_def] using hmem

set_option maxHeartbeats 1200000 in
/-- **Sturmian case**: mechanical tail ⇒ tail-covering.
Interface in ambient terms.

Step 3 (paper (2.10.7)–(2.10.11)):
`η := min α (1−α) / 4 ∈ (0, 1/8]`; `L` from `uniform_syndeticity` at arc
length `η/(2(k−1))`; `S₀` from `MH.subwindow`; `a n = a 0 + δn + e·q n` by
induction from `hgap`; for large `y`, solve `y − k·a0 = δs + ew` along the
admissible AP `s ≡ (y − k·a0)·δ⁻¹ (mod e)` (`ZMod e` inverse; `Nat.Coprime δ e`
from `hco` via `Nat.coprime_add_self_right`); `θ(s) = sα + kβ − w(s)` has
exact step `γ = δ + eα ∈ (0, k − 2η)` by (2.10.10)–(2.10.11); `X₀` large
makes `θ(s_min) < η`; the first admissible `θ ≥ η` lands in `[η, k−η]`
(no-skip); `MH.subwindow` yields the k indices; conclude via
`TailCovering.of_cofinite`. -/
theorem tailCovering_of_sturmian {k d₁ d₂ : ℕ} {a : ℕ → ℕ} (hk : 3 ≤ k)
    (hgaps : HasGapsIn d₁ d₂ a) (hd : d₂ ≤ k)
    (h : ℕ → Bool) (δ e : ℕ) (hδ : 0 < δ) (he : 0 < e)
    (hco : Nat.Coprime δ (δ + e)) (hd₂ : d₂ = δ + e)
    (hgap : ∀ n, gap a n = δ + e * (if h (n + 1) then 1 else 0))
    (α β : ℝ) (hα : Irrational α) (hαI : α ∈ Set.Ioo (0 : ℝ) 1)
    (hmech : ∀ n : ℕ, (qCount h n : ℤ) = ⌊(n : ℝ) * α + β⌋) :
    TailCovering k a := by
  apply TailCovering.of_cofinite
  have hα0 : 0 < α := hαI.1
  have hα1 : α < 1 := hαI.2
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  set η : ℝ := min α (1 - α) / 4 with hη
  have hmin0 : 0 < min α (1 - α) := lt_min hα0 (by linarith)
  have hη0 : 0 < η := by rw [hη]; linarith
  have hmin12 : min α (1 - α) ≤ 1 / 2 := by
    rcases le_total α (1 / 2) with hc | hc
    · exact le_trans (min_le_left _ _) hc
    · exact le_trans (min_le_right _ _) (by linarith)
  have hη8 : η ≤ 1 / 8 := by rw [hη]; linarith
  have hk1R : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  set ε : ℝ := η / (2 * ((k : ℝ) - 1)) with hε
  have hε0 : 0 < ε := by rw [hε]; exact div_pos hη0 (by linarith)
  obtain ⟨L, hL0, hsyn0⟩ := uniform_syndeticity hα hε0
  obtain ⟨S₀, hSW⟩ := MH.subwindow h hmech hk hη0 hη8 L hL0
    (fun u N h1 h2 => hsyn0 β u N h1 h2)
  -- Diophantine + θ-landing: every large integer has an admissible `(s, w)`.
  obtain ⟨X₀, hcore⟩ :
      ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → ∃ (s : ℕ) (w : ℤ),
        S₀ ≤ s ∧ η ≤ (s : ℝ) * α + k * β - w ∧ (s : ℝ) * α + k * β - w ≤ k - η ∧
        (δ : ℤ) * s + e * w = (x : ℤ) - k * (a 0) := by
    have hδe : Nat.Coprime δ e :=
      Nat.coprime_add_self_right.mp (by rwa [Nat.add_comm] at hco)
    set A : ℤ := Nat.gcdA δ e with hA
    set B : ℤ := Nat.gcdB δ e with hB
    have hAB : (δ : ℤ) * A + e * B = 1 := by
      have h := Nat.gcd_eq_gcd_ab δ e
      rw [show Nat.gcd δ e = 1 from hδe] at h; push_cast at h; linarith
    set γ : ℝ := (δ : ℝ) + e * α with hγdef
    have heR : (1 : ℝ) ≤ e := by exact_mod_cast he
    have hδR : (1 : ℝ) ≤ δ := by exact_mod_cast hδ
    have hγ0 : 0 < γ := by rw [hγdef]; nlinarith [hα0, heR, hδR]
    have hγk : γ ≤ (k : ℝ) - 2 * η := by
      have hd2R : (d₂ : ℝ) = δ + e := by rw [hd₂]; push_cast; ring
      have hd2k : (d₂ : ℝ) ≤ k := by exact_mod_cast hd
      have hmul : (1 : ℝ) * (1 - α) ≤ e * (1 - α) :=
        mul_le_mul_of_nonneg_right heR (by linarith)
      have hγd2 : γ = (d₂ : ℝ) - e * (1 - α) := by rw [hγdef, hd2R]; ring
      rw [hη]; linarith [min_le_right α (1 - α), hmul, hd2k, hγd2]
    have hABR : (δ : ℝ) * A + e * B = 1 := by exact_mod_cast hAB
    clear_value A B
    set M1 : ℝ := γ * S₀ + e * (k * β - η) with hM1
    set M2 : ℝ := δ * (η + γ - k * β) / α with hM2
    have hM1toNat : M1 ≤ (⌈M1⌉.toNat : ℝ) :=
      le_trans (Int.le_ceil M1) (by exact_mod_cast Int.self_le_toNat ⌈M1⌉)
    have hM2toNat : M2 ≤ (⌈M2⌉.toNat : ℝ) :=
      le_trans (Int.le_ceil M2) (by exact_mod_cast Int.self_le_toNat ⌈M2⌉)
    refine ⟨k * a 0 + ⌈M1⌉.toNat + ⌈M2⌉.toNat + 1, fun x hx => ?_⟩
    set X : ℤ := (x : ℤ) - k * (a 0) with hX
    clear_value X
    have hXR : ((⌈M1⌉.toNat : ℝ) + ⌈M2⌉.toNat + 1) ≤ (X : ℝ) := by
      have hXge : (⌈M1⌉.toNat : ℤ) + ⌈M2⌉.toNat + 1 ≤ X := by rw [hX]; omega
      have hc : (((⌈M1⌉.toNat : ℤ) + ⌈M2⌉.toNat + 1 : ℤ) : ℝ) ≤ (X : ℝ) := by
        exact_mod_cast hXge
      push_cast at hc; linarith
    have hXM1 : M1 ≤ (X : ℝ) := by
      linarith [hM1toNat, hXR, Nat.cast_nonneg (α := ℝ) ⌈M2⌉.toNat]
    have hXM2 : M2 ≤ (X : ℝ) := by
      linarith [hM2toNat, hXR, Nat.cast_nonneg (α := ℝ) ⌈M1⌉.toNat]
    -- θ-landing
    set θ₀ : ℝ := (X : ℝ) * (A * α - B) + k * β with hθ0
    set n : ℤ := ⌈(η - θ₀) / γ⌉ with hn
    have hθn_lo : η ≤ θ₀ + n * γ := by
      have h1 : (η - θ₀) / γ ≤ (n : ℝ) := by rw [hn]; exact Int.le_ceil _
      have h2 := (div_le_iff₀ hγ0).mp h1; linarith
    have hθn_hi : θ₀ + n * γ < η + γ := by
      have h1 : (n : ℝ) < (η - θ₀) / γ + 1 := by rw [hn]; exact Int.ceil_lt_add_one _
      have h2 : (n : ℝ) * γ < ((η - θ₀) / γ + 1) * γ := by nlinarith [h1, hγ0]
      rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hγ0), one_mul] at h2; linarith
    clear_value θ₀ n
    set sn : ℤ := X * A + e * n with hsn
    set wn : ℤ := X * B - δ * n with hwn
    have hsnR' : (sn : ℝ) = (X : ℝ) * A + e * n := by rw [hsn]; push_cast; ring
    have hwnR' : (wn : ℝ) = (X : ℝ) * B - δ * n := by rw [hwn]; push_cast; ring
    have hθ_eq : (sn : ℝ) * α + k * β - wn = θ₀ + n * γ := by
      rw [hsnR', hwnR', hθ0, hγdef]; ring
    have algS : ∀ Xr Ar Br nr : ℝ, (δ : ℝ) * Ar + e * Br = 1 →
        ((δ : ℝ) + e * α) * (Xr * Ar + e * nr)
          = Xr + e * ((Xr * (Ar * α - Br) + k * β) + nr * ((δ : ℝ) + e * α) - k * β) := by
      intro Xr Ar Br nr hab; linear_combination Xr * hab
    have algW : ∀ Xr Ar Br nr : ℝ, (δ : ℝ) * Ar + e * Br = 1 →
        ((δ : ℝ) + e * α) * (Xr * Br - δ * nr)
          = α * Xr + δ * (k * β - ((Xr * (Ar * α - Br) + k * β) + nr * ((δ : ℝ) + e * α))) := by
      intro Xr Ar Br nr hab; linear_combination (α * Xr) * hab
    have hkey_s : γ * (sn : ℝ) = X + e * (θ₀ + n * γ - k * β) := by
      rw [hsnR', hθ0, hγdef]; exact algS X A B n hABR
    have hkey_w : γ * (wn : ℝ) = α * X + δ * (k * β - (θ₀ + n * γ)) := by
      rw [hwnR', hθ0, hγdef]; exact algW X A B n hABR
    have hsn0 : (0 : ℤ) ≤ sn := by
      have hemul : (e : ℝ) * η ≤ e * (θ₀ + n * γ) :=
        mul_le_mul_of_nonneg_left hθn_lo (by positivity)
      have hge : γ * (S₀ : ℝ) ≤ γ * (sn : ℝ) := by nlinarith [hkey_s, hemul, hXM1, hM1]
      have : (S₀ : ℝ) ≤ (sn : ℝ) := le_of_mul_le_mul_left hge hγ0
      have : (0 : ℝ) ≤ (sn : ℝ) := le_trans (by positivity) this
      exact_mod_cast this
    have hsnS0 : (S₀ : ℤ) ≤ sn := by
      have hemul : (e : ℝ) * η ≤ e * (θ₀ + n * γ) :=
        mul_le_mul_of_nonneg_left hθn_lo (by positivity)
      have hge : γ * (S₀ : ℝ) ≤ γ * (sn : ℝ) := by nlinarith [hkey_s, hemul, hXM1, hM1]
      have : (S₀ : ℝ) ≤ (sn : ℝ) := le_of_mul_le_mul_left hge hγ0
      exact_mod_cast this
    have hwn0 : (0 : ℤ) ≤ wn := by
      have hαM2 : (δ : ℝ) * (η + γ - k * β) ≤ α * X := by
        rw [hM2, div_le_iff₀ hα0] at hXM2; linarith
      have hge : γ * (0 : ℝ) ≤ γ * (wn : ℝ) := by
        rw [mul_zero]; nlinarith [hkey_w, hθn_hi, hαM2, hδR]
      have : (0 : ℝ) ≤ (wn : ℝ) := le_of_mul_le_mul_left hge hγ0
      exact_mod_cast this
    have hsnR : ((sn.toNat : ℕ) : ℝ) = (sn : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hsn0
    refine ⟨sn.toNat, wn, ?_, ?_, ?_, ?_⟩
    · have : (S₀ : ℤ) ≤ (sn.toNat : ℤ) := by rw [Int.toNat_of_nonneg hsn0]; exact hsnS0
      exact_mod_cast this
    · rw [hsnR]; linarith [hθ_eq, hθn_lo]
    · rw [hsnR]; linarith [hθ_eq, hθn_hi, hγk]
    · rw [Int.toNat_of_nonneg hsn0]; simp only [hsn, hwn]; linear_combination (X : ℤ) * hAB
  refine ⟨X₀, fun x hx => ?_⟩
  obtain ⟨s, w, hsS0, hθlo, hθhi, hdioph⟩ := hcore x hx
  obtain ⟨f, hf1, hfs, hfw⟩ := hSW s hsS0 w hθlo hθhi
  have hw0 : 0 ≤ w := by rw [← hfw]; positivity
  have hfwN : ((∑ j, qCount h (f j) : ℕ) : ℤ) = w := by rw [Nat.cast_sum]; exact hfw
  have hwN : w.toNat ∈ Wset h k s :=
    ⟨f, hfs, by rw [← hfwN, Int.toNat_natCast]⟩
  have hmem := mem_kFold_of_Wset hgaps h δ e hgap hwN
  have hwt : (w.toNat : ℤ) = w := Int.toNat_of_nonneg hw0
  have hxeq : x = k * a 0 + δ * s + e * w.toNat := by
    have hZ : (x : ℤ) = ((k * a 0 + δ * s + e * w.toNat : ℕ) : ℤ) := by
      push_cast [hwt]; linarith [hdioph]
    exact_mod_cast hZ
  rw [hxeq]; exact hmem

end Proof
end Erdos1112


/-! Flattened from Erdos1112Proof.NonEx.Main. -/
/-
Non-existence master assembly (the paper's case table): every `(d₁,d₂)`-sequence with
`d₂ ≤ k` is tail-covering; with the certificate (the corresponding paper lemma) this yields the
strong non-existence theorem, statement-identical to the frozen target
`Erdos1112.erdos_1112_strong_nonexistence`.
-/

namespace Erdos1112
namespace Proof

/-- Prefix-count splits along a shift: `q(T+m) = q T + q_tail m`. -/
private lemma qCount_shift (w : ℕ → Bool) (T m : ℕ) :
    qCount w (T + m) = qCount w T + qCount (fun l => w (T + l)) m := by
  induction m with
  | zero => simp [qCount]
  | succ m ih =>
      have e1 : qCount w (T + (m + 1)) = qCount w (T + m) + (if w (T + m + 1) then 1 else 0) := by
        rw [show T + (m + 1) = (T + m) + 1 from by ring, qCount_succ]
      have e2 : qCount (fun l => w (T + l)) (m + 1)
          = qCount (fun l => w (T + l)) m + (if w (T + m + 1) then 1 else 0) := by
        rw [qCount_succ]; simp only [show T + (m + 1) = T + m + 1 from by ring]
      rw [e1, e2, ih]; ring

/-- A width-two antidiagonal of a tail lifts to one of the whole word. -/
private lemma widthTwo_shift (w : ℕ → Bool) (T σ : ℕ)
    (hW : WidthTwoAt (fun l => w (T + l)) σ) : WidthTwoAt w (2 * T + σ) := by
  obtain ⟨i, j, i', j', hij, hij', hcmp⟩ := hW
  refine ⟨T + i, T + j, T + i', T + j', by omega, by omega, ?_⟩
  have qi := qCount_shift w T i; have qj := qCount_shift w T j
  have qi' := qCount_shift w T i'; have qj' := qCount_shift w T j'
  omega

open scoped Classical in
/-- **Two-letter branch**: a tail alphabet of exactly two letters is
tail-covering. It reduces via `sweep` / `width_of_unbalanced` to the
eventually-periodic case or, through Morse–Hedlund, the Sturmian ladder. The other tail-alphabet
sizes are handled elsewhere (1-letter: single-letter; ≥ 3: Slot Lemma). -/
theorem tailCoveringN_of_two_letters {k d₁ d₂ : ℕ} {a : ℕ → ℕ}
    (hk : 3 ≤ k) (hd₁ : 1 ≤ d₁) (hgaps : HasGapsIn d₁ d₂ a) (hd : d₂ ≤ k)
    (htwo : ∃ x y : ℕ, x < y ∧ tailAlphabet a = {x, y}) :
    TailCoveringN k a := by
  classical
  obtain ⟨x, y, hxy, htwoeq⟩ := htwo
  have hxmem : x ∈ tailAlphabet a := by rw [htwoeq]; left; rfl
  have hymem : y ∈ tailAlphabet a := by rw [htwoeq]; right; rfl
  have hxb := mem_tailAlphabet_bounds hgaps hxmem
  have hyb := mem_tailAlphabet_bounds hgaps hymem
  have hx1 : 1 ≤ x := le_trans hd₁ hxb.1
  have hyd2 : y ≤ d₂ := hyb.2
  set g : ℕ := Nat.gcd x y with hgdef
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left y (by omega)
  have hgx : g ∣ x := Nat.gcd_dvd_left x y
  have hgy : g ∣ y := Nat.gcd_dvd_right x y
  have hgyx : g ∣ (y - x) := by
    obtain ⟨p, hp⟩ := hgx; obtain ⟨q, hq⟩ := hgy
    exact ⟨q - p, by rw [hp, hq, Nat.mul_sub]⟩
  set δ : ℕ := x / g with hδdef
  set ee : ℕ := (y - x) / g with heedef
  have hδ0 : 0 < δ := Nat.div_pos (Nat.le_of_dvd (by omega) hgx) hg0
  have hee0 : 0 < ee := Nat.div_pos (Nat.le_of_dvd (by omega) hgyx) hg0
  have hxg : x = g * δ := by rw [hδdef, Nat.mul_div_cancel' hgx]
  have hyxg : y - x = g * ee := by rw [heedef, Nat.mul_div_cancel' hgyx]
  have hyg : y = g * (δ + ee) := by rw [Nat.mul_add, ← hxg, ← hyxg]; omega
  have hdd : δ + ee = y / g := by rw [hyg, Nat.mul_div_cancel_left _ hg0]
  have hco : Nat.Coprime δ (δ + ee) := hdd ▸ Nat.coprime_div_gcd_div_gcd hg0
  -- tail index `T ≥ g` past which gaps ∈ {x, y}
  obtain ⟨T0, hT0⟩ := exists_tail_index hgaps
  set T : ℕ := max T0 g with hTdef
  have hgapxy : ∀ n, gap a (T + n) = x ∨ gap a (T + n) = y := by
    intro n
    have hm := hT0 (T + n) (by omega)
    rw [htwoeq] at hm; exact hm
  have hgdvdgap : ∀ n, g ∣ gap a (T + n) := by
    intro n; rcases hgapxy n with h | h
    · rw [h]; exact hgx
    · rw [h]; exact hgy
  have hgapbnd : ∀ n, g * δ ≤ gap a (T + n) ∧ gap a (T + n) ≤ g * (δ + ee) := by
    intro n
    have e1 : g * δ = x := hxg.symm
    have e2 : g * (δ + ee) = y := hyg.symm
    rcases hgapxy n with h | h <;> rw [h, e1, e2] <;> omega
  have haTn : ∀ n, n ≤ a n := by
    intro n; induction n with
    | zero => omega
    | succ n ih =>
        have h1 := hgaps.le_gap n; have h2 := hgaps.succ_eq_add_gap n; omega
  have haTg : g ≤ a T := le_trans (by omega) (haTn T)
  have hdvd : ∀ n, g ∣ (a (T + n) - a T) := by
    intro n; induction n with
    | zero => simp
    | succ n ih =>
        have he : T + (n + 1) = (T + n) + 1 := by omega
        have hgm := hgdvdgap n
        have hmono : a T ≤ a (T + n) := hgaps.monotone (by omega)
        have hstep : a (T + (n + 1)) = a (T + n) + gap a (T + n) := by
          rw [he, hgaps.succ_eq_add_gap]
        have : a (T + (n + 1)) - a T = (a (T + n) - a T) + gap a (T + n) := by
          rw [hstep]; omega
        rw [this]; exact Nat.dvd_add ih hgm
  set a' : ℕ → ℕ := fun n => (a (T + n) - a T) / g + 1 with ha'def
  set c : ℕ := a T - g with hcdef
  have haffine : ∀ n, a (T + n) = c + g * a' n := by
    intro n
    have hmono : a T ≤ a (T + n) := hgaps.monotone (by omega)
    have hcancel : g * ((a (T + n) - a T) / g) = a (T + n) - a T := Nat.mul_div_cancel' (hdvd n)
    simp only [ha'def, hcdef, Nat.mul_add, Nat.mul_one, hcancel]
    omega
  have hgap' : ∀ n, gap a' n = gap a (T + n) / g := by
    intro n
    have hd1 := hdvd (n + 1); have hd0 := hdvd n
    obtain ⟨X', hX'⟩ := hd1; obtain ⟨Y', hY'⟩ := hd0
    have hmono0 : a T ≤ a (T + n) := hgaps.monotone (by omega)
    have hmono1 : a (T + n) ≤ a (T + (n + 1)) := hgaps.monotone (by omega)
    have hgm := hgdvdgap n
    have he : T + (n + 1) = (T + n) + 1 := by omega
    have hax : a' (n + 1) = X' + 1 := by
      simp only [ha'def]; rw [hX', Nat.mul_div_cancel_left _ hg0]
    have hay : a' n = Y' + 1 := by
      simp only [ha'def]; rw [hY', Nat.mul_div_cancel_left _ hg0]
    have hYX : Y' ≤ X' := by
      have : g * Y' ≤ g * X' := by omega
      exact Nat.le_of_mul_le_mul_left this hg0
    have hgapval : gap a (T + n) = g * (X' - Y') := by
      show a (T + n + 1) - a (T + n) = g * (X' - Y')
      have h1 : a (T + n + 1) = a (T + (n + 1)) := by rw [he]
      rw [Nat.mul_sub, ← hX', ← hY', h1]; omega
    show a' (n + 1) - a' n = gap a (T + n) / g
    rw [hax, hay, hgapval, Nat.mul_div_cancel_left _ hg0]; omega
  have hmono' : ∀ i, a' i ≤ a' (i + 1) := by
    intro i
    have hm : a (T + i) ≤ a (T + (i + 1)) := hgaps.monotone (by omega)
    have hdiv : (a (T + i) - a T) / g ≤ (a (T + (i + 1)) - a T) / g :=
      Nat.div_le_div_right (Nat.sub_le_sub_right hm _)
    show (a (T + i) - a T) / g + 1 ≤ (a (T + (i + 1)) - a T) / g + 1
    exact Nat.add_le_add_right hdiv 1
  have hgaps' : HasGapsIn δ (δ + ee) a' := by
    refine ⟨by simp only [ha'def]; positivity, fun i => ⟨?_, ?_⟩⟩
    · have hgi := hgap' i
      have hlo : δ ≤ gap a' i := by
        rw [hgi, show δ = g * δ / g from by rw [Nat.mul_div_cancel_left _ hg0]]
        exact Nat.div_le_div_right (hgapbnd i).1
      have hgdef' : gap a' i = a' (i + 1) - a' i := rfl
      have := hmono' i; omega
    · have hgi := hgap' i
      have hhi : gap a' i ≤ δ + ee := by
        rw [hgi, show δ + ee = g * (δ + ee) / g from by rw [Nat.mul_div_cancel_left _ hg0]]
        exact Nat.div_le_div_right (hgapbnd i).2
      have hgdef' : gap a' i = a' (i + 1) - a' i := rfl
      have := hmono' i; omega
  -- the two-letter word of `a'`
  have hval : ∀ n, gap a' n = δ ∨ gap a' n = δ + ee := by
    intro n
    have hgi := hgap' n
    rcases hgapxy n with h | h
    · left; rw [hgi, h, hxg, Nat.mul_div_cancel_left _ hg0]
    · right; rw [hgi, h, hyg, Nat.mul_div_cancel_left _ hg0]
  set h' : ℕ → Bool := fun m => decide (gap a' (m - 1) = δ + ee) with hh'def
  have hgaprel : ∀ n, gap a' n = δ + ee * (if h' (n + 1) then 1 else 0) := by
    intro n
    have hh : h' (n + 1) = decide (gap a' n = δ + ee) := by
      simp only [hh'def, Nat.add_one_sub_one]
    rcases hval n with h | h
    · have hf : h' (n + 1) = false := by
        rw [hh, h]; simp only [decide_eq_false_iff_not]; omega
      rw [hf, h]; simp
    · have ht : h' (n + 1) = true := by rw [hh, h]; simp
      rw [ht, h]; simp
  -- reduce to covering `a'`, then rescale-lift back to `a`
  have hd2'k : δ + ee ≤ k := by
    rw [hdd]; exact le_trans (Nat.div_le_self y g) (le_trans hyd2 hd)
  suffices hcov' : TailCoveringN k a' by
    exact tailCoveringN_of_rescaled T g c hg0 a' haffine hcov'
  by_cases hper : EventuallyPeriodicW h'
  · -- eventually periodic word ⇒ eventually periodic gaps (the corresponding paper lemma)
    apply tailCoveringN_of_eventually_periodic (by omega) hδ0 hgaps'
    obtain ⟨p, hp0, Tp, hTp⟩ := hper
    refine ⟨p, hp0, Tp, fun n hn => ?_⟩
    rw [hgaprel (n + p), hgaprel n, show (n + p) + 1 = (n + 1) + p from by ring,
      hTp (n + 1) (by omega)]
  · by_cases hunbal : ∀ T', ∃ σ, T' ≤ σ ∧ WidthTwoAt h' σ
    · -- unbalanced at unboundedly many antidiagonals ⇒ width ⇒ sweep (2.7–2.9)
      obtain ⟨σ₀, _, hσ₀⟩ := hunbal 0
      obtain ⟨S₀, hS₀⟩ := width_of_unbalanced h' hk hd2'k σ₀ hσ₀ hper hunbal
      exact sweep hk hgaps' hd2'k h' δ ee hδ0 hee0 hco rfl hgaprel S₀ hS₀
    · -- some tail is balanced ⇒ classify ⇒ mechanical (not periodic) ⇒ Sturmian (2.10)
      have hbaltail : ∃ T₀, BalancedQ (fun m => h' (T₀ + m)) := by
        by_contra hc; push_neg at hc
        apply hunbal
        intro N
        have hnb := hc N
        have hex : ∃ σ, WidthTwoAt (fun m => h' (N + m)) σ := by
          by_contra hc2; push_neg at hc2
          exact hnb (balancedQ_of_no_widthTwo _ hc2)
        obtain ⟨σ, hσ⟩ := hex
        exact ⟨2 * N + σ, by omega, widthTwo_shift h' N σ hσ⟩
      obtain ⟨T₀, hbT₀⟩ := hbaltail
      rcases balanced_classification (fun m => h' (T₀ + m)) hbT₀ with hpertail | hmechtail
      · -- periodic tail contradicts non-periodicity of `h'`
        exfalso; apply hper
        obtain ⟨p, hp0, Tτ, hTτ⟩ := hpertail
        refine ⟨p, hp0, T₀ + Tτ, fun n hn => ?_⟩
        have hh := hTτ (n - T₀) (by omega)
        simp only [] at hh
        rw [show T₀ + ((n - T₀) + p) = n + p from by omega,
          show T₀ + (n - T₀) = n from by omega] at hh
        exact hh
      · -- mechanical tail ⇒ Sturmian on the tail sequence `a'' = a'(T₂ + ·)`
        obtain ⟨α, β, Tτ, hirr, hαI, hmech⟩ := hmechtail
        set T₂ : ℕ := T₀ + Tτ with hT₂
        set h'' : ℕ → Bool := fun m => h' (T₂ + m) with hh''def
        set a'' : ℕ → ℕ := fun n => a' (T₂ + n) with ha''def
        have ha''0 : 0 < a'' 0 := by simp only [ha''def, ha'def]; positivity
        have hgaps'' : HasGapsIn δ (δ + ee) a'' := by
          refine ⟨ha''0, fun i => ?_⟩
          have hb := hgaps'.2 (T₂ + i)
          simp only [ha''def, show T₂ + (i + 1) = (T₂ + i) + 1 from by ring]
          exact hb
        have hgaprel'' : ∀ n, gap a'' n = δ + ee * (if h'' (n + 1) then 1 else 0) := by
          intro n
          have hgstep : gap a'' n = gap a' (T₂ + n) := by
            simp only [gap, ha''def]; rw [show T₂ + (n + 1) = (T₂ + n) + 1 from by ring]
          have hh'' : h'' (n + 1) = h' ((T₂ + n) + 1) := by
            simp only [hh''def]; rw [show T₂ + (n + 1) = (T₂ + n) + 1 from by ring]
          rw [hgstep, hgaprel (T₂ + n), hh'']
        have hmech'' : ∀ n, (qCount h' (T₂ + n) : ℤ) - qCount h' T₂ = ⌊(n : ℝ) * α + β⌋ := by
          intro n
          have hm := hmech n
          have s1 : qCount h' (T₂ + n)
              = qCount h' T₀ + qCount (fun m => h' (T₀ + m)) (Tτ + n) := by
            have := qCount_shift h' T₀ (Tτ + n)
            rw [show T₀ + (Tτ + n) = T₂ + n from by omega] at this; exact this
          have s2 : qCount h' T₂ = qCount h' T₀ + qCount (fun m => h' (T₀ + m)) Tτ := by
            have := qCount_shift h' T₀ Tτ
            rw [show T₀ + Tτ = T₂ from by omega] at this; exact this
          rw [s1, s2]; push_cast at hm ⊢; linarith [hm]
        have hmechfinal : ∀ n, (qCount h'' n : ℤ) = ⌊(n : ℝ) * α + β⌋ := by
          intro n
          have hsZ : (qCount h' (T₂ + n) : ℤ)
              = qCount h' T₂ + qCount (fun l => h' (T₂ + l)) n := by
            exact_mod_cast qCount_shift h' T₂ n
          have hm'' := hmech'' n
          have : (qCount (fun l => h' (T₂ + l)) n : ℤ) = ⌊(n : ℝ) * α + β⌋ := by omega
          simpa only [hh''def] using this
        have hcovsturm : TailCovering k a'' :=
          tailCovering_of_sturmian hk hgaps'' hd2'k h'' δ ee hδ0 hee0 hco rfl
            hgaprel'' α β hirr hαI hmechfinal
        have halift : ∀ n, a' (T₂ + n) = 0 + 1 * a'' n := by
          intro n; simp [ha''def]
        exact tailCoveringN_of_rescaled T₂ 1 0 one_pos a'' halift hcovsturm

open scoped Classical in
/-- **Non-existence master lemma** (the paper's case table): for `k ≥ 3` and
`d₂ ≤ k`, every admissible `A` is tail-covering. Case on the size of the tail
alphabet `G∞ = {tail letters} ⊆ [d₁, d₂]`: 1 letter (single-letter case),
2 letters (`tailCoveringN_of_two_letters`), ≥ 3 letters (Slot Lemma). -/
theorem all_tailCovering (k d₁ d₂ : ℕ) (hk : 3 ≤ k) (hd₁ : 1 ≤ d₁)
    (_hd : d₁ < d₂) (h : d₂ ≤ k) :
    ∀ a : ℕ → ℕ, HasGapsIn d₁ d₂ a → TailCoveringN k a := by
  intro a hgaps
  classical
  set G : Finset ℕ := (Finset.Icc d₁ d₂).filter (· ∈ tailAlphabet a) with hGdef
  have hmemG : ∀ x, x ∈ G ↔ x ∈ tailAlphabet a := by
    intro x
    rw [hGdef, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨fun hx => hx.2, fun hx => ⟨mem_tailAlphabet_bounds hgaps hx, hx⟩⟩
  have htaileqG : tailAlphabet a = (↑G : Set ℕ) := by
    ext x; rw [Finset.mem_coe, hmemG]
  obtain ⟨T, hT⟩ := exists_tail_index hgaps
  have hGne : G.Nonempty := ⟨gap a T, (hmemG _).mpr (hT T le_rfl)⟩
  have h1card : 1 ≤ G.card := Finset.card_pos.mpr hGne
  rcases Nat.lt_or_ge G.card 3 with hlt | hge
  · interval_cases hc : G.card
    · -- one letter
      obtain ⟨δ, hδ⟩ := Finset.card_eq_one.mp hc
      refine tailCoveringN_of_single_letter (by omega) hd₁ hgaps ⟨δ, ?_⟩
      rw [htaileqG, hδ, Finset.coe_singleton]
    · -- two letters
      obtain ⟨x, y, hxy, hG2⟩ := Finset.card_eq_two.mp hc
      refine tailCoveringN_of_two_letters hk hd₁ hgaps h
        ⟨min x y, max x y, by omega, ?_⟩
      rw [htaileqG, hG2, Finset.coe_pair]
      rcases le_total x y with hle | hle
      · rw [min_eq_left hle, max_eq_right hle]
      · rw [min_eq_right hle, max_eq_left hle, Set.pair_comm]
  · -- ≥ 3 letters
    have he := G.orderEmbOfFin (rfl : G.card = G.card)
    have hmem : ∀ i : Fin G.card, G.orderEmbOfFin rfl i ∈ tailAlphabet a :=
      fun i => (hmemG _).mp (G.orderEmbOfFin_mem rfl i)
    have hsm : StrictMono (G.orderEmbOfFin (rfl : G.card = G.card)) :=
      (G.orderEmbOfFin rfl).strictMono
    exact tailCovering_of_three_letters hk hd₁ hgaps h
      ⟨_, _, _, hmem ⟨0, by omega⟩, hmem ⟨1, by omega⟩, hmem ⟨2, by omega⟩,
        hsm (by simp [Fin.lt_def]), hsm (by simp [Fin.lt_def])⟩

/-- **Part 2 of the Main Theorem** (strong non-existence). -/
theorem strong_nonexistence (k d₁ d₂ : ℕ) (hk : 3 ≤ k)
    (hd₁ : 1 ≤ d₁) (hd : d₁ < d₂) (h : d₂ ≤ k) (R : ℕ → ℕ) :
    ∃ b : ℕ → ℕ, IsVarLacunaryWith R b ∧
      ∀ a : ℕ → ℕ, HasGapsIn d₁ d₂ a →
        ¬ Disjoint (kFoldSumset k a) (Set.range b) :=
  strong_nonexistence_of_tailCovering k d₁ d₂ R
    (all_tailCovering k d₁ d₂ hk hd₁ hd h)

end Proof
end Erdos1112


/-! Flattened from Erdos1112Proof.Final. -/
/-
The three target theorems of Erdős Problem #1112, stated identically to the
statement file `Erdos1112.lean` (`erdos_1112`, `erdos_1112_existence_bound`,
`erdos_1112_strong_nonexistence`) and proved here from the development in
namespace `Erdos1112.Proof`. These are the canonical `Erdos1112.*` results;
`Erdos1112.lean` carries their definitions, this file carries their proofs.
-/

namespace Erdos1112

/-- Existence half with the paper's explicit ratio bound: when
`d₂ ≥ k + 1`, the concrete ratio `192 · d₂` works. -/
theorem erdos_1112_existence_bound (k d₁ d₂ : ℕ) (hk : 3 ≤ k) (hd₁ : 1 ≤ d₁)
    (hd : d₁ < d₂) (h : k + 1 ≤ d₂) :
    RatioWorks k d₁ d₂ (192 * d₂) :=
  Proof.existence_bound k d₁ d₂ hk hd₁ hd h

/-- Non-existence half in the strong, constructive `Nonempty`-intersection
form. The underlying `Proof.strong_nonexistence` produces
the `¬ Disjoint` witness; `Set.not_disjoint_iff_nonempty_inter` exhibits the actual
collision point `kA ∩ B`. -/
theorem erdos_1112_strong_nonexistence (k d₁ d₂ : ℕ) (hk : 3 ≤ k)
    (hd₁ : 1 ≤ d₁) (hd : d₁ < d₂) (h : d₂ ≤ k) (R : ℕ → ℕ) :
    ∃ b : ℕ → ℕ, IsVarLacunaryWith R b ∧
      ∀ a : ℕ → ℕ, HasGapsIn d₁ d₂ a →
        (kFoldSumset k a ∩ Set.range b).Nonempty := by
  obtain ⟨b, hb, hdef⟩ := Proof.strong_nonexistence k d₁ d₂ hk hd₁ hd h R
  exact ⟨b, hb, fun a ha => Set.not_disjoint_iff_nonempty_inter.mp (hdef a ha)⟩

/-- **Erdős Problem 1112, the dichotomy**: `r` exists iff
`d₂ ≥ k + 1`. Derived from the two halves exactly as in the paper's assembly section. -/
theorem erdos_1112 (k d₁ d₂ : ℕ) (hk : 3 ≤ k) (hd₁ : 1 ≤ d₁) (hd : d₁ < d₂) :
    Question k d₁ d₂ ↔ k + 1 ≤ d₂ := by
  constructor
  · rintro ⟨r, hr⟩
    by_contra hlt
    push_neg at hlt
    obtain ⟨b, hb, hdef⟩ :=
      erdos_1112_strong_nonexistence k d₁ d₂ hk hd₁ hd (by omega) (fun _ => r)
    obtain ⟨a, ha, hdisj⟩ := hr b (isVarLacunaryWith_const_iff.mp hb)
    exact (Set.not_disjoint_iff_nonempty_inter.mpr (hdef a ha)) hdisj
  · intro h
    exact ⟨192 * d₂, erdos_1112_existence_bound k d₁ d₂ hk hd₁ hd h⟩

/-- **Erdős Problem 1112, in the problem's literal integer phrasing.**

The problem asks for an *integer* `r`. `QuestionInt` quantifies `r : ℤ`; by the bridge
`question_iff_questionInt` this is equivalent to `Question`, so the dichotomy holds
verbatim for the integer form too. This closes the one modelling step that was
previously argued only in prose. -/
theorem erdos_1112_int (k d₁ d₂ : ℕ) (hk : 3 ≤ k) (hd₁ : 1 ≤ d₁) (hd : d₁ < d₂) :
    QuestionInt k d₁ d₂ ↔ k + 1 ≤ d₂ :=
  (question_iff_questionInt k d₁ d₂).symm.trans (erdos_1112 k d₁ d₂ hk hd₁ hd)

end Erdos1112


namespace Submissions.Erdos1112GapDichotomy.Full

theorem proof :
    ∀ k d₁ d₂ : ℕ, 3 ≤ k → 1 ≤ d₁ → d₁ < d₂ →
      (Erdos1112.QuestionInt k d₁ d₂ ↔ k + 1 ≤ d₂) :=
  Erdos1112.erdos_1112_int

end Submissions.Erdos1112GapDichotomy.Full
