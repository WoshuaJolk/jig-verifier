import Mathlib

/-! Flattened from Hanziwww/erdos260 commit e708b584c9a3b54857f050d6b7efbecb8a5ea27a. -/

/-! Source module: Erdos260/Basic.lean -/

/-!
# Basic semantic objects for Erdős Problem 260

The paper uses `ℕ = {1, 2, ...}`.  Lean's natural numbers include zero, so the
weighted support term is defined to be zero at index zero.  Dyadic blocks use
the paper's half-open convention `(X, 2X]`.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos260

/-- Binary entropy, in base two.  It lives in the basic layer because the
fixed entropy-parameter hierarchy is part of every coherent scale family. -/
def binaryEntropy (x : ℝ) : ℝ :=
  -x * Real.logb 2 x - (1 - x) * Real.logb 2 (1 - x)

/-- The binary digit associated with a support set. -/
def digit (S : Set ℕ) (n : ℕ) : ℕ := by
  classical
  exact if n ∈ S then 1 else 0

/-- The `n`th summand of the weighted binary support series. -/
def weightedSupportTerm (S : Set ℕ) (n : ℕ) : ℝ :=
  by
    classical
    exact if n ∈ S then (n : ℝ) / (2 : ℝ) ^ n else 0

/-- The weighted binary expansion attached to a support set. -/
def weightedBinarySeries (S : Set ℕ) : ℝ :=
  ∑' n : ℕ, weightedSupportTerm S n

/-- Removing the zero index turns an arbitrary support into the paper's
positive support without changing any weighted summand. -/
def positiveSupport (S : Set ℕ) : Set ℕ :=
  {n | n ∈ S ∧ 0 < n}

@[simp]
theorem weightedSupportTerm_positiveSupport (S : Set ℕ) (n : ℕ) :
    weightedSupportTerm (positiveSupport S) n = weightedSupportTerm S n := by
  by_cases hn : n = 0
  · subst n
    simp [weightedSupportTerm, positiveSupport]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    by_cases hmem : n ∈ S
    · simp [weightedSupportTerm, positiveSupport, hnpos, hmem]
    · simp [weightedSupportTerm, positiveSupport, hmem]

theorem positiveSupport_infinite {S : Set ℕ} (hS : S.Infinite) :
    (positiveSupport S).Infinite := by
  have heq : positiveSupport S = S \ ({0} : Set ℕ) := by
    ext n
    simp [positiveSupport, Nat.pos_iff_ne_zero]
  have hdiff : (S \ ({0} : Set ℕ)).Infinite :=
    hS.sdiff (Set.finite_singleton 0)
  simpa [heq] using hdiff

/-- Number of support points in `[1, X]`. -/
def supportCount (S : Set ℕ) (X : ℕ) : ℕ :=
  by
    classical
    exact ((Finset.Icc 1 X).filter fun n => n ∈ S).card

/-- Number of support points in the paper's block `(X, 2X]`. -/
def dyadicBlockCount (S : Set ℕ) (X : ℕ) : ℕ :=
  by
    classical
    exact ((Finset.Ioc X (2 * X)).filter fun n => n ∈ S).card

@[simp]
theorem dyadicBlockCount_positiveSupport (S : Set ℕ) (X : ℕ) :
    dyadicBlockCount (positiveSupport S) X = dyadicBlockCount S X := by
  classical
  unfold dyadicBlockCount
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_Ioc, positiveSupport,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨hIoc, hS, _⟩
    exact ⟨hIoc, hS⟩
  · rintro ⟨hIoc, hS⟩
    exact ⟨hIoc, hS, lt_of_le_of_lt (Nat.zero_le X) hIoc.1⟩

/-- The dyadic scale `X = 2^L`. -/
def dyadicScale (L : ℕ) : ℕ := 2 ^ L

/-- A strictly increasing positive enumeration of an infinite support set. -/
structure SupportEnumeration (S : Set ℕ) where
  a : ℕ → ℕ
  strictMono : StrictMono a
  positive : ∀ n, 0 < a n
  range_eq : Set.range a = S

/-- The canonical increasing enumeration of an infinite positive support. -/
def supportEnumerationOfInfinite (S : Set ℕ) (hInfinite : S.Infinite)
    (hPositive : ∀ n ∈ S, 0 < n) : SupportEnumeration S where
  a := Nat.nth fun n => n ∈ S
  strictMono := by
    apply Nat.nth_strictMono
    simpa only [Set.setOf_mem_eq] using hInfinite
  positive := by
    intro k
    apply hPositive _
    apply Nat.nth_mem_of_infinite
    simpa only [Set.setOf_mem_eq] using hInfinite
  range_eq := by
    apply Nat.range_nth_of_infinite
    simpa only [Set.setOf_mem_eq] using hInfinite

/-- Consecutive gap in a support enumeration. -/
def supportGap {S : Set ℕ} (e : SupportEnumeration S) (k : ℕ) : ℕ :=
  e.a (k + 1) - e.a k

/-- A gap word is an ordered finite list of natural-number gaps. -/
abbrev GapWord := List ℕ

namespace GapWord

/-- Every entry of a genuine gap word is positive. -/
def Positive (w : GapWord) : Prop := ∀ g ∈ w, 0 < g

/-- Spatial span of a gap word. -/
def span (w : GapWord) : ℕ := w.sum

/-- Span of the first `r` gaps. -/
def prefixSpan (w : GapWord) (r : ℕ) : ℕ := (w.take r).sum

/-- The first prefix whose span is strictly larger than `bound`, or the whole
word if there is no such prefix. -/
def firstPrefixAbove : GapWord → ℕ → GapWord
  | [], _ => []
  | g :: gs, bound =>
      if bound < g then [g]
      else g :: firstPrefixAbove gs (bound - g)

theorem firstPrefixAbove_isPrefix (w : GapWord) (bound : ℕ) :
    (w.firstPrefixAbove bound).IsPrefix w := by
  induction w generalizing bound with
  | nil => simp [firstPrefixAbove]
  | cons g gs ih =>
      simp only [firstPrefixAbove]
      split_ifs with h
      · simp
      · rcases ih (bound - g) with ⟨tail, htail⟩
        exact ⟨tail, by simpa using congrArg (List.cons g) htail⟩

theorem firstPrefixAbove_length_le (w : GapWord) (bound : ℕ) :
    (w.firstPrefixAbove bound).length ≤ w.length :=
  (firstPrefixAbove_isPrefix w bound).length_le

theorem firstPrefixAbove_positive (w : GapWord) (bound : ℕ)
    (hpositive : w.Positive) : (w.firstPrefixAbove bound).Positive := by
  intro g hg
  exact hpositive g ((firstPrefixAbove_isPrefix w bound).mem hg)

/-- If the full word crosses the target, the selected prefix crosses it
strictly as well. -/
theorem lt_span_firstPrefixAbove_of_lt_span (w : GapWord) (bound : ℕ)
    (hcross : bound < w.span) : bound < (w.firstPrefixAbove bound).span := by
  induction w generalizing bound with
  | nil => simp [GapWord.span] at hcross
  | cons g gs ih =>
      simp only [firstPrefixAbove]
      by_cases hbg : bound < g
      · simp [hbg, GapWord.span]
      · rw [if_neg hbg]
        simp only [GapWord.span, List.sum_cons]
        have hgle : g ≤ bound := Nat.le_of_not_gt hbg
        have htail : bound - g < GapWord.span gs := by
          simp only [GapWord.span, List.sum_cons] at hcross
          simp only [GapWord.span]
          omega
        have hrec : bound - g <
            (firstPrefixAbove gs (bound - g)).sum := by
          simpa only [GapWord.span] using ih (bound - g) htail
        omega

/-- Minimal crossing overshoots the target by at most one gap. -/
theorem span_firstPrefixAbove_le_add (w : GapWord) (bound cap : ℕ)
    (hcap : ∀ g ∈ w, g ≤ cap) :
    (w.firstPrefixAbove bound).span ≤ bound + cap := by
  induction w generalizing bound with
  | nil => simp [firstPrefixAbove, GapWord.span]
  | cons g gs ih =>
      have hgcap : g ≤ cap := hcap g (by simp)
      have htailcap : ∀ x ∈ gs, x ≤ cap := by
        intro x hx
        exact hcap x (by simp [hx])
      simp only [firstPrefixAbove]
      by_cases hbg : bound < g
      · simp [hbg, GapWord.span]
        omega
      · rw [if_neg hbg]
        simp only [GapWord.span, List.sum_cons]
        have hrec : (firstPrefixAbove gs (bound - g)).sum ≤
            (bound - g) + cap := by
          simpa only [GapWord.span] using ih (bound - g) htailcap
        omega

theorem span_firstPrefixAbove_le_span (w : GapWord) (bound : ℕ) :
    (w.firstPrefixAbove bound).span ≤ w.span := by
  let p := w.firstPrefixAbove bound
  have hp : p.IsPrefix w := firstPrefixAbove_isPrefix w bound
  obtain ⟨tail, htail⟩ := hp
  have hsum : w.span = p.span + tail.sum := by
    rw [← htail]
    simp [GapWord.span]
  change p.span ≤ w.span
  omega

/-- The first prefix whose span is at least `bound`, used for completed
logarithmic blocks.  This is deliberately separate from the strict prefix
selection used for the initial affine-locking prefix. -/
def firstPrefixAtLeast : GapWord → ℕ → GapWord
  | [], _ => []
  | g :: gs, bound =>
      if bound ≤ g then [g]
      else g :: firstPrefixAtLeast gs (bound - g)

theorem firstPrefixAtLeast_isPrefix (w : GapWord) (bound : ℕ) :
    (w.firstPrefixAtLeast bound).IsPrefix w := by
  induction w generalizing bound with
  | nil => simp [firstPrefixAtLeast]
  | cons g gs ih =>
      simp only [firstPrefixAtLeast]
      by_cases hbg : bound ≤ g
      · simp [hbg]
      · rw [if_neg hbg]
        rcases ih (bound - g) with ⟨tail, htail⟩
        exact ⟨tail, by simpa using congrArg (List.cons g) htail⟩

theorem firstPrefixAtLeast_positive (w : GapWord) (bound : ℕ)
    (hpositive : w.Positive) : (w.firstPrefixAtLeast bound).Positive := by
  intro g hg
  exact hpositive g ((firstPrefixAtLeast_isPrefix w bound).mem hg)

theorem span_firstPrefixAtLeast_ge (w : GapWord) (bound : ℕ)
    (hcross : bound ≤ w.span) :
    bound ≤ (w.firstPrefixAtLeast bound).span := by
  induction w generalizing bound with
  | nil =>
      simp [firstPrefixAtLeast, GapWord.span] at hcross ⊢
      exact hcross
  | cons g gs ih =>
      simp only [firstPrefixAtLeast]
      by_cases hbg : bound ≤ g
      · simp [hbg, GapWord.span]
      · rw [if_neg hbg]
        simp only [GapWord.span, List.sum_cons]
        have htail : bound - g ≤ GapWord.span gs := by
          change bound - g ≤ gs.sum
          simp only [GapWord.span, List.sum_cons] at hcross
          omega
        have hrec := ih (bound - g) htail
        simp only [GapWord.span] at hrec ⊢
        omega

theorem firstPrefixAtLeast_ne_nil (w : GapWord) (bound : ℕ)
    (hbound : 0 < bound) (hcross : bound ≤ w.span) :
    w.firstPrefixAtLeast bound ≠ [] := by
  intro hempty
  have hspan := span_firstPrefixAtLeast_ge w bound hcross
  rw [hempty] at hspan
  simp [GapWord.span] at hspan
  omega

theorem prefixSpan_firstPrefixAtLeast_lt (w : GapWord) (bound : ℕ)
    (hbound : 0 < bound) :
    ∀ r < (w.firstPrefixAtLeast bound).length,
      (w.firstPrefixAtLeast bound).prefixSpan r < bound := by
  induction w generalizing bound with
  | nil => simp [firstPrefixAtLeast]
  | cons g gs ih =>
      simp only [firstPrefixAtLeast]
      by_cases hbg : bound ≤ g
      · rw [if_pos hbg]
        intro r hr
        have hr0 : r = 0 := by simp at hr; omega
        subst r
        simpa [GapWord.prefixSpan] using hbound
      · rw [if_neg hbg]
        intro r hr
        have hglt : g < bound := Nat.lt_of_not_ge hbg
        cases r with
        | zero => simpa [GapWord.prefixSpan] using hbound
        | succ r =>
            have hrTail : r < (firstPrefixAtLeast gs (bound - g)).length := by
              simpa using hr
            have htailBound : 0 < bound - g := by omega
            have hrec := ih (bound - g) htailBound r hrTail
            simp only [GapWord.prefixSpan, List.take_succ_cons, List.sum_cons]
            simp only [GapWord.prefixSpan] at hrec
            omega

theorem firstPrefixAtLeast_append_drop (w : GapWord) (bound : ℕ) :
    w.firstPrefixAtLeast bound ++
        w.drop (w.firstPrefixAtLeast bound).length = w := by
  induction w generalizing bound with
  | nil => simp [firstPrefixAtLeast]
  | cons g gs ih =>
      simp only [firstPrefixAtLeast]
      by_cases hbg : bound ≤ g
      · simp [hbg]
      · rw [if_neg hbg]
        simp only [List.length_cons, List.drop_succ_cons, List.cons_append,
          List.cons.injEq, true_and]
        exact ih (bound - g)

/-- A block is the shortest nonempty prefix of its remaining word whose span
reaches `bound`.  This predicate is used to specify the greedy decomposition
without hiding a choice function. -/
def IsGreedyBlock (bound : ℕ) (block : GapWord) : Prop :=
  block ≠ [] ∧ bound ≤ span block ∧
    ∀ r < block.length, prefixSpan block r < bound

theorem firstPrefixAtLeast_isGreedyBlock (w : GapWord) (bound : ℕ)
    (hbound : 0 < bound) (hcross : bound ≤ w.span) :
    IsGreedyBlock bound (w.firstPrefixAtLeast bound) := by
  exact ⟨firstPrefixAtLeast_ne_nil w bound hbound hcross,
    span_firstPrefixAtLeast_ge w bound hcross,
    prefixSpan_firstPrefixAtLeast_lt w bound hbound⟩

/-- A genuine greedy block decomposition of a word. -/
def IsGreedyDecomposition (w : GapWord) (bound : ℕ)
    (blocks : List GapWord) : Prop :=
  blocks.flatten = w ∧ ∀ block ∈ blocks, IsGreedyBlock bound block

/-- Output of the deterministic greedy logarithmic-block procedure.  Only
completed blocks are placed in `completed`; the final short suffix is retained
separately rather than silently discarded. -/
structure GreedyDecomposition where
  completed : List GapWord
  remainder : GapWord
  deriving DecidableEq, Repr

def greedyDecomposeAux : ℕ → GapWord → ℕ → GreedyDecomposition
  | 0, w, _ => ⟨[], w⟩
  | fuel + 1, w, bound =>
      if 0 < bound ∧ bound ≤ span w then
        let block := firstPrefixAtLeast w bound
        let tail := w.drop block.length
        let result := greedyDecomposeAux fuel tail bound
        ⟨block :: result.completed, result.remainder⟩
      else
        ⟨[], w⟩

def greedyDecompose (w : GapWord) (bound : ℕ) : GreedyDecomposition :=
  greedyDecomposeAux w.length w bound

/-- Semantic contract for a greedy decomposition with an explicit incomplete
remainder. -/
def GreedyDecomposition.Valid (w : GapWord) (bound : ℕ)
    (result : GreedyDecomposition) : Prop :=
  result.completed.flatten ++ result.remainder = w ∧
    (∀ block ∈ result.completed, IsGreedyBlock bound block) ∧
    result.remainder.span < bound

theorem greedyDecomposeAux_valid (fuel : ℕ) (w : GapWord) (bound : ℕ)
    (hfuel : w.length ≤ fuel) (hbound : 0 < bound) :
    (greedyDecomposeAux fuel w bound).Valid w bound := by
  induction fuel generalizing w with
  | zero =>
      have hw : w = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst w
      exact ⟨by simp [greedyDecomposeAux], by simp [greedyDecomposeAux],
        by simpa [greedyDecomposeAux, GapWord.span] using hbound⟩
  | succ fuel ih =>
      unfold greedyDecomposeAux
      by_cases hcross : bound ≤ w.span
      · rw [if_pos ⟨hbound, hcross⟩]
        let block := w.firstPrefixAtLeast bound
        let tail := w.drop block.length
        let result := greedyDecomposeAux fuel tail bound
        have hblock : IsGreedyBlock bound block := by
          exact firstPrefixAtLeast_isGreedyBlock w bound hbound hcross
        have happend : block ++ tail = w := by
          exact firstPrefixAtLeast_append_drop w bound
        have hblockLength : 0 < block.length := List.length_pos_iff.mpr hblock.1
        have hblockLe : block.length ≤ w.length :=
          (firstPrefixAtLeast_isPrefix w bound).length_le
        have htailLength : tail.length ≤ fuel := by
          dsimp [tail]
          rw [List.length_drop]
          omega
        have hresult : result.Valid tail bound := by
          exact ih tail htailLength
        rcases hresult with ⟨hflatten, hblocks, hremainder⟩
        change
          (block :: result.completed).flatten ++ result.remainder = w ∧
            (∀ b ∈ block :: result.completed, IsGreedyBlock bound b) ∧
              result.remainder.span < bound
        constructor
        · simp only [List.flatten_cons, List.append_assoc]
          rw [hflatten, happend]
        constructor
        · intro b hb
          simp only [List.mem_cons] at hb
          rcases hb with rfl | hb
          · exact hblock
          · exact hblocks b hb
        · exact hremainder
      · rw [if_neg (by simp [hbound, hcross])]
        exact ⟨by simp, by simp, Nat.lt_of_not_ge hcross⟩

theorem greedyDecompose_valid (w : GapWord) (bound : ℕ)
    (hbound : 0 < bound) :
    (greedyDecompose w bound).Valid w bound := by
  exact greedyDecomposeAux_valid w.length w bound le_rfl hbound

end GapWord

/-- An order-`offset+1` window anchored at an index. -/
structure AnchoredWindow where
  anchor : ℕ
  offset : ℕ
  valid : offset ≤ anchor

/-- Ordered gaps in an anchored window. -/
def windowGapWord {S : Set ℕ} (e : SupportEnumeration S)
    (w : AnchoredWindow) : GapWord :=
  (List.range (w.offset + 1)).map fun j =>
    supportGap e (w.anchor - w.offset + j)

/-- Spatial span of an anchored window. -/
def windowSpan {S : Set ℕ} (e : SupportEnumeration S)
    (w : AnchoredWindow) : ℕ :=
  (windowGapWord e w).span

/-- A window-threshold pair is represented by its discrete anchor and real
threshold.  The surrounding scale context determines the actual window. -/
abbrev WindowThreshold := ℕ × ℝ

/-- Closed threshold interval used by the paper. -/
def thresholdInterval (L C0 : ℕ) (cI : ℝ) : Set ℝ :=
  Set.Icc (2 * (L : ℝ) + C0) (2 * (L : ℝ) + C0 + cI * L)

/-- Structural constants fixed before scale-dependent choices. -/
structure StructuralParams where
  Caff : ℝ
  B : ℝ
  Gamma : ℝ
  rho : ℝ
  cI : ℝ
  C0 : ℕ
  Caff_gt : 2 < Caff
  B_gt : 2 < B
  Gamma_gt : 1 < Gamma
  rho_pos : 0 < rho
  rho_lt : rho < 1 / 6
  cI_pos : 0 < cI

/-- The window-density parameter is chosen after the structural constants,
together with the two strict entropy margins used in the rare and exterior
counts. -/
structure EntropyParams where
  structural : StructuralParams
  kappa : ℝ
  kappa_pos : 0 < kappa
  /-- The initial-prefix entropy argument lies in the monotone half of binary
  entropy.  This hypothesis is used by the binomial-composition estimate and
  cannot be recovered merely from the two strict entropy margins. -/
  kappa_initial_half :
    kappa / (structural.Caff + 1) ≤ 1 / 2
  /-- The post-exit-prefix entropy argument likewise lies in `[0,1/2]`. -/
  kappa_exterior_half :
    kappa / (structural.Gamma + 1) ≤ 1 / 2
  initial_margin :
    (structural.Caff + 1) *
        binaryEntropy (kappa / (structural.Caff + 1)) <
      1 / 2 - 3 * structural.rho
  total_margin :
    (structural.Caff + 1) *
          binaryEntropy (kappa / (structural.Caff + 1)) +
        (structural.Gamma + 1) *
          binaryEntropy (kappa / (structural.Gamma + 1)) <
      1 - 2 * structural.rho

/-- Rational support data from which integral carries are defined. -/
structure RationalSupport where
  S : Set ℕ
  eta : ℚ
  infinite : S.Infinite
  positive : ∀ n, n ∈ S → 0 < n
  hasSum : HasSum (weightedSupportTerm S) (eta : ℝ)

namespace RationalSupport

/-- Normalize arbitrary public support data by deleting the zero index. -/
def normalize (S : Set ℕ) (eta : ℚ) (hinfinite : S.Infinite)
    (hsum : HasSum (weightedSupportTerm S) (eta : ℝ)) : RationalSupport where
  S := positiveSupport S
  eta := eta
  infinite := positiveSupport_infinite hinfinite
  positive := by
    intro n hn
    exact hn.2
  hasSum := hsum.congr_fun fun n =>
    weightedSupportTerm_positiveSupport S n

end RationalSupport

/-- A scale-specific system of overlapping windows and thresholds. -/
structure WindowSystem where
  rational : RationalSupport
  enumeration : SupportEnumeration rational.S
  structural : StructuralParams
  entropy : EntropyParams
  entropy_structural : entropy.structural = structural
  L : ℕ
  s : ℕ
  epsilon : ℝ
  epsilon_nonneg : 0 ≤ epsilon

namespace WindowSystem

def X (W : WindowSystem) : ℕ := dyadicScale W.L

def m (W : WindowSystem) : ℕ := W.s + 1

def anchors (W : WindowSystem) : Finset ℕ :=
  (Finset.range (2 * W.X + 1)).filter fun k =>
    W.X < W.enumeration.a k ∧ W.enumeration.a k ≤ 2 * W.X

def window (W : WindowSystem) (k : ℕ) (hk : W.s ≤ k) : AnchoredWindow :=
  ⟨k, W.s, hk⟩

def rawWindowSpan (W : WindowSystem) (k : ℕ) : ℕ :=
  if hk : W.s ≤ k then windowSpan W.enumeration (W.window k hk) else 0

def rawWindowGapWord (W : WindowSystem) (k : ℕ) : GapWord :=
  if hk : W.s ≤ k then windowGapWord W.enumeration (W.window k hk) else []

def thresholds (W : WindowSystem) : Set ℝ :=
  thresholdInterval W.L W.structural.C0 W.structural.cI

def pairSet (W : WindowSystem) : Set WindowThreshold :=
  {e | e.1 ∈ W.anchors ∧ e.2 ∈ W.thresholds}

def excess (W : WindowSystem) (e : WindowThreshold) : ℝ :=
  max ((W.rawWindowSpan e.1 : ℝ) - e.2 - W.epsilon * W.L) 0

def boundedPairs (W : WindowSystem) (Z0 : ℕ) : Set WindowThreshold :=
  W.pairSet ∩ {e | W.excess e ≤ W.m * Z0}

def largePairs (W : WindowSystem) (Z0 : ℕ) : Set WindowThreshold :=
  W.pairSet ∩ {e | W.m * Z0 < W.excess e}

end WindowSystem

end Erdos260

/-! Source module: Erdos260/Elementary.lean -/

/-!
# Elementary composition, lattice, and slope lemmas

This module corresponds to Appendix A of the manuscript.
-/

noncomputable section

open Filter Set Topology
open scoped BigOperators

namespace Erdos260

private theorem binaryEntropy_eq_binEntropy_div_log_two (x : ℝ) :
    binaryEntropy x = Real.binEntropy x / Real.log 2 := by
  rw [binaryEntropy, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp only [Real.negMulLog, Real.logb]
  field_simp
  ring

/-- A concrete structural hierarchy and a sufficiently small positive entropy
parameter exist.  This closes the denominator-level constant selection used
when `thm_main_density` instantiates the pressure argument. -/
theorem exists_structural_entropy_params :
    ∃ p : StructuralParams, ∃ entropy : EntropyParams,
      entropy.structural = p := by
  let p : StructuralParams :=
    { Caff := 3
      B := 3
      Gamma := 2
      rho := 1 / 100
      cI := 1
      C0 := 0
      Caff_gt := by norm_num
      B_gt := by norm_num
      Gamma_gt := by norm_num
      rho_pos := by norm_num
      rho_lt := by norm_num
      cI_pos := by norm_num }
  have hEntropyContinuous : Continuous binaryEntropy := by
    rw [show binaryEntropy = fun x => Real.binEntropy x / Real.log 2 by
      funext x
      exact binaryEntropy_eq_binEntropy_div_log_two x]
    exact Real.binEntropy_continuous.div_const _
  have hEntropyZero : binaryEntropy 0 = 0 := by simp [binaryEntropy]
  have harg : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have harg4 : Tendsto (fun n : ℕ => ((1 : ℝ) / (n : ℝ)) / 4)
      atTop (𝓝 0) := by simpa using harg.div_const 4
  have harg3 : Tendsto (fun n : ℕ => ((1 : ℝ) / (n : ℝ)) / 3)
      atTop (𝓝 0) := by simpa using harg.div_const 3
  have hH4 : Tendsto
      (fun n : ℕ => binaryEntropy (((1 : ℝ) / (n : ℝ)) / 4))
      atTop (𝓝 0) := by
    have h := hEntropyContinuous.continuousAt.tendsto.comp harg4
    rw [hEntropyZero] at h
    simpa [Function.comp_def] using h
  have hH3 : Tendsto
      (fun n : ℕ => binaryEntropy (((1 : ℝ) / (n : ℝ)) / 3))
      atTop (𝓝 0) := by
    have h := hEntropyContinuous.continuousAt.tendsto.comp harg3
    rw [hEntropyZero] at h
    simpa [Function.comp_def] using h
  have hinitial : Tendsto
      (fun n : ℕ => 4 * binaryEntropy (((1 : ℝ) / (n : ℝ)) / 4))
      atTop (𝓝 0) := by simpa using tendsto_const_nhds.mul hH4
  have htotal : Tendsto
      (fun n : ℕ =>
        4 * binaryEntropy (((1 : ℝ) / (n : ℝ)) / 4) +
          3 * binaryEntropy (((1 : ℝ) / (n : ℝ)) / 3))
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hH4).add
      (tendsto_const_nhds.mul hH3)
  have heventInitial : ∀ᶠ n : ℕ in atTop,
      4 * binaryEntropy (((1 : ℝ) / (n : ℝ)) / 4) < 47 / 100 :=
    (tendsto_order.1 hinitial).2 _ (by norm_num)
  have heventTotal : ∀ᶠ n : ℕ in atTop,
      4 * binaryEntropy (((1 : ℝ) / (n : ℝ)) / 4) +
        3 * binaryEntropy (((1 : ℝ) / (n : ℝ)) / 3) < 49 / 50 :=
    (tendsto_order.1 htotal).2 _ (by norm_num)
  obtain ⟨n, hnInitial, hnTotal, hn⟩ :=
    (heventInitial.and (heventTotal.and (eventually_ge_atTop 1))).exists
  let κ : ℝ := 1 / (n : ℝ)
  have hκ : 0 < κ := by
    dsimp [κ]
    positivity
  let entropy : EntropyParams :=
    { structural := p
      kappa := κ
      kappa_pos := hκ
      kappa_initial_half := by
        dsimp [p, κ]
        have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
        field_simp
        exact_mod_cast (show 2 ≤ n * (3 + 1) by omega)
      kappa_exterior_half := by
        dsimp [p, κ]
        have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
        field_simp
        exact_mod_cast (show 2 ≤ n * (2 + 1) by omega)
      initial_margin := by
        dsimp [p, κ]
        norm_num at hnInitial ⊢
        exact hnInitial
      total_margin := by
        dsimp [p, κ]
        norm_num at hnTotal ⊢
        exact hnTotal }
  exact ⟨p, entropy, rfl⟩

private theorem choose_le_exp_binEntropy (h r : ℕ) (α : ℝ)
    (hα0 : 0 < α) (hα1 : α ≤ 1 / 2)
    (hr1 : 1 ≤ r) (hrα : (r : ℝ) ≤ α * h) :
    (Nat.choose (h - 1) (r - 1) : ℝ) ≤
      Real.exp ((h : ℝ) * Real.binEntropy α) := by
  have hαlt1 : α < 1 := lt_of_le_of_lt hα1 (by norm_num)
  have hβ0 : 0 < 1 - α := sub_pos.mpr hαlt1
  have hαβ : α ≤ 1 - α := by linarith
  have hrh_real : (r : ℝ) ≤ h := by nlinarith [hα1]
  have hrh : r ≤ h := by exact_mod_cast hrh_real
  have hrsub : r - 1 ≤ h - 1 := Nat.sub_le_sub_right hrh 1
  have hprobability :
      (Nat.choose (h - 1) (r - 1) : ℝ) * α ^ (r - 1) *
          (1 - α) ^ ((h - 1) - (r - 1)) ≤ 1 := by
    have hterm :
        α ^ (r - 1) * (1 - α) ^ ((h - 1) - (r - 1)) *
            (Nat.choose (h - 1) (r - 1) : ℝ) ≤
          ∑ m ∈ Finset.range ((h - 1) + 1),
            α ^ m * (1 - α) ^ ((h - 1) - m) *
              (Nat.choose (h - 1) m : ℝ) := by
      exact Finset.single_le_sum (s := Finset.range ((h - 1) + 1))
        (f := fun m => α ^ m * (1 - α) ^ ((h - 1) - m) *
          (Nat.choose (h - 1) m : ℝ))
        (fun _ _ => by positivity) (by simpa using Nat.lt_succ_iff.mpr hrsub)
    rw [← add_pow] at hterm
    have hone : α + (1 - α) = (1 : ℝ) := by ring
    rw [hone, one_pow] at hterm
    simpa [mul_assoc, mul_comm, mul_left_comm] using hterm
  have hrsubα : (((r - 1 : ℕ) : ℕ) : ℝ) ≤ α * h := by
    calc
      (((r - 1 : ℕ) : ℕ) : ℝ) ≤ (r : ℝ) := by
        exact_mod_cast Nat.sub_le r 1
      _ ≤ α * h := hrα
  have hlogαβ : Real.log α ≤ Real.log (1 - α) :=
    Real.strictMonoOn_log.monotoneOn hα0 hβ0 hαβ
  have hlogβ_nonpos : Real.log (1 - α) ≤ 0 :=
    Real.log_nonpos hβ0.le (by linarith)
  have hcomplement_cast :
      ((((h - 1) - (r - 1) : ℕ) : ℕ) : ℝ) =
        (h : ℝ) - 1 - ((r : ℝ) - 1) := by
    rw [show (h - 1) - (r - 1) = h - r by omega, Nat.cast_sub hrh]
    ring
  have hrsub_cast : (((r - 1 : ℕ) : ℕ) : ℝ) = (r : ℝ) - 1 := by
    rw [Nat.cast_sub hr1]
    norm_num
  have hlogweight :
      - (h : ℝ) * Real.binEntropy α ≤
        Real.log (α ^ (r - 1) * (1 - α) ^ ((h - 1) - (r - 1))) := by
    rw [Real.log_mul (pow_ne_zero _ hα0.ne') (pow_ne_zero _ hβ0.ne'),
      Real.log_pow, Real.log_pow]
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    simp only [Real.negMulLog]
    rw [hrsub_cast, hcomplement_cast]
    nlinarith
  have hweight :
      Real.exp (- (h : ℝ) * Real.binEntropy α) ≤
        α ^ (r - 1) * (1 - α) ^ ((h - 1) - (r - 1)) := by
    rw [← Real.exp_log (mul_pos (pow_pos hα0 _) (pow_pos hβ0 _))]
    exact Real.exp_le_exp.mpr hlogweight
  have hmul :
      (Nat.choose (h - 1) (r - 1) : ℝ) *
          Real.exp (- (h : ℝ) * Real.binEntropy α) ≤ 1 := by
    calc
      _ ≤ (Nat.choose (h - 1) (r - 1) : ℝ) *
          (α ^ (r - 1) * (1 - α) ^ ((h - 1) - (r - 1))) := by gcongr
      _ = (Nat.choose (h - 1) (r - 1) : ℝ) * α ^ (r - 1) *
          (1 - α) ^ ((h - 1) - (r - 1)) := by ring
      _ ≤ 1 := hprobability
  calc
    (Nat.choose (h - 1) (r - 1) : ℝ) =
        ((Nat.choose (h - 1) (r - 1) : ℝ) *
            Real.exp (- (h : ℝ) * Real.binEntropy α)) *
          Real.exp ((h : ℝ) * Real.binEntropy α) := by
            rw [mul_assoc, ← Real.exp_add]
            ring_nf
            simp
    _ ≤ 1 * Real.exp ((h : ℝ) * Real.binEntropy α) := by gcongr
    _ = _ := one_mul _

/-- Oriented determinant of two integer vectors. -/
def intDet (z₁ z₂ : ℤ × ℤ) : ℤ := z₁.1 * z₂.2 - z₁.2 * z₂.1

/-- Congruence lattice from Appendix A. -/
def congruenceLattice (A : ℤ) (M : ℕ) : Set (ℤ × ℤ) :=
  {z | Int.ModEq M (A * z.1 + z.2) 0}

/-- Integer multiplier attached to an interior-slope gap word. -/
def wordMultiplier (w : GapWord) : ℕ :=
  ((List.range w.length).map fun j =>
    2 ^ (w.span - w.prefixSpan (j + 1))).sum

/-- Actual iteration of the slope map `μ ↦ 2^g μ - 1`. -/
def slopeAfter : GapWord → ℝ → ℝ
  | [], μ => μ
  | g :: gs, μ => slopeAfter gs ((2 : ℝ) ^ g * μ - 1)

/-- A finite set of integer parameters whose values under a decreasing affine
map lie in an integer interval of length `B` has the expected spacing bound.
This elementary helper is used for both the interior source count and the
exterior corridor count. -/
theorem integerAffineIntervalCount
    (S : Set ℤ) (C J B : ℤ) (hJ : J < 0) (hB : 0 ≤ B)
    (hbound : ∀ t ∈ S, 0 ≤ C + J * t ∧ C + J * t ≤ B) :
    S.Finite ∧
      (S.ncard : ℝ) ≤ 1 + (B : ℝ) / (-(J : ℝ)) := by
  let f : ℤ → ℤ := fun t => C + J * t
  have himage : f '' S ⊆ Set.Icc 0 B := by
    rintro y ⟨t, ht, rfl⟩
    exact hbound t ht
  have hfimage : (f '' S).Finite :=
    (Set.finite_Icc 0 B).subset himage
  have hinj : Set.InjOn f S := by
    intro x _ y _ hxy
    dsimp [f] at hxy
    apply mul_left_cancel₀ (ne_of_lt hJ)
    exact add_left_cancel hxy
  have hfinite : S.Finite :=
    Set.Finite.of_finite_image hfimage hinj
  refine ⟨hfinite, ?_⟩
  by_cases hempty : S = ∅
  · rw [hempty, Set.ncard_empty]
    have hBreal : (0 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
    have hJreal : (0 : ℝ) < -(J : ℝ) := by
      exact_mod_cast (neg_pos.mpr hJ)
    have hquot : (0 : ℝ) ≤ (B : ℝ) / (-(J : ℝ)) :=
      div_nonneg hBreal hJreal.le
    norm_num
    linarith
  · have hnonempty : S.Nonempty := Set.nonempty_iff_ne_empty.mpr hempty
    let s : Finset ℤ := hfinite.toFinset
    have hsne : s.Nonempty := by
      rcases hnonempty with ⟨t, ht⟩
      exact ⟨t, by simpa [s] using ht⟩
    let lo : ℤ := s.min' hsne
    let hi : ℤ := s.max' hsne
    have hlo_mem : lo ∈ s := s.min'_mem hsne
    have hhi_mem : hi ∈ s := s.max'_mem hsne
    have hlohi : lo ≤ hi := s.min'_le hi hhi_mem
    have hsubset : s ⊆ Finset.Icc lo hi := by
      intro t ht
      simp only [Finset.mem_Icc]
      exact ⟨s.min'_le t ht, s.le_max' t ht⟩
    have hcard_nat : s.card ≤ (Finset.Icc lo hi).card :=
      Finset.card_le_card hsubset
    rw [Int.card_Icc] at hcard_nat
    have hnonneg : 0 ≤ hi + 1 - lo := by omega
    have hcard_int : (s.card : ℤ) ≤ hi + 1 - lo := by
      have hcast : (s.card : ℤ) ≤ ((hi + 1 - lo).toNat : ℤ) := by
        exact_mod_cast hcard_nat
      rwa [Int.toNat_of_nonneg hnonneg] at hcast
    have hncard_eq : S.ncard = s.card := by
      simpa [s] using Set.ncard_eq_toFinset_card S hfinite
    have hcard_real : (S.ncard : ℝ) ≤ ((hi + 1 - lo : ℤ) : ℝ) := by
      rw [hncard_eq]
      exact_mod_cast hcard_int
    have hloS : lo ∈ S := by simpa [s] using hlo_mem
    have hhiS : hi ∈ S := by simpa [s] using hhi_mem
    have hspan_int : (-J) * (hi - lo) ≤ B := by
      calc
        (-J) * (hi - lo) =
            (C + J * lo) - (C + J * hi) := by ring
        _ ≤ B := by
          linarith [(hbound lo hloS).2, (hbound hi hhiS).1]
    have hstep : (0 : ℝ) < -(J : ℝ) := by
      exact_mod_cast (neg_pos.mpr hJ)
    have hspan_real₀ :
        (-(J : ℝ)) * ((hi - lo : ℤ) : ℝ) ≤ (B : ℝ) := by
      exact_mod_cast hspan_int
    have hspan_real :
        ((hi - lo : ℤ) : ℝ) * (-(J : ℝ)) ≤ (B : ℝ) := by
      simpa [mul_comm] using hspan_real₀
    have hspan_div :
        ((hi - lo : ℤ) : ℝ) ≤ (B : ℝ) / (-(J : ℝ)) :=
      (le_div_iff₀ hstep).2 hspan_real
    push_cast at hcard_real hspan_div
    linarith

/-- Paper label: `lem:composition-entropy` (Appendix A).

The sum of binomial coefficients is the exact number of positive
compositions with the indicated allowed part counts. -/
theorem lem_composition_entropy (h rMax : ℕ) (α : ℝ)
    (hh : 2 ≤ h) (hα0 : 0 < α) (hα1 : α ≤ 1 / 2)
    (hr : (rMax : ℝ) ≤ α * h) :
    ((∑ r ∈ Finset.Icc 1 rMax, Nat.choose (h - 1) (r - 1) : ℕ) : ℝ) ≤
      (h : ℝ) ^ 2 * Real.rpow 2 ((h : ℝ) * binaryEntropy α) := by
  have hrMaxh_real : (rMax : ℝ) ≤ h := by nlinarith [hα1]
  have hrMaxh : rMax ≤ h := by exact_mod_cast hrMaxh_real
  have hrpow : Real.rpow 2 ((h : ℝ) * binaryEntropy α) =
      Real.exp ((h : ℝ) * Real.binEntropy α) := by
    change (2 : ℝ) ^ ((h : ℝ) * binaryEntropy α) = _
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
      binaryEntropy_eq_binEntropy_div_log_two]
    congr 1
    field_simp
  rw [hrpow]
  calc
    ((∑ r ∈ Finset.Icc 1 rMax, Nat.choose (h - 1) (r - 1) : ℕ) : ℝ) =
        ∑ r ∈ Finset.Icc 1 rMax,
          (Nat.choose (h - 1) (r - 1) : ℝ) := by push_cast; rfl
    _ ≤ ∑ _r ∈ Finset.Icc 1 rMax,
        Real.exp ((h : ℝ) * Real.binEntropy α) := by
      refine Finset.sum_le_sum fun r hrmem => ?_
      have hrmem' : r ∈ Finset.Icc 1 rMax := by simpa only using hrmem
      rw [Finset.mem_Icc] at hrmem'
      have hrr : (r : ℝ) ≤ rMax := by exact_mod_cast hrmem'.2
      exact choose_le_exp_binEntropy h r α hα0 hα1 hrmem'.1 (hrr.trans hr)
    _ = ((Finset.Icc 1 rMax).card : ℝ) *
        Real.exp ((h : ℝ) * Real.binEntropy α) := by simp
    _ ≤ (h : ℝ) * Real.exp ((h : ℝ) * Real.binEntropy α) := by
      gcongr
      exact_mod_cast (calc
        (Finset.Icc 1 rMax).card = rMax := by rw [Nat.card_Icc]; omega
        _ ≤ h := hrMaxh)
    _ ≤ (h : ℝ) ^ 2 * Real.exp ((h : ℝ) * Real.binEntropy α) := by
      gcongr
      have h0 : (0 : ℝ) ≤ h := by positivity
      have h1 : (1 : ℝ) ≤ h := by exact_mod_cast (show 1 ≤ h by omega)
      nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)]

/-- Paper label: `lem:lattice-det` (Appendix A). -/
theorem lem_lattice_det (A : ℤ) (M : ℕ) (hM : 1 ≤ M)
    (z₁ z₂ : ℤ × ℤ)
    (hz₁ : z₁ ∈ congruenceLattice A M)
    (hz₂ : z₂ ∈ congruenceLattice A M) :
    ∃ k : ℤ, intDet z₁ z₂ = (M : ℤ) * k := by
  have _hMne : (M : ℤ) ≠ 0 := by
    exact_mod_cast (show M ≠ 0 by omega)
  change Int.ModEq (M : ℤ) (A * z₁.1 + z₁.2) 0 at hz₁
  change Int.ModEq (M : ℤ) (A * z₂.1 + z₂.2) 0 at hz₂
  have hleft : Int.ModEq (M : ℤ)
      (z₁.1 * (A * z₂.1 + z₂.2)) 0 := by
    simpa using (Int.ModEq.refl z₁.1).mul hz₂
  have hright : Int.ModEq (M : ℤ)
      (z₂.1 * (A * z₁.1 + z₁.2)) 0 := by
    simpa using (Int.ModEq.refl z₂.1).mul hz₁
  have hdet : Int.ModEq (M : ℤ) (intDet z₁ z₂) 0 := by
    have h := hleft.sub hright
    convert h using 1 <;> (simp [intDet] <;> ring)
  rcases (Int.modEq_iff_dvd.mp hdet.symm) with ⟨k, hk⟩
  exact ⟨k, by simpa using hk⟩

/-- Paper label: `lem:farey` (Appendix A). -/
theorem lem_farey (a c : ℤ) (b d D : ℕ)
    (hb : 1 ≤ b) (hd : 1 ≤ d) (hbD : b < 2 * D) (hdD : d < 2 * D)
    (hne : (a : ℚ) / b ≠ (c : ℚ) / d) :
    1 / (4 * (D : ℝ) ^ 2) ≤
      |(a : ℝ) / b - (c : ℝ) / d| := by
  have hb0 : (b : ℚ) ≠ 0 := by positivity
  have hd0 : (d : ℚ) ≠ 0 := by positivity
  have hcross : (a : ℚ) * d ≠ (c : ℚ) * b := by
    intro h
    exact hne ((div_eq_div_iff hb0 hd0).2 h)
  have hz : a * (d : ℤ) - c * (b : ℤ) ≠ 0 := by
    intro h
    apply hcross
    exact_mod_cast (sub_eq_zero.mp h)
  have hnum : (1 : ℝ) ≤
      |(a : ℝ) * d - (c : ℝ) * b| := by
    exact_mod_cast Int.one_le_abs hz
  have hb_le : b ≤ 2 * D := Nat.le_of_lt hbD
  have hd_le : d ≤ 2 * D := Nat.le_of_lt hdD
  have hbd_nat0 : b * d ≤ (2 * D) * (2 * D) :=
    Nat.mul_le_mul hb_le hd_le
  have hbd_nat : b * d ≤ 4 * D ^ 2 := by
    nlinarith [hbd_nat0]
  have hbd : (b : ℝ) * d ≤ 4 * (D : ℝ) ^ 2 := by
    exact_mod_cast hbd_nat
  have hden_pos : (0 : ℝ) < (b : ℝ) * d := by positivity
  have hdiff : (a : ℝ) / b - (c : ℝ) / d =
      ((a : ℝ) * d - (c : ℝ) * b) / ((b : ℝ) * d) := by
    field_simp
  rw [hdiff, abs_div, abs_of_pos hden_pos]
  calc
    1 / (4 * (D : ℝ) ^ 2) ≤ 1 / ((b : ℝ) * d) :=
      one_div_le_one_div_of_le hden_pos hbd
    _ ≤ |(a : ℝ) * d - (c : ℝ) * b| / ((b : ℝ) * d) :=
      (div_le_div_iff_of_pos_right hden_pos).2 hnum

/-- Paper label: `lem:word-cylinder` (Appendix A). -/
theorem lem_word_cylinder (w : GapWord) (μ₀ : ℝ)
    (hfinal : slopeAfter w μ₀ ∈ Set.Ioo (0 : ℝ) 1) :
    μ₀ ∈ Set.Ioo
      ((wordMultiplier w : ℝ) / (2 : ℝ) ^ w.span)
      (((wordMultiplier w : ℝ) + 1) / (2 : ℝ) ^ w.span) := by
  have hclosed (v : GapWord) (μ : ℝ) :
      slopeAfter v μ = (2 : ℝ) ^ v.span * μ - (wordMultiplier v : ℝ) := by
    induction v generalizing μ with
    | nil => simp [slopeAfter, wordMultiplier, GapWord.span]
    | cons g tail ih =>
        have hmul : wordMultiplier (g :: tail) =
            (2 : ℕ) ^ GapWord.span tail + wordMultiplier tail := by
          simp [wordMultiplier, List.range_succ_eq_map, GapWord.span,
            GapWord.prefixSpan, Function.comp_def, Nat.add_sub_add_left]
        rw [slopeAfter, ih, hmul]
        simp only [GapWord.span, List.sum_cons, Nat.cast_add, Nat.cast_pow,
          Nat.cast_ofNat]
        rw [pow_add]
        ring
  rw [hclosed] at hfinal
  have hpow : (0 : ℝ) < (2 : ℝ) ^ w.span := by positivity
  constructor
  · rw [div_lt_iff₀ hpow]
    linarith [hfinal.1]
  · rw [lt_div_iff₀ hpow]
    linarith [hfinal.2]

private theorem eventually_logarithmic_entropy_bound (C : ℝ) (hC : 0 < C) :
    ∀ᶠ D : ℕ in atTop,
      let ell := Nat.ceil (Real.logb 2 (4 * D))
      C * (ell : ℝ) ^ 4 * Real.rpow 2 ((ell : ℝ) / 8) ≤ Real.sqrt D := by
  let K : ℝ := C * 625 * Real.rpow 8 (1 / 8 : ℝ)
  have hK : 0 < K := by
    dsimp [K]
    positivity
  have hsmallReal :=
    (isLittleO_log_rpow_rpow_atTop (4 : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 4)).bound
      (show 0 < (1 : ℝ) / K by positivity)
  have hsmallNat := tendsto_natCast_atTop_atTop.eventually hsmallReal
  filter_upwards [hsmallNat, eventually_ge_atTop 3] with D hsmall hD
  dsimp only
  have hDpos : (0 : ℝ) < D := by positivity
  have hlog : 1 ≤ Real.log (D : ℝ) := by
    rw [Real.le_log_iff_exp_le hDpos]
    exact Real.exp_one_lt_three.le.trans (by exact_mod_cast hD)
  have hlog0 : 0 ≤ Real.log (D : ℝ) := le_trans (by norm_num) hlog
  have hsmall' : Real.log (D : ℝ) ^ 4 ≤
      (1 / K) * (D : ℝ) ^ (1 / 4 : ℝ) := by
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hlog0 (4 : ℝ)),
      Real.norm_of_nonneg (Real.rpow_nonneg hDpos.le (1 / 4 : ℝ))] at hsmall
    rw [← Real.rpow_natCast]
    exact hsmall
  have habsorb : K * Real.log (D : ℝ) ^ 4 ≤
      (D : ℝ) ^ (1 / 4 : ℝ) := by
    calc
      _ ≤ K * ((1 / K) * (D : ℝ) ^ (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hsmall' hK.le
      _ = _ := by field_simp
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.log_two_gt_d9
    norm_num at h ⊢
    linarith
  have hlog2pos : (0 : ℝ) < Real.log 2 :=
    lt_of_lt_of_le (by norm_num) hlog2
  have hlogb_nonneg : 0 ≤ Real.logb 2 (4 * D) := by
    rw [Real.logb]
    apply div_nonneg
    · apply Real.log_nonneg
      exact_mod_cast (show 1 ≤ 4 * D by omega)
    · exact hlog2pos.le
  have hceil_lt := Nat.ceil_lt_add_one hlogb_nonneg
  have hident : Real.logb 2 (4 * (D : ℝ)) =
      2 + Real.log (D : ℝ) / Real.log 2 := by
    rw [Real.logb, Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hDpos.ne']
    have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [hlog4]
    field_simp
  have hdiv : Real.log (D : ℝ) / Real.log 2 ≤ 2 * Real.log (D : ℝ) := by
    rw [div_le_iff₀ hlog2pos]
    nlinarith [mul_nonneg hlog0 (sub_nonneg.mpr hlog2)]
  have hell : ((Nat.ceil (Real.logb 2 (4 * D)) : ℕ) : ℝ) ≤
      5 * Real.log (D : ℝ) := by
    rw [show (4 * D : ℝ) = 4 * (D : ℝ) by norm_num, hident] at hceil_lt ⊢
    linarith
  have hellpow : ((Nat.ceil (Real.logb 2 (4 * D)) : ℕ) : ℝ) ^ 4 ≤
      625 * Real.log (D : ℝ) ^ 4 := by
    have hell0 : (0 : ℝ) ≤ (Nat.ceil (Real.logb 2 (4 * D)) : ℕ) := by
      positivity
    have hp := pow_le_pow_left₀ hell0 hell 4
    nlinarith
  have hexp :
      Real.rpow 2 (((Nat.ceil (Real.logb 2 (4 * D)) : ℕ) : ℝ) / 8) ≤
        Real.rpow 8 (1 / 8 : ℝ) * (D : ℝ) ^ (1 / 8 : ℝ) := by
    have harg : (((Nat.ceil (Real.logb 2 (4 * D)) : ℕ) : ℝ) / 8) ≤
        (Real.logb 2 (4 * (D : ℝ)) + 1) / 8 := by
      have hc : ((Nat.ceil (Real.logb 2 (4 * D)) : ℕ) : ℝ) <
          Real.logb 2 (4 * (D : ℝ)) + 1 := by
        simpa only [Nat.cast_ofNat, Nat.cast_mul] using hceil_lt
      linarith
    calc
      Real.rpow 2 (((Nat.ceil (Real.logb 2 (4 * D)) : ℕ) : ℝ) / 8) ≤
          Real.rpow 2 ((Real.logb 2 (4 * (D : ℝ)) + 1) / 8) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) harg
      _ = Real.rpow (8 * (D : ℝ)) (1 / 8 : ℝ) := by
        change (2 : ℝ) ^ ((Real.logb 2 (4 * (D : ℝ)) + 1) / 8) = _
        rw [show (Real.logb 2 (4 * (D : ℝ)) + 1) / 8 =
            (Real.logb 2 (4 * (D : ℝ)) + 1) * (1 / 8 : ℝ) by ring,
          Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
          Real.rpow_add (by norm_num : (0 : ℝ) < 2),
          Real.rpow_logb (by norm_num) (by norm_num) (by positivity),
          Real.rpow_one]
        congr 1
        ring
      _ = _ := by
        change (8 * (D : ℝ)) ^ (1 / 8 : ℝ) =
          8 ^ (1 / 8 : ℝ) * (D : ℝ) ^ (1 / 8 : ℝ)
        exact Real.mul_rpow (by norm_num) hDpos.le
  have hpolyMul :
      C * ((Nat.ceil (Real.logb 2 (4 * D)) : ℕ) : ℝ) ^ 4 ≤
        C * (625 * Real.log (D : ℝ) ^ 4) :=
    mul_le_mul_of_nonneg_left hellpow hC.le
  have hexpnonneg :
      0 ≤ Real.rpow 2 (((Nat.ceil (Real.logb 2 (4 * D)) : ℕ) : ℝ) / 8) :=
    Real.rpow_nonneg (by norm_num) _
  have hpolyBoundNonneg : 0 ≤ C * (625 * Real.log (D : ℝ) ^ 4) := by
    positivity
  have hfirst := mul_le_mul hpolyMul hexp hexpnonneg hpolyBoundNonneg
  have hmain :
      C * ((Nat.ceil (Real.logb 2 (4 * D)) : ℕ) : ℝ) ^ 4 *
          Real.rpow 2 (((Nat.ceil (Real.logb 2 (4 * D)) : ℕ) : ℝ) / 8) ≤
        (D : ℝ) ^ (3 / 8 : ℝ) := by
    calc
      _ ≤ C * (625 * Real.log (D : ℝ) ^ 4) *
          (Real.rpow 8 (1 / 8 : ℝ) * (D : ℝ) ^ (1 / 8 : ℝ)) := hfirst
      _ = (K * Real.log (D : ℝ) ^ 4) * (D : ℝ) ^ (1 / 8 : ℝ) := by
        dsimp [K]
        ring
      _ ≤ (D : ℝ) ^ (1 / 4 : ℝ) * (D : ℝ) ^ (1 / 8 : ℝ) :=
        mul_le_mul_of_nonneg_right habsorb (Real.rpow_nonneg hDpos.le _)
      _ = (D : ℝ) ^ (3 / 8 : ℝ) := by
        have hr := (Real.rpow_add hDpos (1 / 4 : ℝ) (1 / 8 : ℝ)).symm
        norm_num at hr ⊢
        exact hr
  calc
    _ ≤ (D : ℝ) ^ (3 / 8 : ℝ) := hmain
    _ ≤ (D : ℝ) ^ (1 / 2 : ℝ) := by
      exact Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast (show 1 ≤ D by omega)) (by norm_num)
    _ = Real.sqrt D := by rw [Real.sqrt_eq_rpow]

/-- Paper label: `lem:quant-entropy` (Appendix A). -/
theorem lem_quant_entropy (B c C : ℝ) (hB : 2 < B) (hc : 0 < c) (hC : 0 < C) :
    ∃ Zstar : ℕ, ∀ Z D : ℕ,
      Zstar ≤ Z → c * (2 : ℝ) ^ Z ≤ D →
      let ell := Nat.ceil (Real.logb 2 (4 * D))
      C * (ell : ℝ) ^ 4 *
          Real.rpow 2 ((B + 1) * ell * binaryEntropy (5 / Z)) ≤
        Real.sqrt D := by
  have harg : Tendsto (fun Z : ℕ => (5 : ℝ) / (Z : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hEntropyContinuous : Continuous binaryEntropy := by
    rw [show binaryEntropy = fun x => Real.binEntropy x / Real.log 2 by
      funext x
      exact binaryEntropy_eq_binEntropy_div_log_two x]
    exact Real.binEntropy_continuous.div_const _
  have hEntropyZero : binaryEntropy 0 = 0 := by simp [binaryEntropy]
  have hEntropyTendsto :
      Tendsto (fun Z : ℕ => binaryEntropy (5 / (Z : ℝ))) atTop (nhds 0) := by
    change Tendsto (binaryEntropy ∘ fun Z : ℕ => (5 : ℝ) / (Z : ℝ))
      atTop (nhds 0)
    simpa only [hEntropyZero] using (hEntropyContinuous.tendsto 0).comp harg
  have hBplus : 0 < B + 1 := by linarith
  let δ : ℝ := 1 / (8 * (B + 1))
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hEntropySmall :
      ∀ᶠ Z : ℕ in atTop, binaryEntropy (5 / (Z : ℝ)) ≤ δ :=
    hEntropyTendsto.eventually (eventually_le_nhds hδ)
  obtain ⟨Dstar, hDstar⟩ :=
    eventually_atTop.mp (eventually_logarithmic_entropy_bound C hC)
  have hScaleLarge :
      ∀ᶠ Z : ℕ in atTop, (Dstar : ℝ) ≤ c * (2 : ℝ) ^ Z :=
    ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).const_mul_atTop hc)
      |>.eventually_ge_atTop _
  obtain ⟨Zstar, hZstar⟩ := eventually_atTop.mp (hEntropySmall.and hScaleLarge)
  refine ⟨Zstar, fun Z D hZ hD => ?_⟩
  dsimp only
  have hpair := hZstar Z hZ
  have hDstarD_real : (Dstar : ℝ) ≤ D := hpair.2.trans hD
  have hDstarD : Dstar ≤ D := by exact_mod_cast hDstarD_real
  have hgeneric := hDstar D hDstarD
  let ell := Nat.ceil (Real.logb 2 (4 * D))
  have hell0 : (0 : ℝ) ≤ ell := by positivity
  have hcoef : (B + 1) * binaryEntropy (5 / (Z : ℝ)) ≤ 1 / 8 := by
    have hm := mul_le_mul_of_nonneg_left hpair.1 hBplus.le
    calc
      _ ≤ (B + 1) * δ := hm
      _ = 1 / 8 := by
        dsimp [δ]
        field_simp
  have hexponent :
      (B + 1) * (ell : ℝ) * binaryEntropy (5 / (Z : ℝ)) ≤ (ell : ℝ) / 8 := by
    nlinarith [mul_le_mul_of_nonneg_left hcoef hell0]
  have hrpow :
      Real.rpow 2 ((B + 1) * (ell : ℝ) * binaryEntropy (5 / (Z : ℝ))) ≤
        Real.rpow 2 ((ell : ℝ) / 8) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent
  calc
    C * (ell : ℝ) ^ 4 *
        Real.rpow 2 ((B + 1) * (ell : ℝ) * binaryEntropy (5 / (Z : ℝ))) ≤
      C * (ell : ℝ) ^ 4 * Real.rpow 2 ((ell : ℝ) / 8) := by
        exact mul_le_mul_of_nonneg_left hrpow (by positivity)
    _ ≤ Real.sqrt D := by simpa [ell] using hgeneric

end Erdos260

/-! Source module: Erdos260/Carry.lean -/

/-!
# Integral carries, gap control, and weighted mass

This module corresponds to Section 3 of the manuscript.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos260

/-- Finite-sum integer carry associated with a rational support expansion. -/
def carryInt (R : RationalSupport) (N : ℕ) : ℤ :=
  R.eta.num * (2 : ℤ) ^ N -
    (R.eta.den : ℤ) *
      ∑ n ∈ Finset.Icc 1 N,
        (n : ℤ) * (digit R.S n : ℤ) * (2 : ℤ) ^ (N - n)

/-- A genuine support gap: both endpoints are in the support and the open
integer interval between them is empty. -/
def IsSupportGap (S : Set ℕ) (x g : ℕ) : Prop :=
  0 < g ∧ x ∈ S ∧ x + g ∈ S ∧
    ∀ n, x < n → n < x + g → n ∉ S

/-- Counting measure in the anchor coordinate and Lebesgue measure in the
threshold coordinate. -/
def windowThresholdMeasure : Measure WindowThreshold :=
  Measure.count.prod volume

/-- Paper label: `def:mass` (Section 3).  Nonnegative mass is defined by a
lintegral so that non-integrability cannot silently turn it into zero. -/
def mass (E : Set WindowThreshold) (weight : WindowThreshold → ℝ) : ℝ≥0∞ :=
  ∫⁻ e in E, ENNReal.ofReal (weight e) ∂windowThresholdMeasure

/-- A proof-carrying witness that a mass is finite.  Unlike an unguarded
`ENNReal.toReal`, an
instance of this structure cannot be constructed when the underlying
`ℝ≥0∞`-valued mass is infinite. -/
structure FiniteMass (E : Set WindowThreshold)
    (weight : WindowThreshold → ℝ) : Prop where
  ne_top : mass E weight ≠ ⊤

namespace FiniteMass

/-- Safely convert a finite mass to a real number. -/
def toReal {E : Set WindowThreshold} {weight : WindowThreshold → ℝ}
    (_h : FiniteMass E weight) : ℝ :=
  (mass E weight).toReal

/-- The safe real conversion is nonnegative. -/
theorem toReal_nonneg {E : Set WindowThreshold} {weight : WindowThreshold → ℝ}
    (h : FiniteMass E weight) : 0 ≤ h.toReal := by
  exact ENNReal.toReal_nonneg

/-- Re-embedding the safe real conversion recovers the original mass. -/
@[simp] theorem ofReal_toReal {E : Set WindowThreshold}
    {weight : WindowThreshold → ℝ} (h : FiniteMass E weight) :
    ENNReal.ofReal h.toReal = mass E weight := by
  exact ENNReal.ofReal_toReal h.ne_top

end FiniteMass

namespace WindowSystem

theorem pairSet_eq_prod (W : WindowSystem) :
    W.pairSet = Set.prod (W.anchors : Set ℕ) W.thresholds := by
  ext e
  rfl

theorem measurableSet_pairSet (W : WindowSystem) :
    MeasurableSet W.pairSet := by
  rw [pairSet_eq_prod]
  exact MeasurableSet.prod W.anchors.measurableSet
    (by simp [WindowSystem.thresholds, thresholdInterval])

theorem measurable_excess (W : WindowSystem) :
    Measurable W.excess := by
  unfold WindowSystem.excess
  fun_prop

theorem excess_le_rawWindowSpan (W : WindowSystem) (e : WindowThreshold)
    (he : e ∈ W.pairSet) :
    W.excess e ≤ (W.rawWindowSpan e.1 : ℝ) := by
  have he' : e.1 ∈ W.anchors ∧ e.2 ∈ W.thresholds := he
  have hTlower :
      2 * (W.L : ℝ) + W.structural.C0 ≤ e.2 := he'.2.1
  have hbase :
      0 ≤ 2 * (W.L : ℝ) + W.structural.C0 := by positivity
  have hTnonneg : 0 ≤ e.2 := hbase.trans hTlower
  have heps : 0 ≤ W.epsilon * W.L :=
    mul_nonneg W.epsilon_nonneg (Nat.cast_nonneg _)
  unfold WindowSystem.excess
  apply max_le
  case h₁ => linarith
  case h₂ => positivity

end WindowSystem

theorem mass_mono_set {E F : Set WindowThreshold}
    {weight : WindowThreshold → ℝ} (hEF : E ⊆ F) :
    mass E weight ≤ mass F weight := by
  unfold mass
  exact lintegral_mono_set hEF

theorem windowThresholdMeasure_pairSet_ne_top (W : WindowSystem) :
    windowThresholdMeasure W.pairSet ≠ ⊤ := by
  rw [WindowSystem.pairSet_eq_prod, windowThresholdMeasure]
  have hprod :
      (Measure.count.prod volume)
          (Set.prod (W.anchors : Set ℕ) W.thresholds) =
        Measure.count (W.anchors : Set ℕ) * volume W.thresholds :=
    MeasureTheory.Measure.prod_prod _ _
  rw [hprod]
  simp only [Measure.count_apply_finset, WindowSystem.thresholds,
    thresholdInterval, Real.volume_Icc]
  let v : ℝ :=
    2 * (W.L : ℝ) + W.structural.C0 +
      W.structural.cI * W.L -
        (2 * (W.L : ℝ) + W.structural.C0)
  have hcard : (W.anchors.card : ℝ≥0∞) < ⊤ :=
    ENNReal.natCast_lt_top W.anchors.card
  have hvol : ENNReal.ofReal v < ⊤ := ENNReal.ofReal_lt_top
  change (W.anchors.card : ℝ≥0∞) * ENNReal.ofReal v ≠ ⊤
  exact (ENNReal.mul_lt_top hcard hvol).ne

theorem totalMass_finite (W : WindowSystem) :
    mass W.pairSet W.excess ≠ ⊤ := by
  unfold mass
  apply
    (setLIntegral_lt_top_of_le_nnreal
      (windowThresholdMeasure_pairSet_ne_top W) ?_).ne
  let bound : NNReal :=
    ⟨((W.anchors.sum W.rawWindowSpan : ℕ) : ℝ), by positivity⟩
  refine ⟨bound, ?_⟩
  intro e he
  rw [ENNReal.ofReal_le_coe]
  change
    W.excess e ≤
      ((W.anchors.sum W.rawWindowSpan : ℕ) : ℝ)
  calc
    W.excess e ≤ (W.rawWindowSpan e.1 : ℝ) :=
      W.excess_le_rawWindowSpan e he
    _ ≤ ((W.anchors.sum W.rawWindowSpan : ℕ) : ℝ) := by
      exact_mod_cast
        Finset.single_le_sum
          (fun i hi => Nat.zero_le _) he.1

theorem totalFiniteMass (W : WindowSystem) :
    FiniteMass W.pairSet W.excess :=
  ⟨totalMass_finite W⟩

/-- Every genuine subfamily of the window-pair set inherits a finite mass. -/
theorem finiteMassOfSubset (W : WindowSystem) (E : Set WindowThreshold)
    (hE : E ⊆ W.pairSet) : FiniteMass E W.excess :=
  ⟨ne_top_of_le_ne_top (totalMass_finite W) (mass_mono_set hE)⟩

/-- Safe real value of a finite window-pair subfamily.  The subset proof is
part of the interface, so infinite mass can never be silently mapped to zero. -/
def finiteWindowMass (W : WindowSystem) (E : Set WindowThreshold)
    (hE : E ⊆ W.pairSet) : ℝ :=
  (finiteMassOfSubset W E hE).toReal

def totalMassReal (W : WindowSystem) : ℝ :=
  (totalFiniteMass W).toReal

@[simp] theorem ofReal_totalMassReal (W : WindowSystem) :
    ENNReal.ofReal (totalMassReal W) =
      mass W.pairSet W.excess := by
  exact FiniteMass.ofReal_toReal (totalFiniteMass W)

@[simp] theorem weightedSupportTerm_eq_digit (S : Set ℕ) (n : ℕ) :
    weightedSupportTerm S n =
      (n : ℝ) * (digit S n : ℝ) / (2 : ℝ) ^ n := by
  by_cases hn : n ∈ S <;>
    simp [weightedSupportTerm, digit, hn]

theorem sum_range_weightedSupportTerm (S : Set ℕ) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), weightedSupportTerm S n =
      ∑ n ∈ Finset.Icc 1 N, weightedSupportTerm S n := by
  rw [Finset.range_eq_Ico]
  have hinterval : Finset.Ico 0 (N + 1) = Finset.Icc 0 N := by
    ext n
    simp
  rw [hinterval, ← Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le N),
    Finset.sum_insert (by simp)]
  simp [weightedSupportTerm]

theorem carryFiniteSum_cast (R : RationalSupport) (N : ℕ) :
    ((∑ n ∈ Finset.Icc 1 N,
        (n : ℤ) * (digit R.S n : ℤ) * (2 : ℤ) ^ (N - n) : ℤ) : ℝ) =
      (2 : ℝ) ^ N *
        ∑ n ∈ Finset.Icc 1 N, weightedSupportTerm R.S n := by
  rw [Int.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
  push_cast
  rw [weightedSupportTerm_eq_digit]
  have hpow : (2 : ℝ) ^ (N - n) * (2 : ℝ) ^ n = (2 : ℝ) ^ N := by
    rw [← pow_add]
    congr 1
    omega
  field_simp
  rw [← hpow]
  ring

theorem carryInt_cast_eq_partial (R : RationalSupport) (N : ℕ) :
    (carryInt R N : ℝ) =
      (R.eta.den : ℝ) * (2 : ℝ) ^ N *
        ((R.eta : ℝ) -
          ∑ n ∈ Finset.Icc 1 N, weightedSupportTerm R.S n) := by
  unfold carryInt
  push_cast
  have hfinite := carryFiniteSum_cast R N
  push_cast at hfinite
  rw [hfinite]
  have hden : (R.eta.den : ℝ) ≠ 0 := by positivity
  rw [Rat.cast_def]
  field_simp

/-- Scaled tail summand whose sum is the integer carry. -/
def carryTailTerm (R : RationalSupport) (N j : ℕ) : ℝ :=
  (R.eta.den : ℝ) * (2 : ℝ) ^ N *
    weightedSupportTerm R.S (j + (N + 1))

theorem weightedSupportTerm_nonneg (S : Set ℕ) (n : ℕ) :
    0 ≤ weightedSupportTerm S n := by
  rw [weightedSupportTerm_eq_digit]
  positivity

theorem carryTailTerm_nonneg (R : RationalSupport) (N j : ℕ) :
    0 ≤ carryTailTerm R N j := by
  have hterm :
      0 ≤ weightedSupportTerm R.S (j + (N + 1)) := by
    by_cases hmem : j + (N + 1) ∈ R.S
    · simp [weightedSupportTerm, hmem]
      positivity
    · simp [weightedSupportTerm, hmem]
  unfold carryTailTerm
  exact mul_nonneg (by positivity) hterm

def carryMajorant (R : RationalSupport) (N j : ℕ) : ℝ :=
  (R.eta.den : ℝ) *
    (((N + 1 : ℝ) / 2) * ((1 : ℝ) / 2) ^ j +
      ((1 : ℝ) / 2) * (j : ℝ) * ((1 : ℝ) / 2) ^ j)

theorem carryTailTerm_le_majorant (R : RationalSupport) (N j : ℕ) :
    carryTailTerm R N j ≤ carryMajorant R N j := by
  let n := j + (N + 1)
  have hdigit : (digit R.S n : ℝ) ≤ 1 := by
    by_cases hn : n ∈ R.S <;> simp [digit, hn]
  have hpow : (2 : ℝ) ^ n =
      (2 : ℝ) ^ N * (2 : ℝ) ^ (j + 1) := by
    dsimp [n]
    rw [← pow_add]
    congr 1
    omega
  rw [carryTailTerm, carryMajorant, weightedSupportTerm_eq_digit]
  change
    (R.eta.den : ℝ) * 2 ^ N * ((n : ℝ) * (digit R.S n : ℝ) / 2 ^ n) ≤ _
  calc
    (R.eta.den : ℝ) * 2 ^ N *
          ((n : ℝ) * (digit R.S n : ℝ) / 2 ^ n) ≤
        (R.eta.den : ℝ) * 2 ^ N * ((n : ℝ) * 1 / 2 ^ n) := by
      gcongr
    _ = (R.eta.den : ℝ) *
        (((N + 1 : ℝ) / 2) * ((1 : ℝ) / 2) ^ j +
          ((1 : ℝ) / 2) * (j : ℝ) * ((1 : ℝ) / 2) ^ j) := by
      rw [hpow]
      simp only [div_pow, one_pow]
      field_simp
      dsimp [n]
      push_cast
      ring

theorem exists_support_gt (R : RationalSupport) (N : ℕ) :
    ∃ n ∈ R.S, N < n := by
  by_contra h
  push Not at h
  have hsubset : R.S ⊆ (Finset.range (N + 1) : Set ℕ) := by
    intro n hn
    simp only [Finset.coe_range, Set.mem_Iio]
    have hnle := h n hn
    omega
  exact R.infinite ((Finset.range (N + 1)).finite_toSet.subset hsubset)

theorem carryInt_succ (R : RationalSupport) (N : ℕ) :
    carryInt R (N + 1) =
      2 * carryInt R N -
        (R.eta.den : ℤ) * (N + 1) * (digit R.S (N + 1) : ℤ) := by
  have hsum :
      (∑ n ∈ Finset.Icc 1 (N + 1),
          (n : ℤ) * (digit R.S n : ℤ) * (2 : ℤ) ^ (N + 1 - n)) =
        2 * ∑ n ∈ Finset.Icc 1 N,
          (n : ℤ) * (digit R.S n : ℤ) * (2 : ℤ) ^ (N - n) +
          (N + 1 : ℤ) * (digit R.S (N + 1) : ℤ) := by
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hold :
        (∑ n ∈ Finset.Icc 1 N,
            (n : ℤ) * (digit R.S n : ℤ) * (2 : ℤ) ^ (N + 1 - n)) =
          2 * ∑ n ∈ Finset.Icc 1 N,
            (n : ℤ) * (digit R.S n : ℤ) * (2 : ℤ) ^ (N - n) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
      have hexponent : N + 1 - n = (N - n) + 1 := by omega
      rw [hexponent, pow_succ]
      ring
    rw [hold]
    norm_num
  unfold carryInt
  rw [hsum, pow_succ]
  ring

theorem carryInt_inside_gap (R : RationalSupport) (x g : ℕ)
    (hgap : IsSupportGap R.S x g) :
    ∀ r < g, carryInt R (x + r) = (2 : ℤ) ^ r * carryInt R x := by
  intro r hr
  induction r with
  | zero => simp
  | succ r ih =>
      have hrg : r < g := r.lt_succ_self.trans hr
      have hnotmem : x + (r + 1) ∉ R.S := by
        apply hgap.2.2.2 (x + (r + 1))
        · omega
        · omega
      have hnotmem' : x + r + 1 ∉ R.S := by
        simpa [Nat.add_assoc] using hnotmem
      rw [show x + (r + 1) = (x + r) + 1 by omega,
        carryInt_succ, ih hrg]
      simp [digit, hnotmem', pow_succ]
      ring

/-- Exact carry update from one support point to the next support point. -/
theorem carryInt_across_supportGap (R : RationalSupport) (x g : ℕ)
    (hgap : IsSupportGap R.S x g) :
    carryInt R (x + g) =
      (2 : ℤ) ^ g * carryInt R x -
        (R.eta.den : ℤ) * (x + g) := by
  have hg : 0 < g := hgap.1
  have hinside := carryInt_inside_gap R x g hgap (g - 1) (by omega)
  rw [show x + g = (x + (g - 1)) + 1 by omega, carryInt_succ,
    hinside]
  have hend : x + g ∈ R.S := hgap.2.2.1
  have hdigit : digit R.S (x + g) = 1 := by
    simp [digit, hend]
  rw [show x + (g - 1) + 1 = x + g by omega, hdigit]
  have hpow : (2 : ℤ) ^ g = 2 * (2 : ℤ) ^ (g - 1) := by
    conv_lhs => rw [show g = (g - 1) + 1 by omega, pow_succ]
    ring
  rw [hpow]
  have hcast : ((x + (g - 1) : ℕ) : ℤ) + 1 = (x : ℤ) + g := by
    exact_mod_cast (show (x + (g - 1)) + 1 = x + g by omega)
  linear_combination -(R.eta.den : ℤ) * hcast

/-- Paper label: `prop:carry` (Section 3). -/
theorem prop_carry (R : RationalSupport) :
    (∀ N : ℕ,
      carryInt R (N + 1) =
        2 * carryInt R N -
          (R.eta.den : ℤ) * (N + 1) * (digit R.S (N + 1) : ℤ)) ∧
    (∀ N : ℕ, 0 ≤ carryInt R N) ∧
    (∀ N : ℕ, carryInt R N ≤ (R.eta.den : ℤ) * (N + 2)) ∧
    (∀ N : ℕ, 1 ≤ carryInt R N) := by
  refine ⟨carryInt_succ R, ?_, ?_, ?_⟩
  · intro N
    have htail := (hasSum_nat_add_iff' (f := weightedSupportTerm R.S)
      (N + 1)).mpr R.hasSum
    rw [sum_range_weightedSupportTerm] at htail
    have htail_nonneg :
        0 ≤ (R.eta : ℝ) -
          ∑ n ∈ Finset.Icc 1 N, weightedSupportTerm R.S n := by
      rw [← htail.tsum_eq]
      simpa using htail.summable.sum_le_tsum ∅
        (fun j _ => weightedSupportTerm_nonneg R.S (j + (N + 1)))
    have hcarry : 0 ≤ (carryInt R N : ℝ) := by
      rw [carryInt_cast_eq_partial]
      exact mul_nonneg (by positivity) htail_nonneg
    exact_mod_cast hcarry
  · intro N
    have htail := (hasSum_nat_add_iff' (f := weightedSupportTerm R.S)
      (N + 1)).mpr R.hasSum
    rw [sum_range_weightedSupportTerm] at htail
    have hscaled := htail.mul_left
      ((R.eta.den : ℝ) * (2 : ℝ) ^ N)
    have hgeom := hasSum_geometric_of_norm_lt_one
      (ξ := ((1 : ℝ) / 2)) (by norm_num)
    have hlinear := hasSum_coe_mul_geometric_of_norm_lt_one
      (r := ((1 : ℝ) / 2)) (by norm_num)
    have hmajorBase :=
      (hgeom.mul_left ((N + 1 : ℝ) / 2)).add
        (hlinear.mul_left ((1 : ℝ) / 2))
    have hmajor := hmajorBase.mul_left (R.eta.den : ℝ)
    have hle := hscaled.summable.tsum_le_tsum
      (fun j => by
        simpa only [carryTailTerm, carryMajorant, mul_assoc] using
          carryTailTerm_le_majorant R N j)
      hmajor.summable
    rw [hscaled.tsum_eq, hmajor.tsum_eq] at hle
    rw [← carryInt_cast_eq_partial] at hle
    norm_num at hle
    exact_mod_cast hle
  · intro N
    have htail := (hasSum_nat_add_iff' (f := weightedSupportTerm R.S)
      (N + 1)).mpr R.hasSum
    rw [sum_range_weightedSupportTerm] at htail
    obtain ⟨n, hnS, hnN⟩ := exists_support_gt R N
    let j := n - (N + 1)
    have hindex : j + (N + 1) = n := by
      dsimp [j]
      omega
    have htermpos :
        0 < weightedSupportTerm R.S (j + (N + 1)) := by
      have hnpos : (0 : ℝ) < n := by
        exact_mod_cast R.positive n hnS
      rw [hindex]
      simp only [weightedSupportTerm, hnS, if_pos]
      positivity
    have hterm_le :
        weightedSupportTerm R.S (j + (N + 1)) ≤
          (R.eta : ℝ) -
            ∑ n ∈ Finset.Icc 1 N, weightedSupportTerm R.S n := by
      rw [← htail.tsum_eq]
      simpa using htail.summable.sum_le_tsum {j}
        (fun i _ => weightedSupportTerm_nonneg R.S (i + (N + 1)))
    have htailpos :
        0 < (R.eta : ℝ) -
          ∑ n ∈ Finset.Icc 1 N, weightedSupportTerm R.S n :=
      htermpos.trans_le hterm_le
    have hcarry : 0 < (carryInt R N : ℝ) := by
      rw [carryInt_cast_eq_partial]
      exact mul_pos (by positivity) htailpos
    have hcarryInt : 0 < carryInt R N := by exact_mod_cast hcarry
    omega

theorem gap_power_bound (R : RationalSupport) (x g : ℕ)
    (hgap : IsSupportGap R.S x g) :
    2 ^ (g - 1) ≤ R.eta.den * (x + g + 1) := by
  have hg : 0 < g := hgap.1
  have hiterate := carryInt_inside_gap R x g hgap (g - 1) (by omega)
  have hpositive : 1 ≤ carryInt R x := (prop_carry R).2.2.2 x
  have hupper := (prop_carry R).2.2.1 (x + (g - 1))
  have hpow_nonneg : (0 : ℤ) ≤ (2 : ℤ) ^ (g - 1) := by positivity
  have hint :
      (2 : ℤ) ^ (g - 1) ≤
        (R.eta.den : ℤ) * (x + g + 1) := by
    calc
      (2 : ℤ) ^ (g - 1) ≤
          (2 : ℤ) ^ (g - 1) * carryInt R x := by
        nlinarith
      _ = carryInt R (x + (g - 1)) := hiterate.symm
      _ ≤ (R.eta.den : ℤ) * ((x + (g - 1) : ℕ) + 2) := hupper
      _ = (R.eta.den : ℤ) * (x + g + 1) := by
        congr 1
        omega
  exact_mod_cast hint

theorem eventually_linear_lt_two_pow_pred (Q : ℕ) :
    ∃ x0 : ℕ, ∀ n : ℕ, x0 ≤ n → 3 * Q * n < 2 ^ (n - 1) := by
  have ht :=
    (tendsto_self_mul_const_pow_of_lt_one
      (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).const_mul
      (6 * (Q : ℝ))
  have hevent : ∀ᶠ n : ℕ in atTop,
      (6 * (Q : ℝ)) * ((n : ℝ) * (1 / 2 : ℝ) ^ n) < 1 :=
    (tendsto_order.1 ht).2 1 (by norm_num)
  obtain ⟨x0, hx0⟩ := (eventually_atTop.1 hevent)
  refine ⟨max x0 1, ?_⟩
  intro n hn
  have hnx0 : x0 ≤ n := (le_max_left x0 1).trans hn
  have hn1 : 1 ≤ n := (le_max_right x0 1).trans hn
  have h := hx0 n hnx0
  have hquot :
      (6 * (Q : ℝ) * (n : ℝ)) / (2 : ℝ) ^ n < 1 := by
    simpa only [one_div, one_mul, inv_pow, div_eq_mul_inv, mul_assoc] using h
  have hden : 0 < (2 : ℝ) ^ n := by positivity
  have h6 :
      6 * (Q : ℝ) * (n : ℝ) < (2 : ℝ) ^ n :=
    (div_lt_one hden).mp hquot
  have hpow :
      (2 : ℝ) ^ n = 2 * (2 : ℝ) ^ (n - 1) := by
    calc
      (2 : ℝ) ^ n = (2 : ℝ) ^ ((n - 1) + 1) := by
        congr 1
        omega
      _ = (2 : ℝ) ^ (n - 1) * 2 := by rw [pow_succ]
      _ = 2 * (2 : ℝ) ^ (n - 1) := by ring
  rw [hpow] at h6
  have h3 :
      3 * (Q : ℝ) * (n : ℝ) < (2 : ℝ) ^ (n - 1) := by
    nlinarith
  exact_mod_cast h3

/-- Paper label: `lem:gap` (Section 3).  Both the gap constant and the
starting point are uniform over every rational support with denominator `Q`. -/
theorem lem_gap :
    ∀ Q : ℕ, 0 < Q → ∃ Cgap x0 : ℕ,
      ∀ R : RationalSupport, R.eta.den = Q → ∀ x : ℕ, x0 ≤ x →
        ∀ g : ℕ, IsSupportGap R.S x g →
          g ≤ Nat.log 2 x + Cgap := by
  intro Q hQ
  obtain ⟨xexp, hexp⟩ := eventually_linear_lt_two_pow_pred Q
  refine ⟨Nat.clog 2 (3 * Q) + 1, max xexp 1, ?_⟩
  intro R hden x hx g hgap
  have hxxexp : xexp ≤ x := (le_max_left xexp 1).trans hx
  have hx1 : 1 ≤ x := (le_max_right xexp 1).trans hx
  have hpower := gap_power_bound R x g hgap
  rw [hden] at hpower
  have hgapltx : g < x := by
    by_contra hnot
    have hxg : x ≤ g := Nat.le_of_not_gt hnot
    have hgexp : xexp ≤ g := hxxexp.trans hxg
    have hstrict := hexp g hgexp
    have hsum : x + g + 1 ≤ 3 * g := by omega
    have hlinear : Q * (x + g + 1) ≤ 3 * Q * g := by
      have := Nat.mul_le_mul_left Q hsum
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    exact (Nat.not_lt_of_ge (hpower.trans hlinear)) hstrict
  have hsum : x + g + 1 ≤ 3 * x := by omega
  have hlinear : Q * (x + g + 1) ≤ 3 * Q * x := by
    have := Nat.mul_le_mul_left Q hsum
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  have hpower' : 2 ^ (g - 1) ≤ 3 * Q * x := hpower.trans hlinear
  have hQpow : 3 * Q ≤ 2 ^ Nat.clog 2 (3 * Q) :=
    Nat.le_pow_clog Nat.one_lt_two (3 * Q)
  have hxpow : x < 2 ^ (Nat.log 2 x + 1) := by
    simpa [Nat.succ_eq_add_one] using
      Nat.lt_pow_succ_log_self Nat.one_lt_two x
  have hthreeQ : 0 < 3 * Q := Nat.mul_pos (by omega) hQ
  have hproduct :
      3 * Q * x <
        2 ^ Nat.clog 2 (3 * Q) * 2 ^ (Nat.log 2 x + 1) := by
    calc
      3 * Q * x < 3 * Q * 2 ^ (Nat.log 2 x + 1) :=
        Nat.mul_lt_mul_of_pos_left hxpow hthreeQ
      _ ≤ 2 ^ Nat.clog 2 (3 * Q) * 2 ^ (Nat.log 2 x + 1) :=
        Nat.mul_le_mul_right _ hQpow
  have hpowers :
      2 ^ (g - 1) <
        2 ^ (Nat.clog 2 (3 * Q) + (Nat.log 2 x + 1)) := by
    calc
      2 ^ (g - 1) ≤ 3 * Q * x := hpower'
      _ < 2 ^ Nat.clog 2 (3 * Q) * 2 ^ (Nat.log 2 x + 1) := hproduct
      _ = 2 ^ (Nat.clog 2 (3 * Q) + (Nat.log 2 x + 1)) := by
        exact (pow_add (2 : ℕ) _ _).symm
  have hexponents :
      g - 1 < Nat.clog 2 (3 * Q) + (Nat.log 2 x + 1) :=
    (Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp hpowers
  omega

/-- Denominator-level gap data selected by `lem_gap`.  Keeping the proof in
the structure prevents later affine arguments from accepting an arbitrary
number as though it were a valid uniform gap constant. -/
structure GapParams (Q : ℕ) where
  Cgap : ℕ
  x0 : ℕ
  bound : ∀ R : RationalSupport, R.eta.den = Q → ∀ x : ℕ, x0 ≤ x →
    ∀ g : ℕ, IsSupportGap R.S x g → g ≤ Nat.log 2 x + Cgap

theorem gapParams_exists (Q : ℕ) (hQ : 0 < Q) : Nonempty (GapParams Q) := by
  obtain ⟨Cgap, x0, hbound⟩ := lem_gap Q hQ
  exact ⟨⟨Cgap, x0, hbound⟩⟩

/-- Paper label: `lem:refinement-principle` (Section 3).  Every pair may use
its own finite label set; the weights on that set form a nonnegative partition
of unity. -/
theorem lem_refinement_principle {ι : Type*} [DecidableEq ι]
    (E : Set WindowThreshold) (hE : MeasurableSet E)
    (weight : WindowThreshold → ℝ)
    (labels : WindowThreshold → Finset ι)
    (α : WindowThreshold → ι → ℝ)
    (hweight : ∀ e, e ∈ E → 0 ≤ weight e)
    (hα : ∀ e, e ∈ E →
      (∀ i ∈ labels e, 0 ≤ α e i) ∧ ∑ i ∈ labels e, α e i = 1) :
    (∫⁻ e in E,
        ENNReal.ofReal (∑ i ∈ labels e, weight e * α e i)
        ∂windowThresholdMeasure) = mass E weight := by
  unfold mass
  apply setLIntegral_congr_fun hE
  intro e he
  change ENNReal.ofReal (∑ i ∈ labels e, weight e * α e i) =
    ENNReal.ofReal (weight e)
  have hsum : 0 ≤ ∑ i ∈ labels e, weight e * α e i :=
    Finset.sum_nonneg fun i hi =>
      mul_nonneg (hweight e he) ((hα e he).1 i hi)
  apply (ENNReal.ofReal_eq_ofReal_iff hsum (hweight e he)).2
  rw [← Finset.mul_sum, (hα e he).2, mul_one]

end Erdos260

/-! Source module: Erdos260/Pressure.lean -/

/-!
# Sparse-block lower bound and bounded-excess contribution

This module corresponds to Section 4 of the manuscript.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos260

/-- Data fixed after the denominator is chosen and before the rational
numerator or support set is allowed to vary.  In particular, the positive
pressure parameter is shared by every compatible scale family. -/
structure FixedScaleContext where
  Q : ℕ
  Q_pos : 0 < Q
  structural : StructuralParams
  entropy : EntropyParams
  entropy_structural : entropy.structural = structural
  epsilon : ℝ
  epsilon_pos : 0 < epsilon

/-- A coherent family indexed by the dyadic exponent.  The rational support,
its increasing enumeration, the structural/entropy parameters, and the
pressure offset are fixed before `L` varies. -/
structure ScaleFamily where
  rational : RationalSupport
  enumeration : SupportEnumeration rational.S
  structural : StructuralParams
  entropy : EntropyParams
  entropy_structural : entropy.structural = structural
  epsilon : ℝ
  epsilon_nonneg : 0 ≤ epsilon
  system : ℕ → WindowSystem
  level_eq : ∀ L, (system L).L = L
  rational_eq : ∀ L, (system L).rational = rational
  enumeration_eq : ∀ L n, (system L).enumeration.a n = enumeration.a n
  structural_eq : ∀ L, (system L).structural = structural
  entropy_eq : ∀ L, (system L).entropy = entropy
  epsilon_eq : ∀ L, (system L).epsilon = epsilon
  offset_eq : ∀ L,
    (system L).s = Nat.floor (entropy.kappa * (L : ℝ))

/-- Length of the paper's threshold interval. -/
def thresholdLength (W : WindowSystem) : ℝ :=
  W.structural.cI * W.L

/-- Integrated window excess as the certified finite real value of the
counting × Lebesgue mass. -/
def integratedExcess (W : WindowSystem) : ℝ :=
  totalMassReal W

@[simp] theorem integratedExcess_eq_totalMassReal (W : WindowSystem) :
    integratedExcess W = totalMassReal W := rfl

@[simp] theorem ofReal_integratedExcess (W : WindowSystem) :
    ENNReal.ofReal (integratedExcess W) = mass W.pairSet W.excess := by
  exact ofReal_totalMassReal W

namespace ScaleFamily

/-- A scale family is compatible with a denominator-level context when all
data selected before the rational numerator/support agree with that context. -/
def MatchesContext (F : ScaleFamily) (context : FixedScaleContext) : Prop :=
  F.rational.eta.den = context.Q ∧
    F.structural = context.structural ∧
    F.entropy = context.entropy ∧
    F.epsilon = context.epsilon

end ScaleFamily

/-- The mass formulation of the same window-threshold quantity. -/
def totalWindowMass (W : WindowSystem) : ℝ≥0∞ :=
  mass W.pairSet W.excess

/-! ## Discrete window-counting infrastructure -/

/-- A positive strictly increasing enumeration of naturals lies strictly
above the identity. -/
theorem supportEnumeration_index_lt {S : Set ℕ}
    (e : SupportEnumeration S) (n : ℕ) : n < e.a n := by
  induction n with
  | zero => exact e.positive 0
  | succ n ih =>
      exact lt_of_le_of_lt (Nat.succ_le_iff.mpr ih)
        (e.strictMono (Nat.lt_succ_self n))

/-- First enumeration index whose support point is strictly above `x`. -/
def firstIndexAbove {S : Set ℕ} (e : SupportEnumeration S) (x : ℕ) : ℕ :=
  Nat.find (p := fun n => x < e.a n)
    ⟨x, supportEnumeration_index_lt e x⟩

theorem firstIndexAbove_spec {S : Set ℕ} (e : SupportEnumeration S) (x : ℕ) :
    x < e.a (firstIndexAbove e x) := by
  exact Nat.find_spec (p := fun n => x < e.a n)
    ⟨x, supportEnumeration_index_lt e x⟩

theorem firstIndexAbove_le {S : Set ℕ} (e : SupportEnumeration S) (x : ℕ) :
    firstIndexAbove e x ≤ x := by
  exact Nat.find_min' (p := fun n => x < e.a n)
    ⟨x, supportEnumeration_index_lt e x⟩
    (supportEnumeration_index_lt e x)

theorem firstIndexAbove_minimal {S : Set ℕ} (e : SupportEnumeration S)
    (x n : ℕ) (hn : n < firstIndexAbove e x) : e.a n ≤ x := by
  by_contra hnot
  have hx : x < e.a n := Nat.lt_of_not_ge hnot
  have hle : firstIndexAbove e x ≤ n :=
    Nat.find_min' (p := fun n => x < e.a n)
      ⟨x, supportEnumeration_index_lt e x⟩ hx
  omega

/-- Consecutive points of an increasing enumeration determine a genuine
support gap. -/
theorem supportGap_isSupportGap {S : Set ℕ} (e : SupportEnumeration S)
    (k : ℕ) : IsSupportGap S (e.a k) (supportGap e k) := by
  have hstep : e.a k < e.a (k + 1) := e.strictMono (Nat.lt_succ_self k)
  refine ⟨by simpa [supportGap] using Nat.sub_pos_of_lt hstep,
    ?_, ?_, ?_⟩
  · exact (Set.ext_iff.mp e.range_eq (e.a k)).mp ⟨k, rfl⟩
  · apply (Set.ext_iff.mp e.range_eq
      (e.a k + supportGap e k)).mp
    refine ⟨k + 1, ?_⟩
    exact (Nat.add_sub_of_le hstep.le).symm
  · intro n hkn hnk hnS
    have hnRange : n ∈ Set.range e.a :=
      (Set.ext_iff.mp e.range_eq n).mpr hnS
    rcases hnRange with ⟨j, rfl⟩
    have hkj : k < j := (e.strictMono.lt_iff_lt).mp hkn
    have hjk : j < k + 1 := by
      apply (e.strictMono.lt_iff_lt).mp
      simpa [supportGap, Nat.add_sub_of_le hstep.le] using hnk
    omega

/-- A finite consecutive sum of support gaps telescopes. -/
theorem sum_supportGap_Ico {S : Set ℕ} (e : SupportEnumeration S)
    (lo hi : ℕ) (hlo : lo ≤ hi) :
    ∑ k ∈ Finset.Ico lo hi, supportGap e k = e.a hi - e.a lo := by
  induction hi with
  | zero =>
      have : lo = 0 := by omega
      subst lo
      simp
  | succ hi ih =>
      by_cases hEq : lo = hi + 1
      · subst lo
        simp
      · have hlohi : lo ≤ hi := by omega
        rw [Finset.sum_Ico_succ_top hlohi, ih hlohi]
        have hmono : e.a lo ≤ e.a hi := e.strictMono.monotone hlohi
        have hstep : e.a hi ≤ e.a (hi + 1) :=
          (e.strictMono (Nat.lt_succ_self hi)).le
        simp only [supportGap]
        omega

/-- The raw order-`s+1` span is the corresponding endpoint difference. -/
theorem rawWindowSpan_eq_sub (W : WindowSystem) (k : ℕ) (hk : W.s ≤ k) :
    W.rawWindowSpan k = W.enumeration.a (k + 1) -
      W.enumeration.a (k - W.s) := by
  rw [WindowSystem.rawWindowSpan, dif_pos hk]
  unfold windowSpan windowGapWord GapWord.span WindowSystem.window
  rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
  have htel := sum_supportGap_Ico W.enumeration (k - W.s) (k + 1) (by omega)
  rw [Finset.sum_Ico_eq_sum_range] at htel
  simpa [show k + 1 - (k - W.s) = W.s + 1 by omega] using htel

/-- Across a run with no support digit, the carry doubles at every step. -/
theorem carryInt_zero_run (R : RationalSupport) (N r : ℕ)
    (hzero : ∀ j, 1 ≤ j → j ≤ r → N + j ∉ R.S) :
    carryInt R (N + r) = (2 : ℤ) ^ r * carryInt R N := by
  induction r with
  | zero => simp
  | succ r ih =>
      have hzero' : ∀ j, 1 ≤ j → j ≤ r → N + j ∉ R.S := by
        intro j hj1 hjr
        exact hzero j hj1 (hjr.trans (Nat.le_succ r))
      rw [show N + (r + 1) = (N + r) + 1 by omega,
        carryInt_succ, ih hzero']
      have hnot : N + r + 1 ∉ R.S := by
        simpa [Nat.add_assoc] using hzero (r + 1) (by omega) (by omega)
      simp [digit, hnot, pow_succ]
      ring

/-- Uniformly in the numerator and support, every sufficiently large
multiplicative interval `(N,2N]` contains a support point. -/
theorem exists_support_Ioc_of_large (Q xexp : ℕ)
    (hexp : ∀ n : ℕ, xexp ≤ n → 3 * Q * n < 2 ^ (n - 1))
    (R : RationalSupport) (hden : R.eta.den = Q) (N : ℕ)
    (hN : max xexp 2 ≤ N) :
    ∃ n ∈ R.S, N < n ∧ n ≤ 2 * N := by
  by_contra hnone
  have hzero : ∀ j, 1 ≤ j → j ≤ N → N + j ∉ R.S := by
    intro j hj1 hjN hmem
    apply hnone
    exact ⟨N + j, hmem, by omega, by omega⟩
  have hrun := carryInt_zero_run R N N hzero
  have hlower : 1 ≤ carryInt R N := (prop_carry R).2.2.2 N
  have hupper : carryInt R (N + N) ≤
      (R.eta.den : ℤ) * ((N + N) + 2) := (prop_carry R).2.2.1 (N + N)
  have hpowInt : (2 : ℤ) ^ N ≤ carryInt R (N + N) := by
    rw [hrun]
    have hpnonneg : (0 : ℤ) ≤ (2 : ℤ) ^ N := by positivity
    nlinarith
  have hpow : 2 ^ N ≤ Q * (2 * N + 2) := by
    rw [hden] at hupper
    have := hpowInt.trans hupper
    have hnat : 2 ^ N ≤ Q * (N + N + 2) := by
      exact_mod_cast this
    simpa [two_mul] using hnat
  have hlinear : Q * (2 * N + 2) ≤ 3 * Q * N := by
    have hbase : 2 * N + 2 ≤ 3 * N := by
      have : 2 ≤ N := (le_max_right xexp 2).trans hN
      omega
    have := Nat.mul_le_mul_left Q hbase
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  have hstrict := hexp N ((le_max_left xexp 2).trans hN)
  have hpred_le : 2 ^ (N - 1) ≤ 2 ^ N :=
    Nat.pow_le_pow_right (by omega) (Nat.sub_le N 1)
  omega

/-- Every fixed quadratic polynomial is eventually dominated by `2^L`. -/
theorem eventually_quadratic_lt_two_pow (A : ℕ) :
    ∃ L0 : ℕ, ∀ L : ℕ, L0 ≤ L → A * L ^ 2 < 2 ^ L := by
  have ht := (tendsto_pow_const_div_const_pow_of_one_lt 2
    (show (1 : ℝ) < 2 by norm_num)).const_mul (A : ℝ)
  have ht0 : Tendsto
      (fun L : ℕ => (A : ℝ) * ((L : ℝ) ^ 2 / (2 : ℝ) ^ L))
      atTop (nhds 0) := by
    simpa using ht
  have hevent : ∀ᶠ L : ℕ in atTop,
      (A : ℝ) * ((L : ℝ) ^ 2 / (2 : ℝ) ^ L) < 1 :=
    (tendsto_order.1 ht0).2 1 (by norm_num)
  obtain ⟨L0, hL0⟩ := eventually_atTop.1 hevent
  refine ⟨L0, ?_⟩
  intro L hL
  have h := hL0 L hL
  have hpow : (0 : ℝ) < (2 : ℝ) ^ L := by positivity
  have hreal : (A : ℝ) * (L : ℝ) ^ 2 < (2 : ℝ) ^ L := by
    apply (div_lt_one hpow).mp
    simpa [mul_div_assoc] using h
  exact_mod_cast hreal

/-- The anchors are exactly the interval between the first support index
above `X` and the first support index above `2X`. -/
theorem anchors_eq_Ico_firstIndices (W : WindowSystem) :
    W.anchors = Finset.Ico (firstIndexAbove W.enumeration W.X)
      (firstIndexAbove W.enumeration (2 * W.X)) := by
  classical
  let i := firstIndexAbove W.enumeration W.X
  let j := firstIndexAbove W.enumeration (2 * W.X)
  have hi : W.X < W.enumeration.a i := firstIndexAbove_spec _ _
  have hj : 2 * W.X < W.enumeration.a j := firstIndexAbove_spec _ _
  have hjle : j ≤ 2 * W.X := firstIndexAbove_le _ _
  ext k
  simp only [WindowSystem.anchors, Finset.mem_filter, Finset.mem_range,
    Finset.mem_Ico]
  constructor
  · rintro ⟨_, hkX, hk2X⟩
    have hik : i ≤ k := by
      by_contra hnot
      have hle := firstIndexAbove_minimal W.enumeration W.X k
        (Nat.lt_of_not_ge hnot)
      omega
    have hkj : k < j := by
      by_contra hnot
      have hjk : j ≤ k := Nat.le_of_not_gt hnot
      have := W.enumeration.strictMono.monotone hjk
      omega
    exact ⟨hik, hkj⟩
  · rintro ⟨hik, hkj⟩
    have hkX : W.X < W.enumeration.a k :=
      hi.trans_le (W.enumeration.strictMono.monotone hik)
    have hk2X : W.enumeration.a k ≤ 2 * W.X :=
      firstIndexAbove_minimal W.enumeration (2 * W.X) k hkj
    exact ⟨by omega, hkX, hk2X⟩

theorem self_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      have hone : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
      omega

theorem rawWindowSpan_eq_sum_range (W : WindowSystem) (k : ℕ)
    (hk : W.s ≤ k) :
    W.rawWindowSpan k =
      ∑ r ∈ Finset.range W.m,
        supportGap W.enumeration (k - W.s + r) := by
  rw [WindowSystem.rawWindowSpan, dif_pos hk]
  unfold windowSpan windowGapWord GapWord.span WindowSystem.window
  rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
  rfl

/-- Every gap in the central index interval is counted by all `m=s+1`
overlapping anchored windows. -/
theorem central_gap_multiplicity (W : WindowSystem) (i j : ℕ)
    (hanchors : W.anchors = Finset.Ico i j)
    (hsi : W.s ≤ i) (hij0 : i ≤ j) (hwidth : W.s ≤ j - i) :
    W.m * (W.enumeration.a (j - W.s) - W.enumeration.a i) ≤
      ∑ k ∈ W.anchors, W.rawWindowSpan k := by
  have hij : i ≤ j - W.s := by omega
  have hcentral := sum_supportGap_Ico W.enumeration i (j - W.s) hij
  rw [hanchors]
  calc
    W.m * (W.enumeration.a (j - W.s) - W.enumeration.a i) =
        ∑ r ∈ Finset.range W.m,
          ∑ t ∈ Finset.Ico i (j - W.s), supportGap W.enumeration t := by
      rw [← hcentral]
      simp [WindowSystem.m, mul_comm]
    _ ≤ ∑ r ∈ Finset.range W.m,
          ∑ k ∈ Finset.Ico i j,
            supportGap W.enumeration (k - W.s + r) := by
      apply Finset.sum_le_sum
      intro r hr
      have hrs : r ≤ W.s := by
        simpa [WindowSystem.m] using (Finset.mem_range.mp hr)
      have hshift :
          (∑ k ∈ Finset.Ico i j,
              supportGap W.enumeration (k - W.s + r)) =
            ∑ t ∈ Finset.Ico (i - W.s + r) (j - W.s + r),
              supportGap W.enumeration t := by
        rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
        have hlen :
            (j - W.s + r) - (i - W.s + r) = j - i := by omega
        rw [hlen]
        apply Finset.sum_congr rfl
        intro q hq
        have harg : i + q - W.s + r = i - W.s + r + q := by omega
        rw [harg]
      rw [hshift]
      apply Finset.sum_le_sum_of_subset
      exact Finset.Ico_subset_Ico (by omega) (by omega)
    _ = ∑ k ∈ Finset.Ico i j, W.rawWindowSpan k := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      rw [rawWindowSpan_eq_sum_range W k]
      exact hsi.trans (Finset.mem_Ico.mp hk).1

theorem sum_supportGap_le_mul {S : Set ℕ} (e : SupportEnumeration S)
    (lo hi G : ℕ) (hlo : lo ≤ hi)
    (hgap : ∀ k ∈ Finset.Ico lo hi, supportGap e k ≤ G) :
    e.a hi - e.a lo ≤ (hi - lo) * G := by
  rw [← sum_supportGap_Ico e lo hi hlo]
  calc
    (∑ k ∈ Finset.Ico lo hi, supportGap e k) ≤
        ∑ _k ∈ Finset.Ico lo hi, G := Finset.sum_le_sum hgap
    _ = (hi - lo) * G := by simp

/-- Paper label: `lem:window-count` (Section 4). -/
theorem lem_window_count (Q : ℕ) (hQ : 0 < Q)
    (C : ℝ) (hC : 0 < C) :
    ∃ K : ℝ, 0 < K ∧ ∃ L0 : ℕ, ∀ W : WindowSystem,
      W.rational.eta.den = Q → L0 ≤ W.L →
      (W.s : ℝ) ≤ C * W.L →
       ((W.m * W.X : ℕ) : ℝ) ≤
         (∑ k ∈ W.anchors, W.rawWindowSpan k : ℕ) +
           K * (W.s + 1) * (W.L : ℝ) ^ 2 := by
  obtain ⟨Cgap, x0, hgap⟩ := lem_gap Q hQ
  obtain ⟨xexp, hexp⟩ := eventually_linear_lt_two_pow_pred Q
  let cN := Nat.ceil C
  let K0 := (cN + 1) * (Cgap + 2)
  obtain ⟨Lquad, hquad⟩ := eventually_quadratic_lt_two_pow (4 * K0)
  let L0 := max Lquad (max (max xexp x0 + 2) 4)
  refine ⟨(K0 : ℝ), by positivity, L0, ?_⟩
  intro W hden hL hs
  have hL' : max Lquad (max (max xexp x0 + 2) 4) ≤ W.L := by
    simpa [L0] using hL
  have hLquad : Lquad ≤ W.L := (le_max_left _ _).trans hL'
  have hLbase : max xexp x0 + 2 ≤ W.L :=
    (le_max_left _ 4).trans ((le_max_right Lquad _).trans hL')
  have hL4 : 4 ≤ W.L :=
    (le_max_right (max xexp x0 + 2) 4).trans
      ((le_max_right Lquad _).trans hL')
  let H := 2 ^ (W.L - 2)
  have hHpos : 0 < H := by positivity
  have hxexpH : max xexp 2 ≤ H := by
    have hself := self_le_two_pow (W.L - 2)
    dsimp [H]
    omega
  have hx0H : x0 ≤ H := by
    have hself := self_le_two_pow (W.L - 2)
    dsimp [H]
    omega
  have hX : W.X = 4 * H := by
    unfold WindowSystem.X dyadicScale
    dsimp [H]
    calc
      2 ^ W.L = 2 ^ ((W.L - 2) + 2) := by
        congr 1
        omega
      _ = 2 ^ (W.L - 2) * 2 ^ 2 := pow_add _ _ _
      _ = 4 * 2 ^ (W.L - 2) := by ring
  obtain ⟨nv, hnvS, hnvLower, hnvUpper⟩ :=
    exists_support_Ioc_of_large Q xexp hexp W.rational hden H hxexpH
  have hnvRange : nv ∈ Set.range W.enumeration.a :=
    (Set.ext_iff.mp W.enumeration.range_eq nv).mpr hnvS
  rcases hnvRange with ⟨v, hv⟩
  have hvLower : H < W.enumeration.a v := by simpa [hv] using hnvLower
  have hvUpper : W.enumeration.a v ≤ 2 * H := by simpa [hv] using hnvUpper
  have hxexp2H : max xexp 2 ≤ 2 * H := hxexpH.trans (by omega)
  obtain ⟨nu, hnuS, hnuLower, hnuUpper⟩ :=
    exists_support_Ioc_of_large Q xexp hexp W.rational hden (2 * H) hxexp2H
  have hnuRange : nu ∈ Set.range W.enumeration.a :=
    (Set.ext_iff.mp W.enumeration.range_eq nu).mpr hnuS
  rcases hnuRange with ⟨u, hu⟩
  have huLower : 2 * H < W.enumeration.a u := by simpa [hu] using hnuLower
  have huUpper : W.enumeration.a u ≤ 4 * H := by
    calc
      W.enumeration.a u = nu := hu
      _ ≤ 2 * (2 * H) := hnuUpper
      _ = 4 * H := by ring
  let i := firstIndexAbove W.enumeration W.X
  let j := firstIndexAbove W.enumeration (2 * W.X)
  have hi : W.X < W.enumeration.a i := firstIndexAbove_spec _ _
  have hj : 2 * W.X < W.enumeration.a j := firstIndexAbove_spec _ _
  have hv_i : v < i := by
    by_contra hnot
    have hiv : i ≤ v := Nat.le_of_not_gt hnot
    have hmono := W.enumeration.strictMono.monotone hiv
    omega
  have hu_i : u < i := by
    by_contra hnot
    have hiu : i ≤ u := Nat.le_of_not_gt hnot
    have hmono := W.enumeration.strictMono.monotone hiu
    omega
  have hiPos : 0 < i := by omega
  have hprevX : W.enumeration.a (i - 1) ≤ W.X :=
    firstIndexAbove_minimal W.enumeration W.X (i - 1) (by omega)
  have huPrev : u ≤ i - 1 := by omega
  have hprevLower : 2 * H < W.enumeration.a (i - 1) :=
    huLower.trans_le (W.enumeration.strictMono.monotone huPrev)
  have hprevGap0 := hgap W.rational hden (W.enumeration.a (i - 1))
    (by omega) (supportGap W.enumeration (i - 1))
    (supportGap_isSupportGap W.enumeration (i - 1))
  have hlogPrev : Nat.log 2 (W.enumeration.a (i - 1)) ≤ W.L := by
    calc
      Nat.log 2 (W.enumeration.a (i - 1)) ≤ Nat.log 2 W.X :=
        Nat.log_mono_right hprevX
      _ = W.L := by
        simp [WindowSystem.X, dyadicScale, Nat.log_pow]
  let G := W.L + 1 + Cgap
  have hprevGap : supportGap W.enumeration (i - 1) ≤ G := by
    dsimp [G]
    omega
  have hprevStep : W.enumeration.a (i - 1) < W.enumeration.a i := by
    apply W.enumeration.strictMono
    omega
  have haiSplit :
      W.enumeration.a i = W.enumeration.a (i - 1) +
        supportGap W.enumeration (i - 1) := by
    rw [supportGap, show i - 1 + 1 = i by omega,
      Nat.add_sub_of_le hprevStep.le]
  have haiUpper : W.enumeration.a i ≤ W.X + G := by omega
  have hGapIJ : ∀ t ∈ Finset.Ico i j, supportGap W.enumeration t ≤ G := by
    intro t ht
    have hit : i ≤ t := (Finset.mem_Ico.mp ht).1
    have htj : t < j := (Finset.mem_Ico.mp ht).2
    have hatLower : W.X < W.enumeration.a t :=
      hi.trans_le (W.enumeration.strictMono.monotone hit)
    have hatUpper : W.enumeration.a t ≤ 2 * W.X :=
      firstIndexAbove_minimal W.enumeration (2 * W.X) t htj
    have hgb := hgap W.rational hden (W.enumeration.a t) (by omega)
      (supportGap W.enumeration t) (supportGap_isSupportGap W.enumeration t)
    have hlog : Nat.log 2 (W.enumeration.a t) ≤ W.L + 1 := by
      calc
        Nat.log 2 (W.enumeration.a t) ≤ Nat.log 2 (2 * W.X) :=
          Nat.log_mono_right hatUpper
        _ = W.L + 1 := by
          rw [show 2 * W.X = 2 ^ (W.L + 1) by
            simp [WindowSystem.X, dyadicScale, pow_succ, mul_comm],
            Nat.log_pow (by omega)]
    dsimp [G]
    omega
  have hCceil : C ≤ (cN : ℝ) := by
    simpa [cN] using (Nat.le_ceil C)
  have hsNat : W.s ≤ cN * W.L := by
    have hsReal : (W.s : ℝ) ≤ ((cN * W.L : ℕ) : ℝ) := by
      calc
        (W.s : ℝ) ≤ C * (W.L : ℝ) := hs
        _ ≤ (cN : ℝ) * (W.L : ℝ) :=
          mul_le_mul_of_nonneg_right hCceil (Nat.cast_nonneg _)
        _ = ((cN * W.L : ℕ) : ℝ) := by norm_num
    exact_mod_cast hsReal
  have hmLe : W.m ≤ (cN + 1) * W.L := by
    dsimp [WindowSystem.m]
    nlinarith
  have hGLe : G ≤ (Cgap + 2) * W.L := by
    have hL1 : 1 ≤ W.L := by omega
    have hCmul : Cgap ≤ Cgap * W.L := by
      calc
        Cgap = Cgap * 1 := by simp
        _ ≤ Cgap * W.L := Nat.mul_le_mul_left Cgap hL1
    calc
      G = W.L + 1 + Cgap := rfl
      _ ≤ W.L + W.L + Cgap * W.L := by omega
      _ = (Cgap + 2) * W.L := by ring
  have hmG : W.m * G ≤ K0 * W.L ^ 2 := by
    calc
      W.m * G ≤ ((cN + 1) * W.L) * ((Cgap + 2) * W.L) :=
        Nat.mul_le_mul hmLe hGLe
      _ = K0 * W.L ^ 2 := by simp [K0]; ring
  have hpoly : 4 * K0 * W.L ^ 2 < W.X := by
    simpa [WindowSystem.X, dyadicScale] using hquad W.L hLquad
  have hfourSmall : 4 * (K0 * W.L ^ 2) < 4 * H := by
    calc
      4 * (K0 * W.L ^ 2) = 4 * K0 * W.L ^ 2 := by ring
      _ < W.X := hpoly
      _ = 4 * H := hX
  have hKsmall : K0 * W.L ^ 2 < H := by omega
  have hmGsmall : W.m * G < H := hmG.trans_lt hKsmall
  have hsGsmall : W.s * G < H := by
    have hsm : W.s ≤ W.m := by simp [WindowSystem.m]
    exact (Nat.mul_le_mul_right G hsm).trans_lt hmGsmall
  have hGapVI : ∀ t ∈ Finset.Ico v i, supportGap W.enumeration t ≤ G := by
    intro t ht
    have hvt : v ≤ t := (Finset.mem_Ico.mp ht).1
    have hti : t < i := (Finset.mem_Ico.mp ht).2
    have hatLower : H < W.enumeration.a t :=
      hvLower.trans_le (W.enumeration.strictMono.monotone hvt)
    have hatUpper : W.enumeration.a t ≤ W.X :=
      firstIndexAbove_minimal W.enumeration W.X t hti
    have hgb := hgap W.rational hden (W.enumeration.a t) (by omega)
      (supportGap W.enumeration t) (supportGap_isSupportGap W.enumeration t)
    have hlog : Nat.log 2 (W.enumeration.a t) ≤ W.L := by
      calc
        Nat.log 2 (W.enumeration.a t) ≤ Nat.log 2 W.X :=
          Nat.log_mono_right hatUpper
        _ = W.L := by
          simp [WindowSystem.X, dyadicScale, Nat.log_pow]
    dsimp [G]
    omega
  have hi_s : W.s < i := by
    by_contra hnot
    have his : i ≤ W.s := Nat.le_of_not_gt hnot
    have hsum := sum_supportGap_le_mul W.enumeration v i G hv_i.le hGapVI
    have hmul : (i - v) * G ≤ W.s * G :=
      Nat.mul_le_mul_right G (by omega)
    have hdifflower : 2 * H < W.enumeration.a i - W.enumeration.a v := by
      rw [hX] at hi
      omega
    omega
  have hGsmall : G < H := by
    have hGm : G ≤ W.m * G := by
      have hmpos : 1 ≤ W.m := by simp [WindowSystem.m]
      simpa using Nat.mul_le_mul_right G hmpos
    exact hGm.trans_lt hmGsmall
  have hai2X : W.enumeration.a i ≤ 2 * W.X := by
    rw [hX] at haiUpper ⊢
    omega
  have hij : i < j := by
    by_contra hnot
    have hji : j ≤ i := Nat.le_of_not_gt hnot
    have hmono := W.enumeration.strictMono.monotone hji
    omega
  have hwidth : W.s < j - i := by
    by_contra hnot
    have hjiS : j - i ≤ W.s := Nat.le_of_not_gt hnot
    have hsum := sum_supportGap_le_mul W.enumeration i j G hij.le hGapIJ
    have hmul : (j - i) * G ≤ W.s * G :=
      Nat.mul_le_mul_right G hjiS
    have hdifflower : H < W.enumeration.a j - W.enumeration.a i := by
      rw [hX] at hj haiUpper
      omega
    omega
  have hanchors : W.anchors = Finset.Ico i j :=
    anchors_eq_Ico_firstIndices W
  have hcentral := central_gap_multiplicity W i j hanchors hi_s.le hij.le
    (Nat.le_of_lt hwidth)
  have hi_jsub : i ≤ j - W.s := by omega
  have htailGap : ∀ t ∈ Finset.Ico (j - W.s) j,
      supportGap W.enumeration t ≤ G := by
    intro t ht
    apply hGapIJ t
    exact Finset.mem_Ico.mpr
      ⟨hi_jsub.trans (Finset.mem_Ico.mp ht).1,
        (Finset.mem_Ico.mp ht).2⟩
  have htail := sum_supportGap_le_mul W.enumeration (j - W.s) j G
    (by omega) htailGap
  have htailMul : (j - (j - W.s)) * G ≤ W.s * G := by
    apply Nat.mul_le_mul_right
    omega
  have hajSplit : W.enumeration.a j = W.enumeration.a (j - W.s) +
      (W.enumeration.a j - W.enumeration.a (j - W.s)) := by
    exact (Nat.add_sub_of_le
      (W.enumeration.strictMono.monotone (by omega))).symm
  have hacenterSplit : W.enumeration.a (j - W.s) = W.enumeration.a i +
      (W.enumeration.a (j - W.s) - W.enumeration.a i) := by
    exact (Nat.add_sub_of_le
      (W.enumeration.strictMono.monotone hi_jsub)).symm
  have hmG_eq : W.m * G = W.s * G + G := by
    simp [WindowSystem.m]
    ring
  have hcoordinate : W.X ≤
      (W.enumeration.a (j - W.s) - W.enumeration.a i) + W.m * G := by
    omega
  have hmulCoordinate := Nat.mul_le_mul_left W.m hcoordinate
  have hboundary : W.m * (W.m * G) ≤ W.m * (K0 * W.L ^ 2) :=
    Nat.mul_le_mul_left W.m hmG
  have hnat : W.m * W.X ≤
      (∑ k ∈ W.anchors, W.rawWindowSpan k) +
        K0 * W.m * W.L ^ 2 := by
    calc
      W.m * W.X ≤ W.m *
          ((W.enumeration.a (j - W.s) - W.enumeration.a i) + W.m * G) :=
        hmulCoordinate
      _ = W.m * (W.enumeration.a (j - W.s) - W.enumeration.a i) +
          W.m * (W.m * G) := by ring
      _ ≤ (∑ k ∈ W.anchors, W.rawWindowSpan k) +
          W.m * (K0 * W.L ^ 2) := Nat.add_le_add hcentral hboundary
      _ = (∑ k ∈ W.anchors, W.rawWindowSpan k) +
          K0 * W.m * W.L ^ 2 := by ring
  exact_mod_cast hnat

/-- Tonelli identity for the finite anchor set: each threshold weight is
integrated exactly once after summing all spatial anchors. -/
theorem mass_pairSet_eq_threshold_lintegral (W : WindowSystem) :
    mass W.pairSet W.excess =
      ∫⁻ T in W.thresholds,
        ∑ k ∈ W.anchors, ENNReal.ofReal (W.excess (k, T)) ∂volume := by
  unfold mass windowThresholdMeasure
  rw [WindowSystem.pairSet_eq_prod]
  change (∫⁻ e : WindowThreshold,
      ENNReal.ofReal (W.excess e) ∂
        (Measure.count.prod volume).restrict
          (Set.prod (W.anchors : Set ℕ) W.thresholds)) = _
  have hmeasure :
      (Measure.count.prod volume).restrict
          (Set.prod (W.anchors : Set ℕ) W.thresholds) =
        (Measure.count.restrict (W.anchors : Set ℕ)).prod
          (volume.restrict W.thresholds) :=
    (Measure.prod_restrict (μ := Measure.count) (ν := volume)
      (W.anchors : Set ℕ) W.thresholds).symm
  rw [hmeasure]
  rw [MeasureTheory.lintegral_prod_symm]
  · apply lintegral_congr
    intro T
    rw [MeasureTheory.lintegral_finset]
    simp
  · exact (W.measurable_excess.ennreal_ofReal.aemeasurable)

/-- A uniform lower bound for the sum of excesses at every threshold gives
the corresponding lower bound for the certified real mass. -/
theorem integratedExcess_lower_of_threshold_sum (W : WindowSystem) (A : ℝ)
    (hA : 0 ≤ A)
    (hlower : ∀ T ∈ W.thresholds,
      A ≤ ∑ k ∈ W.anchors, W.excess (k, T)) :
    A * thresholdLength W ≤ integratedExcess W := by
  have hlength : 0 ≤ thresholdLength W :=
    mul_nonneg W.structural.cI_pos.le (Nat.cast_nonneg _)
  have hmass : ENNReal.ofReal (A * thresholdLength W) ≤
      mass W.pairSet W.excess := by
    rw [mass_pairSet_eq_threshold_lintegral]
    rw [ENNReal.ofReal_mul hA]
    calc
      ENNReal.ofReal A * ENNReal.ofReal (thresholdLength W) =
          ∫⁻ _T in W.thresholds, ENNReal.ofReal A ∂volume := by
        rw [MeasureTheory.setLIntegral_const]
        congr 1
        simp [WindowSystem.thresholds, thresholdInterval, Real.volume_Icc,
          thresholdLength]
      _ ≤ ∫⁻ T in W.thresholds,
          ∑ k ∈ W.anchors, ENNReal.ofReal (W.excess (k, T)) ∂volume := by
        apply setLIntegral_mono'
          (by simp [WindowSystem.thresholds, thresholdInterval])
        intro T hT
        rw [← ENNReal.ofReal_sum_of_nonneg]
        · exact ENNReal.ofReal_le_ofReal (hlower T hT)
        · intro k hk
          exact le_max_right _ _
  have hleftTop : ENNReal.ofReal (A * thresholdLength W) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hrightTop : mass W.pairSet W.excess ≠ ⊤ :=
    totalMass_finite W
  have hreal := (ENNReal.toReal_le_toReal hleftTop hrightTop).2 hmass
  rw [ENNReal.toReal_ofReal (mul_nonneg hA hlength)] at hreal
  simpa [integratedExcess, totalMassReal, FiniteMass.toReal] using hreal

/-- Anchor indices inject into the support points in the same dyadic block. -/
theorem anchors_card_le_dyadicBlockCount (W : WindowSystem) :
    W.anchors.card ≤ dyadicBlockCount W.rational.S W.X := by
  classical
  let a : ℕ → ℕ := W.enumeration.a
  have ha_strict : StrictMono a := W.enumeration.strictMono
  have ha_range : Set.range a = W.rational.S := W.enumeration.range_eq
  have hsubset : W.anchors.image a ⊆
      (Finset.Ioc W.X (2 * W.X)).filter (fun n => n ∈ W.rational.S) := by
    rw [Finset.image_subset_iff]
    intro k hk
    simp only [WindowSystem.anchors, Finset.mem_filter, Finset.mem_range] at hk
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    refine ⟨⟨by simpa [a] using hk.2.1, by simpa [a] using hk.2.2⟩, ?_⟩
    have hmem : a k ∈ Set.range a := ⟨k, rfl⟩
    rw [ha_range] at hmem
    exact hmem
  calc
    W.anchors.card = (W.anchors.image a).card :=
      (Finset.card_image_of_injective W.anchors ha_strict.injective).symm
    _ ≤ ((Finset.Ioc W.X (2 * W.X)).filter
        (fun n => n ∈ W.rational.S)).card := Finset.card_le_card hsubset
    _ = dyadicBlockCount W.rational.S W.X := by rfl

theorem eventually_real_quadratic_lt_eighth_two_pow (K : ℝ) :
    ∃ L0 : ℕ, ∀ L : ℕ, L0 ≤ L →
      K * (L : ℝ) ^ 2 < (1 / 8 : ℝ) * (2 : ℝ) ^ L := by
  have ht := (tendsto_pow_const_div_const_pow_of_one_lt 2
    (show (1 : ℝ) < 2 by norm_num)).const_mul K
  have ht0 : Tendsto
      (fun L : ℕ => K * ((L : ℝ) ^ 2 / (2 : ℝ) ^ L))
      atTop (nhds 0) := by
    simpa using ht
  have hevent : ∀ᶠ L : ℕ in atTop,
      K * ((L : ℝ) ^ 2 / (2 : ℝ) ^ L) < (1 / 8 : ℝ) :=
    (tendsto_order.1 ht0).2 (1 / 8) (by norm_num)
  obtain ⟨L0, hL0⟩ := eventually_atTop.1 hevent
  refine ⟨L0, ?_⟩
  intro L hL
  have h := hL0 L hL
  have hpow : (0 : ℝ) < (2 : ℝ) ^ L := by positivity
  apply (div_lt_iff₀ hpow).mp
  simpa [mul_div_assoc] using h

/-- Paper label: `prop:pressure` (Section 4). -/
theorem prop_pressure (Q : ℕ) (hQ : 0 < Q)
    (p : StructuralParams) (entropy : EntropyParams)
    (_hstructural : entropy.structural = p) :
    ∃ ε cLower deltaLower : ℝ,
      0 < ε ∧ 0 < cLower ∧ 0 < deltaLower ∧
      ∃ L0 : ℕ, ∀ W : WindowSystem, ∀ δ : ℝ,
        W.rational.eta.den = Q → W.structural = p →
        W.entropy = entropy → W.epsilon = ε →
        W.s = Nat.floor (entropy.kappa * (W.L : ℝ)) →
        L0 ≤ W.L → 0 < δ → δ ≤ deltaLower →
        (dyadicBlockCount W.rational.S W.X : ℝ) ≤ δ * W.X →
        cLower * W.m * W.X * thresholdLength W ≤ integratedExcess W := by
  let C := entropy.kappa + 1
  have hC : 0 < C := by dsimp [C]; linarith [entropy.kappa_pos]
  obtain ⟨K, hK, Lwindow, hwindow⟩ := lem_window_count Q hQ C hC
  obtain ⟨Lasym, hasym⟩ := eventually_real_quadratic_lt_eighth_two_pow K
  let D : ℝ := 3 + p.cI + p.C0
  have hD : 0 < D := by
    dsimp [D]
    linarith [p.cI_pos]
  let deltaLower := entropy.kappa / (8 * D)
  have hdeltaLower : 0 < deltaLower := by
    dsimp [deltaLower]
    exact div_pos entropy.kappa_pos (mul_pos (by norm_num) hD)
  let L0 := max Lwindow (max Lasym 1)
  refine ⟨1, 1 / 2, deltaLower, by norm_num, by norm_num,
    hdeltaLower, L0, ?_⟩
  intro W δ hden hWp hWentropy hWepsilon hsEq hL hδ hδupper hsparse
  have hL' : max Lwindow (max Lasym 1) ≤ W.L := by
    simpa [L0] using hL
  have hLwindow : Lwindow ≤ W.L := (le_max_left _ _).trans hL'
  have hLasym : Lasym ≤ W.L :=
    (le_max_left _ 1).trans ((le_max_right Lwindow _).trans hL')
  have hL1 : 1 ≤ W.L :=
    (le_max_right Lasym 1).trans ((le_max_right Lwindow _).trans hL')
  have hkLnonneg : 0 ≤ entropy.kappa * (W.L : ℝ) :=
    mul_nonneg entropy.kappa_pos.le (Nat.cast_nonneg _)
  have hsC : (W.s : ℝ) ≤ C * (W.L : ℝ) := by
    rw [hsEq]
    calc
      ((Nat.floor (entropy.kappa * (W.L : ℝ)) : ℕ) : ℝ) ≤
          entropy.kappa * (W.L : ℝ) := Nat.floor_le hkLnonneg
      _ ≤ C * (W.L : ℝ) := by
        dsimp [C]
        calc
          entropy.kappa * (W.L : ℝ) ≤
              entropy.kappa * W.L + 1 * W.L :=
            le_add_of_nonneg_right (by positivity)
          _ = (entropy.kappa + 1) * W.L := by ring
  have hcount := hwindow W hden hLwindow hsC
  have hboundary : K * (W.L : ℝ) ^ 2 ≤ (1 / 8 : ℝ) * W.X := by
    have h := (hasym W.L hLasym).le
    simpa [WindowSystem.X, dyadicScale] using h
  have hmnonneg : (0 : ℝ) ≤ W.m := by positivity
  have hspanLower :
      (7 / 8 : ℝ) * W.m * W.X ≤
        (∑ k ∈ W.anchors, W.rawWindowSpan k : ℕ) := by
    have hboundaryMul :
        K * (W.s + 1 : ℕ) * (W.L : ℝ) ^ 2 ≤
          (1 / 8 : ℝ) * W.m * W.X := by
      have := mul_le_mul_of_nonneg_left hboundary hmnonneg
      calc
        K * (W.s + 1 : ℕ) * (W.L : ℝ) ^ 2 =
            (W.m : ℝ) * (K * (W.L : ℝ) ^ 2) := by
          simp [WindowSystem.m]
          ring
        _ ≤ (W.m : ℝ) * ((1 / 8 : ℝ) * W.X) := this
        _ = (1 / 8 : ℝ) * W.m * W.X := by ring
    have hmXnonneg : (0 : ℝ) ≤ W.m * W.X := by positivity
    simp only [Nat.cast_add, Nat.cast_one] at hboundaryMul
    push_cast at hcount
    calc
      (7 / 8 : ℝ) * W.m * W.X =
          (W.m : ℝ) * W.X - (1 / 8 : ℝ) * W.m * W.X := by ring
      _ ≤ (W.m : ℝ) * W.X -
          K * ((W.s : ℝ) + 1) * (W.L : ℝ) ^ 2 :=
        sub_le_sub_left hboundaryMul _
      _ ≤ ∑ k ∈ W.anchors, (W.rawWindowSpan k : ℝ) := by
        exact (sub_le_iff_le_add).2 hcount
      _ = ((∑ k ∈ W.anchors, W.rawWindowSpan k : ℕ) : ℝ) := by
        push_cast
        rfl
  have hfloorLower : entropy.kappa * (W.L : ℝ) < (W.m : ℝ) := by
    have h := Nat.lt_floor_add_one (entropy.kappa * (W.L : ℝ))
    rw [← hsEq] at h
    simpa [WindowSystem.m] using h
  have hanchor : (W.anchors.card : ℝ) ≤ δ * W.X := by
    calc
      (W.anchors.card : ℝ) ≤ dyadicBlockCount W.rational.S W.X := by
        exact_mod_cast anchors_card_le_dyadicBlockCount W
      _ ≤ δ * W.X := hsparse
  have hdeltaD : δ * D ≤ entropy.kappa / 8 := by
    calc
      δ * D ≤ deltaLower * D :=
        mul_le_mul_of_nonneg_right hδupper hD.le
      _ = entropy.kappa / 8 := by
        dsimp [deltaLower]
        field_simp
  have hpointwise : ∀ T ∈ W.thresholds,
      (1 / 2 : ℝ) * W.m * W.X ≤
        ∑ k ∈ W.anchors, W.excess (k, T) := by
    intro T hT
    have hTupper :
        T ≤ 2 * (W.L : ℝ) + p.C0 + p.cI * W.L := by
      exact hT.2.trans_eq (by rw [hWp])
    have hC0mul : (p.C0 : ℝ) ≤ p.C0 * (W.L : ℝ) := by
      have hnat : p.C0 ≤ p.C0 * W.L := by
        calc
          p.C0 = p.C0 * 1 := by simp
          _ ≤ p.C0 * W.L := Nat.mul_le_mul_left p.C0 hL1
      exact_mod_cast hnat
    have hTU : T + W.epsilon * W.L ≤ D * W.L := by
      rw [hWepsilon]
      dsimp [D]
      nlinarith
    have hTnonneg : 0 ≤ T := by
      have hTlower := hT.1
      have hbase : (0 : ℝ) ≤
          2 * W.L + W.structural.C0 := by positivity
      exact hbase.trans hTlower
    have hTU_nonneg : 0 ≤ T + W.epsilon * W.L := by
      rw [hWepsilon]
      positivity
    have hDWLnonneg : 0 ≤ D * (W.L : ℝ) :=
      mul_nonneg hD.le (Nat.cast_nonneg _)
    have hloss : (W.anchors.card : ℝ) *
        (T + W.epsilon * W.L) ≤ (1 / 8 : ℝ) * W.m * W.X := by
      calc
        (W.anchors.card : ℝ) * (T + W.epsilon * W.L) ≤
            (δ * W.X) * (D * W.L) :=
          mul_le_mul hanchor hTU hTU_nonneg
            (mul_nonneg hδ.le (Nat.cast_nonneg _))
        _ = (δ * D) * W.X * W.L := by ring
        _ ≤ (entropy.kappa / 8) * W.X * W.L := by
          gcongr
        _ ≤ (1 / 8 : ℝ) * W.m * W.X := by
          have hfloorLe : entropy.kappa * (W.L : ℝ) ≤ W.m :=
            hfloorLower.le
          calc
            (entropy.kappa / 8) * W.X * W.L =
                ((1 / 8 : ℝ) * W.X) * (entropy.kappa * W.L) := by ring
            _ ≤ ((1 / 8 : ℝ) * W.X) * W.m :=
              mul_le_mul_of_nonneg_left hfloorLe (by positivity)
            _ = (1 / 8 : ℝ) * W.m * W.X := by ring
    have hterm : ∀ k ∈ W.anchors,
        ((W.rawWindowSpan k : ℕ) : ℝ) - T - W.epsilon * W.L ≤
          W.excess (k, T) := by
      intro k hk
      unfold WindowSystem.excess
      exact le_max_left _ _
    have hsumTerm := Finset.sum_le_sum hterm
    have hsumExpand :
        (∑ k ∈ W.anchors,
            (((W.rawWindowSpan k : ℕ) : ℝ) - T - W.epsilon * W.L)) =
          ((∑ k ∈ W.anchors, W.rawWindowSpan k : ℕ) : ℝ) -
            (W.anchors.card : ℝ) * (T + W.epsilon * W.L) := by
      push_cast
      simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      ring
    rw [hsumExpand] at hsumTerm
    linarith
  have hA : 0 ≤ (1 / 2 : ℝ) * W.m * W.X := by positivity
  have hmass := integratedExcess_lower_of_threshold_sum W
    ((1 / 2 : ℝ) * W.m * W.X) hA hpointwise
  simpa using hmass

theorem boundedPairs_subset_pairSet (W : WindowSystem) (Z0 : ℕ) :
    W.boundedPairs Z0 ⊆ W.pairSet := by
  exact inter_subset_left

/-- Certified real mass of the bounded-excess parent family. -/
def boundedPairsMass (W : WindowSystem) (Z0 : ℕ) : ℝ :=
  finiteWindowMass W (W.boundedPairs Z0) (boundedPairs_subset_pairSet W Z0)

/-- Exact measure of the full window–threshold rectangle. -/
theorem windowThresholdMeasure_pairSet (W : WindowSystem) :
    windowThresholdMeasure W.pairSet =
      (W.anchors.card : ℝ≥0∞) * ENNReal.ofReal (thresholdLength W) := by
  rw [WindowSystem.pairSet_eq_prod, windowThresholdMeasure]
  have hprod :
      (Measure.count.prod volume)
          (Set.prod (W.anchors : Set ℕ) W.thresholds) =
        Measure.count (W.anchors : Set ℕ) * volume W.thresholds :=
    MeasureTheory.Measure.prod_prod _ _
  rw [hprod]
  simp only [Measure.count_apply_finset, WindowSystem.thresholds,
    thresholdInterval, Real.volume_Icc, thresholdLength]
  congr 2
  ring

/-- Paper label: `prop:moderate` (Section 4). -/
theorem prop_moderate (W : WindowSystem) (Z0 : ℕ) (cstar : ℝ)
    (hcstar : 0 ≤ cstar)
    (hsparse : (dyadicBlockCount W.rational.S W.X : ℝ) ≤ cstar * W.X) :
    boundedPairsMass W Z0 ≤
      Z0 * cstar * W.m * W.X * thresholdLength W := by
  have _hcstar : 0 ≤ cstar := hcstar
  have hc : (0 : ℝ) ≤ ((W.m * Z0 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hlength : 0 ≤ thresholdLength W := by
    exact mul_nonneg W.structural.cI_pos.le (Nat.cast_nonneg _)
  have hmass :
      mass (W.boundedPairs Z0) W.excess ≤
        ENNReal.ofReal (((W.m * Z0 : ℕ) : ℝ)) *
          windowThresholdMeasure W.pairSet := by
    unfold mass
    calc
      (∫⁻ e in W.boundedPairs Z0, ENNReal.ofReal (W.excess e)
          ∂windowThresholdMeasure) ≤
          ∫⁻ _e in W.boundedPairs Z0,
            ENNReal.ofReal (((W.m * Z0 : ℕ) : ℝ))
              ∂windowThresholdMeasure := by
        apply setLIntegral_mono measurable_const
        intro e he
        apply ENNReal.ofReal_le_ofReal
        exact_mod_cast he.2
      _ ≤ ∫⁻ _e in W.pairSet,
            ENNReal.ofReal (((W.m * Z0 : ℕ) : ℝ))
              ∂windowThresholdMeasure :=
        lintegral_mono_set (boundedPairs_subset_pairSet W Z0)
      _ = ENNReal.ofReal (((W.m * Z0 : ℕ) : ℝ)) *
            windowThresholdMeasure W.pairSet :=
        setLIntegral_const _ _
  have hleft_top : mass (W.boundedPairs Z0) W.excess ≠ ⊤ :=
    (finiteMassOfSubset W (W.boundedPairs Z0)
      (boundedPairs_subset_pairSet W Z0)).ne_top
  have hright_top :
      ENNReal.ofReal (((W.m * Z0 : ℕ) : ℝ)) *
          windowThresholdMeasure W.pairSet ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (windowThresholdMeasure_pairSet_ne_top W)
  have hto := (ENNReal.toReal_le_toReal hleft_top hright_top).2 hmass
  have hreal : boundedPairsMass W Z0 ≤
      (((W.m * Z0 : ℕ) : ℝ)) * W.anchors.card * thresholdLength W := by
    change (mass (W.boundedPairs Z0) W.excess).toReal ≤ _
    rw [windowThresholdMeasure_pairSet] at hto
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc,
      ENNReal.toReal_natCast, ENNReal.toReal_ofReal hlength, mul_assoc] using hto
  have hanchors : (W.anchors.card : ℝ) ≤ cstar * W.X := by
    calc
      (W.anchors.card : ℝ) ≤ dyadicBlockCount W.rational.S W.X := by
        exact_mod_cast anchors_card_le_dyadicBlockCount W
      _ ≤ cstar * W.X := hsparse
  calc
    boundedPairsMass W Z0 ≤
        (((W.m * Z0 : ℕ) : ℝ)) * W.anchors.card * thresholdLength W := hreal
    _ ≤ (((W.m * Z0 : ℕ) : ℝ)) *
        (cstar * W.X) * thresholdLength W := by
      gcongr
    _ = Z0 * cstar * W.m * W.X * thresholdLength W := by
      push_cast
      ring

end Erdos260

/-! Source module: Erdos260/AffineLocking.lean -/

/-!
# Affine locking and the interior/exterior dichotomy

This module corresponds to Section 5 and incorporates the indexing conventions
from Appendices B and C.
-/

noncomputable section

open Filter MeasureTheory Set Topology Asymptotics
open scoped BigOperators ENNReal

namespace Erdos260

/-- An integer affine line of carry states. -/
structure AffineLine where
  A : ℤ
  C : ℤ
  H : ℤ
  K : ℤ
  H_pos : 0 < H

namespace AffineLine

/-- Normalized slope `K/(QH)`. -/
def slope (Q : ℕ) (line : AffineLine) : ℚ :=
  (line.K : ℚ) / ((Q : ℚ) * line.H)

/-- Shared-gap transformation retaining the original horizontal parameter. -/
def transform (Q g : ℕ) (line : AffineLine) : AffineLine where
  A := line.A + g
  C := (2 : ℤ) ^ g * line.C - (Q : ℤ) * (line.A + g)
  H := line.H
  K := (2 : ℤ) ^ g * line.K - (Q : ℤ) * line.H
  H_pos := line.H_pos

def transformWord (Q : ℕ) : AffineLine → GapWord → AffineLine
  | line, [] => line
  | line, g :: gs => transformWord Q (line.transform Q g) gs

/-- Integer intercept numerator `HC-KA`. -/
def interceptNumerator (line : AffineLine) : ℤ :=
  line.H * line.C - line.K * line.A

/-- Membership of an integer point in the original integer parameterization. -/
def Contains (line : AffineLine) (x r : ℤ) : Prop :=
  ∃ t : ℤ, x = line.A + line.H * t ∧ r = line.C + line.K * t

/-- Horizontal step after primitive reduction. -/
def primitiveHorizontalStep (line : AffineLine) : ℕ :=
  line.H.natAbs / Int.gcd line.H line.K

end AffineLine

/-- Canonical geometric data for an affine lattice line.  Unlike
`AffineLine`, this object has no chosen parameter origin: the primitive
direction and the integer intercept determine the locus. -/
structure GeometricLine where
  H : ℕ
  K : ℤ
  intercept : ℤ
  H_pos : 0 < H
  primitive : Nat.gcd H K.natAbs = 1

namespace GeometricLine

def Contains (line : GeometricLine) (x r : ℤ) : Prop :=
  (line.H : ℤ) * r - line.K * x = line.intercept

def slope (Q : ℕ) (line : GeometricLine) : ℚ :=
  (line.K : ℚ) / ((Q : ℚ) * line.H)

end GeometricLine

/-- A parameterized line and a canonical line have the same integer locus. -/
def RepresentsGeometricLine (line : AffineLine) (geometric : GeometricLine) : Prop :=
  ∀ x r : ℤ, line.Contains x r ↔ geometric.Contains x r

namespace AffineLine

/-- Common divisor removed from the raw integer direction. -/
def directionGCD (line : AffineLine) : ℕ :=
  Int.gcd line.H line.K

theorem directionGCD_pos (line : AffineLine) : 0 < line.directionGCD := by
  exact Int.gcd_pos_of_ne_zero_left line.K (ne_of_gt line.H_pos)

/-- Positive horizontal coordinate of the primitive direction, before
converting it to a natural number. -/
def primitiveHorizontalInt (line : AffineLine) : ℤ :=
  line.H / (line.directionGCD : ℤ)

/-- Vertical coordinate of the primitive direction. -/
def primitiveVertical (line : AffineLine) : ℤ :=
  line.K / (line.directionGCD : ℤ)

theorem primitiveHorizontalInt_pos (line : AffineLine) :
    0 < line.primitiveHorizontalInt := by
  have hd : (0 : ℤ) < line.directionGCD := by
    exact_mod_cast line.directionGCD_pos
  have hfactor :
      line.primitiveHorizontalInt * (line.directionGCD : ℤ) = line.H := by
    exact Int.ediv_mul_cancel (Int.gcd_dvd_left line.H line.K)
  nlinarith [line.H_pos]

/-- Change only the integer parameter origin, retaining the same raw direction. -/
def shiftOrigin (line : AffineLine) (t : ℤ) : AffineLine where
  A := line.A + line.H * t
  C := line.C + line.K * t
  H := line.H
  K := line.K
  H_pos := line.H_pos

/-- Canonical primitive direction and intercept of the geometric line
underlying a raw integer parameterization. -/
def canonicalGeometricLine (line : AffineLine) : GeometricLine where
  H := line.primitiveHorizontalInt.natAbs
  K := line.primitiveVertical
  intercept := line.interceptNumerator / (line.directionGCD : ℤ)
  H_pos := Int.natAbs_pos.mpr (ne_of_gt line.primitiveHorizontalInt_pos)
  primitive := by
    change Int.gcd
      (line.H / (line.directionGCD : ℤ))
      (line.K / (line.directionGCD : ℤ)) = 1
    exact Int.gcd_div_gcd_div_gcd line.directionGCD_pos

theorem canonicalGeometricLine_H_cast (line : AffineLine) :
    (line.canonicalGeometricLine.H : ℤ) = line.primitiveHorizontalInt := by
  simp [canonicalGeometricLine, abs_of_pos line.primitiveHorizontalInt_pos]

/-- Translating the parameter origin along the raw direction leaves the
canonical geometric line unchanged. -/
theorem canonicalGeometricLine_shiftOrigin (line : AffineLine) (t : ℤ) :
    (line.shiftOrigin t).canonicalGeometricLine = line.canonicalGeometricLine := by
  unfold canonicalGeometricLine shiftOrigin primitiveHorizontalInt primitiveVertical
    directionGCD interceptNumerator
  congr 1
  ring_nf

/-- Every point in the raw integer parameterization lies on its canonical
geometric line.  The converse requires a primitive raw direction and is false
for arbitrary `AffineLine`s. -/
theorem contains_canonicalGeometricLine (line : AffineLine) (x r : ℤ)
    (h : line.Contains x r) : line.canonicalGeometricLine.Contains x r := by
  rcases h with ⟨t, rfl, rfl⟩
  rw [GeometricLine.Contains, canonicalGeometricLine_H_cast]
  have hHfactor :
      line.primitiveHorizontalInt * (line.directionGCD : ℤ) = line.H := by
    exact Int.ediv_mul_cancel (Int.gcd_dvd_left line.H line.K)
  have hKfactor :
      line.primitiveVertical * (line.directionGCD : ℤ) = line.K := by
    exact Int.ediv_mul_cancel (Int.gcd_dvd_right line.H line.K)
  have hdvdIntercept :
      (line.directionGCD : ℤ) ∣ line.interceptNumerator := by
    refine ⟨line.primitiveHorizontalInt * line.C -
      line.primitiveVertical * line.A, ?_⟩
    simp only [interceptNumerator]
    rw [← hHfactor, ← hKfactor]
    ring
  have hdne : (line.directionGCD : ℤ) ≠ 0 := by
    exact_mod_cast (ne_of_gt line.directionGCD_pos)
  change
    line.primitiveHorizontalInt * (line.C + line.K * t) -
        line.primitiveVertical * (line.A + line.H * t) =
      line.interceptNumerator / (line.directionGCD : ℤ)
  apply mul_right_cancel₀ hdne
  rw [Int.ediv_mul_cancel hdvdIntercept]
  simp only [← hHfactor, ← hKfactor, interceptNumerator]
  ring

end AffineLine

namespace GeometricLine

/-- Two distinct common integer points determine a canonical primitive
geometric line.  This is the occurrence-line uniqueness principle in a form
that does not depend on any later denominator computation. -/
theorem eq_of_two_common_points
    (u v : GeometricLine) (x₁ r₁ x₂ r₂ : ℤ) (hx : x₁ ≠ x₂)
    (hu₁ : u.Contains x₁ r₁) (hu₂ : u.Contains x₂ r₂)
    (hv₁ : v.Contains x₁ r₁) (hv₂ : v.Contains x₂ r₂) : u = v := by
  have huDet : (u.H : ℤ) * (r₂ - r₁) = u.K * (x₂ - x₁) := by
    rw [GeometricLine.Contains] at hu₁ hu₂
    linarith
  have hvDet : (v.H : ℤ) * (r₂ - r₁) = v.K * (x₂ - x₁) := by
    rw [GeometricLine.Contains] at hv₁ hv₂
    linarith
  have hdx : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hcross : u.K * (v.H : ℤ) = v.K * (u.H : ℤ) := by
    apply mul_right_cancel₀ hdx
    calc
      (u.K * (v.H : ℤ)) * (x₂ - x₁) =
          (v.H : ℤ) * (u.K * (x₂ - x₁)) := by ring
      _ = (v.H : ℤ) * ((u.H : ℤ) * (r₂ - r₁)) := by rw [← huDet]
      _ = (u.H : ℤ) * ((v.H : ℤ) * (r₂ - r₁)) := by ring
      _ = (u.H : ℤ) * (v.K * (x₂ - x₁)) := by rw [hvDet]
      _ = (v.K * (u.H : ℤ)) * (x₂ - x₁) := by ring
  have habs : u.K.natAbs * v.H = v.K.natAbs * u.H := by
    have := congrArg Int.natAbs hcross
    simpa [Int.natAbs_mul] using this
  have huCop : Nat.Coprime u.H u.K.natAbs := u.primitive
  have hvCop : Nat.Coprime v.H v.K.natAbs := v.primitive
  have huDvdMul : u.H ∣ u.K.natAbs * v.H := by
    refine ⟨v.K.natAbs, ?_⟩
    calc
      u.K.natAbs * v.H = v.K.natAbs * u.H := habs
      _ = u.H * v.K.natAbs := Nat.mul_comm _ _
  have hvDvdMul : v.H ∣ v.K.natAbs * u.H := by
    refine ⟨u.K.natAbs, ?_⟩
    calc
      v.K.natAbs * u.H = u.K.natAbs * v.H := habs.symm
      _ = v.H * u.K.natAbs := Nat.mul_comm _ _
  have huDvd : u.H ∣ v.H := (huCop.dvd_mul_left).mp huDvdMul
  have hvDvd : v.H ∣ u.H := (hvCop.dvd_mul_left).mp hvDvdMul
  have hH : u.H = v.H := Nat.dvd_antisymm huDvd hvDvd
  have hK : u.K = v.K := by
    rw [hH] at hcross
    exact mul_right_cancel₀ (by exact_mod_cast v.H_pos.ne') hcross
  have hintercept : u.intercept = v.intercept := by
    rw [GeometricLine.Contains] at hu₁ hv₁
    rw [hH, hK] at hu₁
    linarith
  cases u
  cases v
  simp_all

end GeometricLine

/-- The four slope regions used in the paper. -/
inductive SlopeRegion
  | interior
  | boundaryZero
  | boundaryOne
  | exterior
  deriving DecidableEq, Repr

/-- Exact classification of a rational normalized slope. -/
def classifySlope (μ : ℚ) : SlopeRegion :=
  if μ = 0 then .boundaryZero
  else if μ = 1 then .boundaryOne
  else if 0 < μ ∧ μ < 1 then .interior
  else .exterior

/-- Exact iterated shared-gap relation. -/
inductive SharedGapTrajectory (Q : ℕ) : AffineLine → GapWord → AffineLine → Prop
  | nil (line : AffineLine) : SharedGapTrajectory Q line [] line
  | cons (line next finish : AffineLine) (g : ℕ) (gs : GapWord)
      (hnext : next = line.transform Q g)
      (htail : SharedGapTrajectory Q next gs finish) :
      SharedGapTrajectory Q line (g :: gs) finish

/-- Applying two consecutive gap words is the same as applying their
concatenation.  This elementary identity belongs to the common affine layer:
both the interior and exterior branches use it. -/
theorem AffineLine.transformWord_append (Q : ℕ) (line : AffineLine)
    (u v : GapWord) :
    line.transformWord Q (u ++ v) =
      (line.transformWord Q u).transformWord Q v := by
  induction u generalizing line with
  | nil => rfl
  | cons g gs ih =>
      simp only [List.cons_append, AffineLine.transformWord]
      exact ih (line.transform Q g)

/-- Exact normalized-slope recurrence for one shared gap. -/
theorem AffineLine.slope_transform (Q : ℕ) (hQ : 0 < Q)
    (line : AffineLine) (g : ℕ) :
    (line.transform Q g).slope Q =
      (2 : ℚ) ^ g * line.slope Q - 1 := by
  have hQ0 : (Q : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hQ)
  have hH0 : (line.H : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt line.H_pos)
  simp only [AffineLine.slope, AffineLine.transform]
  push_cast
  field_simp [hQ0, hH0]

/-- Real-cast form of the exact one-gap slope recurrence. -/
theorem AffineLine.transform_slope_real (Q g : ℕ) (hQ : 0 < Q)
    (line : AffineLine) :
    ((line.transform Q g).slope Q : ℝ) =
      (2 : ℝ) ^ g * (line.slope Q : ℝ) - 1 := by
  exact_mod_cast AffineLine.slope_transform Q hQ line g

/-- Real slope after a word agrees with the elementary scalar recurrence. -/
theorem AffineLine.transformWord_slope_real (Q : ℕ) (hQ : 0 < Q)
    (line : AffineLine) (word : GapWord) :
    ((line.transformWord Q word).slope Q : ℝ) =
      slopeAfter word (line.slope Q : ℝ) := by
  induction word generalizing line with
  | nil => rfl
  | cons g gs ih =>
      simp only [AffineLine.transformWord, slopeAfter]
      rw [ih, AffineLine.transform_slope_real Q g hQ line]

/-- Iterated shared-gap slope evolution depends only on the initial normalized
slope, not on the chosen parameter origin or a nonprimitive rescaling. -/
theorem AffineLine.transformWord_slope_eq_of_slope_eq (Q : ℕ) (hQ : 0 < Q)
    (left right : AffineLine) (word : GapWord)
    (hslope : left.slope Q = right.slope Q) :
    (left.transformWord Q word).slope Q =
      (right.transformWord Q word).slope Q := by
  induction word generalizing left right with
  | nil => exact hslope
  | cons g gs ih =>
      simp only [AffineLine.transformWord]
      apply ih
      rw [AffineLine.slope_transform Q hQ,
        AffineLine.slope_transform Q hQ, hslope]

/-- The inductive shared-gap trajectory has the deterministic endpoint given
by `transformWord`. -/
theorem sharedGapTrajectory_iff_transformWord (Q : ℕ) (line : AffineLine)
    (gaps : GapWord) (finish : AffineLine) :
    SharedGapTrajectory Q line gaps finish ↔
      finish = line.transformWord Q gaps := by
  constructor
  · intro h
    induction h with
    | nil => rfl
    | cons line next finish g gs hnext htail ih =>
        subst next
        exact ih
  · intro h
    subst finish
    induction gaps generalizing line with
    | nil => exact SharedGapTrajectory.nil line
    | cons g gs ih =>
        exact SharedGapTrajectory.cons line (line.transform Q g)
          ((line.transform Q g).transformWord Q gs) g gs rfl
          (ih (line.transform Q g))

/-- A slope is exterior precisely when it lies strictly outside `[0,1]`. -/
theorem classifySlope_eq_exterior_iff (μ : ℚ) :
    classifySlope μ = .exterior ↔ μ < 0 ∨ 1 < μ := by
  constructor
  · intro h
    by_cases hneg : μ < 0
    · exact Or.inl hneg
    by_cases hgt : 1 < μ
    · exact Or.inr hgt
    exfalso
    have hnonneg : 0 ≤ μ := le_of_not_gt hneg
    have hle : μ ≤ 1 := le_of_not_gt hgt
    by_cases h0 : μ = 0
    · subst μ
      simp [classifySlope] at h
    by_cases h1 : μ = 1
    · subst μ
      simp [classifySlope] at h
    have hi : 0 < μ ∧ μ < 1 :=
      ⟨lt_of_le_of_ne hnonneg (Ne.symm h0), lt_of_le_of_ne hle h1⟩
    simp [classifySlope, h0, h1, hi] at h
  · rintro (hneg | hgt)
    · have h0 : μ ≠ 0 := ne_of_lt hneg
      have h1 : μ ≠ 1 := by linarith
      have hi : ¬ (0 < μ ∧ μ < 1) := by
        rintro ⟨hpos, _⟩
        linarith
      simp [classifySlope, h0, h1, hi]
    · have h0 : μ ≠ 0 := by linarith
      have h1 : μ ≠ 1 := ne_of_gt hgt
      have hi : ¬ (0 < μ ∧ μ < 1) := by
        rintro ⟨_, hlt⟩
        linarith
      simp [classifySlope, h0, h1, hi]

/-- Exterior slope is forward invariant under a positive shared gap. -/
theorem classifySlope_transform_exterior (Q g : ℕ) (hQ : 0 < Q)
    (hg : 1 ≤ g) (line : AffineLine)
    (hline : classifySlope (line.slope Q) = .exterior) :
    classifySlope ((line.transform Q g).slope Q) = .exterior := by
  rw [AffineLine.slope_transform Q hQ]
  rw [classifySlope_eq_exterior_iff] at hline ⊢
  rcases hline with hneg | hgt
  · left
    have hpow : (0 : ℚ) < (2 : ℚ) ^ g := by positivity
    nlinarith [mul_neg_of_pos_of_neg hpow hneg]
  · right
    have hpow : (2 : ℚ) ≤ (2 : ℚ) ^ g := by
      simpa using (pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) hg)
    nlinarith [mul_le_mul_of_nonneg_left hgt.le (by positivity : (0 : ℚ) ≤ 2 ^ g)]

theorem classifySlope_transformWord_exterior (Q : ℕ) (hQ : 0 < Q)
    (line : AffineLine) (word : GapWord) (hword : word.Positive)
    (hline : classifySlope (line.slope Q) = .exterior) :
    classifySlope ((line.transformWord Q word).slope Q) = .exterior := by
  induction word generalizing line with
  | nil => simpa only [AffineLine.transformWord] using hline
  | cons g gs ih =>
      have hg : 1 ≤ g := hword g (by simp)
      have hgs : GapWord.Positive gs := by
        intro x hx
        exact hword x (by simp [hx])
      exact ih (line.transform Q g) hgs
        (classifySlope_transform_exterior Q g hQ hg line hline)

/-- Every state produced by a gap prefix is interior. -/
def IsInteriorTrajectory (Q : ℕ) (line : AffineLine) (gaps : GapWord) : Prop :=
  ∀ r ≤ gaps.length, ∃ state : AffineLine,
    SharedGapTrajectory Q line (gaps.take r) state ∧
      classifySlope (state.slope Q) = .interior

/-- Every state produced by a nonempty gap prefix is exterior. -/
def IsExteriorTrajectory (Q : ℕ) (line : AffineLine) (gaps : GapWord) : Prop :=
  classifySlope (line.slope Q) = .exterior ∧
    ∀ r ≤ gaps.length, ∃ state : AffineLine,
      SharedGapTrajectory Q line (gaps.take r) state ∧
        classifySlope (state.slope Q) = .exterior

theorem isExteriorTrajectory_of_positive (Q : ℕ) (hQ : 0 < Q)
    (line : AffineLine) (word : GapWord) (hword : word.Positive)
    (hline : classifySlope (line.slope Q) = .exterior) :
    IsExteriorTrajectory Q line word := by
  refine ⟨hline, ?_⟩
  intro r hr
  refine ⟨line.transformWord Q (word.take r), ?_, ?_⟩
  · exact (sharedGapTrajectory_iff_transformWord Q line _ _).2 rfl
  · apply classifySlope_transformWord_exterior Q hQ line (word.take r)
    · intro g hg
      exact hword g (List.mem_of_mem_take hg)
    · exact hline

/-- Initial long prefix selected independently of the threshold. -/
def initialLongPrefix (W : WindowSystem) (k : ℕ) : GapWord :=
  (W.rawWindowGapWord k).firstPrefixAbove
    (Nat.floor (W.structural.Caff * W.L))

/-- Anchors that admit at least one large-excess threshold. -/
def highAnchors (W : WindowSystem) (Z0 : ℕ) : Finset ℕ :=
  by
    classical
    exact W.anchors.filter fun k =>
      ∃ T : ℝ, T ∈ W.thresholds ∧ W.m * Z0 < W.excess (k, T)

/-- Set of selected initial prefixes at one scale. -/
def initialPrefixes (W : WindowSystem) (Z0 : ℕ) : Finset GapWord :=
  (highAnchors W Z0).image (initialLongPrefix W)

/-- Anchor multiplicity of a selected prefix; thresholds are not counted. -/
def prefixMultiplicity (W : WindowSystem) (Z0 : ℕ) (p : GapWord) : ℕ :=
  ((highAnchors W Z0).filter fun k => initialLongPrefix W k = p).card

def frequencyCutoff (W : WindowSystem) : ℝ :=
  Real.rpow W.X (1 / 2 + W.structural.rho)

def IsFrequentPrefix (W : WindowSystem) (Z0 : ℕ) (p : GapWord) : Prop :=
  frequencyCutoff W ≤ prefixMultiplicity W Z0 p

def IsRarePrefix (W : WindowSystem) (Z0 : ℕ) (p : GapWord) : Prop :=
  (prefixMultiplicity W Z0 p : ℝ) < frequencyCutoff W

/-- Large-excess pairs with a rare selected prefix. -/
def rareLargePairs (W : WindowSystem) (Z0 : ℕ) : Set WindowThreshold :=
  W.largePairs Z0 ∩ {e | IsRarePrefix W Z0 (initialLongPrefix W e.1)}

theorem rareLargePairs_subset_pairSet (W : WindowSystem) (Z0 : ℕ) :
    rareLargePairs W Z0 ⊆ W.pairSet := by
  intro e he
  exact he.1.1

/-- Certified real mass of the rare-prefix family. -/
def rareLargePairsMass (W : WindowSystem) (Z0 : ℕ) : ℝ :=
  finiteWindowMass W (rareLargePairs W Z0)
    (rareLargePairs_subset_pairSet W Z0)

/-- Anchors occurring in the rare-prefix parent family. -/
def rareAnchors (W : WindowSystem) (Z0 : ℕ) : Finset ℕ :=
  by
    classical
    exact (highAnchors W Z0).filter fun k =>
      IsRarePrefix W Z0 (initialLongPrefix W k)

theorem rareLargePairs_subset_rareRectangle (W : WindowSystem) (Z0 : ℕ) :
    rareLargePairs W Z0 ⊆
      Set.prod (rareAnchors W Z0 : Set ℕ) W.thresholds := by
  classical
  intro e he
  refine ⟨?_, he.1.1.2⟩
  rw [Finset.mem_coe, rareAnchors, Finset.mem_filter]
  constructor
  · rw [highAnchors, Finset.mem_filter]
    refine ⟨he.1.1.1, e.2, he.1.1.2, ?_⟩
    exact he.1.2
  · exact he.2

theorem rareAnchors_card_le (W : WindowSystem) (Z0 : ℕ) :
    ((rareAnchors W Z0).card : ℝ) ≤
      ((initialPrefixes W Z0).card : ℝ) * frequencyCutoff W := by
  classical
  let rarePrefixes : Finset GapWord :=
    (initialPrefixes W Z0).filter fun p => IsRarePrefix W Z0 p
  let fibres : GapWord → Finset ℕ := fun p =>
    (highAnchors W Z0).filter fun k => initialLongPrefix W k = p
  have hsubset : rareAnchors W Z0 ⊆ rarePrefixes.biUnion fibres := by
    intro k hk
    rw [rareAnchors, Finset.mem_filter] at hk
    rw [Finset.mem_biUnion]
    refine ⟨initialLongPrefix W k, ?_, ?_⟩
    · change initialLongPrefix W k ∈
        (initialPrefixes W Z0).filter fun p => IsRarePrefix W Z0 p
      rw [Finset.mem_filter]
      constructor
      · rw [initialPrefixes, Finset.mem_image]
        exact ⟨k, hk.1, rfl⟩
      · exact hk.2
    · change k ∈ (highAnchors W Z0).filter fun j =>
        initialLongPrefix W j = initialLongPrefix W k
      rw [Finset.mem_filter]
      exact ⟨hk.1, rfl⟩
  have hcardNat : (rareAnchors W Z0).card ≤
      ∑ p ∈ rarePrefixes, (fibres p).card :=
    (Finset.card_le_card hsubset).trans Finset.card_biUnion_le
  have hcardReal : ((rareAnchors W Z0).card : ℝ) ≤
      ∑ p ∈ rarePrefixes, ((fibres p).card : ℝ) := by
    exact_mod_cast hcardNat
  calc
    ((rareAnchors W Z0).card : ℝ) ≤
        ∑ p ∈ rarePrefixes, ((fibres p).card : ℝ) := hcardReal
    _ ≤ ∑ _p ∈ rarePrefixes, frequencyCutoff W := by
      apply Finset.sum_le_sum
      intro p hp
      have hp' : p ∈ (initialPrefixes W Z0).filter fun q =>
          IsRarePrefix W Z0 q := hp
      rw [Finset.mem_filter] at hp'
      simpa only [fibres, prefixMultiplicity] using hp'.2.le
    _ = (rarePrefixes.card : ℝ) * frequencyCutoff W := by simp
    _ ≤ ((initialPrefixes W Z0).card : ℝ) * frequencyCutoff W := by
      have hcard : rarePrefixes.card ≤ (initialPrefixes W Z0).card := by
        apply Finset.card_le_card
        intro p hp
        have hp' : p ∈ (initialPrefixes W Z0).filter fun q =>
            IsRarePrefix W Z0 q := hp
        exact (Finset.mem_filter.mp hp').1
      apply mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
      unfold frequencyCutoff
      exact Real.rpow_nonneg (by exact_mod_cast Nat.zero_le W.X) _

private theorem windowThresholdMeasure_rareRectangle
    (W : WindowSystem) (Z0 : ℕ) :
    windowThresholdMeasure
        (Set.prod (rareAnchors W Z0 : Set ℕ) W.thresholds) =
      ((rareAnchors W Z0).card : ℝ≥0∞) *
        ENNReal.ofReal (thresholdLength W) := by
  rw [windowThresholdMeasure]
  have hprod :
      (Measure.count.prod volume)
          (Set.prod (rareAnchors W Z0 : Set ℕ) W.thresholds) =
        Measure.count (rareAnchors W Z0 : Set ℕ) * volume W.thresholds :=
    MeasureTheory.Measure.prod_prod _ _
  rw [hprod]
  simp only [Measure.count_apply_finset, WindowSystem.thresholds,
    thresholdInterval, Real.volume_Icc, thresholdLength]
  congr 2
  ring

private theorem rareLargePairsMass_le (W : WindowSystem) (Z0 : ℕ) (M : ℝ)
    (hM : 0 ≤ M)
    (hbound : ∀ e ∈ rareLargePairs W Z0, W.excess e ≤ M) :
    rareLargePairsMass W Z0 ≤
      M * (rareAnchors W Z0).card * thresholdLength W := by
  have hmass : mass (rareLargePairs W Z0) W.excess ≤
      ENNReal.ofReal M * windowThresholdMeasure
        (Set.prod (rareAnchors W Z0 : Set ℕ) W.thresholds) := by
    unfold mass
    calc
      (∫⁻ e in rareLargePairs W Z0, ENNReal.ofReal (W.excess e)
          ∂windowThresholdMeasure) ≤
          ∫⁻ _e in rareLargePairs W Z0, ENNReal.ofReal M
            ∂windowThresholdMeasure := by
        apply setLIntegral_mono measurable_const
        intro e he
        exact ENNReal.ofReal_le_ofReal (hbound e he)
      _ ≤ ∫⁻ _e in Set.prod (rareAnchors W Z0 : Set ℕ) W.thresholds,
          ENNReal.ofReal M ∂windowThresholdMeasure :=
        lintegral_mono_set (rareLargePairs_subset_rareRectangle W Z0)
      _ = ENNReal.ofReal M * windowThresholdMeasure
          (Set.prod (rareAnchors W Z0 : Set ℕ) W.thresholds) :=
        setLIntegral_const _ _
  have hleftTop : mass (rareLargePairs W Z0) W.excess ≠ ⊤ :=
    (finiteMassOfSubset W (rareLargePairs W Z0)
      (rareLargePairs_subset_pairSet W Z0)).ne_top
  have hlength : 0 ≤ thresholdLength W :=
    mul_nonneg W.structural.cI_pos.le (Nat.cast_nonneg _)
  have hrightTop :
      ENNReal.ofReal M * windowThresholdMeasure
          (Set.prod (rareAnchors W Z0 : Set ℕ) W.thresholds) ≠ ⊤ := by
    rw [windowThresholdMeasure_rareRectangle]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top)
  have hto := (ENNReal.toReal_le_toReal hleftTop hrightTop).2 hmass
  change (mass (rareLargePairs W Z0) W.excess).toReal ≤ _
  rw [windowThresholdMeasure_rareRectangle] at hto
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hM,
    ENNReal.toReal_natCast, ENNReal.toReal_ofReal hlength, mul_assoc] using hto

/-- All occurrences of one selected prefix lie on this affine line. -/
def IsOccurrenceLine (W : WindowSystem) (Z0 : ℕ) (p : GapWord)
    (line : AffineLine) : Prop :=
  ∀ k, k ∈ highAnchors W Z0 → initialLongPrefix W k = p →
    line.Contains
      (W.enumeration.a (k - W.s) + p.span : ℤ)
      (carryInt W.rational (W.enumeration.a (k - W.s) + p.span))

private theorem highAnchor_offset_le (W : WindowSystem) (Z0 k : ℕ)
    (hk : k ∈ highAnchors W Z0) : W.s ≤ k := by
  classical
  rw [highAnchors, Finset.mem_filter] at hk
  rcases hk.2 with ⟨T, hT, hlarge⟩
  by_contra hnot
  have hspan : W.rawWindowSpan k = 0 := by
    simp [WindowSystem.rawWindowSpan, hnot]
  have hTnonneg : 0 ≤ T := le_trans (by positivity) hT.1
  have hexcess : W.excess (k, T) = 0 := by
    rw [WindowSystem.excess, hspan]
    simp only [Nat.cast_zero, zero_sub]
    rw [max_eq_right]
    have heps : 0 ≤ W.epsilon * W.L :=
      mul_nonneg W.epsilon_nonneg (by positivity)
    linarith
  rw [hexcess] at hlarge
  have hnonneg : (0 : ℝ) ≤ W.m * Z0 := by positivity
  linarith

/-- Once a prefix has at least two occurrences, its geometric occurrence
line is canonical: every raw occurrence-line witness reduces to the same
primitive direction and intercept. -/
theorem occurrenceLines_canonical_eq_of_frequent
    (W : WindowSystem) (Z0 : ℕ) (p : GapWord)
    (hcutoff : 1 < frequencyCutoff W)
    (hfrequent : IsFrequentPrefix W Z0 p)
    (u v : AffineLine)
    (hu : IsOccurrenceLine W Z0 p u)
    (hv : IsOccurrenceLine W Z0 p v) :
    u.canonicalGeometricLine = v.canonicalGeometricLine := by
  classical
  let fibre := (highAnchors W Z0).filter fun k => initialLongPrefix W k = p
  have hcardReal : (1 : ℝ) < (fibre.card : ℝ) :=
    lt_of_lt_of_le hcutoff hfrequent
  have hcard : 1 < fibre.card := by exact_mod_cast hcardReal
  obtain ⟨k₁, hk₁, k₂, hk₂, hkne⟩ := Finset.one_lt_card.mp hcard
  have hk₁' := Finset.mem_filter.mp hk₁
  have hk₂' := Finset.mem_filter.mp hk₂
  let x₁ : ℤ := W.enumeration.a (k₁ - W.s) + p.span
  let x₂ : ℤ := W.enumeration.a (k₂ - W.s) + p.span
  let r₁ : ℤ := carryInt W.rational
    (W.enumeration.a (k₁ - W.s) + p.span)
  let r₂ : ℤ := carryInt W.rational
    (W.enumeration.a (k₂ - W.s) + p.span)
  have hs₁ := highAnchor_offset_le W Z0 k₁ hk₁'.1
  have hs₂ := highAnchor_offset_le W Z0 k₂ hk₂'.1
  have hind : k₁ - W.s ≠ k₂ - W.s := by omega
  have hx : x₁ ≠ x₂ := by
    intro heq
    have henum : W.enumeration.a (k₁ - W.s) =
        W.enumeration.a (k₂ - W.s) := by
      have hsumInt :
          (W.enumeration.a (k₁ - W.s) : ℤ) + p.span =
            W.enumeration.a (k₂ - W.s) + p.span := by
        simpa only [x₁, x₂] using heq
      have hsumNat : W.enumeration.a (k₁ - W.s) + p.span =
          W.enumeration.a (k₂ - W.s) + p.span := by
        exact_mod_cast hsumInt
      exact Nat.add_right_cancel hsumNat
    exact hind (W.enumeration.strictMono.injective henum)
  have hu₁ : u.Contains x₁ r₁ := hu k₁ hk₁'.1 hk₁'.2
  have hu₂ : u.Contains x₂ r₂ := hu k₂ hk₂'.1 hk₂'.2
  have hv₁ : v.Contains x₁ r₁ := hv k₁ hk₁'.1 hk₁'.2
  have hv₂ : v.Contains x₂ r₂ := hv k₂ hk₂'.1 hk₂'.2
  apply GeometricLine.eq_of_two_common_points
    u.canonicalGeometricLine v.canonicalGeometricLine x₁ r₁ x₂ r₂ hx
  · exact u.contains_canonicalGeometricLine x₁ r₁ hu₁
  · exact u.contains_canonicalGeometricLine x₂ r₂ hu₂
  · exact v.contains_canonicalGeometricLine x₁ r₁ hv₁
  · exact v.contains_canonicalGeometricLine x₂ r₂ hv₂

/-- The actual suffix of an anchored gap window after its deterministic
initial long prefix. -/
def actualPostPrefixGaps (W : WindowSystem) (k : ℕ) : GapWord :=
  (W.rawWindowGapWord k).drop (initialLongPrefix W k).length

/-- Genuine anchored gap words consist only of positive support gaps. -/
theorem rawWindowGapWord_positive (W : WindowSystem) (k : ℕ) :
    (W.rawWindowGapWord k).Positive := by
  unfold WindowSystem.rawWindowGapWord
  split
  next hk =>
    change ∀ g, g ∈
      (List.range (W.s + 1)).map
        (fun j => supportGap W.enumeration (k - W.s + j)) → 0 < g
    intro g hg
    obtain ⟨j, _hj, rfl⟩ := List.mem_map.mp hg
    exact (supportGap_isSupportGap W.enumeration (k - W.s + j)).1
  next => simp [GapWord.Positive]

/-- An order-`m` anchored word contains at most `m` gaps. -/
theorem rawWindowGapWord_length_le (W : WindowSystem) (k : ℕ) :
    (W.rawWindowGapWord k).length ≤ W.m := by
  unfold WindowSystem.rawWindowGapWord
  split
  next hk => simp [WindowSystem.window, windowGapWord, WindowSystem.m]
  next => simp [WindowSystem.m]

theorem actualPostPrefixGaps_positive (W : WindowSystem) (k : ℕ) :
    (actualPostPrefixGaps W k).Positive := by
  intro g hg
  exact rawWindowGapWord_positive W k g (List.mem_of_mem_drop hg)

theorem actualPostPrefixGaps_length_le (W : WindowSystem) (k : ℕ) :
    (actualPostPrefixGaps W k).length ≤ W.m := by
  rw [actualPostPrefixGaps, List.length_drop]
  exact (Nat.sub_le _ _).trans (rawWindowGapWord_length_le W k)

theorem initialLongPrefix_append_actualPostPrefixGaps
    (W : WindowSystem) (k : ℕ) :
    initialLongPrefix W k ++ actualPostPrefixGaps W k =
      W.rawWindowGapWord k := by
  let w := W.rawWindowGapWord k
  let p := initialLongPrefix W k
  obtain ⟨tail, htail⟩ := GapWord.firstPrefixAbove_isPrefix
    (W.rawWindowGapWord k) (Nat.floor (W.structural.Caff * W.L))
  have hpw : p ++ tail = w := by
    simpa [p, w, initialLongPrefix] using htail
  change p ++ w.drop p.length = w
  have htake : w.take p.length = p := by
    rw [← hpw]
    simp
  simpa only [htake] using List.take_append_drop p.length w

theorem actualPostPrefixGaps_span (W : WindowSystem) (k : ℕ) :
    (W.rawWindowGapWord k).span =
      (initialLongPrefix W k).span + (actualPostPrefixGaps W k).span := by
  rw [← initialLongPrefix_append_actualPostPrefixGaps W k]
  exact List.sum_append

/-- A shared continuation beginning at the post-prefix occurrence line and
using an actual initial subword of the anchored suffix. -/
def IsActualInitialContinuation (W : WindowSystem) (Z0 : ℕ)
    (e : WindowThreshold) (line : AffineLine) (gaps : GapWord) : Prop :=
  IsOccurrenceLine W Z0 (initialLongPrefix W e.1) line ∧
    gaps.IsPrefix (actualPostPrefixGaps W e.1) ∧
    ∃ finish : AffineLine,
      SharedGapTrajectory W.rational.eta.den line gaps finish

/-- A shared continuation beginning later in the same actual anchored suffix.
The prefix trajectory determines the line at which `gaps` begins. -/
def IsActualContinuationAt (W : WindowSystem) (Z0 : ℕ)
    (e : WindowThreshold) (line : AffineLine) (gaps : GapWord) : Prop :=
  ∃ base finish : AffineLine, ∃ before after : GapWord,
    IsOccurrenceLine W Z0 (initialLongPrefix W e.1) base ∧
      actualPostPrefixGaps W e.1 = before ++ gaps ++ after ∧
      SharedGapTrajectory W.rational.eta.den base before line ∧
      SharedGapTrajectory W.rational.eta.den line gaps finish

/-- A continuation beginning at the first exterior state of the actual
anchored suffix.  Every proper prefix of `before` is still non-exterior, and
the complete prefix reaches the exterior line at which `gaps` starts. -/
def IsActualFirstExteriorContinuation (W : WindowSystem) (Z0 : ℕ)
    (e : WindowThreshold) (line : AffineLine) (gaps : GapWord) : Prop :=
  ∃ base finish : AffineLine, ∃ before after : GapWord,
    IsOccurrenceLine W Z0 (initialLongPrefix W e.1) base ∧
      actualPostPrefixGaps W e.1 = before ++ gaps ++ after ∧
      SharedGapTrajectory W.rational.eta.den base before line ∧
      (∀ r < before.length, ∀ state : AffineLine,
        SharedGapTrajectory W.rational.eta.den base (before.take r) state →
          classifySlope (state.slope W.rational.eta.den) ≠ .exterior) ∧
      classifySlope (line.slope W.rational.eta.den) = .exterior ∧
      SharedGapTrajectory W.rational.eta.den line gaps finish

/-- A pair has a long interior continuation in the genuine slope dynamics. -/
def LongInteriorPair (W : WindowSystem) (Z0 : ℕ) (e : WindowThreshold) : Prop :=
  e ∈ W.largePairs Z0 ∧ IsFrequentPrefix W Z0 (initialLongPrefix W e.1) ∧
    ∃ line : AffineLine, ∃ gaps : GapWord,
      IsActualInitialContinuation W Z0 e line gaps ∧
      IsInteriorTrajectory W.rational.eta.den line gaps ∧
      W.excess e / 8 ≤ gaps.span

/-- Complementary pair with a long exterior continuation. -/
def LongExteriorPair (W : WindowSystem) (Z0 : ℕ) (e : WindowThreshold) : Prop :=
  e ∈ W.largePairs Z0 ∧ IsFrequentPrefix W Z0 (initialLongPrefix W e.1) ∧
    ¬ LongInteriorPair W Z0 e ∧
    ∃ line : AffineLine, ∃ gaps : GapWord,
      IsActualFirstExteriorContinuation W Z0 e line gaps ∧
      IsExteriorTrajectory W.rational.eta.den line gaps ∧
      W.excess e / 4 ≤ gaps.span

def interiorPairs (W : WindowSystem) (Z0 : ℕ) : Set WindowThreshold :=
  {e | LongInteriorPair W Z0 e}

def exteriorPairs (W : WindowSystem) (Z0 : ℕ) : Set WindowThreshold :=
  {e | LongExteriorPair W Z0 e}

/-- Entropy exponent `Δ` used for initial prefixes. -/
def initialPrefixExponent (p : EntropyParams) : ℝ :=
  (p.structural.Caff + 1) *
    binaryEntropy (p.kappa / (p.structural.Caff + 1))

/-! The next few private lemmas provide the finite combinatorial model used
for the initial-prefix count.  A positive word is encoded by its strictly
increasing list of cumulative sums. -/

private def cumulativeSums : GapWord → List ℕ
  | [] => []
  | g :: gs => g :: (cumulativeSums gs).map (g + ·)

@[simp] private theorem cumulativeSums_nil : cumulativeSums [] = [] := rfl

@[simp] private theorem cumulativeSums_cons (g : ℕ) (gs : GapWord) :
    cumulativeSums (g :: gs) = g :: (cumulativeSums gs).map (g + ·) := rfl

private theorem cumulativeSums_length (w : GapWord) :
    (cumulativeSums w).length = w.length := by
  induction w with
  | nil => rfl
  | cons g gs ih => simp [cumulativeSums, ih]

private theorem cumulativeSums_pos {w : GapWord}
    (hpos : ∀ g ∈ w, 0 < g) :
    ∀ x ∈ cumulativeSums w, 0 < x := by
  induction w with
  | nil => simp
  | cons g gs ih =>
      have hg : 0 < g := hpos g (by simp)
      have htail : ∀ x ∈ gs, 0 < x := by
        intro x hx
        exact hpos x (by simp [hx])
      intro x hx
      simp only [cumulativeSums_cons, List.mem_cons, List.mem_map] at hx
      rcases hx with rfl | ⟨y, hy, rfl⟩
      · exact hg
      · exact Nat.add_pos_right g (ih htail y hy)

private theorem cumulativeSums_pairwise {w : GapWord}
    (hpos : ∀ g ∈ w, 0 < g) :
    (cumulativeSums w).Pairwise (· < ·) := by
  induction w with
  | nil => simp
  | cons g gs ih =>
      have hg : 0 < g := hpos g (by simp)
      have htail : ∀ x ∈ gs, 0 < x := by
        intro x hx
        exact hpos x (by simp [hx])
      rw [cumulativeSums_cons, List.pairwise_cons]
      constructor
      · intro x hx
        rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
        have hypos := cumulativeSums_pos htail y hy
        omega
      · rw [List.pairwise_map]
        exact (ih htail).imp (by intro a b hab; omega)

private theorem cumulativeSums_le_span {w : GapWord}
    (hpos : ∀ g ∈ w, 0 < g) :
    ∀ x ∈ cumulativeSums w, x ≤ w.span := by
  induction w with
  | nil => simp
  | cons g gs ih =>
      have htail : ∀ x ∈ gs, 0 < x := by
        intro x hx
        exact hpos x (by simp [hx])
      intro x hx
      simp only [cumulativeSums_cons, List.mem_cons, List.mem_map] at hx
      rcases hx with rfl | ⟨y, hy, rfl⟩
      · simp [GapWord.span]
      · have hy_le : y ≤ gs.sum := by
          simpa only [GapWord.span] using ih htail y hy
        simp only [GapWord.span, List.sum_cons]
        omega

private theorem cumulativeSums_injective : Function.Injective cumulativeSums := by
  intro w
  induction w with
  | nil =>
      intro v hv
      cases v with
      | nil => rfl
      | cons g gs => simp at hv
  | cons g gs ih =>
      intro v hv
      cases v with
      | nil => simp at hv
      | cons h hs =>
          simp only [cumulativeSums_cons] at hv
          have hgh : g = h := (List.cons.inj hv).1
          subst h
          have htail : cumulativeSums gs = cumulativeSums hs := by
            have hm : (cumulativeSums gs).map (g + ·) =
                (cumulativeSums hs).map (g + ·) := by
              exact List.cons.inj hv |>.2
            exact Function.Injective.list_map
              (fun _ _ hab => Nat.add_left_cancel hab) hm
          exact congrArg (g :: ·) (ih htail)

private theorem perm_of_nodup_toFinset_eq {u v : List ℕ}
    (hu : u.Nodup) (hv : v.Nodup) (hset : u.toFinset = v.toFinset) :
    u.Perm v := by
  rw [List.perm_iff_count]
  intro x
  rw [hu.count, hv.count]
  have hmem : x ∈ u ↔ x ∈ v := by
    rw [← List.mem_toFinset, ← List.mem_toFinset, hset]
  simp only [hmem]

private theorem cumulativeEncoding_injective_on_positive :
    Set.InjOn (fun w : GapWord => (cumulativeSums w).toFinset)
      {w | ∀ g ∈ w, 0 < g} := by
  intro u hu v hv henc
  have hpu := cumulativeSums_pairwise hu
  have hpv := cumulativeSums_pairwise hv
  have hperm : (cumulativeSums u).Perm (cumulativeSums v) :=
    perm_of_nodup_toFinset_eq hpu.nodup hpv.nodup henc
  have heq : cumulativeSums u = cumulativeSums v :=
    hperm.eq_of_pairwise' hpu hpv
  exact cumulativeSums_injective heq

theorem positiveGapWords_card_le_compositions (words : Finset GapWord)
    (H rMax : ℕ)
    (hpositive : ∀ p ∈ words, ∀ g ∈ p, 0 < g)
    (hspan : ∀ p ∈ words, p.span ≤ H)
    (hlength : ∀ p ∈ words, p.length ≤ rMax) :
    words.card ≤
      ∑ r ∈ Finset.Icc 0 rMax,
        H.choose r := by
  classical
  let target : Finset (Finset ℕ) :=
    (Finset.Icc 0 rMax).biUnion fun r =>
      Finset.powersetCard r (Finset.Icc 1 H)
  have hmaps : Set.MapsTo
      (fun w : GapWord => (cumulativeSums w).toFinset)
      (words : Set GapWord) (target : Set (Finset ℕ)) := by
    intro p hp
    have hcard : (cumulativeSums p).toFinset.card = p.length := by
      rw [List.toFinset_card_of_nodup (cumulativeSums_pairwise
        (hpositive p hp)).nodup, cumulativeSums_length]
    have hsubset : (cumulativeSums p).toFinset ⊆ Finset.Icc 1 H := by
      intro x hx
      rw [List.mem_toFinset] at hx
      rw [Finset.mem_Icc]
      constructor
      · exact cumulativeSums_pos (hpositive p hp) x hx
      · exact (cumulativeSums_le_span (hpositive p hp) x hx).trans (hspan p hp)
    simp only [Finset.mem_coe, target, Finset.mem_biUnion]
    refine ⟨p.length, ?_, ?_⟩
    · exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, hlength p hp⟩
    · exact Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩
  calc
    words.card ≤ target.card :=
      Finset.card_le_card_of_injOn _ hmaps
        (cumulativeEncoding_injective_on_positive.mono (by
          intro p hp
          exact hpositive p hp))
    _ ≤ ∑ r ∈ Finset.Icc 0 rMax,
          (Finset.powersetCard r (Finset.Icc 1 H)).card :=
      Finset.card_biUnion_le
    _ = ∑ r ∈ Finset.Icc 0 rMax, H.choose r := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.card_powersetCard, Nat.card_Icc]
      congr 1

/-- Positive gap words of bounded span and bounded length form a finite set.
This is the set-level companion to `positiveGapWords_card_le_compositions`. -/
theorem positiveGapWords_bounded_finite (H rMax : ℕ) :
    {w : GapWord |
      (∀ g ∈ w, 0 < g) ∧ w.span ≤ H ∧ w.length ≤ rMax}.Finite := by
  classical
  let E : Set GapWord :=
    {w : GapWord |
      (∀ g ∈ w, 0 < g) ∧ w.span ≤ H ∧ w.length ≤ rMax}
  let target : Finset (Finset ℕ) :=
    (Finset.Icc 0 rMax).biUnion fun r =>
      Finset.powersetCard r (Finset.Icc 1 H)
  let encode : GapWord → Finset ℕ :=
    fun w => (cumulativeSums w).toFinset
  have hmaps : Set.MapsTo encode E (target : Set (Finset ℕ)) := by
    intro w hw
    have hcard : (encode w).card = w.length := by
      dsimp [encode]
      rw [List.toFinset_card_of_nodup (cumulativeSums_pairwise hw.1).nodup,
        cumulativeSums_length]
    have hsubset : encode w ⊆ Finset.Icc 1 H := by
      intro x hx
      dsimp [encode] at hx
      rw [List.mem_toFinset] at hx
      exact Finset.mem_Icc.mpr ⟨cumulativeSums_pos hw.1 x hx,
        (cumulativeSums_le_span hw.1 x hx).trans hw.2.1⟩
    simp only [target, Finset.mem_coe, Finset.mem_biUnion]
    exact ⟨w.length, Finset.mem_Icc.mpr ⟨Nat.zero_le _, hw.2.2⟩,
      Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩⟩
  have himage : encode '' E ⊆ (target : Set (Finset ℕ)) := by
    rintro y ⟨w, hw, rfl⟩
    exact hmaps hw
  have hfiniteImage : (encode '' E).Finite := target.finite_toSet.subset himage
  have hinj : Set.InjOn encode E := by
    exact cumulativeEncoding_injective_on_positive.mono (by
      intro w hw
      exact hw.1)
  simpa only [E] using Set.Finite.of_finite_image hfiniteImage hinj

theorem sum_choose_Icc_zero_eq_shift (H m : ℕ) :
    (∑ r ∈ Finset.Icc 0 m, H.choose r) =
      ∑ q ∈ Finset.Icc 1 (m + 1), H.choose (q - 1) := by
  apply Finset.sum_bij (fun r _ => r + 1)
  · intro r hr
    simp only [Finset.mem_Icc] at hr ⊢
    omega
  · intro r₁ hr₁ r₂ hr₂ h
    omega
  · intro q hq
    simp only [Finset.mem_Icc] at hq
    refine ⟨q - 1, ?_, ?_⟩
    · simp only [Finset.mem_Icc]
      omega
    · omega
  · intro r hr
    simp

theorem tendsto_natFloor_affine_div (a c : ℝ)
    (ha : 0 < a) (hc : 0 ≤ c) :
    Tendsto
      (fun L : ℕ =>
        (Nat.floor (a * (L : ℝ) + c) : ℝ) / (L : ℝ))
      atTop (𝓝 a) := by
  have hlo : Tendsto
      (fun L : ℕ => a + (c - 1) / (L : ℝ)) atTop (𝓝 a) := by
    simpa using tendsto_const_nhds.add
      (tendsto_const_nhds.div_atTop
        (tendsto_natCast_atTop_atTop : Tendsto (fun L : ℕ => (L : ℝ)) atTop atTop))
  have hhi : Tendsto
      (fun L : ℕ => a + c / (L : ℝ)) atTop (𝓝 a) := by
    simpa using tendsto_const_nhds.add
      (tendsto_const_nhds.div_atTop
        (tendsto_natCast_atTop_atTop : Tendsto (fun L : ℕ => (L : ℝ)) atTop atTop))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with L hL
    have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
    have hxlt := Nat.lt_floor_add_one (a * (L : ℝ) + c)
    have hnum : a * (L : ℝ) + c - 1 <
        (Nat.floor (a * (L : ℝ) + c) : ℝ) := by
      linarith
    have hdiv := (div_lt_div_iff_of_pos_right hLpos).2 hnum
    have heq : a + (c - 1) / (L : ℝ) =
        (a * (L : ℝ) + c - 1) / (L : ℝ) := by
      field_simp
      ring
    rw [heq]
    exact hdiv.le
  · filter_upwards [eventually_ge_atTop 1] with L hL
    have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
    have hxnonneg : 0 ≤ a * (L : ℝ) + c := by positivity
    have hnum := Nat.floor_le hxnonneg
    have hdiv := (div_le_div_iff_of_pos_right hLpos).2 hnum
    have heq : a + c / (L : ℝ) =
        (a * (L : ℝ) + c) / (L : ℝ) := by
      field_simp
    rw [heq]
    exact hdiv

theorem binaryEntropy_continuous : Continuous binaryEntropy := by
  rw [show binaryEntropy = fun x => Real.binEntropy x / Real.log 2 by
    funext x
    rw [binaryEntropy, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    simp only [Real.negMulLog, Real.logb]
    field_simp
    ring]
  exact Real.binEntropy_continuous.div_const _

private def initialCountSpanCap (context : FixedScaleContext) (CQ : ℝ) (L : ℕ) : ℕ :=
  Nat.floor
    ((context.structural.Caff + 1) * (L : ℝ) + CQ)

private def initialCountAlpha (context : FixedScaleContext) (CQ : ℝ) (L : ℕ) : ℝ :=
  ((Nat.floor (context.entropy.kappa * (L : ℝ)) + 2 : ℕ) : ℝ) /
    ((initialCountSpanCap context CQ L + 1 : ℕ) : ℝ)

private theorem binaryEntropy_half : binaryEntropy (1 / 2 : ℝ) = 1 := by
  rw [binaryEntropy]
  have hhalf : (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, hhalf]
  simp only [Real.logb, Real.log_inv]
  have hlog2 : Real.log (2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp
  ring

private theorem initialCountAlpha_tendsto (context : FixedScaleContext)
    (CQ : ℝ) (hCQ : 0 ≤ CQ) :
    Tendsto (initialCountAlpha context CQ) atTop
      (𝓝 (context.entropy.kappa / (context.structural.Caff + 1))) := by
  let A : ℝ := context.structural.Caff + 1
  have hA : 0 < A := by
    dsimp [A]
    linarith [context.structural.Caff_gt]
  have hnatTop : Tendsto (fun L : ℕ => (L : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have honeDiv : Tendsto (fun L : ℕ => (1 : ℝ) / (L : ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hnatTop
  have hcapFloor : Tendsto
      (fun L : ℕ =>
        (initialCountSpanCap context CQ L : ℝ) / (L : ℝ))
      atTop (𝓝 A) := by
    simpa only [initialCountSpanCap, A] using
      tendsto_natFloor_affine_div A CQ hA hCQ
  have hcap : Tendsto
      (fun L : ℕ =>
        ((initialCountSpanCap context CQ L + 1 : ℕ) : ℝ) / (L : ℝ))
      atTop (𝓝 A) := by
    convert hcapFloor.add honeDiv using 1 <;> simp [Nat.cast_add, add_div]
  have hkFloor : Tendsto
      (fun L : ℕ =>
        (Nat.floor (context.entropy.kappa * (L : ℝ)) : ℝ) / (L : ℝ))
      atTop (𝓝 context.entropy.kappa) := by
    simpa using tendsto_natFloor_affine_div context.entropy.kappa 0
      context.entropy.kappa_pos (le_refl 0)
  have htwoDiv : Tendsto (fun L : ℕ => (2 : ℝ) / (L : ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hnatTop
  have hnum : Tendsto
      (fun L : ℕ =>
        ((Nat.floor (context.entropy.kappa * (L : ℝ)) + 2 : ℕ) : ℝ) /
          (L : ℝ))
      atTop (𝓝 context.entropy.kappa) := by
    convert hkFloor.add htwoDiv using 1 <;> simp [Nat.cast_add, add_div]
  have hquot := hnum.div hcap (ne_of_gt hA)
  apply hquot.congr'
  filter_upwards [eventually_ge_atTop 1] with L hL
  have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
  dsimp [initialCountAlpha]
  field_simp

private def initialCountError (context : FixedScaleContext) (CQ : ℝ) (L : ℕ) : ℝ :=
  if L = 0 then 0 else
    |(((initialCountSpanCap context CQ L + 1 : ℕ) : ℝ) / (L : ℝ)) *
          binaryEntropy (initialCountAlpha context CQ L) -
        initialPrefixExponent context.entropy| +
      2 * Real.log (((initialCountSpanCap context CQ L + 1 : ℕ) : ℝ)) /
        ((L : ℝ) * Real.log 2)

private theorem initialCountError_tendsto_zero (context : FixedScaleContext)
    (CQ : ℝ) (hCQ : 0 ≤ CQ) :
    Tendsto (initialCountError context CQ) atTop (𝓝 0) := by
  let A : ℝ := context.structural.Caff + 1
  have hA : 0 < A := by
    dsimp [A]
    linarith [context.structural.Caff_gt]
  have hA0 : A ≠ 0 := ne_of_gt hA
  have hnatTop : Tendsto (fun L : ℕ => (L : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have honeDiv : Tendsto (fun L : ℕ => (1 : ℝ) / (L : ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hnatTop
  have hcapFloor : Tendsto
      (fun L : ℕ =>
        (initialCountSpanCap context CQ L : ℝ) / (L : ℝ))
      atTop (𝓝 A) := by
    simpa only [initialCountSpanCap, A] using
      tendsto_natFloor_affine_div A CQ hA hCQ
  have hcap : Tendsto
      (fun L : ℕ =>
        ((initialCountSpanCap context CQ L + 1 : ℕ) : ℝ) / (L : ℝ))
      atTop (𝓝 A) := by
    convert hcapFloor.add honeDiv using 1 <;> simp [Nat.cast_add, add_div]
  have hkFloor : Tendsto
      (fun L : ℕ =>
        (Nat.floor (context.entropy.kappa * (L : ℝ)) : ℝ) / (L : ℝ))
      atTop (𝓝 context.entropy.kappa) := by
    simpa using tendsto_natFloor_affine_div context.entropy.kappa 0
      context.entropy.kappa_pos (le_refl 0)
  have htwoDiv : Tendsto (fun L : ℕ => (2 : ℝ) / (L : ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hnatTop
  have hnum : Tendsto
      (fun L : ℕ =>
        ((Nat.floor (context.entropy.kappa * (L : ℝ)) + 2 : ℕ) : ℝ) /
          (L : ℝ))
      atTop (𝓝 context.entropy.kappa) := by
    convert hkFloor.add htwoDiv using 1 <;> simp [Nat.cast_add, add_div]
  have halpha : Tendsto (initialCountAlpha context CQ) atTop
      (𝓝 (context.entropy.kappa / A)) := by
    have hquot := hnum.div hcap hA0
    apply hquot.congr'
    filter_upwards [eventually_ge_atTop 1] with L hL
    have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
    dsimp [initialCountAlpha]
    field_simp
  have hentropy : Tendsto
      (fun L => binaryEntropy (initialCountAlpha context CQ L))
      atTop (𝓝 (binaryEntropy (context.entropy.kappa / A))) :=
    binaryEntropy_continuous.continuousAt.tendsto.comp halpha
  have hmain : Tendsto
      (fun L : ℕ =>
        ((initialCountSpanCap context CQ L + 1 : ℕ) : ℝ) / (L : ℝ) *
          binaryEntropy (initialCountAlpha context CQ L))
      atTop (𝓝 (initialPrefixExponent context.entropy)) := by
    have := hcap.mul hentropy
    rw [initialPrefixExponent, context.entropy_structural]
    simpa only [A] using this
  have habs : Tendsto
      (fun L : ℕ =>
        |(((initialCountSpanCap context CQ L + 1 : ℕ) : ℝ) / (L : ℝ)) *
            binaryEntropy (initialCountAlpha context CQ L) -
          initialPrefixExponent context.entropy|)
      atTop (𝓝 0) := by
    have hconst : Tendsto
        (fun _ : ℕ => initialPrefixExponent context.entropy)
        atTop (𝓝 (initialPrefixExponent context.entropy)) := tendsto_const_nhds
    simpa using (hmain.sub hconst).abs
  have hxTop : Tendsto
      (fun L : ℕ => A * (L : ℝ) + CQ) atTop atTop := by
    have hmul : Tendsto (fun L : ℕ => A * (L : ℝ)) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hA hnatTop
    exact Filter.tendsto_atTop_mono
      (fun L => le_add_of_nonneg_right hCQ) hmul
  have hcapNatTop : Tendsto
      (fun L : ℕ => initialCountSpanCap context CQ L + 1) atTop atTop := by
    have hfloor : Tendsto
        (fun L : ℕ => initialCountSpanCap context CQ L) atTop atTop := by
      simpa only [initialCountSpanCap, A, Function.comp_def] using
        tendsto_nat_floor_atTop.comp hxTop
    exact Filter.tendsto_atTop_mono (fun L => Nat.le_succ _) hfloor
  have hcapRealTop : Tendsto
      (fun L : ℕ => ((initialCountSpanCap context CQ L + 1 : ℕ) : ℝ))
      atTop atTop := hnatTop.comp hcapNatTop
  have hlogOverCap : Tendsto
      (fun L : ℕ =>
        Real.log (((initialCountSpanCap context CQ L + 1 : ℕ) : ℝ)) /
          (((initialCountSpanCap context CQ L + 1 : ℕ) : ℝ)))
      atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hcapRealTop
  have hlogOverL : Tendsto
      (fun L : ℕ =>
        Real.log (((initialCountSpanCap context CQ L + 1 : ℕ) : ℝ)) /
          (L : ℝ))
      atTop (𝓝 0) := by
    have hprod := hlogOverCap.mul hcap
    have hprod' : Tendsto
        (fun L : ℕ =>
          Real.log (((initialCountSpanCap context CQ L + 1 : ℕ) : ℝ)) /
              (((initialCountSpanCap context CQ L + 1 : ℕ) : ℝ)) *
            (((initialCountSpanCap context CQ L + 1 : ℕ) : ℝ) / (L : ℝ)))
        atTop (𝓝 0) := by simpa using hprod
    apply hprod'.congr'
    filter_upwards [eventually_ge_atTop 1] with L hL
    have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
    have hcapPos : (0 : ℝ) <
        ((initialCountSpanCap context CQ L + 1 : ℕ) : ℝ) := by positivity
    field_simp [hL0, ne_of_gt hcapPos]
  have hpoly : Tendsto
      (fun L : ℕ =>
        2 * Real.log (((initialCountSpanCap context CQ L + 1 : ℕ) : ℝ)) /
          ((L : ℝ) * Real.log 2))
      atTop (𝓝 0) := by
    have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
    have hsimple : Tendsto
        (fun L : ℕ =>
          (2 * (Real.log (((initialCountSpanCap context CQ L + 1 : ℕ) : ℝ)) /
            (L : ℝ))) / Real.log 2)
        atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul hlogOverL).div_const (Real.log 2)
    apply hsimple.congr'
    filter_upwards [eventually_ge_atTop 1] with L hL
    have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
    field_simp [hL0, hlog2]
  have hsum : Tendsto
      (fun L : ℕ =>
        |(((initialCountSpanCap context CQ L + 1 : ℕ) : ℝ) / (L : ℝ)) *
            binaryEntropy (initialCountAlpha context CQ L) -
          initialPrefixExponent context.entropy| +
        2 * Real.log (((initialCountSpanCap context CQ L + 1 : ℕ) : ℝ)) /
          ((L : ℝ) * Real.log 2))
      atTop (𝓝 0) := by simpa using habs.add hpoly
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop 1] with L hL
  simp only [initialCountError, Nat.ne_of_gt hL, if_false]

private theorem initialPrefixes_card_le_compositions (W : WindowSystem)
    (Z0 H : ℕ)
    (hspan : ∀ p ∈ initialPrefixes W Z0, p.span ≤ H) :
    (initialPrefixes W Z0).card ≤
      ∑ r ∈ Finset.Icc 0 W.m,
        H.choose r := by
  have hpositive : ∀ p ∈ initialPrefixes W Z0, ∀ g ∈ p, 0 < g := by
    intro p hp g hg
    rw [initialPrefixes, Finset.mem_image] at hp
    rcases hp with ⟨k, hk, rfl⟩
    have hpref := GapWord.firstPrefixAbove_isPrefix
      (W.rawWindowGapWord k)
      (Nat.floor (W.structural.Caff * W.L))
    have hgraw : g ∈ W.rawWindowGapWord k := hpref.subset hg
    unfold WindowSystem.rawWindowGapWord at hgraw
    split at hgraw
    next hsk =>
      simp only [WindowSystem.window, windowGapWord, List.mem_map,
        List.mem_range] at hgraw
      rcases hgraw with ⟨j, hj, rfl⟩
      exact (supportGap_isSupportGap W.enumeration _).1
    next hsk => simp at hgraw
  have hlength : ∀ p ∈ initialPrefixes W Z0, p.length ≤ W.m := by
    intro p hp
    rw [initialPrefixes, Finset.mem_image] at hp
    rcases hp with ⟨k, hk, rfl⟩
    have hpref := GapWord.firstPrefixAbove_isPrefix
      (W.rawWindowGapWord k)
      (Nat.floor (W.structural.Caff * W.L))
    calc
      (initialLongPrefix W k).length ≤ (W.rawWindowGapWord k).length :=
        List.IsPrefix.length_le hpref
      _ ≤ W.m := by
        unfold WindowSystem.rawWindowGapWord
        split
        · simp [WindowSystem.window, windowGapWord, WindowSystem.m]
        · exact Nat.zero_le _
  exact positiveGapWords_card_le_compositions _ H W.m hpositive hspan hlength

/-- Every gap occurring in an anchored order-`m` word is eventually bounded
by `L + Cgap + 1`.  The finitely many support points below the uniform
starting point `x0` are absorbed into the family-dependent lower bound on
`L`; all later points use the denominator-uniform gap theorem. -/
theorem eventually_rawWindowGap_le (context : FixedScaleContext)
    (gap : GapParams context.Q) (F : ScaleFamily)
    (hF : F.MatchesContext context) :
    ∀ᶠ L : ℕ in atTop, ∀ k : ℕ, k ∈ (F.system L).anchors →
      ∀ g ∈ (F.system L).rawWindowGapWord k,
        g ≤ L + gap.Cgap + 1 := by
  let earlyBound :=
    (Finset.range gap.x0).sup fun i => supportGap F.enumeration i
  filter_upwards [eventually_ge_atTop earlyBound] with L hL
  intro k hk g hg
  have hkUpper : (F.system L).enumeration.a k ≤ 2 * (F.system L).X :=
    (Finset.mem_filter.mp hk).2.2
  unfold WindowSystem.rawWindowGapWord at hg
  split at hg
  next hsk =>
    simp only [WindowSystem.window, windowGapWord, List.mem_map,
      List.mem_range] at hg
    obtain ⟨j, hj, rfl⟩ := hg
    let i := k - (F.system L).s + j
    have hi_le_k : i ≤ k := by
      dsimp [i]
      omega
    have hiIndex : i < F.enumeration.a i :=
      supportEnumeration_index_lt F.enumeration i
    have henum_i : (F.system L).enumeration.a i = F.enumeration.a i :=
      F.enumeration_eq L i
    have henum_k : (F.system L).enumeration.a k = F.enumeration.a k :=
      F.enumeration_eq L k
    have hsupportGap :
        supportGap (F.system L).enumeration i = supportGap F.enumeration i := by
      simp only [supportGap, F.enumeration_eq]
    rw [hsupportGap]
    by_cases hearly : F.enumeration.a i < gap.x0
    · have hiRange : i ∈ Finset.range gap.x0 := by
        simp only [Finset.mem_range]
        exact hiIndex.trans hearly
      have hgapEarly : supportGap F.enumeration i ≤ earlyBound := by
        exact Finset.le_sup (f := fun t => supportGap F.enumeration t) hiRange
      omega
    · have hx0 : gap.x0 ≤ F.enumeration.a i := Nat.le_of_not_gt hearly
      have hden : F.rational.eta.den = context.Q := hF.1
      have hgap := gap.bound F.rational hden (F.enumeration.a i) hx0
        (supportGap F.enumeration i)
        (supportGap_isSupportGap F.enumeration i)
      have hai_le_hak : F.enumeration.a i ≤ F.enumeration.a k :=
        F.enumeration.strictMono.monotone hi_le_k
      have hai_le_scale : F.enumeration.a i ≤ 2 * dyadicScale L := by
        calc
          F.enumeration.a i ≤ F.enumeration.a k := hai_le_hak
          _ = (F.system L).enumeration.a k := henum_k.symm
          _ ≤ 2 * (F.system L).X := hkUpper
          _ = 2 * dyadicScale L := by
            rw [WindowSystem.X, F.level_eq]
      have hlog : Nat.log 2 (F.enumeration.a i) ≤ L + 1 := by
        calc
          Nat.log 2 (F.enumeration.a i) ≤
              Nat.log 2 (2 * dyadicScale L) := Nat.log_mono_right hai_le_scale
          _ = L + 1 := by
            rw [dyadicScale, show 2 * 2 ^ L = 2 ^ (L + 1) by
              rw [pow_succ]
              omega]
            exact Nat.log_pow Nat.one_lt_two (L + 1)
      omega
  next hsk => simp at hg

private theorem rawWindowGapWord_span (W : WindowSystem) (k : ℕ) :
    (W.rawWindowGapWord k).span = W.rawWindowSpan k := by
  unfold WindowSystem.rawWindowGapWord WindowSystem.rawWindowSpan
  split <;> rfl

/-- Paper label: `lem:firstdeep-exists` (Section 5).  The overshoot constant
is selected from the denominator-level context before the cutoff, rational
numerator, or support family. -/
theorem lem_firstdeep_exists (context : FixedScaleContext) :
    ∃ CQ : ℝ, 0 ≤ CQ ∧ ∀ Z0 : ℕ,
      Nat.ceil
          (2 * context.structural.Caff / context.entropy.kappa) ≤ Z0 →
      ∀ F : ScaleFamily, F.MatchesContext context →
        ∀ᶠ L : ℕ in atTop,
          ∀ e : WindowThreshold, e ∈ (F.system L).largePairs Z0 →
            let p := initialLongPrefix (F.system L) e.1
            (F.system L).structural.Caff * (F.system L).L < p.span ∧
              (p.span : ℝ) ≤
                ((F.system L).structural.Caff + 1) *
                    (F.system L).L + CQ ∧
              (F.system L).excess e / 2 ≤
                (F.system L).rawWindowSpan e.1 - p.span := by
  obtain ⟨gap⟩ := gapParams_exists context.Q context.Q_pos
  let CQ : ℝ := gap.Cgap + 1
  refine ⟨CQ, by positivity, ?_⟩
  intro Z0 hZ0 F hF
  filter_upwards [eventually_rawWindowGap_le context gap F hF,
    eventually_ge_atTop (gap.Cgap + 2)] with L hgap hL
  intro e he
  dsimp only
  let p := initialLongPrefix (F.system L) e.1
  have hstruct : (F.system L).structural = context.structural :=
    (F.structural_eq L).trans hF.2.1
  have hpEq : p =
      ((F.system L).rawWindowGapWord e.1).firstPrefixAbove
        (Nat.floor (context.structural.Caff * (L : ℝ))) := by
    dsimp [p, initialLongPrefix]
    rw [F.level_eq, hstruct]
  have hs : (F.system L).s =
      Nat.floor (context.entropy.kappa * (L : ℝ)) := by
    rw [F.offset_eq, hF.2.2.1]
  have hLposNat : 0 < L := by omega
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hLposNat
  have hCaffPos : 0 < context.structural.Caff :=
    lt_trans (by norm_num) context.structural.Caff_gt
  have hcutReal :
      2 * context.structural.Caff / context.entropy.kappa ≤ (Z0 : ℝ) := by
    exact (Nat.le_ceil _).trans (by exact_mod_cast hZ0)
  have hcoeff :
      2 * context.structural.Caff ≤ context.entropy.kappa * (Z0 : ℝ) := by
    have := (div_le_iff₀ context.entropy.kappa_pos).mp hcutReal
    simpa [mul_comm] using this
  have hZpos : (0 : ℝ) < Z0 := by
    have hquot : 0 <
        2 * context.structural.Caff / context.entropy.kappa :=
      div_pos (mul_pos (by norm_num) hCaffPos) context.entropy.kappa_pos
    exact hquot.trans_le hcutReal
  have hmLower :
      context.entropy.kappa * (L : ℝ) < ((F.system L).m : ℝ) := by
    rw [WindowSystem.m, hs]
    simpa only [Nat.cast_add, Nat.cast_one] using
      (Nat.lt_floor_add_one (context.entropy.kappa * (L : ℝ)))
  have hmassLower :
      2 * context.structural.Caff * (L : ℝ) <
        ((F.system L).m : ℝ) * (Z0 : ℝ) := by
    have h₁ :
        2 * context.structural.Caff * (L : ℝ) ≤
          (context.entropy.kappa * (Z0 : ℝ)) * L := by
      exact mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg L)
    have h₂ :
        (context.entropy.kappa * (Z0 : ℝ)) * L <
          ((F.system L).m : ℝ) * Z0 := by
      have := mul_lt_mul_of_pos_right hmLower hZpos
      nlinarith
    exact h₁.trans_lt h₂
  have hlarge :
      ((F.system L).m : ℝ) * (Z0 : ℝ) < (F.system L).excess e := by
    simpa only [Set.mem_setOf_eq] using he.2
  have hexcessLower :
      2 * context.structural.Caff * (L : ℝ) <
        (F.system L).excess e := hmassLower.trans hlarge
  have hexcessPos : 0 < (F.system L).excess e := by
    have hbase : 0 < 2 * context.structural.Caff * (L : ℝ) := by positivity
    exact hbase.trans hexcessLower
  have hsk : (F.system L).s ≤ e.1 := by
    by_contra hnot
    have hraw : (F.system L).rawWindowSpan e.1 = 0 := by
      simp [WindowSystem.rawWindowSpan, hnot]
    have hupper := (F.system L).excess_le_rawWindowSpan e he.1
    rw [hraw, Nat.cast_zero] at hupper
    linarith
  have hrawUpper := (F.system L).excess_le_rawWindowSpan e he.1
  have hrawReal :
      context.structural.Caff * (L : ℝ) <
        ((F.system L).rawWindowSpan e.1 : ℝ) := by
    have hdouble :
        context.structural.Caff * (L : ℝ) <
          2 * context.structural.Caff * L := by nlinarith
    exact hdouble.trans (hexcessLower.trans_le hrawUpper)
  have hfloorNonneg :
      0 ≤ context.structural.Caff * (L : ℝ) := by positivity
  have hfloorCross :
      Nat.floor (context.structural.Caff * (L : ℝ)) <
        (F.system L).rawWindowSpan e.1 := by
    exact_mod_cast (lt_of_le_of_lt (Nat.floor_le hfloorNonneg) hrawReal)
  have hwordCross :
      Nat.floor (context.structural.Caff * (L : ℝ)) <
        ((F.system L).rawWindowGapWord e.1).span := by
    simpa only [rawWindowGapWord_span] using hfloorCross
  have hpLowerNat :
      Nat.floor (context.structural.Caff * (L : ℝ)) < p.span := by
    rw [hpEq]
    exact GapWord.lt_span_firstPrefixAbove_of_lt_span _ _ hwordCross
  have hpLower :
      context.structural.Caff * (L : ℝ) < (p.span : ℝ) := by
    have hnext :=
      Nat.lt_floor_add_one (context.structural.Caff * (L : ℝ))
    have hsucc : Nat.floor (context.structural.Caff * (L : ℝ)) + 1 ≤ p.span :=
      Nat.succ_le_iff.mpr hpLowerNat
    exact hnext.trans_le (by exact_mod_cast hsucc)
  have hpCap : ∀ g ∈ (F.system L).rawWindowGapWord e.1,
      g ≤ L + gap.Cgap + 1 := hgap e.1 he.1.1
  have hpUpperNat : p.span ≤
      Nat.floor (context.structural.Caff * (L : ℝ)) +
        (L + gap.Cgap + 1) := by
    rw [hpEq]
    exact GapWord.span_firstPrefixAbove_le_add _ _ _ hpCap
  have hpUpper : (p.span : ℝ) ≤
      (context.structural.Caff + 1) * (L : ℝ) + CQ := by
    have hfloor := Nat.floor_le hfloorNonneg
    dsimp [CQ]
    have hpUpperCast : (p.span : ℝ) ≤
        (Nat.floor (context.structural.Caff * (L : ℝ)) : ℝ) +
          ((L : ℝ) + gap.Cgap + 1) := by exact_mod_cast hpUpperNat
    nlinarith
  have hpSpanLe : p.span ≤ (F.system L).rawWindowSpan e.1 := by
    rw [← rawWindowGapWord_span]
    rw [hpEq]
    exact GapWord.span_firstPrefixAbove_le_span _ _
  have hexcessEq :
      (F.system L).excess e =
        ((F.system L).rawWindowSpan e.1 : ℝ) - e.2 -
          (F.system L).epsilon * (F.system L).L := by
    unfold WindowSystem.excess
    apply max_eq_left
    by_contra hnot
    have hle :
        ((F.system L).rawWindowSpan e.1 : ℝ) - e.2 -
            (F.system L).epsilon * (F.system L).L ≤ 0 :=
      le_of_not_ge hnot
    have hpositive := hexcessPos
    rw [WindowSystem.excess, max_eq_right hle] at hpositive
    exact (lt_irrefl 0) hpositive
  have hthreshold :
      2 * ((F.system L).L : ℝ) + (F.system L).structural.C0 ≤ e.2 :=
    he.1.2.1
  have hepsilon :
      0 ≤ (F.system L).epsilon * ((F.system L).L : ℝ) :=
    mul_nonneg (F.system L).epsilon_nonneg (Nat.cast_nonneg _)
  have hCQltL : CQ < (L : ℝ) := by
    dsimp [CQ]
    exact_mod_cast (show gap.Cgap + 1 < L by omega)
  have hremainingReal :
      (F.system L).excess e / 2 ≤
        ((F.system L).rawWindowSpan e.1 : ℝ) - p.span := by
    rw [hexcessEq]
    rw [F.level_eq]
    rw [F.level_eq] at hthreshold hepsilon
    rw [hstruct] at hthreshold
    nlinarith
  have hcastSub :
      (((F.system L).rawWindowSpan e.1 - p.span : ℕ) : ℝ) =
        ((F.system L).rawWindowSpan e.1 : ℝ) - p.span := by
    exact Nat.cast_sub hpSpanLe
  constructor
  · rw [F.level_eq, hstruct]
    exact hpLower
  constructor
  · rw [F.level_eq, hstruct]
    exact hpUpper
  · change (F.system L).excess e / 2 ≤
      ((F.system L).rawWindowSpan e.1 : ℝ) - (p.span : ℝ)
    exact hremainingReal

/-- Paper label: `lem:firstdeep-count` (Section 5).  Once the cutoff is large
enough for the deterministic long prefix to exist, its subexponential error
is fixed uniformly over all compatible supports. -/
theorem lem_firstdeep_count (context : FixedScaleContext) :
    ∀ Z0 : ℕ,
      Nat.ceil
          (2 * context.structural.Caff / context.entropy.kappa) ≤ Z0 →
      ∃ error : ℕ → ℝ, Tendsto error atTop (𝓝 0) ∧
      ∀ F : ScaleFamily, F.MatchesContext context →
        ∀ᶠ L : ℕ in atTop,
          ((initialPrefixes (F.system L) Z0).card : ℝ) ≤
            Real.rpow (F.system L).X
              (initialPrefixExponent (F.system L).entropy + error L) := by
  classical
  obtain ⟨CQ, hCQ, hfirst⟩ := lem_firstdeep_exists context
  intro Z0 hZ0
  refine ⟨initialCountError context CQ,
    initialCountError_tendsto_zero context CQ hCQ, ?_⟩
  have hkappaHalf :
      context.entropy.kappa / (context.structural.Caff + 1) ≤ 1 / 2 := by
    simpa only [context.entropy_structural] using
      context.entropy.kappa_initial_half
  have hkappaHalfStrict :
      context.entropy.kappa / (context.structural.Caff + 1) < 1 / 2 := by
    apply lt_of_le_of_ne hkappaHalf
    intro heq
    have hentropy :
        binaryEntropy
            (context.entropy.kappa / (context.structural.Caff + 1)) = 1 := by
      rw [heq]
      exact binaryEntropy_half
    have hmargin := context.entropy.initial_margin
    rw [context.entropy_structural, hentropy] at hmargin
    nlinarith [context.structural.Caff_gt, context.structural.rho_pos]
  intro F hF
  have halpha := initialCountAlpha_tendsto context CQ hCQ
  have halphaHalf : ∀ᶠ L : ℕ in atTop,
      initialCountAlpha context CQ L ≤ 1 / 2 :=
    ((tendsto_order.1 halpha).2 _ hkappaHalfStrict).mono fun _ h => h.le
  filter_upwards [hfirst Z0 hZ0 F hF, halphaHalf,
    eventually_ge_atTop 1] with L hfirstL halphaL hL
  let H := initialCountSpanCap context CQ L
  have hspan : ∀ p ∈ initialPrefixes (F.system L) Z0, p.span ≤ H := by
    intro p hp
    rw [initialPrefixes, Finset.mem_image] at hp
    rcases hp with ⟨k, hk, rfl⟩
    rw [highAnchors, Finset.mem_filter] at hk
    rcases hk.2 with ⟨T, hT, hlarge⟩
    have he : (k, T) ∈ (F.system L).largePairs Z0 :=
      ⟨⟨hk.1, hT⟩, hlarge⟩
    have hup := (hfirstL (k, T) he).2.1
    have hstruct : (F.system L).structural = context.structural :=
      (F.structural_eq L).trans hF.2.1
    rw [F.level_eq, hstruct] at hup
    exact Nat.le_floor hup
  have hcardNat :=
    initialPrefixes_card_le_compositions (F.system L) Z0 H hspan
  have hm : (F.system L).m =
      Nat.floor (context.entropy.kappa * (L : ℝ)) + 1 := by
    rw [WindowSystem.m, F.offset_eq, hF.2.2.1]
  have hH : 2 ≤ H + 1 := by
    have hreal : (1 : ℝ) ≤
        (context.structural.Caff + 1) * (L : ℝ) + CQ := by
      have hCaff : 2 < context.structural.Caff := context.structural.Caff_gt
      have hLreal : (1 : ℝ) ≤ L := by exact_mod_cast hL
      nlinarith
    have : 1 ≤ H := by
      apply Nat.le_floor
      norm_num only [Nat.cast_one]
      exact hreal
    omega
  have halphaPos : 0 < initialCountAlpha context CQ L := by
    dsimp [initialCountAlpha]
    positivity
  have hr : (((F.system L).m + 1 : ℕ) : ℝ) ≤
      initialCountAlpha context CQ L * ((H + 1 : ℕ) : ℝ) := by
    rw [hm]
    dsimp [initialCountAlpha, H]
    have hden : (0 : ℝ) <
        ((initialCountSpanCap context CQ L + 1 : ℕ) : ℝ) := by positivity
    field_simp
    norm_num
  have hcomposition := lem_composition_entropy (H + 1)
    ((F.system L).m + 1) (initialCountAlpha context CQ L)
    hH halphaPos halphaL hr
  have hcardReal : ((initialPrefixes (F.system L) Z0).card : ℝ) ≤
      (((H + 1 : ℕ) : ℝ) ^ 2) *
        Real.rpow 2
          (((H + 1 : ℕ) : ℝ) *
            binaryEntropy (initialCountAlpha context CQ L)) := by
    calc
      ((initialPrefixes (F.system L) Z0).card : ℝ) ≤
          ((∑ r ∈ Finset.Icc 0 (F.system L).m, H.choose r : ℕ) : ℝ) := by
        exact_mod_cast hcardNat
      _ = ((∑ q ∈ Finset.Icc 1 ((F.system L).m + 1),
          H.choose (q - 1) : ℕ) : ℝ) := by
        rw [sum_choose_Icc_zero_eq_shift]
      _ ≤ (((H + 1 : ℕ) : ℝ) ^ 2) *
          Real.rpow 2
            (((H + 1 : ℕ) : ℝ) *
              binaryEntropy (initialCountAlpha context CQ L)) := by
        simpa only [Nat.add_sub_cancel] using hcomposition
  rw [F.entropy_eq, hF.2.2.1, WindowSystem.X, F.level_eq, dyadicScale]
  apply hcardReal.trans
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hL0 : (L : ℝ) ≠ 0 := ne_of_gt hLpos
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt hlog2pos
  have hHreal : (0 : ℝ) < ((H + 1 : ℕ) : ℝ) := by positivity
  have hbase : (0 : ℝ) < (((2 ^ L : ℕ) : ℝ)) := by positivity
  have hrpowTwo : Real.rpow 2
      (((H + 1 : ℕ) : ℝ) *
        binaryEntropy (initialCountAlpha context CQ L)) =
      Real.exp (Real.log 2 *
        (((H + 1 : ℕ) : ℝ) *
          binaryEntropy (initialCountAlpha context CQ L))) :=
    Real.rpow_def_of_pos (x := 2) (by norm_num) _
  have hrpowBase : Real.rpow (((2 ^ L : ℕ) : ℝ))
      (initialPrefixExponent context.entropy + initialCountError context CQ L) =
      Real.exp (Real.log (((2 ^ L : ℕ) : ℝ)) *
        (initialPrefixExponent context.entropy + initialCountError context CQ L)) :=
    Real.rpow_def_of_pos (x := (((2 ^ L : ℕ) : ℝ))) hbase _
  rw [hrpowTwo, hrpowBase]
  have hpolyExp : (((H + 1 : ℕ) : ℝ) ^ 2) =
      Real.exp (2 * Real.log (((H + 1 : ℕ) : ℝ))) := by
    calc
      (((H + 1 : ℕ) : ℝ) ^ 2) =
          Real.exp (Real.log (((H + 1 : ℕ) : ℝ) ^ 2)) :=
        (Real.exp_log (pow_pos hHreal 2)).symm
      _ = Real.exp (2 * Real.log (((H + 1 : ℕ) : ℝ))) := by
        rw [Real.log_pow]
        norm_num
  rw [hpolyExp, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hcastPow : (((2 ^ L : ℕ) : ℝ)) = (2 : ℝ) ^ L := by norm_num
  rw [hcastPow, Real.log_pow]
  have herror : initialCountError context CQ L =
      |(((H + 1 : ℕ) : ℝ) / (L : ℝ)) *
          binaryEntropy (initialCountAlpha context CQ L) -
        initialPrefixExponent context.entropy| +
        2 * Real.log (((H + 1 : ℕ) : ℝ)) /
          ((L : ℝ) * Real.log 2) := by
    simp only [initialCountError, Nat.ne_of_gt hL, if_false, H,
      initialCountSpanCap]
  rw [herror]
  have habs := le_abs_self
    ((((H + 1 : ℕ) : ℝ) / (L : ℝ)) *
      binaryEntropy (initialCountAlpha context CQ L) -
      initialPrefixExponent context.entropy)
  have hmainLe :
      (((H + 1 : ℕ) : ℝ) / (L : ℝ)) *
          binaryEntropy (initialCountAlpha context CQ L) ≤
        initialPrefixExponent context.entropy +
          |(((H + 1 : ℕ) : ℝ) / (L : ℝ)) *
            binaryEntropy (initialCountAlpha context CQ L) -
            initialPrefixExponent context.entropy| := by
    linarith
  have hscalePos : 0 < (L : ℝ) * Real.log 2 := mul_pos hLpos hlog2pos
  have hscaled := mul_le_mul_of_nonneg_left hmainLe hscalePos.le
  have hpolyCancel :
      ((L : ℝ) * Real.log 2) *
          (2 * Real.log (((H + 1 : ℕ) : ℝ)) /
            ((L : ℝ) * Real.log 2)) =
        2 * Real.log (((H + 1 : ℕ) : ℝ)) := by
    field_simp [hL0, hlog2]
  have hentropyScale :
      Real.log 2 *
          (((H + 1 : ℕ) : ℝ) *
            binaryEntropy (initialCountAlpha context CQ L)) =
        ((L : ℝ) * Real.log 2) *
          ((((H + 1 : ℕ) : ℝ) / (L : ℝ)) *
            binaryEntropy (initialCountAlpha context CQ L)) := by
    field_simp [hL0]
  calc
    2 * Real.log (((H + 1 : ℕ) : ℝ)) +
        Real.log 2 *
          (((H + 1 : ℕ) : ℝ) *
            binaryEntropy (initialCountAlpha context CQ L)) =
      2 * Real.log (((H + 1 : ℕ) : ℝ)) +
        ((L : ℝ) * Real.log 2) *
          ((((H + 1 : ℕ) : ℝ) / (L : ℝ)) *
            binaryEntropy (initialCountAlpha context CQ L)) := by
      rw [hentropyScale]
    _ ≤ 2 * Real.log (((H + 1 : ℕ) : ℝ)) +
        ((L : ℝ) * Real.log 2) *
          (initialPrefixExponent context.entropy +
            |(((H + 1 : ℕ) : ℝ) / (L : ℝ)) *
              binaryEntropy (initialCountAlpha context CQ L) -
              initialPrefixExponent context.entropy|) :=
      by simpa [add_comm] using
        add_le_add_left hscaled (2 * Real.log (((H + 1 : ℕ) : ℝ)))
    _ = ((L : ℝ) * Real.log 2) *
        (initialPrefixExponent context.entropy +
          (|(((H + 1 : ℕ) : ℝ) / (L : ℝ)) *
              binaryEntropy (initialCountAlpha context CQ L) -
              initialPrefixExponent context.entropy| +
            2 * Real.log (((H + 1 : ℕ) : ℝ)) /
              ((L : ℝ) * Real.log 2))) := by
      calc
        2 * Real.log (((H + 1 : ℕ) : ℝ)) +
            ((L : ℝ) * Real.log 2) *
              (initialPrefixExponent context.entropy +
                |(((H + 1 : ℕ) : ℝ) / (L : ℝ)) *
                  binaryEntropy (initialCountAlpha context CQ L) -
                  initialPrefixExponent context.entropy|) =
          ((L : ℝ) * Real.log 2) * initialPrefixExponent context.entropy +
            ((L : ℝ) * Real.log 2) *
              |(((H + 1 : ℕ) : ℝ) / (L : ℝ)) *
                binaryEntropy (initialCountAlpha context CQ L) -
                initialPrefixExponent context.entropy| +
            2 * Real.log (((H + 1 : ℕ) : ℝ)) := by ring
        _ = ((L : ℝ) * Real.log 2) * initialPrefixExponent context.entropy +
            ((L : ℝ) * Real.log 2) *
              |(((H + 1 : ℕ) : ℝ) / (L : ℝ)) *
                binaryEntropy (initialCountAlpha context CQ L) -
                initialPrefixExponent context.entropy| +
            ((L : ℝ) * Real.log 2) *
              (2 * Real.log (((H + 1 : ℕ) : ℝ)) /
                ((L : ℝ) * Real.log 2)) := by rw [hpolyCancel]
        _ = ((L : ℝ) * Real.log 2) *
            (initialPrefixExponent context.entropy +
              (|(((H + 1 : ℕ) : ℝ) / (L : ℝ)) *
                  binaryEntropy (initialCountAlpha context CQ L) -
                  initialPrefixExponent context.entropy| +
                2 * Real.log (((H + 1 : ℕ) : ℝ)) /
                  ((L : ℝ) * Real.log 2))) := by ring

/-- Paper label: `prop:low-firstdeep` (Section 5).  The same cutoff condition
as in `lem_firstdeep_exists` is retained explicitly. -/
theorem prop_low_firstdeep (context : FixedScaleContext) :
    ∀ Z0 : ℕ,
      Nat.ceil
          (2 * context.structural.Caff / context.entropy.kappa) ≤ Z0 →
      ∀ F : ScaleFamily, F.MatchesContext context →
      (fun L => rareLargePairsMass (F.system L) Z0) =o[atTop]
        (fun L =>
          ((F.system L).m : ℝ) * (F.system L).X *
            thresholdLength (F.system L)) := by
  classical
  intro Z0 hZ0 F hF
  obtain ⟨gap⟩ := gapParams_exists context.Q context.Q_pos
  obtain ⟨error, herrorZero, hcount⟩ :=
    lem_firstdeep_count context Z0 hZ0
  let Δ : ℝ := initialPrefixExponent context.entropy
  let δ : ℝ := 1 / 2 - context.structural.rho - Δ
  let d : ℝ := δ / 2
  have hΔ : Δ < 1 / 2 - 3 * context.structural.rho := by
    dsimp [Δ, initialPrefixExponent]
    simpa only [context.entropy_structural] using
      context.entropy.initial_margin
  have hδ : 0 < δ := by
    dsimp [δ]
    have hrho := context.structural.rho_pos
    linarith
  have hd : 0 < d := by dsimp [d]; linarith
  have herrorSmall : ∀ᶠ L : ℕ in atTop, error L ≤ d :=
    ((tendsto_order.1 herrorZero).2 d hd).mono fun _ h => h.le
  have hnatTop : Tendsto (fun L : ℕ => (L : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  let b : ℝ := Real.log 2 * d
  have hb : 0 < b := mul_pos (Real.log_pos (by norm_num)) hd
  have hpolyExp :
      Tendsto (fun L : ℕ => (L : ℝ) / Real.exp (b * (L : ℝ)))
        atTop (𝓝 0) := by
    have hlittle :=
      (isLittleO_pow_exp_pos_mul_atTop 1 hb).comp_tendsto hnatTop
    simpa only [Function.comp_apply, pow_one] using
      hlittle.tendsto_div_nhds_zero
  have hexpTop : Tendsto (fun L : ℕ => Real.exp (b * (L : ℝ)))
      atTop atTop := by
    exact Real.tendsto_exp_atTop.comp
      (Filter.Tendsto.const_mul_atTop hb hnatTop)
  have hconstExp : Tendsto
      (fun L : ℕ => ((gap.Cgap : ℝ) + 1) /
        Real.exp (b * (L : ℝ))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hexpTop
  have hdecayExp : Tendsto
      (fun L : ℕ => ((L : ℝ) + gap.Cgap + 1) /
        Real.exp (b * (L : ℝ))) atTop (𝓝 0) := by
    simpa only [add_div, zero_add, add_assoc] using
      hpolyExp.add hconstExp
  have hrpowExp : ∀ L : ℕ,
      Real.rpow (dyadicScale L) d = Real.exp (b * (L : ℝ)) := by
    intro L
    have hdyadic : (0 : ℝ) < dyadicScale L := by
      rw [dyadicScale]
      positivity
    rw [Real.rpow_eq_pow, Real.rpow_def_of_pos
      (x := (dyadicScale L : ℝ)) (y := d) hdyadic]
    simp only [dyadicScale, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    dsimp [b]
    ring_nf
  have hdecay : Tendsto
      (fun L : ℕ => ((L : ℝ) + gap.Cgap + 1) /
        Real.rpow (dyadicScale L) d) atTop (𝓝 0) := by
    simpa only [hrpowExp] using hdecayExp
  apply IsLittleO.of_bound
  intro c hc
  have hdecayC : ∀ᶠ L : ℕ in atTop,
      ((L : ℝ) + gap.Cgap + 1) /
          Real.rpow (dyadicScale L) d ≤ c :=
    ((tendsto_order.1 hdecay).2 c hc).mono fun _ h => h.le
  filter_upwards [eventually_rawWindowGap_le context gap F hF,
    hcount F hF, herrorSmall, hdecayC, eventually_ge_atTop 1]
      with L hgap hprefixCount herrorL hdecayL hL
  let W := F.system L
  let G : ℕ := L + gap.Cgap + 1
  have hWstruct : W.structural = context.structural :=
    (F.structural_eq L).trans hF.2.1
  have hWentropy : W.entropy = context.entropy :=
    (F.entropy_eq L).trans hF.2.2.1
  have hlevel : W.L = L := F.level_eq L
  have hX : W.X = dyadicScale L := by rw [WindowSystem.X, hlevel]
  have hXpos : 0 < (W.X : ℝ) := by
    rw [hX, dyadicScale]
    positivity
  have hXone : (1 : ℝ) ≤ W.X := by
    rw [hX, dyadicScale]
    exact_mod_cast (Left.one_le_pow_of_le (by norm_num : (1 : ℕ) ≤ 2) L)
  have hGnonneg : (0 : ℝ) ≤ G := by positivity
  have hmnonneg : (0 : ℝ) ≤ W.m := by positivity
  have hlengthNonneg : 0 ≤ thresholdLength W := by
    unfold thresholdLength
    exact mul_nonneg W.structural.cI_pos.le (Nat.cast_nonneg _)
  have hrareBound : ∀ e ∈ rareLargePairs W Z0,
      W.excess e ≤ ((W.m : ℝ) * G) := by
    intro e he
    have hexcess := W.excess_le_rawWindowSpan e he.1.1
    have hsum : (W.rawWindowGapWord e.1).sum ≤
        (W.rawWindowGapWord e.1).length * G := by
      simpa [nsmul_eq_mul] using
        List.sum_le_card_nsmul (W.rawWindowGapWord e.1) G
          (hgap e.1 he.1.1.1)
    have hlen : (W.rawWindowGapWord e.1).length ≤ W.m := by
      unfold WindowSystem.rawWindowGapWord
      split
      · simp [windowGapWord, WindowSystem.window, WindowSystem.m]
      · exact Nat.zero_le _
    have hspan : W.rawWindowSpan e.1 ≤ W.m * G := by
      rw [← rawWindowGapWord_span]
      exact hsum.trans (Nat.mul_le_mul_right G hlen)
    exact hexcess.trans (by exact_mod_cast hspan)
  have hmass := rareLargePairsMass_le W Z0 ((W.m : ℝ) * G)
    (mul_nonneg hmnonneg hGnonneg) hrareBound
  have hanchors := rareAnchors_card_le W Z0
  have hcountW : ((initialPrefixes W Z0).card : ℝ) ≤
      Real.rpow W.X (Δ + error L) := by
    simpa only [W, hWentropy, Δ] using hprefixCount
  have hcutoff : frequencyCutoff W =
      Real.rpow W.X (1 / 2 + context.structural.rho) := by
    unfold frequencyCutoff
    rw [hWstruct]
  have hanchorEstimate : ((rareAnchors W Z0).card : ℝ) ≤
      Real.rpow W.X
        (Δ + error L + (1 / 2 + context.structural.rho)) := by
    calc
      ((rareAnchors W Z0).card : ℝ) ≤
          ((initialPrefixes W Z0).card : ℝ) * frequencyCutoff W := hanchors
      _ ≤ Real.rpow W.X (Δ + error L) * frequencyCutoff W := by
        exact mul_le_mul_of_nonneg_right hcountW
          (by unfold frequencyCutoff; exact Real.rpow_nonneg hXpos.le _)
      _ = Real.rpow W.X
          (Δ + error L + (1 / 2 + context.structural.rho)) := by
        rw [hcutoff]
        exact (Real.rpow_add hXpos _ _).symm
  have hexponent :
      Δ + error L + (1 / 2 + context.structural.rho) ≤ 1 - d := by
    dsimp [δ, d] at hδ hd herrorL ⊢
    linarith
  have hrpowExponent : Real.rpow W.X
      (Δ + error L + (1 / 2 + context.structural.rho)) ≤
      Real.rpow W.X (1 - d) :=
    Real.rpow_le_rpow_of_exponent_le hXone hexponent
  have hanchorFinal : ((rareAnchors W Z0).card : ℝ) ≤
      W.X / Real.rpow W.X d := by
    calc
      ((rareAnchors W Z0).card : ℝ) ≤
          Real.rpow W.X
            (Δ + error L + (1 / 2 + context.structural.rho)) :=
        hanchorEstimate
      _ ≤ Real.rpow W.X (1 - d) := hrpowExponent
      _ = W.X / Real.rpow W.X d := by
        simp only [Real.rpow_eq_pow]
        rw [Real.rpow_sub hXpos 1 d, Real.rpow_one]
  have hdecayW : (G : ℝ) / Real.rpow W.X d ≤ c := by
    rw [hX]
    simpa only [G, Nat.cast_add, Nat.cast_one] using hdecayL
  have hmassFinal : rareLargePairsMass W Z0 ≤
      c * ((W.m : ℝ) * W.X * thresholdLength W) := by
    calc
      rareLargePairsMass W Z0 ≤
          ((W.m : ℝ) * G) * (rareAnchors W Z0).card *
            thresholdLength W := hmass
      _ ≤ ((W.m : ℝ) * G) *
          (W.X / Real.rpow W.X d) * thresholdLength W := by
        gcongr
      _ = ((W.m : ℝ) * W.X * thresholdLength W) *
          ((G : ℝ) / Real.rpow W.X d) := by ring
      _ ≤ ((W.m : ℝ) * W.X * thresholdLength W) * c := by
        gcongr
      _ = c * ((W.m : ℝ) * W.X * thresholdLength W) := by ring
  have hmassNonneg : 0 ≤ rareLargePairsMass W Z0 := by
    unfold rareLargePairsMass finiteWindowMass FiniteMass.toReal
    exact ENNReal.toReal_nonneg
  simpa only [Real.norm_eq_abs, abs_of_nonneg hmassNonneg,
    abs_of_nonneg (mul_nonneg (mul_nonneg hmnonneg hXpos.le)
      hlengthNonneg), W] using hmassFinal

/-- The eventual denominator-uniform gap bound can be enlarged to cover the
finitely many possible starting positions below its uniform cutoff. -/
theorem exists_global_gap_bound (Q : ℕ) (hQ : 0 < Q) :
    ∃ Cgap : ℕ, ∀ R : RationalSupport, R.eta.den = Q →
      ∀ x g : ℕ, IsSupportGap R.S x g →
        g ≤ Nat.log 2 (x + 1) + Cgap := by
  obtain ⟨gap⟩ := gapParams_exists Q hQ
  obtain ⟨xexp, hexp⟩ := eventually_linear_lt_two_pow_pred Q
  let Bearly := max xexp (max gap.x0 1)
  refine ⟨max gap.Cgap Bearly, ?_⟩
  intro R hden x g hgap
  by_cases hx : gap.x0 ≤ x
  · have h := gap.bound R hden x hx g hgap
    have hlog : Nat.log 2 x ≤ Nat.log 2 (x + 1) :=
      Nat.log_mono_right (by omega)
    omega
  · have hgEarly : g < Bearly := by
      by_contra hnot
      have hB : Bearly ≤ g := Nat.le_of_not_gt hnot
      have hxg : x < g := by
        have hxx0 : x < gap.x0 := Nat.lt_of_not_ge hx
        exact hxx0.trans_le ((le_max_left gap.x0 1).trans
          ((le_max_right xexp (max gap.x0 1)).trans hB))
      have hg1 : 1 ≤ g :=
        (le_max_right gap.x0 1).trans
          ((le_max_right xexp (max gap.x0 1)).trans hB)
      have hlinear : Q * (x + g + 1) ≤ 3 * Q * g := by
        have hsum : x + g + 1 ≤ 3 * g := by omega
        nlinarith
      have hpower := gap_power_bound R x g hgap
      rw [hden] at hpower
      have hstrict := hexp g ((le_max_left xexp (max gap.x0 1)).trans hB)
      omega
    have hmax : Bearly ≤ max gap.Cgap Bearly := le_max_right _ _
    omega

def carryAlongWord (Q x : ℕ) (r : ℤ) : GapWord → ℤ
  | [] => r
  | g :: gs => carryAlongWord Q (x + g)
      ((2 : ℤ) ^ g * r - (Q : ℤ) * (x + g)) gs

private theorem wordMultiplier_cons (g : ℕ) (w : GapWord) :
    wordMultiplier (g :: w) = 2 ^ w.span + wordMultiplier w := by
  simp [wordMultiplier, List.range_succ_eq_map, GapWord.span,
    GapWord.prefixSpan, Function.comp_def, Nat.add_sub_add_left]

private theorem carryAlongWord_difference (Q x y : ℕ) (r s : ℤ)
    (w : GapWord) :
    carryAlongWord Q y s w - carryAlongWord Q x r w =
      (2 : ℤ) ^ w.span * (s - r) -
        (Q : ℤ) * wordMultiplier w * ((y : ℤ) - x) := by
  induction w generalizing x y r s with
  | nil => simp [carryAlongWord, GapWord.span, wordMultiplier]
  | cons g w ih =>
      simp only [carryAlongWord]
      rw [ih]
      rw [wordMultiplier_cons]
      simp only [GapWord.span, List.sum_cons, pow_add]
      push_cast
      ring

def enumerationGapWord {S : Set ℕ} (e : SupportEnumeration S)
    (i n : ℕ) : GapWord :=
  (List.range n).map fun j => supportGap e (i + j)

theorem enumerationGapWord_succ {S : Set ℕ}
    (e : SupportEnumeration S) (i n : ℕ) :
    enumerationGapWord e i (n + 1) =
      supportGap e i :: enumerationGapWord e (i + 1) n := by
  unfold enumerationGapWord
  rw [List.range_succ_eq_map]
  simp [Nat.add_comm, Nat.add_left_comm]

theorem enumerationGapWord_span {S : Set ℕ}
    (e : SupportEnumeration S) (i n : ℕ) :
    (enumerationGapWord e i n).span = e.a (i + n) - e.a i := by
  unfold enumerationGapWord GapWord.span
  rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
  have htel := sum_supportGap_Ico e i (i + n) (by omega)
  rw [Finset.sum_Ico_eq_sum_range] at htel
  simpa using htel

theorem carryAlong_enumeration (R : RationalSupport)
    (e : SupportEnumeration R.S) (i n : ℕ) :
    carryAlongWord R.eta.den (e.a i) (carryInt R (e.a i))
        (enumerationGapWord e i n) =
      carryInt R (e.a (i + n)) := by
  induction n generalizing i with
  | zero => simp [enumerationGapWord, carryAlongWord]
  | succ n ih =>
      rw [show n + 1 = n.succ by rfl, enumerationGapWord_succ]
      simp only [carryAlongWord]
      have hgap := supportGap_isSupportGap e i
      have hupdate :
          (2 : ℤ) ^ supportGap e i * carryInt R (e.a i) -
              (R.eta.den : ℤ) * (e.a i + supportGap e i) =
            carryInt R (e.a i + supportGap e i) := by
        exact (carryInt_across_supportGap R (e.a i)
          (supportGap e i) hgap).symm
      rw [hupdate]
      have hend : e.a i + supportGap e i = e.a (i + 1) := by
        simp only [supportGap]
        exact Nat.add_sub_of_le
          (e.strictMono (Nat.lt_succ_self i)).le
      rw [hend]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (i + 1)

theorem initialPrefix_eq_enumerationGapWord
    (W : WindowSystem) (Z0 k : ℕ) (p : GapWord)
    (hk : k ∈ highAnchors W Z0)
    (hp : initialLongPrefix W k = p) :
    p = enumerationGapWord W.enumeration (k - W.s) p.length := by
  have hsk : W.s ≤ k := highAnchor_offset_le W Z0 k hk
  have hprefix : p.IsPrefix (W.rawWindowGapWord k) := by
    rw [← hp]
    exact GapWord.firstPrefixAbove_isPrefix _ _
  rcases hprefix with ⟨tail, htail⟩
  have hlen : p.length ≤ W.s + 1 := by
    have hlength := congrArg List.length htail
    have hlength' : p.length + tail.length = W.s + 1 := by
      simpa [WindowSystem.rawWindowGapWord, hsk,
        WindowSystem.window, windowGapWord] using hlength
    omega
  have htake := congrArg (List.take p.length) htail
  rw [List.take_append_of_le_length (le_refl p.length)] at htake
  rw [WindowSystem.rawWindowGapWord, dif_pos hsk,
    WindowSystem.window, windowGapWord] at htake
  unfold enumerationGapWord
  simpa [← List.map_take, List.take_range, hlen] using htake

private theorem occurrenceCarry_difference
    (W : WindowSystem) (Z0 : ℕ) (p : GapWord)
    (k₁ k₂ : ℕ) (hk₁ : k₁ ∈ highAnchors W Z0)
    (hk₂ : k₂ ∈ highAnchors W Z0)
    (hp₁ : initialLongPrefix W k₁ = p)
    (hp₂ : initialLongPrefix W k₂ = p) :
    let x₁ := W.enumeration.a (k₁ - W.s) + p.span
    let x₂ := W.enumeration.a (k₂ - W.s) + p.span
    carryInt W.rational x₂ - carryInt W.rational x₁ =
      (2 : ℤ) ^ p.span *
        (carryInt W.rational (W.enumeration.a (k₂ - W.s)) -
          carryInt W.rational (W.enumeration.a (k₁ - W.s))) -
      (W.rational.eta.den : ℤ) * wordMultiplier p *
        ((x₂ : ℤ) - x₁) := by
  dsimp only
  have hpword₁ := initialPrefix_eq_enumerationGapWord W Z0 k₁ p hk₁ hp₁
  have hpword₂ := initialPrefix_eq_enumerationGapWord W Z0 k₂ p hk₂ hp₂
  let i₁ := k₁ - W.s
  let i₂ := k₂ - W.s
  have hspan₁ := enumerationGapWord_span W.enumeration i₁ p.length
  have hspan₂ := enumerationGapWord_span W.enumeration i₂ p.length
  rw [← hpword₁] at hspan₁
  rw [← hpword₂] at hspan₂
  have hmono₁ : W.enumeration.a i₁ ≤ W.enumeration.a (i₁ + p.length) :=
    W.enumeration.strictMono.monotone (by omega)
  have hmono₂ : W.enumeration.a i₂ ≤ W.enumeration.a (i₂ + p.length) :=
    W.enumeration.strictMono.monotone (by omega)
  have hend₁ : W.enumeration.a i₁ + p.span =
      W.enumeration.a (i₁ + p.length) := by omega
  have hend₂ : W.enumeration.a i₂ + p.span =
      W.enumeration.a (i₂ + p.length) := by omega
  have hcarry₁ := carryAlong_enumeration W.rational W.enumeration i₁ p.length
  have hcarry₂ := carryAlong_enumeration W.rational W.enumeration i₂ p.length
  dsimp [i₁] at hpword₁ hspan₁ hmono₁ hend₁ hcarry₁
  dsimp [i₂] at hpword₂ hspan₂ hmono₂ hend₂ hcarry₂
  rw [← hpword₁, ← hend₁] at hcarry₁
  rw [← hpword₂, ← hend₂] at hcarry₂
  have hdiff := carryAlongWord_difference W.rational.eta.den
    (W.enumeration.a i₁) (W.enumeration.a i₂)
    (carryInt W.rational (W.enumeration.a i₁))
    (carryInt W.rational (W.enumeration.a i₂)) p
  rw [hcarry₁, hcarry₂] at hdiff
  dsimp [i₁, i₂] at hdiff ⊢
  convert hdiff using 1
  ring_nf

private def occurrenceX (W : WindowSystem) (p : GapWord) (k : ℕ) : ℤ :=
  W.enumeration.a (k - W.s) + p.span

private def occurrenceR (W : WindowSystem) (p : GapWord) (k : ℕ) : ℤ :=
  carryInt W.rational (W.enumeration.a (k - W.s) + p.span)

private theorem occurrenceDifference_mem_lattice
    (W : WindowSystem) (Z0 : ℕ) (p : GapWord)
    (k₁ k₂ : ℕ) (hk₁ : k₁ ∈ highAnchors W Z0)
    (hk₂ : k₂ ∈ highAnchors W Z0)
    (hp₁ : initialLongPrefix W k₁ = p)
    (hp₂ : initialLongPrefix W k₂ = p) :
    (occurrenceX W p k₂ - occurrenceX W p k₁,
      occurrenceR W p k₂ - occurrenceR W p k₁) ∈
      congruenceLattice
        ((W.rational.eta.den : ℤ) * wordMultiplier p) (2 ^ p.span) := by
  have hdiff := occurrenceCarry_difference W Z0 p k₁ k₂
    hk₁ hk₂ hp₁ hp₂
  dsimp only at hdiff
  unfold congruenceLattice occurrenceX occurrenceR
  change Int.ModEq (2 ^ p.span : ℤ)
    ((W.rational.eta.den : ℤ) * wordMultiplier p *
        ((W.enumeration.a (k₂ - W.s) : ℤ) + p.span -
          ((W.enumeration.a (k₁ - W.s) : ℤ) + p.span)) +
      (carryInt W.rational (W.enumeration.a (k₂ - W.s) + p.span) -
        carryInt W.rational (W.enumeration.a (k₁ - W.s) + p.span))) 0
  rw [Int.modEq_zero_iff_dvd]
  refine ⟨carryInt W.rational (W.enumeration.a (k₂ - W.s)) -
    carryInt W.rational (W.enumeration.a (k₁ - W.s)), ?_⟩
  rw [hdiff]
  push_cast
  ring

private theorem nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      have hone : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      omega

private theorem occurrenceX_le
    (W : WindowSystem) (Z0 : ℕ) (p : GapWord) (Cgap : ℕ)
    (hglobal : ∀ R : RationalSupport,
      R.eta.den = W.rational.eta.den → ∀ x g : ℕ,
        IsSupportGap R.S x g → g ≤ Nat.log 2 (x + 1) + Cgap)
    (k : ℕ) (hk : k ∈ highAnchors W Z0)
    (hp : initialLongPrefix W k = p) :
    (occurrenceX W p k).natAbs ≤ (Cgap + 5) * W.X := by
  classical
  have hkAnchor : k ∈ W.anchors := by
    rw [highAnchors, Finset.mem_filter] at hk
    exact hk.1
  have hsk : W.s ≤ k := highAnchor_offset_le W Z0 k hk
  have hpPrefix : p.IsPrefix (W.rawWindowGapWord k) := by
    rw [← hp]
    exact GapWord.firstPrefixAbove_isPrefix _ _
  have hpSpan : p.span ≤ W.rawWindowSpan k := by
    rcases hpPrefix with ⟨tail, htail⟩
    have hspanEq : (W.rawWindowGapWord k).span = W.rawWindowSpan k := by
      unfold WindowSystem.rawWindowGapWord WindowSystem.rawWindowSpan
      split <;> rfl
    rw [← hspanEq]
    rw [← htail]
    simp only [GapWord.span, List.sum_append]
    omega
  have hkData := Finset.mem_filter.mp hkAnchor
  have hkUpper : W.enumeration.a k ≤ 2 * W.X := hkData.2.2
  have hgap := hglobal W.rational rfl (W.enumeration.a k)
    (supportGap W.enumeration k) (supportGap_isSupportGap W.enumeration k)
  have hXone : 1 ≤ W.X := by
    unfold WindowSystem.X dyadicScale
    exact Nat.one_le_two_pow
  have harg : W.enumeration.a k + 1 ≤ 4 * W.X := by omega
  have hlog : Nat.log 2 (W.enumeration.a k + 1) ≤ W.L + 2 := by
    calc
      Nat.log 2 (W.enumeration.a k + 1) ≤ Nat.log 2 (4 * W.X) :=
        Nat.log_mono_right harg
      _ = W.L + 2 := by
        rw [WindowSystem.X, dyadicScale,
          show 4 * 2 ^ W.L = 2 ^ (W.L + 2) by
            rw [pow_add]
            norm_num
            ring]
        exact Nat.log_pow Nat.one_lt_two (W.L + 2)
  have hnext : W.enumeration.a (k + 1) =
      W.enumeration.a k + supportGap W.enumeration k := by
    simp only [supportGap]
    exact (Nat.add_sub_of_le
      (W.enumeration.strictMono (Nat.lt_succ_self k)).le).symm
  have hendpoint : (occurrenceX W p k).natAbs ≤
      W.enumeration.a (k + 1) := by
    have hraw := rawWindowSpan_eq_sub W k hsk
    have hmono : W.enumeration.a (k - W.s) ≤ W.enumeration.a (k + 1) :=
      W.enumeration.strictMono.monotone (by omega)
    change W.enumeration.a (k - W.s) + p.span ≤ W.enumeration.a (k + 1)
    omega
  have hLpow : W.L ≤ W.X := by
    rw [WindowSystem.X, dyadicScale]
    exact nat_le_two_pow W.L
  have hboundNext : W.enumeration.a (k + 1) ≤ (Cgap + 5) * W.X := by
    rw [hnext]
    have hgap' : supportGap W.enumeration k ≤ W.L + 2 + Cgap :=
      hgap.trans (Nat.add_le_add_right hlog Cgap)
    nlinarith
  exact hendpoint.trans hboundNext

private theorem occurrenceR_bounds
    (W : WindowSystem) (p : GapWord) (Cx : ℕ) (k : ℕ)
    (_hx : 0 ≤ occurrenceX W p k)
    (hxle : occurrenceX W p k ≤ (Cx : ℤ) * W.X) :
    0 ≤ occurrenceR W p k ∧
      occurrenceR W p k ≤
        (W.rational.eta.den : ℤ) * (Cx + 2) * W.X := by
  have hcarry := prop_carry W.rational
  have hXone : (1 : ℤ) ≤ W.X := by
    unfold WindowSystem.X dyadicScale
    exact_mod_cast Nat.one_le_two_pow
  unfold occurrenceX at hxle
  unfold occurrenceR
  constructor
  · exact hcarry.2.1 _
  · have hup := hcarry.2.2.1
      (W.enumeration.a (k - W.s) + p.span)
    have hQnonneg : (0 : ℤ) ≤ W.rational.eta.den := by positivity
    calc
      carryInt W.rational (W.enumeration.a (k - W.s) + p.span) ≤
          (W.rational.eta.den : ℤ) *
            (W.enumeration.a (k - W.s) + p.span + 2) := hup
      _ ≤ (W.rational.eta.den : ℤ) * (Cx + 2) * W.X := by
        nlinarith

private theorem AffineLine.contains_of_direction_eq_of_primitive
    (line : AffineLine) (hprimitive : Int.gcd line.H line.K = 1)
    (x r : ℤ)
    (hdirection : line.H * (r - line.C) = line.K * (x - line.A)) :
    line.Contains x r := by
  have hdvdMul : line.H ∣ line.K * (x - line.A) := by
    exact ⟨r - line.C, hdirection.symm⟩
  have hdvd : line.H ∣ x - line.A :=
    Int.dvd_of_dvd_mul_right_of_gcd_one hdvdMul hprimitive
  rcases hdvd with ⟨t, ht⟩
  refine ⟨t, ?_, ?_⟩
  · linarith
  · have hHne : line.H ≠ 0 := ne_of_gt line.H_pos
    apply mul_left_cancel₀ hHne
    calc
      line.H * r = line.H * line.C + line.K * (x - line.A) := by
        linarith
      _ = line.H * (line.C + line.K * t) := by
        rw [ht]
        ring

private theorem intDet_abs_le_of_box
    (Bx Br : ℤ) (hBx : 0 ≤ Bx) (hBr : 0 ≤ Br)
    (x₀ r₀ x₁ r₁ x₂ r₂ : ℤ)
    (hx₀ : 0 ≤ x₀) (hx₀' : x₀ ≤ Bx)
    (hx₁ : 0 ≤ x₁) (hx₁' : x₁ ≤ Bx)
    (hx₂ : 0 ≤ x₂) (hx₂' : x₂ ≤ Bx)
    (hr₀ : 0 ≤ r₀) (hr₀' : r₀ ≤ Br)
    (hr₁ : 0 ≤ r₁) (hr₁' : r₁ ≤ Br)
    (hr₂ : 0 ≤ r₂) (hr₂' : r₂ ≤ Br) :
    |intDet (x₁ - x₀, r₁ - r₀) (x₂ - x₀, r₂ - r₀)| ≤
      2 * Bx * Br := by
  have hdx₁ : |x₁ - x₀| ≤ Bx := by rw [abs_le]; constructor <;> linarith
  have hdx₂ : |x₂ - x₀| ≤ Bx := by rw [abs_le]; constructor <;> linarith
  have hdr₁ : |r₁ - r₀| ≤ Br := by rw [abs_le]; constructor <;> linarith
  have hdr₂ : |r₂ - r₀| ≤ Br := by rw [abs_le]; constructor <;> linarith
  unfold intDet
  calc
    |(x₁ - x₀) * (r₂ - r₀) - (r₁ - r₀) * (x₂ - x₀)| ≤
        |(x₁ - x₀) * (r₂ - r₀)| + |(r₁ - r₀) * (x₂ - x₀)| :=
      abs_sub _ _
    _ = |x₁ - x₀| * |r₂ - r₀| + |r₁ - r₀| * |x₂ - x₀| := by
      rw [abs_mul, abs_mul]
    _ ≤ Bx * Br + Br * Bx := by gcongr
    _ = 2 * Bx * Br := by ring

private theorem intDet_eq_zero_of_lattice_bounds
    (A : ℤ) (M D : ℕ) (hM : 1 ≤ M) (hlarge : D < M)
    (z₁ z₂ : ℤ × ℤ)
    (hz₁ : z₁ ∈ congruenceLattice A M)
    (hz₂ : z₂ ∈ congruenceLattice A M)
    (hdetBound : |intDet z₁ z₂| ≤ D) :
    intDet z₁ z₂ = 0 := by
  obtain ⟨q, hq⟩ := lem_lattice_det A M hM z₁ z₂ hz₁ hz₂
  by_contra hdet
  have hqne : q ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hq
    exact hdet hq
  have hqabs : (1 : ℤ) ≤ |q| := Int.one_le_abs hqne
  have hMnonneg : (0 : ℤ) ≤ M := by positivity
  have hMle : (M : ℤ) ≤ |intDet z₁ z₂| := by
    rw [hq, abs_mul, abs_of_nonneg hMnonneg]
    nlinarith
  have hlargeInt : (D : ℤ) < M := by exact_mod_cast hlarge
  have hboundInt : |intDet z₁ z₂| ≤ (D : ℤ) := by exact_mod_cast hdetBound
  linarith

/-- Paper label: `lem:ap-locking` (Section 5).  Both the determinant slack
and the spacing constant are selected after the denominator and before the
window/support data. -/
theorem lem_ap_locking (Q : ℕ) (hQ : 0 < Q) :
    ∃ Cline : ℕ, ∃ Clock : ℝ, 0 < Clock ∧ ∀ W : WindowSystem,
      W.rational.eta.den = Q → ∀ Z0 : ℕ, ∀ p : GapWord,
      p ∈ initialPrefixes W Z0 →
      2 * W.L + Cline < p.span → IsFrequentPrefix W Z0 p →
      ∃ line : AffineLine,
        IsOccurrenceLine W Z0 p line ∧
        Int.gcd line.H line.K = 1 ∧
        (line.H : ℝ) ≤ Clock * W.X / frequencyCutoff W := by
  classical
  obtain ⟨Cgap, hglobal⟩ := exists_global_gap_bound Q hQ
  let Cx : ℕ := Cgap + 5
  let Cr : ℕ := Q * (Cx + 2)
  let D : ℕ := 2 * Cx * Cr
  have hpowTop : Tendsto (fun n : ℕ => (2 : ℕ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hevent : ∀ᶠ n : ℕ in atTop, D < 2 ^ n :=
    hpowTop.eventually_gt_atTop D
  obtain ⟨Cline, hClineAll⟩ := eventually_atTop.1 hevent
  have hCline : D < 2 ^ Cline := hClineAll Cline le_rfl
  let Clock : ℝ := 2 * Cx + 1
  refine ⟨Cline, Clock, by dsimp [Clock]; positivity, ?_⟩
  intro W hden Z0 p hpSet hpLong hfrequent
  let fibre : Finset ℕ :=
    (highAnchors W Z0).filter fun k => initialLongPrefix W k = p
  have hfreqCard : frequencyCutoff W ≤ (fibre.card : ℝ) := by
    simpa only [IsFrequentPrefix, prefixMultiplicity, fibre] using hfrequent
  have hXposNat : 0 < W.X := by
    unfold WindowSystem.X dyadicScale
    positivity
  have hXpos : (0 : ℝ) < W.X := by exact_mod_cast hXposNat
  have hXoneNat : 1 ≤ W.X := Nat.one_le_iff_ne_zero.mpr hXposNat.ne'
  have hXone : (1 : ℝ) ≤ W.X := by exact_mod_cast hXoneNat
  have hfreqPos : 0 < frequencyCutoff W := by
    unfold frequencyCutoff
    exact Real.rpow_pos_of_pos hXpos _
  have hfreqLeX : frequencyCutoff W ≤ (W.X : ℝ) := by
    unfold frequencyCutoff
    calc
      Real.rpow W.X (1 / 2 + W.structural.rho) ≤ Real.rpow W.X 1 := by
        apply Real.rpow_le_rpow_of_exponent_le hXone
        nlinarith [W.structural.rho_lt]
      _ = W.X := by simp [Real.rpow_eq_pow]
  rw [initialPrefixes, Finset.mem_image] at hpSet
  rcases hpSet with ⟨kbase, hkbase, hpbase⟩
  have hkbaseF : kbase ∈ fibre := by
    change kbase ∈ (highAnchors W Z0).filter fun k =>
      initialLongPrefix W k = p
    rw [Finset.mem_filter]
    exact ⟨hkbase, hpbase⟩
  by_cases hcard : fibre.card ≤ 1
  · let x₀ := occurrenceX W p kbase
    let r₀ := occurrenceR W p kbase
    let line : AffineLine :=
      { A := x₀
        C := r₀
        H := 1
        K := 0
        H_pos := by norm_num }
    have hline : IsOccurrenceLine W Z0 p line := by
      intro k hk hpk
      have hkF : k ∈ fibre := by
        change k ∈ (highAnchors W Z0).filter fun j =>
          initialLongPrefix W j = p
        rw [Finset.mem_filter]
        exact ⟨hk, hpk⟩
      have hEq : k = kbase := by
        exact (Finset.card_le_one.mp hcard) k hkF kbase hkbaseF
      subst k
      refine ⟨0, ?_, ?_⟩ <;>
        simp [line, x₀, r₀, occurrenceX, occurrenceR]
    have hprimitive : Int.gcd line.H line.K = 1 := by
      simp [line, Int.gcd_def]
    have hfreqOne : frequencyCutoff W ≤ 1 :=
      hfreqCard.trans (by exact_mod_cast hcard)
    have hClockOne : (1 : ℝ) ≤ Clock := by
      dsimp [Clock, Cx]
      have : (0 : ℝ) ≤ Cgap := by positivity
      nlinarith
    have hbound : (line.H : ℝ) ≤
        Clock * W.X / frequencyCutoff W := by
      rw [le_div_iff₀ hfreqPos]
      dsimp [line]
      have hprod : (1 : ℝ) ≤ Clock * W.X := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hClockOne)
          (sub_nonneg.mpr hXone)]
      simpa using hfreqOne.trans hprod
    exact ⟨line, hline, hprimitive, hbound⟩
  · have hcardTwo : 1 < fibre.card := by omega
    obtain ⟨k₀, hk₀F, k₁, hk₁F, hkne⟩ :=
      Finset.one_lt_card.mp hcardTwo
    obtain ⟨ka, hkaF, kb, hkbF, hkab⟩ :
        ∃ ka ∈ fibre, ∃ kb ∈ fibre, ka < kb := by
      rcases lt_or_gt_of_ne hkne with hlt | hgt
      · exact ⟨k₀, hk₀F, k₁, hk₁F, hlt⟩
      · exact ⟨k₁, hk₁F, k₀, hk₀F, hgt⟩
    have hka := Finset.mem_filter.mp (show ka ∈
      (highAnchors W Z0).filter fun k => initialLongPrefix W k = p from hkaF)
    have hkb := Finset.mem_filter.mp (show kb ∈
      (highAnchors W Z0).filter fun k => initialLongPrefix W k = p from hkbF)
    let x₀ := occurrenceX W p ka
    let r₀ := occurrenceR W p ka
    let x₁ := occurrenceX W p kb
    let r₁ := occurrenceR W p kb
    have hsa := highAnchor_offset_le W Z0 ka hka.1
    have hsb := highAnchor_offset_le W Z0 kb hkb.1
    have hindex : ka - W.s < kb - W.s := by omega
    have hx01 : x₀ < x₁ := by
      dsimp [x₀, x₁, occurrenceX]
      have henum : (W.enumeration.a (ka - W.s) : ℤ) <
          W.enumeration.a (kb - W.s) := by
        exact_mod_cast W.enumeration.strictMono hindex
      linarith
    let raw : AffineLine :=
      { A := x₀
        C := r₀
        H := x₁ - x₀
        K := r₁ - r₀
        H_pos := sub_pos.mpr hx01 }
    let line : AffineLine :=
      { A := x₀
        C := r₀
        H := (raw.canonicalGeometricLine.H : ℤ)
        K := raw.canonicalGeometricLine.K
        H_pos := by exact_mod_cast raw.canonicalGeometricLine.H_pos }
    have hprimitive : Int.gcd line.H line.K = 1 := by
      simpa [line, Int.gcd_def] using raw.canonicalGeometricLine.primitive
    have pointBounds : ∀ k ∈ fibre,
        0 ≤ occurrenceX W p k ∧
        occurrenceX W p k ≤ (Cx : ℤ) * W.X ∧
        0 ≤ occurrenceR W p k ∧
        occurrenceR W p k ≤ (Cr : ℤ) * W.X := by
      intro k hkF
      have hk := Finset.mem_filter.mp (show k ∈
        (highAnchors W Z0).filter fun j => initialLongPrefix W j = p from hkF)
      have hxnonneg : 0 ≤ occurrenceX W p k := by
        unfold occurrenceX
        positivity
      have hxNat := occurrenceX_le W Z0 p Cgap
        (by simpa only [hden] using hglobal) k hk.1 hk.2
      have hxle : occurrenceX W p k ≤ (Cx : ℤ) * W.X := by
        change W.enumeration.a (k - W.s) + p.span ≤ Cx * W.X at hxNat
        unfold occurrenceX
        exact_mod_cast hxNat
      have hr := occurrenceR_bounds W p Cx k hxnonneg hxle
      refine ⟨hxnonneg, hxle, hr.1, ?_⟩
      dsimp [Cr]
      rw [← hden]
      simpa only [mul_assoc] using hr.2
    have hMlarge : D * W.X ^ 2 < 2 ^ p.span := by
      have hpPow : 2 ^ (2 * W.L + Cline) < 2 ^ p.span :=
        (Nat.pow_lt_pow_iff_right Nat.one_lt_two).2 hpLong
      have hfactor : 2 ^ (2 * W.L + Cline) = W.X ^ 2 * 2 ^ Cline := by
        rw [pow_add, WindowSystem.X, dyadicScale]
        congr 1
        rw [← pow_mul]
        congr 1
        omega
      calc
        D * W.X ^ 2 < 2 ^ Cline * W.X ^ 2 :=
          Nat.mul_lt_mul_of_pos_right hCline (pow_pos hXposNat 2)
        _ = W.X ^ 2 * 2 ^ Cline := Nat.mul_comm _ _
        _ = 2 ^ (2 * W.L + Cline) := hfactor.symm
        _ < 2 ^ p.span := hpPow
    have hline : IsOccurrenceLine W Z0 p line := by
      intro k hk hpk
      have hkF : k ∈ fibre := by
        change k ∈ (highAnchors W Z0).filter fun j =>
          initialLongPrefix W j = p
        rw [Finset.mem_filter]
        exact ⟨hk, hpk⟩
      let x := occurrenceX W p k
      let r := occurrenceR W p k
      let z₁ : ℤ × ℤ := (x₁ - x₀, r₁ - r₀)
      let z : ℤ × ℤ := (x - x₀, r - r₀)
      have hz₁ := occurrenceDifference_mem_lattice W Z0 p ka kb
        hka.1 hkb.1 hka.2 hkb.2
      have hzk := occurrenceDifference_mem_lattice W Z0 p ka k
        hka.1 hk hka.2 hpk
      have hb₀ := pointBounds ka hkaF
      have hb₁ := pointBounds kb hkbF
      have hbk := pointBounds k hkF
      have hdetBoundInt := intDet_abs_le_of_box
        ((Cx : ℤ) * W.X) ((Cr : ℤ) * W.X)
        (by positivity) (by positivity)
        x₀ r₀ x₁ r₁ x r
        hb₀.1 hb₀.2.1 hb₁.1 hb₁.2.1 hbk.1 hbk.2.1
        hb₀.2.2.1 hb₀.2.2.2 hb₁.2.2.1 hb₁.2.2.2
        hbk.2.2.1 hbk.2.2.2
      have hdetBoundNat : |intDet z₁ z| ≤ D * W.X ^ 2 := by
        have hright :
            2 * ((Cx : ℤ) * W.X) * ((Cr : ℤ) * W.X) =
              ((D * W.X ^ 2 : ℕ) : ℤ) := by
          dsimp [D]
          ring
        rw [hright] at hdetBoundInt
        exact_mod_cast hdetBoundInt
      have hdet : intDet z₁ z = 0 :=
        intDet_eq_zero_of_lattice_bounds
          ((W.rational.eta.den : ℤ) * wordMultiplier p)
          (2 ^ p.span) (D * W.X ^ 2) Nat.one_le_two_pow hMlarge
          z₁ z (by simpa [z₁, x₀, r₀, x₁, r₁] using hz₁)
          (by simpa [z, x, r, x₀, r₀] using hzk) hdetBoundNat
      have hrawDirection :
          raw.H * (r - raw.C) = raw.K * (x - raw.A) := by
        dsimp [z₁, z, raw] at hdet ⊢
        simp only [intDet] at hdet
        linarith
      have hdne : (raw.directionGCD : ℤ) ≠ 0 := by
        exact_mod_cast raw.directionGCD_pos.ne'
      have hHfactor : raw.primitiveHorizontalInt *
          (raw.directionGCD : ℤ) = raw.H :=
        Int.ediv_mul_cancel (Int.gcd_dvd_left raw.H raw.K)
      have hKfactor : raw.primitiveVertical *
          (raw.directionGCD : ℤ) = raw.K :=
        Int.ediv_mul_cancel (Int.gcd_dvd_right raw.H raw.K)
      have hprimitiveDirection :
          line.H * (r - line.C) = line.K * (x - line.A) := by
        dsimp [line]
        rw [raw.canonicalGeometricLine_H_cast]
        change raw.primitiveHorizontalInt * (r - r₀) =
          raw.primitiveVertical * (x - x₀)
        apply mul_right_cancel₀ hdne
        calc
          (raw.primitiveHorizontalInt * (r - r₀)) *
              (raw.directionGCD : ℤ) = raw.H * (r - r₀) := by
                rw [← hHfactor]
                ring
          _ = raw.K * (x - x₀) := hrawDirection
          _ = (raw.primitiveVertical * (x - x₀)) *
              (raw.directionGCD : ℤ) := by
                rw [← hKfactor]
                ring
      have hcontains := line.contains_of_direction_eq_of_primitive
        hprimitive x r hprimitiveDirection
      simpa [x, r, occurrenceX, occurrenceR] using hcontains
    let param : {k // k ∈ fibre} → ℤ := fun k =>
      Classical.choose (hline k.1 (Finset.mem_filter.mp k.2).1
        (Finset.mem_filter.mp k.2).2)
    have hparamSpec (k : {k // k ∈ fibre}) :
        occurrenceX W p k.1 = line.A + line.H * param k ∧
        occurrenceR W p k.1 = line.C + line.K * param k :=
      Classical.choose_spec (hline k.1 (Finset.mem_filter.mp k.2).1
        (Finset.mem_filter.mp k.2).2)
    have hparamInjective : Function.Injective param := by
      intro a b hab
      have hxa := (hparamSpec a).1
      have hxb := (hparamSpec b).1
      rw [hab] at hxa
      have hxEq : occurrenceX W p a.1 = occurrenceX W p b.1 :=
        hxa.trans hxb.symm
      have haData := Finset.mem_filter.mp a.2
      have hbData := Finset.mem_filter.mp b.2
      have hsa' := highAnchor_offset_le W Z0 a.1 haData.1
      have hsb' := highAnchor_offset_le W Z0 b.1 hbData.1
      have hind : a.1 - W.s = b.1 - W.s := by
        apply W.enumeration.strictMono.injective
        have : W.enumeration.a (a.1 - W.s) + p.span =
            W.enumeration.a (b.1 - W.s) + p.span := by
          unfold occurrenceX at hxEq
          exact_mod_cast hxEq
        exact Nat.add_right_cancel this
      apply Subtype.ext
      omega
    let params : Finset ℤ := fibre.attach.image param
    have hparamsCard : params.card = fibre.card := by
      dsimp [params]
      rw [Finset.card_image_of_injective _ hparamInjective]
      simp
    let Bx : ℤ := (Cx : ℤ) * W.X
    let C : ℤ := Bx - line.A
    let J : ℤ := -line.H
    have hJ : J < 0 := by dsimp [J]; exact neg_lt_zero.mpr line.H_pos
    have hBx : 0 ≤ Bx := by dsimp [Bx]; positivity
    have hparamBound : ∀ t ∈ (params : Set ℤ),
        0 ≤ C + J * t ∧ C + J * t ≤ Bx := by
      intro t ht
      rw [Finset.mem_coe] at ht
      change t ∈ fibre.attach.image param at ht
      rw [Finset.mem_image] at ht
      rcases ht with ⟨k, hk, rfl⟩
      have hkF : k.1 ∈ fibre := k.2
      have hb := pointBounds k.1 hkF
      have hx := (hparamSpec k).1
      dsimp [C, J]
      constructor <;> linarith
    have hcount := integerAffineIntervalCount
      (params : Set ℤ) C J Bx hJ hBx hparamBound
    have hcountReal : (fibre.card : ℝ) ≤
        1 + (Bx : ℝ) / (line.H : ℝ) := by
      rw [← hparamsCard]
      simpa [J] using hcount.2
    have hcardReal : (2 : ℝ) ≤ fibre.card := by exact_mod_cast hcardTwo
    have hHreal : (0 : ℝ) < line.H := by exact_mod_cast line.H_pos
    have hspacing : ((fibre.card : ℝ) - 1) * line.H ≤ Bx := by
      have hmul := mul_le_mul_of_nonneg_right hcountReal hHreal.le
      field_simp at hmul
      nlinarith
    have hfreqTwice : frequencyCutoff W ≤
        2 * ((fibre.card : ℝ) - 1) := by
      calc
        frequencyCutoff W ≤ fibre.card := hfreqCard
        _ ≤ 2 * ((fibre.card : ℝ) - 1) := by linarith
    have hHfreq : (line.H : ℝ) * frequencyCutoff W ≤
        2 * (Cx : ℝ) * W.X := by
      have hmul := mul_le_mul_of_nonneg_left hfreqTwice hHreal.le
      have hBxCast : (Bx : ℝ) = (Cx : ℝ) * W.X := by
        dsimp [Bx]
        push_cast
        ring
      rw [hBxCast] at hspacing
      nlinarith
    have hClockCx : 2 * (Cx : ℝ) ≤ Clock := by
      dsimp [Clock]
      norm_num
    have hbound : (line.H : ℝ) ≤
        Clock * W.X / frequencyCutoff W := by
      rw [le_div_iff₀ hfreqPos]
      calc
        (line.H : ℝ) * frequencyCutoff W ≤
            2 * (Cx : ℝ) * W.X := hHfreq
        _ ≤ Clock * W.X := by gcongr
    exact ⟨line, hline, hprimitive, hbound⟩

/-- Paper label: `lem:strict-unique` (Section 5). -/
theorem lem_strict_unique (μ : ℝ) (hμ : μ ∈ Set.Ioo (0 : ℝ) 1) :
    Set.Subsingleton {g : ℕ | 1 ≤ g ∧ (2 : ℝ) ^ g * μ - 1 ∈ Set.Ioo (0 : ℝ) 1} := by
  rintro g ⟨hg, hgI⟩ h ⟨hh, hhI⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hsucc : g + 1 ≤ h := Nat.succ_le_iff.mpr hlt
    have hpow : (2 : ℝ) ^ (g + 1) ≤ (2 : ℝ) ^ h :=
      pow_le_pow_right₀ (by norm_num) hsucc
    rw [pow_succ] at hpow
    have hmul := mul_le_mul_of_nonneg_right hpow hμ.1.le
    nlinarith [hgI.1, hhI.2]
  · have hsucc : h + 1 ≤ g := Nat.succ_le_iff.mpr hgt
    have hpow : (2 : ℝ) ^ (h + 1) ≤ (2 : ℝ) ^ g :=
      pow_le_pow_right₀ (by norm_num) hsucc
    rw [pow_succ] at hpow
    have hmul := mul_le_mul_of_nonneg_right hpow hμ.1.le
    nlinarith [hhI.1, hgI.2]

/-- Paper label: `lem:step-monotone` (Section 5). -/
theorem lem_step_monotone (Q g : ℕ) (line : AffineLine) :
    (line.transform Q g).primitiveHorizontalStep ∣ line.H.natAbs := by
  exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_left line.H.natAbs
    (line.transform Q g).K.natAbs)

/-- A boundary-transition word: every proper post-entry state is a boundary
state and the final state is exterior, unless the word is empty. -/
def IsBoundaryTransition (Q : ℕ) (line : AffineLine) (gaps : GapWord) : Prop :=
  gaps = [] ∨
    (∀ r < gaps.length, ∃ state : AffineLine,
      SharedGapTrajectory Q line (gaps.take r) state ∧
        classifySlope (state.slope Q) ∈
          ({SlopeRegion.boundaryZero, SlopeRegion.boundaryOne} : Set SlopeRegion)) ∧
    ∃ finish : AffineLine,
      SharedGapTrajectory Q line gaps finish ∧
        classifySlope (finish.slope Q) = .exterior

/-- Paper label: `lem:boundary-stretch` (Section 5). -/
theorem lem_boundary_stretch (Q m L Cgap : ℕ) (line : AffineLine)
    (gaps : GapWord) (htrans : IsBoundaryTransition Q line gaps)
    (hlen : gaps.length ≤ m)
    (hgap : ∀ g ∈ gaps, g ≤ L + Cgap) :
    gaps.span ≤ m + 2 * (L + Cgap) := by
  have trajectory_nil_eq (start finish : AffineLine)
      (h : SharedGapTrajectory Q start [] finish) : finish = start := by
    cases h
    rfl
  have trajectory_cons_iff (start finish : AffineLine) (g : ℕ) (gs : GapWord) :
      SharedGapTrajectory Q start (g :: gs) finish ↔
        SharedGapTrajectory Q (start.transform Q g) gs finish := by
    constructor
    · intro h
      cases h with
      | cons _ next _ _ _ hnext htail =>
          subst next
          exact htail
    · intro h
      exact SharedGapTrajectory.cons start (start.transform Q g) finish g gs rfl h
  have boundary_slope (μ : ℚ)
      (hμ : classifySlope μ ∈
        ({SlopeRegion.boundaryZero, SlopeRegion.boundaryOne} : Set SlopeRegion)) :
      μ = 0 ∨ μ = 1 := by
    by_cases hzero : μ = 0
    · exact Or.inl hzero
    by_cases hone : μ = 1
    · exact Or.inr hone
    simp [classifySlope, hzero, hone] at hμ
    split at hμ <;> simp_all
  have slope_transform (hQ : 0 < Q) (start : AffineLine) (g : ℕ) :
      (start.transform Q g).slope Q =
        (2 : ℚ) ^ g * start.slope Q - 1 := by
    have hQ0 : (Q : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hQ)
    have hH0 : (start.H : ℚ) ≠ 0 := by
      exact_mod_cast (ne_of_gt start.H_pos)
    simp only [AffineLine.slope, AffineLine.transform]
    push_cast
    field_simp [hQ0, hH0]
  have boundary_gap_le_one (hQ : 0 < Q) (start : AffineLine) (g : ℕ)
      (hstart : classifySlope (start.slope Q) ∈
        ({SlopeRegion.boundaryZero, SlopeRegion.boundaryOne} : Set SlopeRegion))
      (hnext : classifySlope ((start.transform Q g).slope Q) ∈
        ({SlopeRegion.boundaryZero, SlopeRegion.boundaryOne} : Set SlopeRegion)) :
      g ≤ 1 := by
    rcases boundary_slope (start.slope Q) hstart with hzero | hone
    · rcases boundary_slope ((start.transform Q g).slope Q) hnext with hnextzero | hnextone
      · rw [slope_transform hQ start g, hzero] at hnextzero
        norm_num at hnextzero
      · rw [slope_transform hQ start g, hzero] at hnextone
        norm_num at hnextone
    · rcases boundary_slope ((start.transform Q g).slope Q) hnext with hnextzero | hnextone
      · by_contra hg
        have hg2 : 2 ≤ g := by omega
        have hpow : (2 : ℚ) ^ 2 ≤ (2 : ℚ) ^ g :=
          pow_le_pow_right₀ (by norm_num) hg2
        rw [slope_transform hQ start g, hone] at hnextzero
        norm_num at hnextzero
        nlinarith
      · by_contra hg
        have hg2 : 2 ≤ g := by omega
        have hpow : (2 : ℚ) ^ 2 ≤ (2 : ℚ) ^ g :=
          pow_le_pow_right₀ (by norm_num) hg2
        rw [slope_transform hQ start g, hone] at hnextone
        norm_num at hnextone
        nlinarith
  have span_bound : ∀ (start : AffineLine) (word : GapWord),
      IsBoundaryTransition Q start word →
      (∀ g ∈ word, g ≤ L + Cgap) →
      word.span ≤ word.length + (L + Cgap) := by
    intro start word
    induction word generalizing start with
    | nil => simp [GapWord.span]
    | cons g gs ih =>
        intro htransition hword
        rcases htransition with hempty | ⟨hboundary, hfinish⟩
        · simp at hempty
        · by_cases hgs : gs = []
          · subst gs
            have hg := hword g (by simp)
            simp only [GapWord.span, List.sum_cons, List.sum_nil, List.length_cons,
              List.length_nil]
            omega
          · have hQ : 0 < Q := by
              by_contra hnot
              have hQzero : Q = 0 := Nat.eq_zero_of_not_pos hnot
              subst Q
              rcases hfinish with ⟨finish, _htrajectory, hexterior⟩
              simp [AffineLine.slope, classifySlope] at hexterior
            rcases hboundary 0 (by simp) with ⟨initial, hinitial, hinitialBoundary⟩
            have hinitial_eq : initial = start := by
              apply trajectory_nil_eq start initial
              simpa using hinitial
            subst initial
            have hgsLength : 0 < gs.length := List.length_pos_iff.mpr hgs
            rcases hboundary 1 (by simp; omega) with ⟨next, hnext, hnextBoundary⟩
            have hnextTail :
                SharedGapTrajectory Q (start.transform Q g) [] next :=
              (trajectory_cons_iff start next g []).mp (by simpa using hnext)
            have hnext_eq : next = start.transform Q g :=
              trajectory_nil_eq (start.transform Q g) next hnextTail
            subst next
            have hg : g ≤ 1 :=
              boundary_gap_le_one hQ start g hinitialBoundary hnextBoundary
            have htailTransition :
                IsBoundaryTransition Q (start.transform Q g) gs := by
              right
              constructor
              · intro r hr
                rcases hboundary (r + 1) (by simp; omega) with
                  ⟨state, hstate, hstateBoundary⟩
                refine ⟨state, ?_, hstateBoundary⟩
                apply (trajectory_cons_iff start state g (gs.take r)).mp
                simpa [List.take_succ_cons] using hstate
              · rcases hfinish with ⟨finish, htrajectory, hexterior⟩
                exact ⟨finish,
                  (trajectory_cons_iff start finish g gs).mp htrajectory,
                  hexterior⟩
            have htailGap : ∀ x ∈ gs, x ≤ L + Cgap := by
              intro x hx
              exact hword x (by simp [hx])
            have htail := ih (start.transform Q g) htailTransition htailGap
            have htail' : gs.sum ≤ gs.length + (L + Cgap) := by
              simpa only [GapWord.span] using htail
            simp only [GapWord.span, List.sum_cons, List.length_cons]
            omega
  have hspan := span_bound line gaps htrans hgap
  have hscale : L + Cgap ≤ 2 * (L + Cgap) := by omega
  omega

private theorem classifySlope_mem_boundary_iff (μ : ℚ) :
    classifySlope μ ∈
        ({SlopeRegion.boundaryZero, SlopeRegion.boundaryOne} : Set SlopeRegion) ↔
      μ = 0 ∨ μ = 1 := by
  constructor
  · intro h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h
    · left
      unfold classifySlope at h
      by_cases h0 : μ = 0
      · exact h0
      rw [if_neg h0] at h
      split at h
      next h1 => simp_all
      next h1 =>
        split at h <;> simp_all
    · right
      unfold classifySlope at h
      by_cases h0 : μ = 0
      · simp [h0] at h
      rw [if_neg h0] at h
      by_cases h1 : μ = 1
      · exact h1
      rw [if_neg h1] at h
      split at h <;> simp_all
  · rintro (rfl | rfl) <;> simp [classifySlope]

private theorem boundary_transform_of_nonexterior (Q g : ℕ) (hQ : 0 < Q)
    (hg : 1 ≤ g) (line : AffineLine)
    (hline : classifySlope (line.slope Q) ∈
      ({SlopeRegion.boundaryZero, SlopeRegion.boundaryOne} : Set SlopeRegion))
    (hnext : classifySlope ((line.transform Q g).slope Q) ≠ .exterior) :
    classifySlope ((line.transform Q g).slope Q) ∈
      ({SlopeRegion.boundaryZero, SlopeRegion.boundaryOne} : Set SlopeRegion) := by
  rcases (classifySlope_mem_boundary_iff _).mp hline with hzero | hone
  · have hslope : (line.transform Q g).slope Q = -1 := by
      rw [AffineLine.slope_transform Q hQ, hzero]
      ring
    exfalso
    apply hnext
    rw [hslope, classifySlope_eq_exterior_iff]
    exact Or.inl (by norm_num)
  · by_cases hg1 : g = 1
    · subst g
      apply (classifySlope_mem_boundary_iff _).2
      right
      rw [AffineLine.slope_transform Q hQ, hone]
      norm_num
    · have hg2 : 2 ≤ g := by omega
      have hpow : (4 : ℚ) ≤ (2 : ℚ) ^ g := by
        have hpow' := pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) hg2
        norm_num at hpow' ⊢
        exact hpow'
      exfalso
      apply hnext
      rw [AffineLine.slope_transform Q hQ, hone,
        classifySlope_eq_exterior_iff]
      right
      nlinarith

private theorem boundary_before_first_exterior (Q : ℕ) (hQ : 0 < Q) :
    ∀ (line : AffineLine) (word : GapWord),
      word.Positive →
      classifySlope (line.slope Q) ∈
        ({SlopeRegion.boundaryZero, SlopeRegion.boundaryOne} : Set SlopeRegion) →
      (∀ r < word.length,
        classifySlope ((line.transformWord Q (word.take r)).slope Q) ≠ .exterior) →
      ∀ r < word.length,
        classifySlope ((line.transformWord Q (word.take r)).slope Q) ∈
          ({SlopeRegion.boundaryZero, SlopeRegion.boundaryOne} : Set SlopeRegion) := by
  intro line word
  induction word generalizing line with
  | nil => simp
  | cons g gs ih =>
      intro hpos hline hbefore r hr
      cases r with
      | zero => simpa only [List.take_zero, AffineLine.transformWord] using hline
      | succ r =>
          have hrTail : r < gs.length := by simpa using hr
          have hgsNonempty : gs ≠ [] := List.ne_nil_of_length_pos
            (lt_of_le_of_lt (Nat.zero_le r) hrTail)
          have hg : 1 ≤ g := hpos g (by simp)
          have hnextNon :
              classifySlope ((line.transform Q g).slope Q) ≠ .exterior := by
            have := hbefore 1 (by simp; exact List.length_pos_iff.mpr hgsNonempty)
            simpa only [List.take_succ_cons, List.take_zero,
              AffineLine.transformWord] using this
          have hnextBoundary := boundary_transform_of_nonexterior Q g hQ hg
            line hline hnextNon
          have htailPos : GapWord.Positive gs := by
            intro x hx
            exact hpos x (by simp [hx])
          have htailBefore : ∀ q < gs.length,
              classifySlope
                (((line.transform Q g).transformWord Q (gs.take q)).slope Q) ≠
                  .exterior := by
            intro q hq
            have := hbefore (q + 1) (by simpa using Nat.succ_lt_succ hq)
            simpa only [List.take_succ_cons, AffineLine.transformWord] using this
          simpa only [List.take_succ_cons, AffineLine.transformWord] using
            ih (line.transform Q g) htailPos hnextBoundary htailBefore r hrTail

private theorem take_isPrefix (word : GapWord) (r : ℕ) :
    (word.take r).IsPrefix word := by
  exact ⟨word.drop r, List.take_append_drop r word⟩

private theorem exists_first_noninterior (Q : ℕ) (line : AffineLine)
    (word : GapWord) (hnot : ¬ IsInteriorTrajectory Q line word) :
    ∃ j ≤ word.length,
      classifySlope ((line.transformWord Q (word.take j)).slope Q) ≠ .interior ∧
      ∀ r < j,
        classifySlope ((line.transformWord Q (word.take r)).slope Q) = .interior := by
  have hexists : ∃ j : ℕ, j ≤ word.length ∧
      classifySlope ((line.transformWord Q (word.take j)).slope Q) ≠ .interior := by
    by_contra hnone
    apply hnot
    intro r hr
    refine ⟨line.transformWord Q (word.take r),
      (sharedGapTrajectory_iff_transformWord Q line _ _).2 rfl, ?_⟩
    by_contra hregion
    exact hnone ⟨r, hr, hregion⟩
  let j := Nat.find hexists
  have hj := Nat.find_spec hexists
  refine ⟨j, hj.1, hj.2, ?_⟩
  intro r hr
  by_contra hregion
  exact (Nat.find_min hexists hr) ⟨le_trans (Nat.le_of_lt hr) hj.1, hregion⟩

private theorem isBoundaryTransition_of_first_exterior
    (Q : ℕ) (hQ : 0 < Q) (line : AffineLine) (word : GapWord)
    (hpos : word.Positive)
    (hline : classifySlope (line.slope Q) ∈
      ({SlopeRegion.boundaryZero, SlopeRegion.boundaryOne} : Set SlopeRegion))
    (hbefore : ∀ r < word.length,
      classifySlope ((line.transformWord Q (word.take r)).slope Q) ≠ .exterior)
    (hfinal : classifySlope ((line.transformWord Q word).slope Q) = .exterior) :
    IsBoundaryTransition Q line word := by
  by_cases hnil : word = []
  · exact Or.inl hnil
  right
  constructor
  · intro r hr
    refine ⟨line.transformWord Q (word.take r),
      (sharedGapTrajectory_iff_transformWord Q line _ _).2 rfl, ?_⟩
    exact boundary_before_first_exterior Q hQ line word hpos hline hbefore r hr
  · refine ⟨line.transformWord Q word,
      (sharedGapTrajectory_iff_transformWord Q line _ _).2 rfl, hfinal⟩

private theorem exists_virtual_boundary_transition
    (Q : ℕ) (hQ : 0 < Q) (line : AffineLine) (word : GapWord)
    (hpos : word.Positive)
    (hline : classifySlope (line.slope Q) ∈
      ({SlopeRegion.boundaryZero, SlopeRegion.boundaryOne} : Set SlopeRegion))
    (hnone : ∀ r ≤ word.length,
      classifySlope ((line.transformWord Q (word.take r)).slope Q) ≠ .exterior) :
    ∃ exitGap : ℕ, 1 ≤ exitGap ∧ exitGap ≤ 2 ∧
      IsBoundaryTransition Q line (word ++ [exitGap]) := by
  have hproperDummy : ∀ r < (word ++ [1]).length,
      classifySlope ((line.transformWord Q ((word ++ [1]).take r)).slope Q) ≠
        .exterior := by
    intro r hr
    have hrle : r ≤ word.length := by simpa using hr
    rw [List.take_append_of_le_length hrle]
    exact hnone r hrle
  have hposDummy : (word ++ [1]).Positive := by
    intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hpos g hg
    · norm_num
  have hendBoundary :
      classifySlope ((line.transformWord Q word).slope Q) ∈
        ({SlopeRegion.boundaryZero, SlopeRegion.boundaryOne} : Set SlopeRegion) := by
    have h := boundary_before_first_exterior Q hQ line (word ++ [1])
      hposDummy hline hproperDummy word.length (by simp)
    simpa [List.take_append_of_le_length (le_refl word.length)] using h
  rcases (classifySlope_mem_boundary_iff _).mp hendBoundary with hzero | hone
  · refine ⟨1, by norm_num, by norm_num, ?_⟩
    apply isBoundaryTransition_of_first_exterior Q hQ line (word ++ [1])
      hposDummy hline hproperDummy
    simp only [AffineLine.transformWord_append, AffineLine.transformWord]
    rw [AffineLine.slope_transform Q hQ, hzero]
    norm_num [classifySlope]
  · let extended := word ++ [2]
    have hproper : ∀ r < extended.length,
        classifySlope ((line.transformWord Q (extended.take r)).slope Q) ≠
          .exterior := by
      intro r hr
      have hrle : r ≤ word.length := by simpa [extended] using hr
      simp only [extended, List.take_append_of_le_length hrle]
      exact hnone r hrle
    have hposExtended : extended.Positive := by
      intro g hg
      simp only [extended, List.mem_append, List.mem_singleton] at hg
      rcases hg with hg | rfl
      · exact hpos g hg
      · norm_num
    refine ⟨2, by norm_num, by norm_num, ?_⟩
    apply isBoundaryTransition_of_first_exterior Q hQ line extended
      hposExtended hline hproper
    simp only [extended, AffineLine.transformWord_append, AffineLine.transformWord]
    rw [AffineLine.slope_transform Q hQ, hone]
    norm_num [classifySlope]

theorem longExteriorSplit_of_no_longInterior
    (Q : ℕ) (hQ : 0 < Q) (line : AffineLine) (word : GapWord)
    (y : ℝ) (m cap : ℕ) (hy : 0 < y)
    (hpos : word.Positive) (hlen : word.length ≤ m)
    (hcapTwo : 2 ≤ cap) (hcap : ∀ g ∈ word, g ≤ cap)
    (hremaining : y / 2 ≤ (word.span : ℝ))
    (hno : ∀ u : GapWord, u.IsPrefix word →
      IsInteriorTrajectory Q line u → (u.span : ℝ) < y / 8)
    (hloss : ((m + 1 + 3 * cap : ℕ) : ℝ) ≤ y / 8) :
    ∃ before continuation : GapWord, ∃ exteriorLine : AffineLine,
      word = before ++ continuation ∧
      SharedGapTrajectory Q line before exteriorLine ∧
      (∀ r < before.length, ∀ state : AffineLine,
        SharedGapTrajectory Q line (before.take r) state →
          classifySlope (state.slope Q) ≠ .exterior) ∧
      classifySlope (exteriorLine.slope Q) = .exterior ∧
      IsExteriorTrajectory Q exteriorLine continuation ∧
      y / 4 ≤ (continuation.span : ℝ) := by
  have hnotFull : ¬ IsInteriorTrajectory Q line word := by
    intro hfull
    have hshort := hno word ⟨[], by simp⟩ hfull
    linarith
  obtain ⟨j, hjlen, hjnon, hjbefore⟩ :=
    exists_first_noninterior Q line word hnotFull
  let lineJ := line.transformWord Q (word.take j)
  have hprefixJ : (word.take j).IsPrefix word := take_isPrefix word j
  have hprefixJBound : (GapWord.span (word.take j) : ℝ) < y / 8 + cap := by
    cases j with
    | zero =>
        simp only [List.take_zero, GapWord.span, List.sum_nil, Nat.cast_zero]
        positivity
    | succ i =>
        have hiLen : i < word.length := lt_of_lt_of_le (Nat.lt_succ_self i) hjlen
        have hint : IsInteriorTrajectory Q line (word.take i) := by
          intro r hr
          have hriLe : r ≤ i := hr.trans (List.length_take_le i word)
          have hri : r < i + 1 := Nat.lt_succ_iff.mpr hriLe
          refine ⟨line.transformWord Q (word.take r), ?_, hjbefore r hri⟩
          have htake : (word.take i).take r = word.take r := by
            rw [List.take_take, min_eq_left hriLe]
          simpa only [htake] using
            (sharedGapTrajectory_iff_transformWord Q line (word.take r)
              (line.transformWord Q (word.take r))).2 rfl
        have hshort := hno (word.take i) (take_isPrefix word i) hint
        have hsum := List.sum_take_succ word i hiLen
        have helem : word[i] ≤ cap := hcap word[i] (List.getElem_mem hiLen)
        have hsumReal : ((word.take (i + 1)).sum : ℝ) =
            ((word.take i).sum : ℝ) + word[i] := by exact_mod_cast hsum
        have helemReal : (word[i] : ℝ) ≤ cap := by exact_mod_cast helem
        change ((word.take i).sum : ℝ) < y / 8 at hshort
        change ((word.take (i + 1)).sum : ℝ) < y / 8 + cap
        linarith
  have hcapLoss : (cap : ℝ) ≤ y / 8 := by
    have hnat : cap ≤ m + 1 + 3 * cap := by omega
    exact (by exact_mod_cast hnat : (cap : ℝ) ≤ (m + 1 + 3 * cap : ℕ)).trans hloss
  by_cases hjExterior : classifySlope (lineJ.slope Q) = .exterior
  · refine ⟨word.take j, word.drop j, lineJ, ?_, ?_, ?_, hjExterior, ?_, ?_⟩
    · exact (List.take_append_drop j word).symm
    · exact (sharedGapTrajectory_iff_transformWord Q line _ _).2 rfl
    · intro r hr state hstate
      have hrj : r < j := by simpa [List.length_take, hjlen] using hr
      have htake : (word.take j).take r = word.take r := by
        rw [List.take_take, min_eq_left (Nat.le_of_lt hrj)]
      have hstateEq :=
        (sharedGapTrajectory_iff_transformWord Q line _ state).1 hstate
      rw [htake] at hstateEq
      subst state
      rw [hjbefore r hrj]
      decide
    · apply isExteriorTrajectory_of_positive Q hQ lineJ (word.drop j)
      · intro g hg
        exact hpos g (List.mem_of_mem_drop hg)
      · exact hjExterior
    · have hsum : (word.span : ℝ) =
          (GapWord.span (word.take j) : ℝ) +
            (GapWord.span (word.drop j) : ℝ) := by
        have := congrArg (fun w : GapWord => (w.span : ℝ))
          (List.take_append_drop j word)
        simpa only [GapWord.span, List.sum_append, Nat.cast_add] using this.symm
      linarith
  · have hjnon' : classifySlope (lineJ.slope Q) ≠ .interior := by
      simpa only [lineJ] using hjnon
    have hjBoundary : classifySlope (lineJ.slope Q) ∈
        ({SlopeRegion.boundaryZero, SlopeRegion.boundaryOne} : Set SlopeRegion) := by
      cases hregion : classifySlope (lineJ.slope Q) with
      | interior => exact (hjnon' hregion).elim
      | boundaryZero => simp
      | boundaryOne => simp
      | exterior => exact (hjExterior hregion).elim
    let tail := word.drop j
    have htailPos : GapWord.Positive tail := by
      intro g hg
      exact hpos g (List.mem_of_mem_drop hg)
    have htailLen : tail.length ≤ m := by
      have htailWord : tail.length ≤ word.length := by
        dsimp [tail]
        rw [List.length_drop]
        omega
      exact htailWord.trans hlen
    have htailCap : ∀ g ∈ tail, g ≤ cap := by
      intro g hg
      exact hcap g (List.mem_of_mem_drop hg)
    by_cases hexists : ∃ t : ℕ, t ≤ tail.length ∧
        classifySlope ((lineJ.transformWord Q (tail.take t)).slope Q) = .exterior
    · let t := Nat.find hexists
      have ht := Nat.find_spec hexists
      have htBefore : ∀ r < t,
          classifySlope ((lineJ.transformWord Q (tail.take r)).slope Q) ≠
            .exterior := by
        intro r hr hext
        exact (Nat.find_min hexists hr) ⟨le_trans (Nat.le_of_lt hr) ht.1, hext⟩
      let transition := tail.take t
      let exteriorLine := lineJ.transformWord Q transition
      have htransitionLen : transition.length ≤ m := by
        dsimp [transition]
        rw [List.length_take_of_le ht.1]
        exact ht.1.trans htailLen
      have htransitionCap : ∀ g ∈ transition, g ≤ cap := by
        intro g hg
        exact htailCap g (List.mem_of_mem_take hg)
      have htransitionPos : GapWord.Positive transition := by
        intro g hg
        exact htailPos g (List.mem_of_mem_take hg)
      have htransitionBoundary : IsBoundaryTransition Q lineJ transition := by
        apply isBoundaryTransition_of_first_exterior Q hQ lineJ transition
          htransitionPos hjBoundary
        · intro r hr
          have htransitionLength : transition.length = t := by
            dsimp [transition]
            exact List.length_take_of_le ht.1
          have hr' : r < t := by simpa only [htransitionLength] using hr
          have htake : transition.take r = tail.take r := by
            simp [transition, List.take_take, min_eq_left (Nat.le_of_lt hr')]
          simpa only [htake] using htBefore r hr'
        · simpa only [transition, exteriorLine] using ht.2
      have htransitionSpan : GapWord.span transition ≤ m + 2 * cap := by
        exact lem_boundary_stretch Q m cap 0 lineJ transition htransitionBoundary
          htransitionLen (by simpa using htransitionCap)
      let before := word.take (j + t)
      let continuation := word.drop (j + t)
      have hjtLen : j + t ≤ word.length := by
        have htlen : t ≤ tail.length := ht.1
        dsimp [tail] at htlen
        rw [List.length_drop] at htlen
        omega
      have hbeforeSplit : before = word.take j ++ transition := by
        dsimp [before, transition, tail]
        exact List.take_add
      have hbeforeBound : (GapWord.span before : ℝ) < y / 4 := by
        have htransitionSpanReal : (GapWord.span transition : ℝ) ≤ m + 2 * cap := by
          exact_mod_cast htransitionSpan
        have hbeforeSpan : (GapWord.span before : ℝ) =
            (GapWord.span (word.take j) : ℝ) + GapWord.span transition := by
          have hnat : GapWord.span before =
              GapWord.span (word.take j) + GapWord.span transition := by
            change before.sum = (word.take j).sum + transition.sum
            rw [hbeforeSplit, List.sum_append]
          exact_mod_cast hnat
        have hloss' : ((m : ℝ) + 3 * cap) ≤ y / 8 := by
          have hnat : m + 3 * cap ≤ m + 1 + 3 * cap := by omega
          have hcast : ((m + 3 * cap : ℕ) : ℝ) ≤ y / 8 :=
            (by exact_mod_cast hnat :
              ((m + 3 * cap : ℕ) : ℝ) ≤ (m + 1 + 3 * cap : ℕ)).trans hloss
          simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hcast
        rw [hbeforeSpan]
        nlinarith
      refine ⟨before, continuation, exteriorLine, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact (List.take_append_drop (j + t) word).symm
      · rw [sharedGapTrajectory_iff_transformWord]
        dsimp [exteriorLine]
        rw [hbeforeSplit, AffineLine.transformWord_append]
      · intro r hr state hstate
        have hrjt : r < j + t := by
          simpa [before, List.length_take, hjtLen] using hr
        have htakeBefore : before.take r = word.take r := by
          dsimp [before]
          rw [List.take_take, min_eq_left (Nat.le_of_lt hrjt)]
        have hstateEq :=
          (sharedGapTrajectory_iff_transformWord Q line _ state).1 hstate
        rw [htakeBefore] at hstateEq
        subst state
        by_cases hrj : r < j
        · rw [hjbefore r hrj]
          decide
        · let q := r - j
          have hrEq : r = j + q := by dsimp [q]; omega
          have hqt : q < t := by dsimp [q]; omega
          have hstateRewrite :
              line.transformWord Q (word.take r) =
                lineJ.transformWord Q (tail.take q) := by
            rw [hrEq, List.take_add, AffineLine.transformWord_append]
          rw [hstateRewrite]
          exact htBefore q hqt
      · simpa only [exteriorLine, transition] using ht.2
      · apply isExteriorTrajectory_of_positive Q hQ exteriorLine continuation
        · intro g hg
          exact hpos g (List.mem_of_mem_drop hg)
        · simpa only [exteriorLine, transition] using ht.2
      · have hsum : (word.span : ℝ) =
            (GapWord.span before : ℝ) + (GapWord.span continuation : ℝ) := by
          have := congrArg (fun w : GapWord => (w.span : ℝ))
            (List.take_append_drop (j + t) word)
          simpa only [before, continuation, GapWord.span, List.sum_append,
            Nat.cast_add] using this.symm
        linarith
    · have hnone : ∀ t ≤ tail.length,
          classifySlope ((lineJ.transformWord Q (tail.take t)).slope Q) ≠
            .exterior := by
        intro t ht hext
        exact hexists ⟨t, ht, hext⟩
      obtain ⟨exitGap, hexitPos, hexitTwo, hvirtual⟩ :=
        exists_virtual_boundary_transition Q hQ lineJ tail htailPos hjBoundary hnone
      have hvirtualLen : (tail ++ [exitGap]).length ≤ m + 1 := by
        simpa using Nat.add_le_add_right htailLen 1
      have hvirtualCap : ∀ g ∈ tail ++ [exitGap], g ≤ cap := by
        intro g hg
        simp only [List.mem_append, List.mem_singleton] at hg
        rcases hg with hg | rfl
        · exact htailCap g hg
        · exact hexitTwo.trans hcapTwo
      have hvirtualSpan := lem_boundary_stretch Q (m + 1) cap 0 lineJ
        (tail ++ [exitGap]) hvirtual hvirtualLen (by simpa using hvirtualCap)
      have htailSpan : GapWord.span tail ≤ m + 1 + 2 * cap := by
        have hsum : GapWord.span (tail ++ [exitGap]) =
            GapWord.span tail + exitGap := by
          simp [GapWord.span]
        rw [hsum] at hvirtualSpan
        omega
      have hwordSum : (word.span : ℝ) =
          (GapWord.span (word.take j) : ℝ) + (GapWord.span tail : ℝ) := by
        have := congrArg (fun w : GapWord => (w.span : ℝ))
          (List.take_append_drop j word)
        simpa only [tail, GapWord.span, List.sum_append, Nat.cast_add] using this.symm
      have htailSpanReal : (GapWord.span tail : ℝ) ≤ m + 1 + 2 * cap := by
        exact_mod_cast htailSpan
      have hlossReal : (m : ℝ) + 1 + 3 * cap ≤ y / 8 := by
        simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
          using hloss
      rw [hwordSum] at hremaining
      nlinarith

private theorem eventually_boundary_loss_le (κ : ℝ) (hκ : 0 < κ)
    (Cgap : ℕ) :
    ∃ Zloss : ℕ, ∀ Z0 : ℕ, Zloss ≤ Z0 →
      ∀ᶠ L : ℕ in atTop,
        let m := Nat.floor (κ * (L : ℝ)) + 1
        (((m + 1 + 3 * (L + Cgap + 1) : ℕ) : ℝ) ≤
          (m : ℝ) * Z0 / 8) := by
  let coeff : ℝ := 8 * (2 + 3 / κ)
  let Zloss := Nat.ceil coeff
  refine ⟨Zloss, ?_⟩
  intro Z0 hZ0
  let constant : ℕ := 1 + 3 * (Cgap + 1)
  let L0 : ℕ := Nat.ceil ((constant : ℝ) / κ)
  filter_upwards [eventually_ge_atTop L0] with L hL
  dsimp only
  let m := Nat.floor (κ * (L : ℝ)) + 1
  have hκLnonneg : 0 ≤ κ * (L : ℝ) :=
    mul_nonneg hκ.le (Nat.cast_nonneg L)
  have hmLower : κ * (L : ℝ) < (m : ℝ) := by
    dsimp [m]
    simpa only [Nat.cast_add, Nat.cast_one] using
      (Nat.lt_floor_add_one (κ * (L : ℝ)))
  have hconstantDiv : (constant : ℝ) / κ ≤ (L : ℝ) := by
    calc
      (constant : ℝ) / κ ≤ Nat.ceil ((constant : ℝ) / κ) := Nat.le_ceil _
      _ = (L0 : ℕ) := rfl
      _ ≤ L := by exact_mod_cast hL
  have hconstant : (constant : ℝ) ≤ κ * (L : ℝ) := by
    have := (div_le_iff₀ hκ).mp hconstantDiv
    simpa [mul_comm] using this
  have hconstantM : (constant : ℝ) ≤ m := hconstant.trans hmLower.le
  have hLover : (L : ℝ) < (m : ℝ) / κ := by
    exact (lt_div_iff₀ hκ).2 (by simpa [mul_comm] using hmLower)
  have hcoeffZ : coeff ≤ (Z0 : ℝ) := by
    calc
      coeff ≤ Nat.ceil coeff := Nat.le_ceil coeff
      _ = (Zloss : ℕ) := rfl
      _ ≤ Z0 := by exact_mod_cast hZ0
  have hmPos : (0 : ℝ) < m := by positivity
  have hlossExpand :
      (((m + 1 + 3 * (L + Cgap + 1) : ℕ) : ℝ)) =
        (m : ℝ) + 3 * L + constant := by
    dsimp [constant]
    push_cast
    ring
  rw [hlossExpand]
  have hbound : (m : ℝ) + 3 * L + constant <
      (2 + 3 / κ) * m := by
    have hthree : 3 * (L : ℝ) < (3 / κ) * m := by
      have := mul_lt_mul_of_pos_left hLover (by norm_num : (0 : ℝ) < 3)
      field_simp at this ⊢
      nlinarith
    nlinarith
  have hcoeffMul : 8 * ((2 + 3 / κ) * m) ≤ (Z0 : ℝ) * m := by
    have := mul_le_mul_of_nonneg_right hcoeffZ hmPos.le
    simpa [coeff, mul_assoc, mul_comm, mul_left_comm] using this
  nlinarith

/-- Paper label: `lem:dichotomy` (Section 5).  The cutoff is selected before
the numerator/support family; only the eventual scale may depend on that
family.  The gap constant must carry the uniform theorem supplied by
`lem_gap`, rather than being an arbitrary natural number. -/
theorem lem_dichotomy (context : FixedScaleContext)
    (gap : GapParams context.Q) :
    ∃ Zmin : ℕ, ∀ Z0 : ℕ, Zmin ≤ Z0 →
      ∀ F : ScaleFamily, F.MatchesContext context →
        ∀ᶠ L : ℕ in atTop, ∀ e : WindowThreshold,
          e ∈ (F.system L).largePairs Z0 →
          IsFrequentPrefix (F.system L) Z0
            (initialLongPrefix (F.system L) e.1) →
          (LongInteriorPair (F.system L) Z0 e ∨
            LongExteriorPair (F.system L) Z0 e) ∧
          ¬ (LongInteriorPair (F.system L) Z0 e ∧
            LongExteriorPair (F.system L) Z0 e) := by
  classical
  obtain ⟨Cline, Clock, hClock, hlocking⟩ :=
    lem_ap_locking context.Q context.Q_pos
  obtain ⟨CQ, hCQ, hfirst⟩ := lem_firstdeep_exists context
  obtain ⟨Zloss, hZloss⟩ :=
    eventually_boundary_loss_le context.entropy.kappa
      context.entropy.kappa_pos gap.Cgap
  let Zfirst := Nat.ceil
    (2 * context.structural.Caff / context.entropy.kappa)
  let Zmin := max Zfirst Zloss
  refine ⟨Zmin, ?_⟩
  intro Z0 hZ0 F hF
  have hZfirst : Zfirst ≤ Z0 := (le_max_left _ _).trans hZ0
  have hZlossBound : Zloss ≤ Z0 := (le_max_right _ _).trans hZ0
  have hdiff : 0 < context.structural.Caff - 2 := by
    linarith [context.structural.Caff_gt]
  let Lline := Nat.ceil (((Cline : ℝ) + 1) /
    (context.structural.Caff - 2))
  filter_upwards [hfirst Z0 (by simpa only [Zfirst] using hZfirst) F hF,
    eventually_rawWindowGap_le context gap F hF,
    hZloss Z0 hZlossBound,
    eventually_ge_atTop Lline,
    eventually_ge_atTop 1] with L hfirstL hgapL hlossL hLline hLone
  intro e he hfrequent
  let W := F.system L
  let p := initialLongPrefix W e.1
  let suffix := actualPostPrefixGaps W e.1
  have hlevel : W.L = L := F.level_eq L
  have hstruct : W.structural = context.structural :=
    (F.structural_eq L).trans hF.2.1
  have hentropy : W.entropy = context.entropy :=
    (F.entropy_eq L).trans hF.2.2.1
  have hden : W.rational.eta.den = context.Q := by
    change (F.system L).rational.eta.den = context.Q
    rw [F.rational_eq]
    exact hF.1
  have hWQpos : 0 < W.rational.eta.den := by
    rw [hden]
    exact context.Q_pos
  have hfirstE := hfirstL e he
  dsimp only at hfirstE
  have hpLower : context.structural.Caff * (L : ℝ) < (p.span : ℝ) := by
    have hlower := hfirstE.1
    change W.structural.Caff * (W.L : ℝ) < (p.span : ℝ) at hlower
    rw [hlevel, hstruct] at hlower
    exact hlower
  have hlineScale : (Cline : ℝ) <
      (context.structural.Caff - 2) * (L : ℝ) := by
    have hquot : ((Cline : ℝ) + 1) /
        (context.structural.Caff - 2) ≤ (L : ℝ) := by
      calc
        ((Cline : ℝ) + 1) / (context.structural.Caff - 2) ≤ Lline :=
          Nat.le_ceil _
        _ ≤ L := by exact_mod_cast hLline
    have hmul := (div_le_iff₀ hdiff).mp hquot
    nlinarith
  have hpLongReal : (2 * L + Cline : ℕ) < (p.span : ℝ) := by
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    nlinarith
  have hpLong : 2 * W.L + Cline < p.span := by
    rw [hlevel]
    exact_mod_cast hpLongReal
  have heHigh : e.1 ∈ highAnchors W Z0 := by
    rw [highAnchors, Finset.mem_filter]
    exact ⟨he.1.1, e.2, he.1.2, he.2⟩
  have hpSet : p ∈ initialPrefixes W Z0 := by
    rw [initialPrefixes, Finset.mem_image]
    exact ⟨e.1, heHigh, rfl⟩
  obtain ⟨line, hline, hprimitive, hstep⟩ :=
    hlocking W hden Z0 p hpSet hpLong hfrequent
  have hdisjoint : ¬ (LongInteriorPair W Z0 e ∧
      LongExteriorPair W Z0 e) := by
    rintro ⟨hinterior, hexterior⟩
    exact hexterior.2.2.1 hinterior
  by_cases hinterior : LongInteriorPair W Z0 e
  · exact ⟨Or.inl hinterior, hdisjoint⟩
  · have hmEq : W.m =
        Nat.floor (context.entropy.kappa * (L : ℝ)) + 1 := by
      rw [WindowSystem.m]
      change (F.system L).s + 1 = _
      rw [F.offset_eq, hF.2.2.1]
    have hlossBase :
        (((W.m + 1 + 3 * (L + gap.Cgap + 1) : ℕ) : ℝ) ≤
          (W.m : ℝ) * Z0 / 8) := by
      simpa only [hmEq] using hlossL
    have hlarge : (W.m : ℝ) * (Z0 : ℝ) < W.excess e := by
      simpa only [Set.mem_setOf_eq, Nat.cast_mul] using he.2
    have hy : 0 < W.excess e := by
      have hnonneg : 0 ≤ (W.m : ℝ) * (Z0 : ℝ) := by positivity
      exact hnonneg.trans_lt hlarge
    have hlossExcess :
        (((W.m + 1 + 3 * (L + gap.Cgap + 1) : ℕ) : ℝ) ≤
          W.excess e / 8) := by
      exact hlossBase.trans (by nlinarith)
    have hsuffixNat : W.rawWindowSpan e.1 = p.span + suffix.span := by
      have hraw : (W.rawWindowGapWord e.1).span = W.rawWindowSpan e.1 := by
        unfold WindowSystem.rawWindowGapWord WindowSystem.rawWindowSpan
        split <;> rfl
      rw [← hraw]
      simpa only [p, suffix] using actualPostPrefixGaps_span W e.1
    have hsuffixEq :
        ((W.rawWindowSpan e.1 : ℝ) - (p.span : ℝ)) = suffix.span := by
      have hcast : (W.rawWindowSpan e.1 : ℝ) =
          (p.span : ℝ) + suffix.span := by exact_mod_cast hsuffixNat
      linarith
    have hsuffixRemaining : W.excess e / 2 ≤ (suffix.span : ℝ) := by
      rw [← hsuffixEq]
      simpa only [p] using hfirstE.2.2
    have hsuffixPos : suffix.Positive := actualPostPrefixGaps_positive W e.1
    have hsuffixLen : suffix.length ≤ W.m :=
      actualPostPrefixGaps_length_le W e.1
    let cap := L + gap.Cgap + 1
    have hcapTwo : 2 ≤ cap := by dsimp [cap]; omega
    have hsuffixCap : ∀ g ∈ suffix, g ≤ cap := by
      intro g hg
      exact hgapL e.1 he.1.1 g (List.mem_of_mem_drop hg)
    have hnoLong : ∀ u : GapWord, u.IsPrefix suffix →
        IsInteriorTrajectory W.rational.eta.den line u →
          (u.span : ℝ) < W.excess e / 8 := by
      intro u hu htrajectory
      by_contra hnot
      apply hinterior
      refine ⟨he, hfrequent, line, u, ?_, htrajectory, le_of_not_gt hnot⟩
      refine ⟨hline, hu, ?_⟩
      exact ⟨line.transformWord W.rational.eta.den u,
        (sharedGapTrajectory_iff_transformWord _ _ _ _).2 rfl⟩
    obtain ⟨before, continuation, exteriorLine, hsplit, hbeforeTrajectory,
        hfirstExterior, hexteriorSlope, hexteriorTrajectory, hcontinuationSpan⟩ :=
      longExteriorSplit_of_no_longInterior W.rational.eta.den hWQpos line
        suffix (W.excess e) W.m cap hy hsuffixPos hsuffixLen hcapTwo
        hsuffixCap hsuffixRemaining hnoLong (by simpa only [cap] using hlossExcess)
    have hactual : IsActualFirstExteriorContinuation W Z0 e
        exteriorLine continuation := by
      refine ⟨line, exteriorLine.transformWord W.rational.eta.den continuation,
        before, [], hline, ?_, hbeforeTrajectory, hfirstExterior,
        hexteriorSlope, ?_⟩
      · simpa only [suffix, List.append_nil] using hsplit
      · exact (sharedGapTrajectory_iff_transformWord _ _ _ _).2 rfl
    have hexteriorPair : LongExteriorPair W Z0 e := by
      refine ⟨he, hfrequent, hinterior, exteriorLine, continuation,
        hactual, hexteriorTrajectory, hcontinuationSpan⟩
    exact ⟨Or.inr hexteriorPair, hdisjoint⟩

end Erdos260

/-! Source module: Erdos260/Interior.lean -/

/-!
# Long-interior contribution

This module corresponds to Section 6 of the manuscript.
-/

noncomputable section

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal

namespace Erdos260

/-- Primitive normalization preserves the rational normalized slope. -/
theorem AffineLine.canonicalGeometricLine_slope (Q : ℕ) (hQ : 0 < Q)
    (line : AffineLine) :
    line.canonicalGeometricLine.slope Q = line.slope Q := by
  have hdpos : (0 : ℤ) < (line.directionGCD : ℤ) := by
    exact_mod_cast line.directionGCD_pos
  have hdne : (line.directionGCD : ℤ) ≠ 0 := ne_of_gt hdpos
  have hHfactor :
      line.primitiveHorizontalInt * (line.directionGCD : ℤ) = line.H :=
    Int.ediv_mul_cancel (Int.gcd_dvd_left line.H line.K)
  have hKfactor :
      line.primitiveVertical * (line.directionGCD : ℤ) = line.K :=
    Int.ediv_mul_cancel (Int.gcd_dvd_right line.H line.K)
  have hdneQ : ((line.directionGCD : ℤ) : ℚ) ≠ 0 := by
    exact_mod_cast hdne
  have hpneQ : (line.primitiveHorizontalInt : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt line.primitiveHorizontalInt_pos)
  rw [GeometricLine.slope, AffineLine.slope]
  change ((line.primitiveVertical : ℤ) : ℚ) /
      ((Q : ℚ) * (line.canonicalGeometricLine.H : ℚ)) =
    (line.K : ℚ) / ((Q : ℚ) * (line.H : ℚ))
  have hHcast : (line.canonicalGeometricLine.H : ℚ) =
      (line.primitiveHorizontalInt : ℚ) := by
    exact_mod_cast line.canonicalGeometricLine_H_cast
  rw [hHcast]
  have hHfactorQ : (line.primitiveHorizontalInt : ℚ) *
      (line.directionGCD : ℚ) = (line.H : ℚ) := by
    exact_mod_cast hHfactor
  have hKfactorQ : (line.primitiveVertical : ℚ) *
      (line.directionGCD : ℚ) = (line.K : ℚ) := by
    exact_mod_cast hKfactor
  rw [← hHfactorQ, ← hKfactorQ]
  field_simp [hpneQ, hdneQ]
  exact (mul_div_cancel_right₀ (line.primitiveVertical : ℚ) hdneQ).symm

/-- Exact one-gap monodromy for the integer intercept numerator. -/
theorem AffineLine.interceptNumerator_transform (Q g : ℕ)
    (line : AffineLine) :
    (line.transform Q g).interceptNumerator =
      (2 : ℤ) ^ g * line.interceptNumerator -
        (2 : ℤ) ^ g * line.K * g := by
  simp only [AffineLine.interceptNumerator, AffineLine.transform]
  ring

/-- Applying one fixed shared word to two lines with the same direction
multiplies their intercept-numerator difference by the exact dyadic span. -/
theorem AffineLine.interceptDifference_transformWord (Q : ℕ)
    (u v : AffineLine) (w : GapWord) (hH : u.H = v.H) (hK : u.K = v.K) :
    (u.transformWord Q w).interceptNumerator -
        (v.transformWord Q w).interceptNumerator =
      (2 : ℤ) ^ w.span *
        (u.interceptNumerator - v.interceptNumerator) := by
  induction w generalizing u v with
  | nil => simp [AffineLine.transformWord, GapWord.span]
  | cons g gs ih =>
      simp only [AffineLine.transformWord]
      have hH' : (u.transform Q g).H = (v.transform Q g).H := by
        simpa [AffineLine.transform] using hH
      have hK' : (u.transform Q g).K = (v.transform Q g).K := by
        simp only [AffineLine.transform]
        rw [hH, hK]
      rw [ih (u.transform Q g) (v.transform Q g) hH' hK']
      rw [AffineLine.interceptNumerator_transform,
        AffineLine.interceptNumerator_transform]
      simp only [GapWord.span, List.sum_cons, pow_add]
      rw [hK]
      ring

/-- For a primitive raw direction, canonical geometric membership is exactly
membership in the original integer parameterization. -/
theorem AffineLine.contains_of_canonicalGeometricLine_of_primitive
    (line : AffineLine) (hprimitive : Int.gcd line.H line.K = 1)
    (x r : ℤ) (hcontains : line.canonicalGeometricLine.Contains x r) :
    line.Contains x r := by
  have hcanonicalH : (line.canonicalGeometricLine.H : ℤ) = line.H := by
    rw [line.canonicalGeometricLine_H_cast]
    simp [AffineLine.primitiveHorizontalInt, AffineLine.directionGCD,
      hprimitive]
  have hcanonicalK : line.canonicalGeometricLine.K = line.K := by
    simp [AffineLine.canonicalGeometricLine, AffineLine.primitiveVertical,
      AffineLine.directionGCD, hprimitive]
  have hcanonicalIntercept : line.canonicalGeometricLine.intercept =
      line.interceptNumerator := by
    simp [AffineLine.canonicalGeometricLine, AffineLine.directionGCD,
      hprimitive]
  rw [GeometricLine.Contains, hcanonicalH, hcanonicalK,
    hcanonicalIntercept] at hcontains
  have hmul : line.H * (r - line.C) = line.K * (x - line.A) := by
    simp only [AffineLine.interceptNumerator] at hcontains
    linarith
  have hdvdMul : line.H ∣ line.K * (x - line.A) := by
    exact ⟨r - line.C, hmul.symm⟩
  have hdvd : line.H ∣ x - line.A :=
    Int.dvd_of_dvd_mul_right_of_gcd_one hdvdMul hprimitive
  rcases hdvd with ⟨t, ht⟩
  refine ⟨t, ?_, ?_⟩
  · linarith
  · have hHne : line.H ≠ 0 := ne_of_gt line.H_pos
    apply mul_left_cancel₀ hHne
    calc
      line.H * r = line.H * line.C + line.K * (x - line.A) := by
        linarith
      _ = line.H * (line.C + line.K * t) := by
        rw [ht]
        ring

/-- A stabilized interior segment with one reduced odd denominator. -/
structure OddDenominatorSegment where
  startLine : AffineLine
  gaps : GapWord
  slopes : List ℚ
  q : ℕ

namespace OddDenominatorSegment

/-- The exact normalized slopes along every prefix of a shared gap word. -/
def slopeTrace (Q : ℕ) (line : AffineLine) (gaps : GapWord) : List ℚ :=
  (List.range (gaps.length + 1)).map fun r =>
    (line.transformWord Q (gaps.take r)).slope Q

def Valid (Q : ℕ) (segment : OddDenominatorSegment) : Prop :=
  0 < Q ∧ segment.gaps.Positive ∧
    Int.gcd segment.startLine.H segment.startLine.K = 1 ∧
    segment.slopes = slopeTrace Q segment.startLine segment.gaps ∧
    1 < segment.q ∧ Odd segment.q ∧
    ∀ μ ∈ segment.slopes,
      μ ∈ Set.Ioo (0 : ℚ) 1 ∧ μ.den = segment.q ∧ Odd μ.num

def span (segment : OddDenominatorSegment) : ℕ := segment.gaps.span

def gapCount (segment : OddDenominatorSegment) : ℕ := segment.gaps.length

end OddDenominatorSegment

/-- A retained completed logarithmic block. -/
structure LowGapBlock where
  offset : ℕ
  gaps : GapWord
  deriving DecidableEq, Repr

namespace LowGapBlock

def span (block : LowGapBlock) : ℕ := block.gaps.span

/-- The block occurs at its recorded offset in the supplied segment. -/
def OccursIn (segment : OddDenominatorSegment) (block : LowGapBlock) : Prop :=
  block.offset + block.gaps.length ≤ segment.gaps.length ∧
    (segment.gaps.drop block.offset).take block.gaps.length = block.gaps

end LowGapBlock

def blocksWithOffsetsFrom : ℕ → List GapWord → List LowGapBlock
  | _, [] => []
  | offset, gaps :: rest =>
      ⟨offset, gaps⟩ :: blocksWithOffsetsFrom (offset + gaps.length) rest

/-- The maximal initial list of completed blocks whose genuine post-block
suffix still has the required forward span. -/
private def forwardEligibleWords (remainder : GapWord) (forward : ℕ) :
    List GapWord → List GapWord
  | [] => []
  | block :: rest =>
      if forward ≤ GapWord.span (rest.flatten ++ remainder) then
        block :: forwardEligibleWords remainder forward rest
      else []

/-- The complementary final list discarded by the forward-span rule. -/
private def forwardDiscardedWords (remainder : GapWord) (forward : ℕ) :
    List GapWord → List GapWord
  | [] => []
  | block :: rest =>
      if forward ≤ GapWord.span (rest.flatten ++ remainder) then
        forwardDiscardedWords remainder forward rest
      else block :: rest

/-- Deterministically retained completed low-gap blocks.  The construction is
spatial: it depends on the segment and fixed band parameters, never on a
threshold coordinate. -/
def selectedBlocks (segment : OddDenominatorSegment) (B : ℝ)
    (ell Z forward : ℕ) : List LowGapBlock :=
  let decomposition :=
    GapWord.greedyDecompose segment.gaps (Nat.ceil (B * ell))
  let eligible :=
    forwardEligibleWords decomposition.remainder forward decomposition.completed
  (blocksWithOffsetsFrom 0 eligible).filter fun block =>
    Z * block.gaps.length ≤ 4 * block.span

/-- The equivalent pointwise form used by the encoding argument: forward
eligibility is tested separately at every completed-block offset. -/
private def pointwiseSelectedBlocks (segment : OddDenominatorSegment) (B : ℝ)
    (ell Z forward : ℕ) : List LowGapBlock :=
  let decomposition :=
    GapWord.greedyDecompose segment.gaps (Nat.ceil (B * ell))
  (blocksWithOffsetsFrom 0 decomposition.completed).filter fun block =>
    Z * block.gaps.length ≤ 4 * block.span ∧
      block.offset + block.gaps.length ≤ segment.gaps.length ∧
      forward ≤
        GapWord.span
          (segment.gaps.drop (block.offset + block.gaps.length))

/-- Data retained by the block encoding map `Σ`. -/
@[ext] structure BlockEncoding where
  D : ℕ
  Z : ℕ
  h : ℕ
  r : ℕ
  gaps : GapWord
  deriving DecidableEq

namespace BlockEncoding

def Valid (σ : BlockEncoding) : Prop :=
  (∃ k : ℕ, σ.D = 2 ^ k) ∧ (∃ k : ℕ, σ.Z = 2 ^ k) ∧
    σ.h = σ.gaps.span ∧ σ.r = σ.gaps.length ∧ σ.gaps.Positive

end BlockEncoding

/-- Encoding of a concrete retained block. -/
def encodeBlock (D Z : ℕ) (block : LowGapBlock) : BlockEncoding where
  D := D
  Z := Z
  h := block.span
  r := block.gaps.length
  gaps := block.gaps

/-- Candidate encodings in fixed denominator and mean-gap bands. -/
def encodingCandidates (D Z : ℕ) (B : ℝ) : Set BlockEncoding :=
  {σ | σ.Valid ∧ σ.D = D ∧ σ.Z = Z ∧
    B * Nat.ceil (Real.logb 2 (4 * D)) ≤ σ.h ∧
    (σ.h : ℝ) ≤ (B + 1) * Nat.ceil (Real.logb 2 (4 * D)) ∧
    (σ.r : ℝ) ≤ 4 * σ.h / Z}

/-- The selected blocks occur in order inside the stabilized segment, are
greedy completed blocks, and cover at least half its span. -/
def IsLowGapCover (segment : OddDenominatorSegment) (B : ℝ)
    (ell Z forward : ℕ) (blocks : List LowGapBlock) : Prop :=
  blocks = selectedBlocks segment B ell Z forward ∧
    (∀ block ∈ blocks, LowGapBlock.OccursIn segment block ∧
      GapWord.IsGreedyBlock (Nat.ceil (B * ell)) block.gaps ∧
      Z * block.gaps.length ≤ 4 * block.span) ∧
    segment.span ≤ 2 * (blocks.map LowGapBlock.span).sum

/-- Exact nonnegative component weight used for the interior refinement. -/
def interiorComponentWeight (y : ℝ) (blocks : List LowGapBlock)
    (block : LowGapBlock) : ℝ :=
  y * block.span / (blocks.map LowGapBlock.span).sum

/-- A line realizes an encoding when its normalized slope has denominator in
the recorded band and its shared gap word is exactly the encoded word. -/
def LineRealizesEncoding (Q : ℕ) (line : AffineLine)
    (σ : BlockEncoding) : Prop :=
  σ.D ≤ (line.slope Q).den ∧ (line.slope Q).den < 2 * σ.D ∧
    ∃ finish : AffineLine, SharedGapTrajectory Q line σ.gaps finish

def GeometricLineRealizesEncoding (Q : ℕ) (line : GeometricLine)
    (σ : BlockEncoding) : Prop :=
  σ.D ≤ (line.slope Q).den ∧ (line.slope Q).den < 2 * σ.D ∧
    slopeAfter σ.gaps (line.slope Q : ℝ) ∈ Set.Ioo (0 : ℝ) 1

/-- Actual stabilized-segment data selected deterministically for one anchor.
The `before` word starts at the end of the initial long prefix. -/
structure AnchorInteriorData where
  baseLine : AffineLine
  before : GapWord
  segment : OddDenominatorSegment

namespace AnchorInteriorData

/-- Semantic validity of one anchor's stabilized segment.  This records only
facts supplied by the actual support window and shared-gap dynamics. -/
def Valid (Q : ℕ) (W : WindowSystem) (Z0 k : ℕ)
    (data : AnchorInteriorData) : Prop :=
  W.s ≤ k ∧ k ∈ highAnchors W Z0 ∧
    IsFrequentPrefix W Z0 (initialLongPrefix W k) ∧
    IsOccurrenceLine W Z0 (initialLongPrefix W k) data.baseLine ∧
    data.segment.Valid Q ∧
    (∃ after : GapWord,
      actualPostPrefixGaps W k =
        data.before ++ data.segment.gaps ++ after) ∧
    (data.baseLine.transformWord Q data.before).canonicalGeometricLine =
      data.segment.startLine.canonicalGeometricLine

end AnchorInteriorData

/-- At most one deterministic stabilized segment is retained for each anchor. -/
abbrev InteriorAnchorSelection := ℕ → Option AnchorInteriorData

def ValidInteriorAnchorSelection (Q : ℕ) (W : WindowSystem) (Z0 : ℕ)
    (selection : InteriorAnchorSelection) : Prop :=
  ∀ k data, selection k = some data → data.Valid Q W Z0 k

/-- The block's absolute position among the gaps of the anchored order-`m`
window. -/
def sourceWindowOffset (W : WindowSystem) (k : ℕ)
    (data : AnchorInteriorData) (block : LowGapBlock) : ℕ :=
  (initialLongPrefix W k).length + data.before.length + block.offset

/-- Raw affine line at the start of a selected block. -/
def sourceRawLine (Q : ℕ) (data : AnchorInteriorData)
    (block : LowGapBlock) : AffineLine :=
  data.segment.startLine.transformWord Q
    (data.segment.gaps.take block.offset)

/-- Absolute support coordinate at the selected block start. -/
def sourceCoordinate (W : WindowSystem) (k : ℕ)
    (data : AnchorInteriorData) (block : LowGapBlock) : ℕ :=
  W.enumeration.a (k - W.s + sourceWindowOffset W k data block)

/-- The proposed spatial injection code: absolute block-start coordinate and
its offset from the left edge of the anchored window.  Injectivity is a theorem
to be derived from line uniqueness and the strict support enumeration, not a
field of the source data. -/
def spatialSourceCode (W : WindowSystem) (selection : InteriorAnchorSelection)
    (kb : ℕ × LowGapBlock) : Option (ℕ × ℕ) :=
  (selection kb.1).map fun data =>
    (sourceCoordinate W kb.1 data kb.2,
      sourceWindowOffset W kb.1 data kb.2)

@[simp] theorem spatialSourceCode_of_selected (W : WindowSystem)
    (selection : InteriorAnchorSelection) (k : ℕ) (block : LowGapBlock)
    (data : AnchorInteriorData) (hdata : selection k = some data) :
    spatialSourceCode W selection (k, block) =
      some (sourceCoordinate W k data block,
        sourceWindowOffset W k data block) := by
  simp [spatialSourceCode, hdata]

/-- Original parameters whose horizontal coordinates lie in the enlarged
dyadic corridor. -/
def horizontalParameters (X : ℕ) (line : AffineLine) : Set ℤ :=
  {t | -(X : ℤ) ≤ line.A + line.H * t ∧
    line.A + line.H * t ≤ 3 * X}

/-- The original integer parameter realizes the actual block-start support
point on the unreduced affine line. -/
def IsOriginalSourceParameter (Q : ℕ) (W : WindowSystem) (k : ℕ)
    (data : AnchorInteriorData) (block : LowGapBlock) (t : ℤ) : Prop :=
  let raw := sourceRawLine Q data block
  let x := sourceCoordinate W k data block
  (x : ℤ) = raw.A + raw.H * t ∧
    carryInt W.rational x = raw.C + raw.K * t ∧
    t ∈ horizontalParameters W.X raw

theorem sourceCoordinate_on_canonicalLine (Q : ℕ) (W : WindowSystem) (k : ℕ)
    (data : AnchorInteriorData) (block : LowGapBlock) (t : ℤ)
    (hparameter : IsOriginalSourceParameter Q W k data block t) :
    (sourceRawLine Q data block).canonicalGeometricLine.Contains
      (sourceCoordinate W k data block : ℤ)
      (carryInt W.rational (sourceCoordinate W k data block)) := by
  apply (sourceRawLine Q data block).contains_canonicalGeometricLine
  exact ⟨t, hparameter.1, hparameter.2.1⟩

theorem originalSourceParameter_mem_corridor (Q : ℕ) (W : WindowSystem)
    (k : ℕ) (data : AnchorInteriorData) (block : LowGapBlock) (t : ℤ)
    (hparameter : IsOriginalSourceParameter Q W k data block t) :
    t ∈ horizontalParameters W.X (sourceRawLine Q data block) :=
  hparameter.2.2

/-- Logarithmic block length attached to the denominator band in an encoding. -/
def encodingLogLength (σ : BlockEncoding) : ℕ :=
  Nat.ceil (Real.logb 2 (4 * σ.D))

/-- Forward reserve retained after every selected interior block. -/
def reconstructionForwardLength (W : WindowSystem) (Cgap : ℕ) : ℕ :=
  3 * W.L + 2 * Cgap

/-- The actual interior suffix beginning immediately after a retained block. -/
def sourceForwardSuffix (data : AnchorInteriorData)
    (block : LowGapBlock) : GapWord :=
  data.segment.gaps.drop (block.offset + block.gaps.length)

/-- The deterministic shortest reconstruction word cut from the actual
post-block interior suffix. -/
def sourceForwardWord (W : WindowSystem) (Cgap : ℕ)
    (data : AnchorInteriorData) (block : LowGapBlock) : GapWord :=
  (sourceForwardSuffix data block).firstPrefixAbove (2 * W.L + Cgap)

/-- The raw affine line at the end of the encoded block, before any primitive
renormalization. -/
def sourceBlockEndLine (Q : ℕ) (data : AnchorInteriorData)
    (block : LowGapBlock) : AffineLine :=
  (sourceRawLine Q data block).transformWord Q block.gaps

/-- A canonical line reconstructed from one *actual* selected spatial source.
The source anchor, selected segment, retained block, raw primitive line, and
forward word are all fixed in the arguments.  In particular, the forward
word is not existential data: it is the shortest prefix of the genuine
post-block suffix whose span exceeds the paper's reconstruction threshold. -/
def IsReconstructedOccurrenceLine (Q Cgap : ℕ) (B Cstep : ℝ)
    (W : WindowSystem) (Z0 : ℕ)
    (selection : InteriorAnchorSelection) (σ : BlockEncoding)
    (k : ℕ) (data : AnchorInteriorData) (block : LowGapBlock)
    (line : GeometricLine) : Prop :=
  selection k = some data ∧
    data.Valid Q W Z0 k ∧
    IsFrequentPrefix W Z0 (initialLongPrefix W k) ∧
    block ∈ selectedBlocks data.segment B (encodingLogLength σ) σ.Z
      (reconstructionForwardLength W Cgap) ∧
    LowGapBlock.OccursIn data.segment block ∧
    sourceWindowOffset W k data block < W.m ∧
    σ ∈ encodingCandidates σ.D σ.Z B ∧
    0 < σ.D ∧
    encodeBlock σ.D σ.Z block = σ ∧
    Int.gcd (sourceRawLine Q data block).H
      (sourceRawLine Q data block).K = 1 ∧
    (sourceRawLine Q data block).canonicalGeometricLine = line ∧
    ((sourceRawLine Q data block).canonicalGeometricLine.H : ℝ) ≤
      Cstep * W.X / frequencyCutoff W ∧
    LineRealizesEncoding Q (sourceRawLine Q data block) σ ∧
    GeometricLineRealizesEncoding Q line σ ∧
    SharedGapTrajectory Q (sourceRawLine Q data block) block.gaps
      (sourceBlockEndLine Q data block) ∧
    2 * W.L + Cgap < (sourceForwardWord W Cgap data block).span ∧
    (sourceForwardWord W Cgap data block).span ≤
      reconstructionForwardLength W Cgap ∧
    (sourceForwardWord W Cgap data block).Positive ∧
    IsInteriorTrajectory Q (sourceBlockEndLine Q data block)
      (sourceForwardWord W Cgap data block)

/-- A genuine spatial source of an encoding.  Every field is tied to the
actual anchored suffix and deterministic block rule.  In particular no
fibre-size or injectivity assertion is included here. -/
def IsSpatialEncodingSource (Q Cgap : ℕ) (B Cstep : ℝ) (W : WindowSystem)
    (Z0 : ℕ) (selection : InteriorAnchorSelection) (σ : BlockEncoding)
    (kb : ℕ × LowGapBlock) : Prop :=
  ∃ data : AnchorInteriorData, ∃ t : ℤ,
    IsReconstructedOccurrenceLine Q Cgap B Cstep W Z0 selection σ
      kb.1 data kb.2
        (sourceRawLine Q data kb.2).canonicalGeometricLine ∧
    IsOriginalSourceParameter Q W kb.1 data kb.2 t

/-- Spatial preimage of one encoding, before threshold integration. -/
def spatialPreimage (Q Cgap : ℕ) (B Cstep : ℝ)
    (W : WindowSystem) (Z0 : ℕ)
    (selection : InteriorAnchorSelection) (σ : BlockEncoding) :
    Set (ℕ × LowGapBlock) :=
  {kb | IsSpatialEncodingSource Q Cgap B Cstep W Z0 selection σ kb}

/-- Canonical geometric lines actually represented by the spatial preimage
of one encoding.  This image contains no arbitrary reconstructed line. -/
def spatialCanonicalLines (Q Cgap : ℕ) (B Cstep : ℝ)
    (W : WindowSystem) (Z0 : ℕ)
    (selection : InteriorAnchorSelection) (σ : BlockEncoding) :
    Set GeometricLine :=
  {line | ∃ k : ℕ, ∃ data : AnchorInteriorData, ∃ block : LowGapBlock,
    IsSpatialEncodingSource Q Cgap B Cstep W Z0 selection σ (k, block) ∧
      selection k = some data ∧
      (sourceRawLine Q data block).canonicalGeometricLine = line}

/-- The spatial code is injective on genuine sources.  This is the single
order factor in the paper's fibre argument: no threshold coordinate is
present, and the offset contributes exactly one factor of `m`. -/
theorem spatialSourceCode_injective (Q Cgap : ℕ) (B Cstep : ℝ)
    (W : WindowSystem) (Z0 : ℕ) (selection : InteriorAnchorSelection)
    (σ : BlockEncoding) :
    Set.InjOn (spatialSourceCode W selection)
      (spatialPreimage Q Cgap B Cstep W Z0 selection σ) := by
  rintro ⟨k₁, block₁⟩ hsource₁ ⟨k₂, block₂⟩ hsource₂ hcode
  change IsSpatialEncodingSource Q Cgap B Cstep W Z0 selection σ
    (k₁, block₁) at hsource₁
  change IsSpatialEncodingSource Q Cgap B Cstep W Z0 selection σ
    (k₂, block₂) at hsource₂
  rcases hsource₁ with
    ⟨data₁, t₁, hreconstructed₁, _hparameter₁⟩
  rcases hsource₂ with
    ⟨data₂, t₂, hreconstructed₂, _hparameter₂⟩
  rcases hreconstructed₁ with
    ⟨hselected₁, hvalid₁, _hfrequent₁, _hblock₁, _hoccurs₁,
      _hoffsetBound₁, _hcandidate₁, _hD₁, hencoding₁,
      _hprimitive₁, _hline₁, _hstep₁, _hrealizes₁, _hgeometric₁,
      _hblockTrajectory₁, _hlower₁, _hupper₁, _hpositive₁,
      _hinterior₁⟩
  rcases hreconstructed₂ with
    ⟨hselected₂, hvalid₂, _hfrequent₂, _hblock₂, _hoccurs₂,
      _hoffsetBound₂, _hcandidate₂, _hD₂, hencoding₂,
      _hprimitive₂, _hline₂, _hstep₂, _hrealizes₂, _hgeometric₂,
      _hblockTrajectory₂, _hlower₂, _hupper₂, _hpositive₂,
      _hinterior₂⟩
  rw [spatialSourceCode_of_selected W selection k₁ block₁ data₁ hselected₁,
    spatialSourceCode_of_selected W selection k₂ block₂ data₂ hselected₂] at hcode
  have hpair := Option.some.inj hcode
  have hcoordinate := congrArg Prod.fst hpair
  have hoffset := congrArg Prod.snd hpair
  have hindex :
      k₁ - W.s + sourceWindowOffset W k₁ data₁ block₁ =
        k₂ - W.s + sourceWindowOffset W k₂ data₂ block₂ := by
    apply W.enumeration.strictMono.injective
    simpa only [sourceCoordinate] using hcoordinate
  have hanchor : k₁ = k₂ := by
    have hs₁ : W.s ≤ k₁ := hvalid₁.1
    have hs₂ : W.s ≤ k₂ := hvalid₂.1
    omega
  subst k₂
  have hdata : data₁ = data₂ := by
    rw [hselected₁] at hselected₂
    exact Option.some.inj hselected₂
  subst data₂
  have hblockOffset : block₁.offset = block₂.offset := by
    simp only [sourceWindowOffset] at hoffset
    omega
  have hblockGaps : block₁.gaps = block₂.gaps := by
    have hencoding :
        encodeBlock σ.D σ.Z block₁ = encodeBlock σ.D σ.Z block₂ :=
      hencoding₁.trans hencoding₂.symm
    exact congrArg BlockEncoding.gaps hencoding
  have hblock : block₁ = block₂ := by
    cases block₁
    cases block₂
    simp_all
  subst block₂
  rfl

/-! The next lemmas identify every post-prefix subword with the corresponding
run of genuine support gaps and propagate the actual carry point along that
run.  They are kept public because the interior uniqueness and exterior
first-exit arguments use the same source geometry. -/

theorem enumerationGapWord_append {S : Set ℕ}
    (e : SupportEnumeration S) (i r n : ℕ) :
    enumerationGapWord e i (r + n) =
      enumerationGapWord e i r ++ enumerationGapWord e (i + r) n := by
  induction r generalizing i with
  | zero => simp [enumerationGapWord]
  | succ r ih =>
      rw [show r + 1 + n = (r + n) + 1 by omega,
        enumerationGapWord_succ, enumerationGapWord_succ, ih]
      congr 1
      simp [Nat.add_comm, Nat.add_left_comm]

theorem rawWindowGapWord_eq_enumerationGapWord
    (W : WindowSystem) (k : ℕ) (hsk : W.s ≤ k) :
    W.rawWindowGapWord k =
      enumerationGapWord W.enumeration (k - W.s) W.m := by
  simp [WindowSystem.rawWindowGapWord, hsk, WindowSystem.window,
    windowGapWord, enumerationGapWord, WindowSystem.m]

theorem actualPostPrefixGaps_eq_enumerationGapWord
    (W : WindowSystem) (Z0 k : ℕ) (hsk : W.s ≤ k)
    (hk : k ∈ highAnchors W Z0) :
    actualPostPrefixGaps W k =
      enumerationGapWord W.enumeration
        (k - W.s + (initialLongPrefix W k).length)
        (W.m - (initialLongPrefix W k).length) := by
  let p := initialLongPrefix W k
  have hpword : p =
      enumerationGapWord W.enumeration (k - W.s) p.length :=
    initialPrefix_eq_enumerationGapWord W Z0 k p hk rfl
  have hprefix : p.IsPrefix (W.rawWindowGapWord k) := by
    exact GapWord.firstPrefixAbove_isPrefix _ _
  have hlen : p.length ≤ W.m :=
    hprefix.length_le.trans (rawWindowGapWord_length_le W k)
  have hsplit := enumerationGapWord_append W.enumeration
    (k - W.s) p.length (W.m - p.length)
  rw [Nat.add_sub_of_le hlen] at hsplit
  unfold actualPostPrefixGaps
  rw [rawWindowGapWord_eq_enumerationGapWord W k hsk, hsplit]
  rw [← hpword]
  simp [p]

theorem prefix_actualPostPrefixGaps_eq_enumerationGapWord
    (W : WindowSystem) (Z0 k : ℕ) (hsk : W.s ≤ k)
    (hk : k ∈ highAnchors W Z0) (before : GapWord)
    (hbefore : before.IsPrefix (actualPostPrefixGaps W k)) :
    before = enumerationGapWord W.enumeration
      (k - W.s + (initialLongPrefix W k).length) before.length := by
  let j := k - W.s + (initialLongPrefix W k).length
  let n := W.m - (initialLongPrefix W k).length
  have hactual : actualPostPrefixGaps W k =
      enumerationGapWord W.enumeration j n := by
    simpa [j, n] using
      actualPostPrefixGaps_eq_enumerationGapWord W Z0 k hsk hk
  have hlen : before.length ≤ n := by
    have := hbefore.length_le
    rw [hactual] at this
    simpa [enumerationGapWord] using this
  have henumPrefix :
      (enumerationGapWord W.enumeration j before.length).IsPrefix
        (actualPostPrefixGaps W k) := by
    rw [hactual]
    rw [show n = before.length + (n - before.length) by omega,
      enumerationGapWord_append]
    exact List.prefix_append _ _
  have hb := List.prefix_iff_eq_take.mp hbefore
  have he := List.prefix_iff_eq_take.mp henumPrefix
  have hlength :
      (enumerationGapWord W.enumeration j before.length).length =
        before.length := by simp [enumerationGapWord]
  rw [hlength] at he
  exact hb.trans he.symm

theorem AffineLine.contains_transform_supportGap (Q : ℕ)
    (R : RationalSupport) (hQ : R.eta.den = Q)
    (e : SupportEnumeration R.S) (line : AffineLine) (i : ℕ)
    (hcontains : line.Contains (e.a i) (carryInt R (e.a i))) :
    (line.transform Q (supportGap e i)).Contains
      (e.a (i + 1)) (carryInt R (e.a (i + 1))) := by
  rcases hcontains with ⟨t, hx, hr⟩
  refine ⟨t, ?_, ?_⟩
  · simp only [AffineLine.transform]
    have hendpoint : e.a i + supportGap e i = e.a (i + 1) := by
      simp only [supportGap]
      exact Nat.add_sub_of_le (e.strictMono (Nat.lt_succ_self i)).le
    have hendpointInt :
        (e.a (i + 1) : ℤ) = (e.a i : ℤ) + supportGap e i := by
      exact_mod_cast hendpoint.symm
    rw [hx] at hendpointInt
    linarith
  · have hgap := supportGap_isSupportGap e i
    have hendpoint : e.a i + supportGap e i = e.a (i + 1) := by
      simp only [supportGap]
      exact Nat.add_sub_of_le (e.strictMono (Nat.lt_succ_self i)).le
    rw [← hendpoint,
      carryInt_across_supportGap R (e.a i) (supportGap e i) hgap]
    simp only [AffineLine.transform]
    rw [hQ, hr, hx]
    ring

/-- A genuine support-gap transformation preserves the original integer
parameter, not merely membership in the transformed line. -/
theorem AffineLine.transform_supportGap_parameter (Q : ℕ)
    (R : RationalSupport) (hQ : R.eta.den = Q)
    (e : SupportEnumeration R.S) (line : AffineLine) (i : ℕ) (t : ℤ)
    (hx : (e.a i : ℤ) = line.A + line.H * t)
    (hr : carryInt R (e.a i) = line.C + line.K * t) :
    (e.a (i + 1) : ℤ) =
        (line.transform Q (supportGap e i)).A +
          (line.transform Q (supportGap e i)).H * t ∧
      carryInt R (e.a (i + 1)) =
        (line.transform Q (supportGap e i)).C +
          (line.transform Q (supportGap e i)).K * t := by
  have hxExplicit :
      (e.a (i + 1) : ℤ) =
        (line.transform Q (supportGap e i)).A +
          (line.transform Q (supportGap e i)).H * t := by
    simp only [AffineLine.transform]
    have hendpoint : e.a i + supportGap e i = e.a (i + 1) := by
      simp only [supportGap]
      exact Nat.add_sub_of_le (e.strictMono (Nat.lt_succ_self i)).le
    have hendpointInt :
        (e.a (i + 1) : ℤ) = (e.a i : ℤ) + supportGap e i := by
      exact_mod_cast hendpoint.symm
    rw [hx] at hendpointInt
    linarith
  refine ⟨hxExplicit, ?_⟩
  have hgap := supportGap_isSupportGap e i
  have hendpoint : e.a i + supportGap e i = e.a (i + 1) := by
    simp only [supportGap]
    exact Nat.add_sub_of_le (e.strictMono (Nat.lt_succ_self i)).le
  rw [← hendpoint,
    carryInt_across_supportGap R (e.a i) (supportGap e i) hgap]
  simp only [AffineLine.transform]
  rw [hQ, hr, hx]
  ring

theorem AffineLine.transformWord_contains_enumerationGapWord (Q : ℕ)
    (R : RationalSupport) (hQ : R.eta.den = Q)
    (e : SupportEnumeration R.S) (line : AffineLine) (i n : ℕ)
    (hcontains : line.Contains (e.a i) (carryInt R (e.a i))) :
    (line.transformWord Q (enumerationGapWord e i n)).Contains
      (e.a (i + n)) (carryInt R (e.a (i + n))) := by
  induction n generalizing i line with
  | zero => simpa [enumerationGapWord, AffineLine.transformWord] using hcontains
  | succ n ih =>
      rw [enumerationGapWord_succ]
      simp only [AffineLine.transformWord]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (i := i + 1) (line := line.transform Q (supportGap e i))
          (line.contains_transform_supportGap Q R hQ e i hcontains)

/-- Iterating a genuine support run preserves one fixed original integer
parameter through every raw affine transformation. -/
theorem AffineLine.transformWord_parameter_enumerationGapWord (Q : ℕ)
    (R : RationalSupport) (hQ : R.eta.den = Q)
    (e : SupportEnumeration R.S) (line : AffineLine) (i n : ℕ) (t : ℤ)
    (hx : (e.a i : ℤ) = line.A + line.H * t)
    (hr : carryInt R (e.a i) = line.C + line.K * t) :
    let finish := line.transformWord Q (enumerationGapWord e i n)
    (e.a (i + n) : ℤ) = finish.A + finish.H * t ∧
      carryInt R (e.a (i + n)) = finish.C + finish.K * t := by
  induction n generalizing i line with
  | zero => simpa [enumerationGapWord, AffineLine.transformWord] using And.intro hx hr
  | succ n ih =>
      rw [enumerationGapWord_succ]
      simp only [AffineLine.transformWord]
      obtain ⟨hxnext, hrnext⟩ :=
        line.transform_supportGap_parameter Q R hQ e i t hx hr
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (i := i + 1) (line := line.transform Q (supportGap e i))
          hxnext hrnext

theorem occurrence_transformWord_contains_actualPrefix
    (Q : ℕ) (W : WindowSystem) (Z0 k : ℕ)
    (hden : W.rational.eta.den = Q) (hsk : W.s ≤ k)
    (hk : k ∈ highAnchors W Z0) (line : AffineLine)
    (hoccurrence : IsOccurrenceLine W Z0 (initialLongPrefix W k) line)
    (before : GapWord)
    (hbefore : before.IsPrefix (actualPostPrefixGaps W k)) :
    (line.transformWord Q before).Contains
      (W.enumeration.a
        (k - W.s + (initialLongPrefix W k).length + before.length))
      (carryInt W.rational (W.enumeration.a
        (k - W.s + (initialLongPrefix W k).length + before.length))) := by
  let i := k - W.s
  let p := initialLongPrefix W k
  let j := i + p.length
  have hpword : p = enumerationGapWord W.enumeration i p.length := by
    exact initialPrefix_eq_enumerationGapWord W Z0 k p hk rfl
  have hpspan := enumerationGapWord_span W.enumeration i p.length
  rw [← hpword] at hpspan
  have hx : W.enumeration.a i + p.span = W.enumeration.a j := by
    dsimp [j]
    have hmono := W.enumeration.strictMono.monotone
      (show i ≤ i + p.length by omega)
    omega
  have hbase : line.Contains (W.enumeration.a j)
      (carryInt W.rational (W.enumeration.a j)) := by
    rw [← hx]
    exact hoccurrence k hk rfl
  have hbeforeWord : before =
      enumerationGapWord W.enumeration j before.length := by
    simpa [i, p, j] using
      prefix_actualPostPrefixGaps_eq_enumerationGapWord
        W Z0 k hsk hk before hbefore
  rw [hbeforeWord]
  simpa [i, p, j, Nat.add_assoc, enumerationGapWord] using
    line.transformWord_contains_enumerationGapWord Q W.rational hden
      W.enumeration j before.length hbase

/-- The stabilized segment word in valid anchor data is the literal support
gap run beginning after `before`; it cannot be replaced by an unrelated word. -/
theorem AnchorInteriorData.segmentGaps_eq_enumerationGapWord
    (Q : ℕ) (W : WindowSystem) (Z0 k : ℕ)
    (data : AnchorInteriorData) (hvalid : data.Valid Q W Z0 k) :
    data.segment.gaps = enumerationGapWord W.enumeration
      (k - W.s + (initialLongPrefix W k).length + data.before.length)
      data.segment.gaps.length := by
  rcases hvalid.2.2.2.2.2.1 with ⟨after, hactual⟩
  have hbeforePrefix : data.before.IsPrefix (actualPostPrefixGaps W k) := by
    exact ⟨data.segment.gaps ++ after,
      by simpa [List.append_assoc] using hactual.symm⟩
  have htotalPrefix :
      (data.before ++ data.segment.gaps).IsPrefix
        (actualPostPrefixGaps W k) := by
    exact ⟨after, hactual.symm⟩
  have hbefore :=
    prefix_actualPostPrefixGaps_eq_enumerationGapWord W Z0 k
      hvalid.1 hvalid.2.1 data.before hbeforePrefix
  have htotal :=
    prefix_actualPostPrefixGaps_eq_enumerationGapWord W Z0 k
      hvalid.1 hvalid.2.1 (data.before ++ data.segment.gaps) htotalPrefix
  have hsplit := enumerationGapWord_append W.enumeration
    (k - W.s + (initialLongPrefix W k).length)
    data.before.length data.segment.gaps.length
  simp only [List.length_append] at htotal
  rw [hsplit, ← hbefore] at htotal
  exact List.append_right_injective data.before htotal

/-- The longest initial subword for which every successive state remains in
the open slope interval.  This depends only on the anchor word and its locked
line, never on the threshold coordinate. -/
def maximalInteriorPrefix (Q : ℕ) (line : AffineLine) : GapWord → GapWord
  | [] => []
  | g :: gs =>
      if classifySlope ((line.transform Q g).slope Q) = .interior then
        g :: maximalInteriorPrefix Q (line.transform Q g) gs
      else []

theorem maximalInteriorPrefix_isPrefix (Q : ℕ) (line : AffineLine)
    (word : GapWord) :
    (maximalInteriorPrefix Q line word).IsPrefix word := by
  induction word generalizing line with
  | nil => simp [maximalInteriorPrefix]
  | cons g gs ih =>
      simp only [maximalInteriorPrefix]
      split_ifs
      · rcases ih (line.transform Q g) with ⟨tail, htail⟩
        exact ⟨tail, by simpa using congrArg (List.cons g) htail⟩
      · exact List.nil_prefix

theorem isInteriorTrajectory_iff_transformWord (Q : ℕ)
    (line : AffineLine) (word : GapWord) :
    IsInteriorTrajectory Q line word ↔
      ∀ r ≤ word.length,
        classifySlope ((line.transformWord Q (word.take r)).slope Q) =
          .interior := by
  constructor
  · intro h r hr
    obtain ⟨state, htrajectory, hinterior⟩ := h r hr
    have hstate :=
      (sharedGapTrajectory_iff_transformWord Q line _ _).mp htrajectory
    subst state
    exact hinterior
  · intro h r hr
    exact ⟨line.transformWord Q (word.take r),
      (sharedGapTrajectory_iff_transformWord Q line _ _).mpr rfl, h r hr⟩

theorem isInteriorTrajectory_cons_iff (Q : ℕ) (line : AffineLine)
    (g : ℕ) (word : GapWord) :
    IsInteriorTrajectory Q line (g :: word) ↔
      classifySlope (line.slope Q) = .interior ∧
      classifySlope ((line.transform Q g).slope Q) = .interior ∧
      IsInteriorTrajectory Q (line.transform Q g) word := by
  rw [isInteriorTrajectory_iff_transformWord,
    isInteriorTrajectory_iff_transformWord]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · simpa [AffineLine.transformWord] using h 0 (by simp)
    · simpa [AffineLine.transformWord] using h 1 (by simp)
    · intro r hr
      have hall := h (r + 1) (by simp; omega)
      simpa [AffineLine.transformWord_append, AffineLine.transformWord] using hall
  · rintro ⟨hzero, _hone, htail⟩ r hr
    cases r with
    | zero => simpa [AffineLine.transformWord] using hzero
    | succ r =>
        simpa [AffineLine.transformWord_append, AffineLine.transformWord] using
          htail r (by simp at hr; omega)

theorem maximalInteriorPrefix_interior (Q : ℕ) (line : AffineLine)
    (word : GapWord) (hline : classifySlope (line.slope Q) = .interior) :
    IsInteriorTrajectory Q line (maximalInteriorPrefix Q line word) := by
  induction word generalizing line with
  | nil =>
      rw [isInteriorTrajectory_iff_transformWord]
      simpa [maximalInteriorPrefix, AffineLine.transformWord] using hline
  | cons g gs ih =>
      simp only [maximalInteriorPrefix]
      by_cases hnext : classifySlope ((line.transform Q g).slope Q) = .interior
      · rw [if_pos hnext, isInteriorTrajectory_cons_iff]
        exact ⟨hline, hnext, ih (line.transform Q g) hnext⟩
      · rw [if_neg hnext, isInteriorTrajectory_iff_transformWord]
        simpa [AffineLine.transformWord] using hline

theorem maximalInteriorPrefix_maximal (Q : ℕ) (line : AffineLine)
    (word u : GapWord) (hp : u.IsPrefix word)
    (hinterior : IsInteriorTrajectory Q line u) :
    u.IsPrefix (maximalInteriorPrefix Q line word) := by
  induction u generalizing line word with
  | nil => exact List.nil_prefix
  | cons g gs ih =>
      obtain ⟨tail, rfl⟩ := hp
      have hparts := (isInteriorTrajectory_cons_iff Q line g gs).mp hinterior
      change (g :: gs).IsPrefix
        (if classifySlope ((line.transform Q g).slope Q) = .interior then
          g :: maximalInteriorPrefix Q (line.transform Q g) (gs ++ tail)
        else [])
      rw [if_pos hparts.2.1]
      rcases ih (line.transform Q g) (gs ++ tail)
          (List.prefix_append gs tail) hparts.2.2 with ⟨rest, hrest⟩
      exact ⟨rest, by simpa using congrArg (List.cons g) hrest⟩

theorem isInteriorTrajectory_append_iff (Q : ℕ) (line : AffineLine)
    (u v : GapWord) :
    IsInteriorTrajectory Q line (u ++ v) ↔
      IsInteriorTrajectory Q line u ∧
        IsInteriorTrajectory Q (line.transformWord Q u) v := by
  induction u generalizing line with
  | nil =>
      simp only [List.nil_append, AffineLine.transformWord]
      constructor
      · intro h
        have hzero :=
          (isInteriorTrajectory_iff_transformWord Q line v).mp h 0 (by simp)
        refine ⟨?_, h⟩
        rw [isInteriorTrajectory_iff_transformWord]
        simpa [AffineLine.transformWord] using hzero
      · exact fun h => h.2
  | cons g gs ih =>
      simp only [List.cons_append]
      rw [isInteriorTrajectory_cons_iff,
        isInteriorTrajectory_cons_iff, ih]
      simp only [AffineLine.transformWord]
      tauto

/-- Primitive reduction of a raw affine parameterization, retaining its
chosen origin. -/
def AffineLine.primitiveReduction (line : AffineLine) : AffineLine where
  A := line.A
  C := line.C
  H := line.primitiveHorizontalInt
  K := line.primitiveVertical
  H_pos := line.primitiveHorizontalInt_pos

theorem AffineLine.primitiveReduction_primitive (line : AffineLine) :
    Int.gcd line.primitiveReduction.H line.primitiveReduction.K = 1 := by
  change Int.gcd
    (line.H / (line.directionGCD : ℤ))
    (line.K / (line.directionGCD : ℤ)) = 1
  exact Int.gcd_div_gcd_div_gcd line.directionGCD_pos

theorem AffineLine.primitiveReduction_canonicalGeometricLine
    (line : AffineLine) :
    line.primitiveReduction.canonicalGeometricLine =
      line.canonicalGeometricLine := by
  have hdir : line.primitiveReduction.directionGCD = 1 :=
    line.primitiveReduction_primitive
  rw [GeometricLine.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · change ((line.primitiveReduction.H /
      (line.primitiveReduction.directionGCD : ℤ)).natAbs) =
        line.primitiveHorizontalInt.natAbs
    rw [hdir]
    simp [AffineLine.primitiveReduction]
  · change line.primitiveReduction.K /
      (line.primitiveReduction.directionGCD : ℤ) = line.primitiveVertical
    rw [hdir]
    simp [AffineLine.primitiveReduction]
  · change line.primitiveReduction.interceptNumerator /
      (line.primitiveReduction.directionGCD : ℤ) =
        line.interceptNumerator / (line.directionGCD : ℤ)
    rw [hdir]
    simp only [Nat.cast_one, Int.ediv_one]
    change line.primitiveHorizontalInt * line.C -
        line.primitiveVertical * line.A =
      line.interceptNumerator / (line.directionGCD : ℤ)
    unfold AffineLine.primitiveHorizontalInt AffineLine.primitiveVertical
      AffineLine.interceptNumerator AffineLine.directionGCD
    have hHfactor :
        line.H / (Int.gcd line.H line.K : ℤ) *
            (Int.gcd line.H line.K : ℤ) = line.H :=
      Int.ediv_mul_cancel (Int.gcd_dvd_left line.H line.K)
    have hKfactor :
        line.K / (Int.gcd line.H line.K : ℤ) *
            (Int.gcd line.H line.K : ℤ) = line.K :=
      Int.ediv_mul_cancel (Int.gcd_dvd_right line.H line.K)
    have hdvd : (Int.gcd line.H line.K : ℤ) ∣
        line.H * line.C - line.K * line.A := by
      exact dvd_sub
        (dvd_mul_of_dvd_left (Int.gcd_dvd_left line.H line.K) line.C)
        (dvd_mul_of_dvd_left (Int.gcd_dvd_right line.H line.K) line.A)
    have hdne : (Int.gcd line.H line.K : ℤ) ≠ 0 := by
      exact_mod_cast line.directionGCD_pos.ne'
    apply mul_right_cancel₀ hdne
    rw [Int.ediv_mul_cancel hdvd]
    calc
      (line.H / (Int.gcd line.H line.K : ℤ) * line.C -
          line.K / (Int.gcd line.H line.K : ℤ) * line.A) *
            (Int.gcd line.H line.K : ℤ) =
          (line.H / (Int.gcd line.H line.K : ℤ) *
              (Int.gcd line.H line.K : ℤ)) * line.C -
            (line.K / (Int.gcd line.H line.K : ℤ) *
              (Int.gcd line.H line.K : ℤ)) * line.A := by ring
      _ = line.H * line.C - line.K * line.A := by
        rw [hHfactor, hKfactor]

theorem AnchorInteriorData.segmentStart_contains_actual
    (Q : ℕ) (W : WindowSystem) (Z0 k : ℕ)
    (hden : W.rational.eta.den = Q)
    (data : AnchorInteriorData) (hvalid : data.Valid Q W Z0 k) :
    data.segment.startLine.Contains
      (W.enumeration.a
        (k - W.s + (initialLongPrefix W k).length + data.before.length))
      (carryInt W.rational (W.enumeration.a
        (k - W.s + (initialLongPrefix W k).length + data.before.length))) := by
  rcases hvalid.2.2.2.2.2.1 with ⟨after, hactual⟩
  have hbeforePrefix : data.before.IsPrefix (actualPostPrefixGaps W k) := by
    exact ⟨data.segment.gaps ++ after,
      by simpa [List.append_assoc] using hactual.symm⟩
  have hraw := occurrence_transformWord_contains_actualPrefix
    Q W Z0 k hden hvalid.1 hvalid.2.1 data.baseLine
      hvalid.2.2.2.1 data.before hbeforePrefix
  have hcanonical :=
    (data.baseLine.transformWord Q data.before).contains_canonicalGeometricLine
      _ _ hraw
  rw [hvalid.2.2.2.2.2.2] at hcanonical
  apply data.segment.startLine.contains_of_canonicalGeometricLine_of_primitive
    hvalid.2.2.2.2.1.2.2.1
  exact hcanonical

theorem odd_den_pow_mul_of_padicValNat_le (μ : ℚ) (G : ℕ)
    (hG : padicValNat 2 μ.den ≤ G) :
    Odd (((2 : ℚ) ^ G * μ).den) := by
  rw [Rat.mul_den]
  simp only [Rat.den_pow, Rat.den_ofNat, one_pow, one_mul,
    Rat.num_pow, Rat.num_ofNat]
  let a := padicValNat 2 μ.den
  let oddPart := μ.den.divMaxPow 2
  let d := Nat.gcd ((2 : ℤ) ^ G * μ.num).natAbs μ.den
  have hden : 2 ^ a * oddPart = μ.den := by
    exact Nat.pow_padicValNat_mul_divMaxPow 2 μ.den
  have hpowDiv : 2 ^ a ∣ 2 ^ G * μ.num.natAbs := by
    exact (Nat.pow_dvd_pow 2 hG).trans (dvd_mul_right _ _)
  have habs : ((2 : ℤ) ^ G * μ.num).natAbs =
      2 ^ G * μ.num.natAbs := by
    rw [Int.natAbs_mul, Int.natAbs_pow]
    norm_num
  have hpowDen : 2 ^ a ∣ μ.den := pow_padicValNat_dvd
  have hpowGcd : 2 ^ a ∣ d := by
    exact Nat.dvd_gcd (by simpa [d, habs] using hpowDiv) hpowDen
  have hdDiv : d ∣ μ.den := Nat.gcd_dvd_right _ _
  have hquotDiv : μ.den / d ∣ oddPart := by
    have hmain := Nat.div_dvd_div_left hdDiv hpowGcd
    have hpowPos : 0 < 2 ^ a := pow_pos (by norm_num) _
    have hoddEq : μ.den / 2 ^ a = oddPart := by
      rw [← hden, Nat.mul_comm, Nat.mul_div_left _ hpowPos]
    simpa [hoddEq] using hmain
  have hoddPart : Odd oddPart := by
    apply Nat.not_even_iff_odd.mp
    rw [even_iff_two_dvd]
    exact Nat.not_dvd_divMaxPow (by norm_num) μ.den_ne_zero
  simpa [d] using Odd.of_dvd_nat hoddPart hquotDiv

theorem den_pow_mul_sub_one_of_odd (μ : ℚ) (g : ℕ)
    (hodd : Odd μ.den) :
    ((2 : ℚ) ^ g * μ - 1).den = μ.den := by
  rw [Rat.sub_ofNat_den, Rat.mul_den]
  simp only [Rat.den_pow, Rat.den_ofNat, one_pow, one_mul,
    Rat.num_pow, Rat.num_ofNat]
  have htwo : Nat.Coprime (2 ^ g) μ.den :=
    (Nat.coprime_two_left.mpr hodd).pow_left g
  have hprod : Nat.Coprime (2 ^ g * μ.num.natAbs) μ.den :=
    htwo.mul_left μ.reduced
  rw [Int.natAbs_mul, Int.natAbs_pow]
  norm_num
  rw [hprod.gcd_eq_one, Nat.div_one]

theorem odd_num_pow_mul_sub_one (μ : ℚ) (g : ℕ) (hg : 0 < g)
    (hodd : Odd μ.den) :
    Odd (((2 : ℚ) ^ g * μ - 1).num) := by
  let ν := (2 : ℚ) ^ g * μ - 1
  have hden : ν.den = μ.den := den_pow_mul_sub_one_of_odd μ g hodd
  have hrepr : ν =
      ((2 : ℚ) ^ g * (μ.num : ℚ) - μ.den) / μ.den := by
    dsimp [ν]
    calc
      (2 : ℚ) ^ g * μ - 1 =
          (2 : ℚ) ^ g * ((μ.num : ℚ) / μ.den) - 1 := by
            rw [μ.num_div_den]
      _ = ((2 : ℚ) ^ g * (μ.num : ℚ) - μ.den) / μ.den := by
        field_simp
  have hnumRat : (ν.num : ℚ) =
      (2 : ℚ) ^ g * (μ.num : ℚ) - μ.den := by
    have hcanonical := ν.num_div_den
    rw [hden] at hcanonical
    conv_rhs at hcanonical => rw [hrepr]
    field_simp at hcanonical
    exact hcanonical
  have hnumInt : ν.num = (2 : ℤ) ^ g * μ.num - μ.den := by
    exact_mod_cast hnumRat
  rw [hnumInt]
  have hevenPow : Even ((2 : ℤ) ^ g) :=
    Even.pow_of_ne_zero (even_two : Even (2 : ℤ)) hg.ne'
  have hevenProduct : Even ((2 : ℤ) ^ g * μ.num) :=
    hevenPow.mul_right μ.num
  exact hevenProduct.sub_odd (by exact_mod_cast hodd)

def stabilizationSlopeOffset : GapWord → ℕ
  | [] => 0
  | _g :: gs => 2 ^ GapWord.span gs + stabilizationSlopeOffset gs

theorem AffineLine.transformWord_slope_formula (Q : ℕ) (hQ : 0 < Q)
    (line : AffineLine) (word : GapWord) :
    (line.transformWord Q word).slope Q =
      (2 : ℚ) ^ word.span * line.slope Q - stabilizationSlopeOffset word := by
  induction word generalizing line with
  | nil => simp [AffineLine.transformWord, GapWord.span, stabilizationSlopeOffset]
  | cons g gs ih =>
      simp only [AffineLine.transformWord]
      rw [ih, AffineLine.slope_transform Q hQ]
      simp only [GapWord.span, List.sum_cons, stabilizationSlopeOffset, pow_add]
      push_cast
      ring

theorem AffineLine.transformWord_den_odd_of_padicVal_le_span
    (Q : ℕ) (hQ : 0 < Q) (line : AffineLine) (word : GapWord)
    (hspan : padicValNat 2 (line.slope Q).den ≤ word.span) :
    Odd ((line.transformWord Q word).slope Q).den := by
  rw [line.transformWord_slope_formula Q hQ]
  have hden :
      ((2 : ℚ) ^ word.span * line.slope Q -
          stabilizationSlopeOffset word).den =
        ((2 : ℚ) ^ word.span * line.slope Q).den :=
    Rat.sub_ofNat_den _ _
  rw [hden]
  exact odd_den_pow_mul_of_padicValNat_le (line.slope Q) word.span hspan

theorem AffineLine.transformWord_odd_stable (Q : ℕ) (hQ : 0 < Q)
    (line : AffineLine) (word : GapWord) (hpositive : word.Positive)
    (hdenOdd : Odd (line.slope Q).den)
    (hnumOdd : Odd (line.slope Q).num) :
    ((line.transformWord Q word).slope Q).den = (line.slope Q).den ∧
      Odd ((line.transformWord Q word).slope Q).num := by
  induction word generalizing line with
  | nil => exact ⟨rfl, hnumOdd⟩
  | cons g gs ih =>
      have hg : 0 < g := hpositive g (by simp)
      have hgs : GapWord.Positive gs := by
        intro x hx
        exact hpositive x (by simp [hx])
      simp only [AffineLine.transformWord]
      have hden : ((line.transform Q g).slope Q).den =
          (line.slope Q).den := by
        rw [AffineLine.slope_transform Q hQ]
        exact den_pow_mul_sub_one_of_odd (line.slope Q) g hdenOdd
      have hnextDenOdd : Odd ((line.transform Q g).slope Q).den := by
        rw [hden]
        exact hdenOdd
      have hnextNumOdd : Odd ((line.transform Q g).slope Q).num := by
        rw [AffineLine.slope_transform Q hQ]
        exact odd_num_pow_mul_sub_one (line.slope Q) g hg hdenOdd
      obtain ⟨hfinalDen, hfinalNum⟩ :=
        ih (line.transform Q g) hgs hnextDenOdd hnextNumOdd
      exact ⟨hfinalDen.trans hden, hfinalNum⟩

/-- The denominator of a primitive normalized direction determines its
positive horizontal step. -/
theorem primitiveDirectionDenominator (Q : ℕ) (hQ : 0 < Q)
    (line : AffineLine) (hprimitive : Int.gcd line.H line.K = 1) :
    line.H.natAbs = (line.slope Q).den /
      Nat.gcd (line.slope Q).den Q := by
  have hHne : line.H ≠ 0 := ne_of_gt line.H_pos
  have hHnat : 0 < line.H.natAbs := Int.natAbs_pos.mpr hHne
  have hcop : Nat.Coprime line.H.natAbs line.K.natAbs := by
    exact hprimitive
  have hQint : (Q : ℤ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hden : (line.slope Q).den =
      Q * line.H.natAbs / Nat.gcd Q line.K.natAbs := by
    rw [AffineLine.slope]
    have hcast : (Q : ℚ) * (line.H : ℚ) =
        ((((Q : ℤ) * line.H : ℤ) : ℚ)) := by norm_num
    rw [hcast]
    rw [← Rat.divInt_eq_div, Rat.den_divInt,
      if_neg (mul_ne_zero hQint hHne)]
    simp only [Int.natAbs_mul, Int.natAbs_natCast, Int.gcd_def]
    rw [hcop.gcd_mul_right_cancel Q]
  rw [hden]
  exact show line.H.natAbs =
      (Q * line.H.natAbs / Nat.gcd Q line.K.natAbs) /
        Nat.gcd (Q * line.H.natAbs / Nat.gcd Q line.K.natAbs) Q from by
    let d := Nat.gcd Q line.K.natAbs
    let e := Q / d
    have hdQ : d ∣ Q := Nat.gcd_dvd_left Q line.K.natAbs
    have hdK : d ∣ line.K.natAbs := Nat.gcd_dvd_right Q line.K.natAbs
    have hdpos : 0 < d := Nat.gcd_pos_of_pos_left line.K.natAbs hQ
    have hepos : 0 < e := Nat.div_pos (Nat.le_of_dvd hQ hdQ) hdpos
    have hQeq : e * d = Q := by
      dsimp [e]
      exact Nat.div_mul_cancel hdQ
    have hcopHd : Nat.Coprime line.H.natAbs d :=
      Nat.Coprime.of_dvd_right hdK hcop
    have hq : Q * line.H.natAbs / d = e * line.H.natAbs := by
      rw [← hQeq]
      calc
        e * d * line.H.natAbs / d =
            (e * line.H.natAbs) * d / d := by
          rw [Nat.mul_right_comm e d line.H.natAbs]
        _ = e * line.H.natAbs := Nat.mul_div_left _ hdpos
    rw [show Nat.gcd Q line.K.natAbs = d by rfl, hq, ← hQeq,
      Nat.gcd_mul_left, hcopHd.gcd_eq_one, Nat.mul_one]
    have hcancel : e * line.H.natAbs / e = line.H.natAbs := by
      simpa [Nat.mul_comm] using Nat.mul_div_left line.H.natAbs hepos
    exact hcancel.symm

theorem AffineLine.transformWord_H (Q : ℕ) (line : AffineLine)
    (word : GapWord) : (line.transformWord Q word).H = line.H := by
  induction word generalizing line with
  | nil => rfl
  | cons g gs ih =>
      simp only [AffineLine.transformWord]
      rw [ih]
      rfl

theorem stableSegment_span_firstPrefixAtLeast_le_add (w : GapWord) (bound cap : ℕ)
    (hcap : ∀ g ∈ w, g ≤ cap) :
    (w.firstPrefixAtLeast bound).span ≤ bound + cap := by
  induction w generalizing bound with
  | nil => simp [GapWord.firstPrefixAtLeast, GapWord.span]
  | cons g gs ih =>
      have hgcap : g ≤ cap := hcap g (by simp)
      have htailcap : ∀ x ∈ gs, x ≤ cap := by
        intro x hx
        exact hcap x (by simp [hx])
      simp only [GapWord.firstPrefixAtLeast]
      by_cases hbg : bound ≤ g
      · simp [hbg, GapWord.span]
        omega
      · rw [if_neg hbg]
        simp only [GapWord.span, List.sum_cons]
        have hrec : (GapWord.firstPrefixAtLeast gs (bound - g)).sum ≤
            (bound - g) + cap := by
          simpa only [GapWord.span] using ih (bound - g) htailcap
        omega

theorem stableSegment_prefix_append_drop {α : Type*} (u w : List α)
    (hprefix : u.IsPrefix w) : u ++ w.drop u.length = w := by
  nth_rw 1 [List.prefix_iff_eq_take.mp hprefix]
  exact List.take_append_drop _ _

def denominatorStabilizationPrefix (Q : ℕ) (line : AffineLine)
    (word : GapWord) : GapWord :=
  word.firstPrefixAtLeast (padicValNat 2 (line.slope Q).den)

def parityStabilizationPrefix (Q : ℕ) (line : AffineLine)
    (word : GapWord) : GapWord :=
  let denPrefix := denominatorStabilizationPrefix Q line word
  let remainder := word.drop denPrefix.length
  if Odd ((line.transformWord Q denPrefix).slope Q).num then []
  else remainder.take 1

def stabilizationPrefix (Q : ℕ) (line : AffineLine)
    (word : GapWord) : GapWord :=
  denominatorStabilizationPrefix Q line word ++ parityStabilizationPrefix Q line word

def stabilizedGaps (Q : ℕ) (line : AffineLine)
    (word : GapWord) : GapWord :=
  word.drop (stabilizationPrefix Q line word).length

theorem denominatorStabilizationPrefix_isPrefix (Q : ℕ) (line : AffineLine)
    (word : GapWord) :
    (denominatorStabilizationPrefix Q line word).IsPrefix word := by
  exact GapWord.firstPrefixAtLeast_isPrefix _ _

theorem parityStabilizationPrefix_isPrefix_remainder (Q : ℕ) (line : AffineLine)
    (word : GapWord) :
    (parityStabilizationPrefix Q line word).IsPrefix
      (word.drop (denominatorStabilizationPrefix Q line word).length) := by
  change (if Odd ((line.transformWord Q
      (denominatorStabilizationPrefix Q line word)).slope Q).num then []
    else (word.drop (denominatorStabilizationPrefix Q line word).length).take 1).IsPrefix _
  by_cases hodd : Odd ((line.transformWord Q
      (denominatorStabilizationPrefix Q line word)).slope Q).num
  · rw [if_pos hodd]
    exact List.nil_prefix
  · rw [if_neg hodd]
    exact List.take_prefix 1 _

theorem stabilizationPrefix_append_stabilizedGaps
    (Q : ℕ) (line : AffineLine) (word : GapWord) :
    stabilizationPrefix Q line word ++
        stabilizedGaps Q line word = word := by
  let d := denominatorStabilizationPrefix Q line word
  let p := parityStabilizationPrefix Q line word
  have hd : d ++ word.drop d.length = word :=
    stableSegment_prefix_append_drop d word (denominatorStabilizationPrefix_isPrefix Q line word)
  have hp : p ++ (word.drop d.length).drop p.length = word.drop d.length :=
    stableSegment_prefix_append_drop p (word.drop d.length)
      (parityStabilizationPrefix_isPrefix_remainder Q line word)
  change (d ++ p) ++ word.drop (d ++ p).length = word
  rw [List.length_append, ← List.drop_drop]
  rw [List.append_assoc, hp, hd]

theorem stabilizationPrefix_isPrefix (Q : ℕ) (line : AffineLine)
    (word : GapWord) :
    (stabilizationPrefix Q line word).IsPrefix word := by
  exact ⟨stabilizedGaps Q line word,
    stabilizationPrefix_append_stabilizedGaps Q line word⟩

theorem stabilizationPrefix_positive (Q : ℕ) (line : AffineLine)
    (word : GapWord) (hpositive : word.Positive) :
    (stabilizationPrefix Q line word).Positive := by
  intro g hg
  exact hpositive g ((stabilizationPrefix_isPrefix Q line word).mem hg)

theorem stabilizedGaps_positive (Q : ℕ) (line : AffineLine)
    (word : GapWord) (hpositive : word.Positive) :
    (stabilizedGaps Q line word).Positive := by
  intro g hg
  exact hpositive g (List.mem_of_mem_drop hg)

theorem stabilizationPrefix_span_le (Q cap : ℕ) (line : AffineLine)
    (word : GapWord) (hcap : ∀ g ∈ word, g ≤ cap) :
    (stabilizationPrefix Q line word).span ≤
      padicValNat 2 (line.slope Q).den + 2 * cap := by
  let d := denominatorStabilizationPrefix Q line word
  let p := parityStabilizationPrefix Q line word
  have hdspan : d.span ≤ padicValNat 2 (line.slope Q).den + cap := by
    exact stableSegment_span_firstPrefixAtLeast_le_add word _ cap hcap
  have hpspan : p.span ≤ cap := by
    change (parityStabilizationPrefix Q line word).span ≤ cap
    unfold parityStabilizationPrefix
    by_cases hodd : Odd ((line.transformWord Q
        (denominatorStabilizationPrefix Q line word)).slope Q).num
    · rw [if_pos hodd]
      simp [GapWord.span]
    · rw [if_neg hodd]
      let remainder := word.drop d.length
      change GapWord.span (remainder.take 1) ≤ cap
      have hremcap : ∀ x ∈ remainder, x ≤ cap := by
        intro x hx
        exact hcap x (List.mem_of_mem_drop hx)
      cases hrem : remainder with
      | nil => simp [GapWord.span]
      | cons g gs =>
          simp only [List.take, GapWord.span, List.sum_cons, List.sum_nil,
            add_zero]
          apply hremcap g
          rw [hrem]
          exact List.mem_cons_self
  change GapWord.span (d ++ p) ≤ _
  simp only [GapWord.span, List.sum_append] at hdspan hpspan ⊢
  omega

theorem stableSegment_primitiveReduction_slope (Q : ℕ) (hQ : 0 < Q)
    (line : AffineLine) : line.primitiveReduction.slope Q = line.slope Q := by
  calc
    line.primitiveReduction.slope Q =
        line.primitiveReduction.canonicalGeometricLine.slope Q :=
      (AffineLine.canonicalGeometricLine_slope Q hQ line.primitiveReduction).symm
    _ = line.canonicalGeometricLine.slope Q := by
      rw [line.primitiveReduction_canonicalGeometricLine]
    _ = line.slope Q := AffineLine.canonicalGeometricLine_slope Q hQ line

theorem stableSegment_one_lt_den_of_mem_Ioo (μ : ℚ) (hμ : μ ∈ Set.Ioo (0 : ℚ) 1) :
    1 < μ.den := by
  have hnumPos : 0 < μ.num := Rat.num_pos.mpr hμ.1
  have hnumPos' : (1 : ℤ) ≤ μ.num := (Int.add_one_le_iff).2 hnumPos
  have hnumLtDenQ : (μ.num : ℚ) < μ.den := by
    have hdenPos : (0 : ℚ) < μ.den := by positivity
    apply (div_lt_one hdenPos).mp
    rw [μ.num_div_den]
    exact hμ.2
  have hnumLtDen : μ.num < (μ.den : ℤ) := by exact_mod_cast hnumLtDenQ
  omega

theorem stableSegment_classifySlope_eq_interior_iff (μ : ℚ) :
    classifySlope μ = .interior ↔ μ ∈ Set.Ioo (0 : ℚ) 1 := by
  by_cases hzero : μ = 0
  · simp [classifySlope, hzero]
  by_cases hone : μ = 1
  · simp [classifySlope, hone]
  by_cases hi : 0 < μ ∧ μ < 1
  · simp [classifySlope, hzero, hone, hi]
  · simp [classifySlope, hzero, hone, hi]

theorem stabilizationPrefix_odd (Q : ℕ) (hQ : 0 < Q)
    (line : AffineLine) (word : GapWord) (hpositive : word.Positive)
    (hcross : padicValNat 2 (line.slope Q).den ≤ word.span)
    (hproper : (stabilizationPrefix Q line word).span < word.span) :
    let finish := line.transformWord Q (stabilizationPrefix Q line word)
    Odd (finish.slope Q).den ∧ Odd (finish.slope Q).num := by
  let d := denominatorStabilizationPrefix Q line word
  let remainder := word.drop d.length
  let afterDen := line.transformWord Q d
  have hdspan : padicValNat 2 (line.slope Q).den ≤ d.span := by
    exact GapWord.span_firstPrefixAtLeast_ge word _ hcross
  have hdOdd : Odd (afterDen.slope Q).den := by
    exact line.transformWord_den_odd_of_padicVal_le_span Q hQ d hdspan
  by_cases hnum : Odd (afterDen.slope Q).num
  · have hbefore : stabilizationPrefix Q line word = d := by
      simp [stabilizationPrefix, parityStabilizationPrefix, d, afterDen, hnum]
    simpa [hbefore, afterDen] using And.intro hdOdd hnum
  · have hremNonempty : remainder ≠ [] := by
      intro hrem
      have hdEq : d = word := by
        have happ := stableSegment_prefix_append_drop d word
          (denominatorStabilizationPrefix_isPrefix Q line word)
        simpa [remainder, hrem] using happ
      have hbefore : stabilizationPrefix Q line word = d := by
        simp [stabilizationPrefix, parityStabilizationPrefix, d, remainder,
          afterDen, hnum, hrem]
      rw [hbefore, hdEq] at hproper
      exact (Nat.lt_irrefl _ hproper)
    obtain ⟨g, gs, hrem⟩ := List.exists_cons_of_ne_nil hremNonempty
    have hgmem : g ∈ word := by
      have hgdrop : g ∈ word.drop d.length := by
        change g ∈ remainder
        rw [hrem]
        exact List.mem_cons_self
      exact List.mem_of_mem_drop hgdrop
    have hg : 0 < g := hpositive g hgmem
    have hbefore : stabilizationPrefix Q line word = d ++ [g] := by
      simp [stabilizationPrefix, parityStabilizationPrefix, d, remainder,
        afterDen, hnum, hrem]
    have hslope :
        (line.transformWord Q (stabilizationPrefix Q line word)).slope Q =
          (afterDen.transform Q g).slope Q := by
      rw [hbefore, AffineLine.transformWord_append]
      rfl
    dsimp only
    rw [hslope, AffineLine.slope_transform Q hQ]
    exact ⟨by
        rw [den_pow_mul_sub_one_of_odd (afterDen.slope Q) g hdOdd]
        exact hdOdd,
      odd_num_pow_mul_sub_one (afterDen.slope Q) g hg hdOdd⟩

def stabilizedSegment (Q : ℕ) (line : AffineLine)
    (word : GapWord) : OddDenominatorSegment :=
  let before := stabilizationPrefix Q line word
  let raw := line.transformWord Q before
  let start := raw.primitiveReduction
  let gaps := stabilizedGaps Q line word
  { startLine := start
    gaps := gaps
    slopes := OddDenominatorSegment.slopeTrace Q start gaps
    q := (raw.slope Q).den }

theorem stabilizedSegment_valid (Q : ℕ) (hQ : 0 < Q)
    (line : AffineLine) (word : GapWord) (hpositive : word.Positive)
    (hinterior : IsInteriorTrajectory Q line word)
    (hcross : padicValNat 2 (line.slope Q).den ≤ word.span)
    (hproper : (stabilizationPrefix Q line word).span < word.span) :
    (stabilizedSegment Q line word).Valid Q := by
  let before := stabilizationPrefix Q line word
  let raw := line.transformWord Q before
  let start := raw.primitiveReduction
  let gaps := stabilizedGaps Q line word
  have hdecomp : before ++ gaps = word :=
    stabilizationPrefix_append_stabilizedGaps Q line word
  have hsplit :
      IsInteriorTrajectory Q line before ∧
        IsInteriorTrajectory Q raw gaps := by
    apply (isInteriorTrajectory_append_iff Q line before gaps).mp
    rw [hdecomp]
    exact hinterior
  have hrawInterior : classifySlope (raw.slope Q) = .interior := by
    have hzero := (isInteriorTrajectory_iff_transformWord Q raw gaps).mp
      hsplit.2 0 (by simp)
    simpa [AffineLine.transformWord] using hzero
  have hstartSlope : start.slope Q = raw.slope Q := by
    exact stableSegment_primitiveReduction_slope Q hQ raw
  have hstartInterior : classifySlope (start.slope Q) = .interior := by
    rw [hstartSlope]
    exact hrawInterior
  have hstartTrajectory : IsInteriorTrajectory Q start gaps := by
    rw [isInteriorTrajectory_iff_transformWord]
    intro r hr
    have hrawState :=
      (isInteriorTrajectory_iff_transformWord Q raw gaps).mp hsplit.2 r hr
    rw [start.transformWord_slope_eq_of_slope_eq Q hQ raw (gaps.take r)
      hstartSlope]
    exact hrawState
  have hoddRaw := stabilizationPrefix_odd Q hQ line word hpositive
    hcross hproper
  change Odd ((line.transformWord Q before).slope Q).den ∧
      Odd ((line.transformWord Q before).slope Q).num at hoddRaw
  have hoddStartDen : Odd (start.slope Q).den := by
    rw [hstartSlope]
    exact hoddRaw.1
  have hoddStartNum : Odd (start.slope Q).num := by
    rw [hstartSlope]
    exact hoddRaw.2
  have hgapsPositive : gaps.Positive :=
    stabilizedGaps_positive Q line word hpositive
  have hallOdd : ∀ r ≤ gaps.length,
      ((start.transformWord Q (gaps.take r)).slope Q).den =
          (start.slope Q).den ∧
        Odd ((start.transformWord Q (gaps.take r)).slope Q).num := by
    intro r hr
    apply start.transformWord_odd_stable Q hQ (gaps.take r)
    · intro g hg
      exact hgapsPositive g (List.mem_of_mem_take hg)
    · exact hoddStartDen
    · exact hoddStartNum
  have hqEq : (raw.slope Q).den = (start.slope Q).den := by
    rw [hstartSlope]
  have hstartIoo : start.slope Q ∈ Set.Ioo (0 : ℚ) 1 :=
    (stableSegment_classifySlope_eq_interior_iff _).mp hstartInterior
  have hqOne : 1 < (raw.slope Q).den := by
    rw [hqEq]
    exact stableSegment_one_lt_den_of_mem_Ioo (start.slope Q) hstartIoo
  refine ⟨hQ, hgapsPositive, raw.primitiveReduction_primitive,
    rfl, hqOne, ?_, ?_⟩
  · exact hoddRaw.1
  · intro μ hμ
    change μ ∈ OddDenominatorSegment.slopeTrace Q start gaps at hμ
    unfold OddDenominatorSegment.slopeTrace at hμ
    rcases List.mem_map.mp hμ with ⟨r, hr, rfl⟩
    have hrle : r ≤ gaps.length := by
      rw [List.mem_range] at hr
      omega
    have hinteriorState :=
      (isInteriorTrajectory_iff_transformWord Q start gaps).mp
        hstartTrajectory r hrle
    have hoddState := hallOdd r hrle
    exact ⟨(stableSegment_classifySlope_eq_interior_iff _).mp hinteriorState,
      hoddState.1.trans hqEq.symm, hoddState.2⟩

def anchorInteriorWord (Q : ℕ) (W : WindowSystem) (k : ℕ)
    (line : AffineLine) : GapWord :=
  maximalInteriorPrefix Q line (actualPostPrefixGaps W k)

def anchorInteriorData (Q : ℕ) (W : WindowSystem) (k : ℕ)
    (line : AffineLine) : AnchorInteriorData :=
  let word := anchorInteriorWord Q W k line
  { baseLine := line
    before := stabilizationPrefix Q line word
    segment := stabilizedSegment Q line word }

theorem anchorInteriorData_valid (Q : ℕ) (hQ : 0 < Q)
    (W : WindowSystem) (Z0 k : ℕ) (line : AffineLine)
    (hsk : W.s ≤ k) (hk : k ∈ highAnchors W Z0)
    (hfrequent : IsFrequentPrefix W Z0 (initialLongPrefix W k))
    (hoccurrence : IsOccurrenceLine W Z0 (initialLongPrefix W k) line)
    (hlineInterior : classifySlope (line.slope Q) = .interior)
    (hcross : padicValNat 2 (line.slope Q).den ≤
      (anchorInteriorWord Q W k line).span)
    (hproper : (stabilizationPrefix Q line
        (anchorInteriorWord Q W k line)).span <
      (anchorInteriorWord Q W k line).span) :
    (anchorInteriorData Q W k line).Valid Q W Z0 k := by
  let word := anchorInteriorWord Q W k line
  let before := stabilizationPrefix Q line word
  let segment := stabilizedSegment Q line word
  have hactualPositive : (actualPostPrefixGaps W k).Positive := by
    intro g hg
    exact rawWindowGapWord_positive W k g (List.mem_of_mem_drop hg)
  have hwordPrefix : word.IsPrefix (actualPostPrefixGaps W k) :=
    maximalInteriorPrefix_isPrefix Q line _
  have hwordPositive : word.Positive := by
    intro g hg
    exact hactualPositive g (hwordPrefix.mem hg)
  have hwordInterior : IsInteriorTrajectory Q line word :=
    maximalInteriorPrefix_interior Q line _ hlineInterior
  have hsegmentValid : segment.Valid Q := by
    exact stabilizedSegment_valid Q hQ line word hwordPositive
      hwordInterior (by simpa [word] using hcross)
      (by simpa [word, before] using hproper)
  rcases hwordPrefix with ⟨after, hafter⟩
  have hstabilized : before ++ segment.gaps = word := by
    exact stabilizationPrefix_append_stabilizedGaps Q line word
  refine ⟨hsk, hk, hfrequent, hoccurrence, hsegmentValid, ?_, ?_⟩
  · refine ⟨after, ?_⟩
    calc
      actualPostPrefixGaps W k = word ++ after := hafter.symm
      _ = (before ++ segment.gaps) ++ after := by rw [hstabilized]
      _ = before ++ segment.gaps ++ after := rfl
  · change (line.transformWord Q before).canonicalGeometricLine =
      (line.transformWord Q before).primitiveReduction.canonicalGeometricLine
    exact (line.transformWord Q before).primitiveReduction_canonicalGeometricLine.symm

theorem stableSegment_nat_log_mul_pow_two (C L : ℕ) (hC : 0 < C) :
    Nat.log 2 (C * 2 ^ L) = Nat.log 2 C + L := by
  induction L with
  | zero => simp
  | succ L ih =>
      rw [pow_succ]
      rw [← Nat.mul_assoc, Nat.log_mul_base Nat.one_lt_two]
      · rw [ih]
        omega
      · exact mul_ne_zero hC.ne' (pow_ne_zero _ (by norm_num))

theorem stableSegment_primitiveReduction_H_le (line : AffineLine) :
    (line.primitiveReduction.H : ℝ) ≤ line.H := by
  have hfactor : line.primitiveHorizontalInt *
      (line.directionGCD : ℤ) = line.H :=
    Int.ediv_mul_cancel (Int.gcd_dvd_left line.H line.K)
  have hfactorReal : (line.primitiveHorizontalInt : ℝ) *
      (line.directionGCD : ℝ) = line.H := by
    exact_mod_cast hfactor
  have hdOne : (1 : ℝ) ≤ line.directionGCD := by
    exact_mod_cast line.directionGCD_pos
  have hpNonneg : (0 : ℝ) ≤ line.primitiveHorizontalInt := by
    exact_mod_cast line.primitiveHorizontalInt_pos.le
  change (line.primitiveHorizontalInt : ℝ) ≤ line.H
  nlinarith

theorem stableSegment_longInterior_anchorWord
    (Q : ℕ) (hQ : 0 < Q) (W : WindowSystem) (Z0 : ℕ)
    (e : WindowThreshold) (base : AffineLine)
    (hden : W.rational.eta.den = Q)
    (hcutoff : 1 < frequencyCutoff W)
    (hbase : IsOccurrenceLine W Z0 (initialLongPrefix W e.1) base)
    (hlong : LongInteriorPair W Z0 e) :
    classifySlope (base.slope Q) = .interior ∧
      W.excess e / 8 ≤ (anchorInteriorWord Q W e.1 base).span := by
  rcases hlong.2.2 with ⟨line, gaps, hcontinuation, hinterior, hspan⟩
  have hcanonical := occurrenceLines_canonical_eq_of_frequent W Z0
    (initialLongPrefix W e.1) hcutoff hlong.2.1 base line
    hbase hcontinuation.1
  have hslope : base.slope Q = line.slope Q := by
    calc
      base.slope Q = base.canonicalGeometricLine.slope Q :=
        (base.canonicalGeometricLine_slope Q hQ).symm
      _ = line.canonicalGeometricLine.slope Q := by rw [hcanonical]
      _ = line.slope Q := line.canonicalGeometricLine_slope Q hQ
  have hinteriorQ : IsInteriorTrajectory Q line gaps := by
    simpa only [hden] using hinterior
  have hlineInterior : classifySlope (line.slope Q) = .interior := by
    have hzero := (isInteriorTrajectory_iff_transformWord Q line gaps).mp
      hinteriorQ 0 (by simp)
    simpa [AffineLine.transformWord] using hzero
  have hbaseInterior : classifySlope (base.slope Q) = .interior := by
    rw [hslope]
    exact hlineInterior
  have hbaseTrajectory : IsInteriorTrajectory Q base gaps := by
    rw [isInteriorTrajectory_iff_transformWord]
    intro r hr
    have hstate := (isInteriorTrajectory_iff_transformWord Q line gaps).mp
      hinteriorQ r hr
    rw [base.transformWord_slope_eq_of_slope_eq Q hQ line
      (gaps.take r) hslope]
    exact hstate
  have hprefix : gaps.IsPrefix (actualPostPrefixGaps W e.1) :=
    hcontinuation.2.1
  have hmaxPrefix : gaps.IsPrefix
      (anchorInteriorWord Q W e.1 base) := by
    exact maximalInteriorPrefix_maximal Q base _ gaps hprefix hbaseTrajectory
  have hspanNat : gaps.span ≤
      (anchorInteriorWord Q W e.1 base).span := by
    rcases hmaxPrefix with ⟨tail, htail⟩
    rw [← htail]
    simp [GapWord.span]
  refine ⟨hbaseInterior, hspan.trans ?_⟩
  exact_mod_cast hspanNat

theorem stableSegment_stabilizationPrefix_span_le_four_levels
    (Q : ℕ) (hQ : 0 < Q) (gap : GapParams Q)
    (Clock : ℝ) (hClock : 0 < Clock)
    (W : WindowSystem) (L k : ℕ) (base : AffineLine)
    (hlevel : W.L = L)
    (hprimitive : Int.gcd base.H base.K = 1)
    (hheight : (base.H : ℝ) ≤
      Clock * W.X / frequencyCutoff W)
    (hfrequencyOne : (1 : ℝ) ≤ frequencyCutoff W)
    (hL : Nat.log 2 (Q * Nat.ceil Clock) +
      2 * (gap.Cgap + 1) ≤ L)
    (hcap : ∀ g ∈ actualPostPrefixGaps W k,
      g ≤ L + gap.Cgap + 1) :
    padicValNat 2 (base.slope Q).den ≤ 4 * L ∧
      (stabilizationPrefix Q base
        (anchorInteriorWord Q W k base)).span ≤ 4 * L := by
  have hfrequencyPos : (0 : ℝ) < frequencyCutoff W :=
    lt_of_lt_of_le zero_lt_one hfrequencyOne
  have hstepBase : (base.H : ℝ) ≤ Clock * W.X := by
    refine hheight.trans ?_
    rw [div_le_iff₀ hfrequencyPos]
    have hnonneg : (0 : ℝ) ≤ Clock * W.X := by positivity
    nlinarith
  have hHnatReal : (base.H.natAbs : ℝ) = (base.H : ℝ) := by
    have hHnatInt : (base.H.natAbs : ℤ) = base.H :=
      Int.natAbs_of_nonneg base.H_pos.le
    calc
      (base.H.natAbs : ℝ) = ((base.H.natAbs : ℤ) : ℝ) := by norm_num
      _ = (base.H : ℝ) := by rw [hHnatInt]
  have hClockCeil : Clock ≤ (Nat.ceil Clock : ℝ) := Nat.le_ceil Clock
  have hHceilReal : (base.H.natAbs : ℝ) ≤
      (Nat.ceil Clock : ℝ) * W.X := by
    rw [hHnatReal]
    have hXnonneg : (0 : ℝ) ≤ W.X := by positivity
    exact hstepBase.trans (mul_le_mul_of_nonneg_right hClockCeil hXnonneg)
  have hHceil : base.H.natAbs ≤ Nat.ceil Clock * W.X := by
    exact_mod_cast hHceilReal
  let q := (base.slope Q).den
  let d := Nat.gcd q Q
  have hdvd : d ∣ q := Nat.gcd_dvd_left q Q
  have hdQ : d ≤ Q := Nat.gcd_le_right q hQ
  have hqboundH : q ≤ base.H.natAbs * Q := by
    have hformula := primitiveDirectionDenominator Q hQ base hprimitive
    calc
      q = q / d * d := (Nat.div_mul_cancel hdvd).symm
      _ ≤ q / d * Q := Nat.mul_le_mul_left _ hdQ
      _ = base.H.natAbs * Q := by rw [hformula]
  have hqbound : q ≤ (Q * Nat.ceil Clock) * 2 ^ L := by
    have hX : W.X = 2 ^ L := by
      rw [WindowSystem.X, dyadicScale, hlevel]
    rw [hX] at hHceil
    calc
      q ≤ base.H.natAbs * Q := hqboundH
      _ ≤ (Nat.ceil Clock * 2 ^ L) * Q :=
        Nat.mul_le_mul_right Q hHceil
      _ = (Q * Nat.ceil Clock) * 2 ^ L := by ring
  have hCpos : 0 < Q * Nat.ceil Clock := by
    exact mul_pos hQ (Nat.ceil_pos.mpr hClock)
  have hpadic : padicValNat 2 q ≤ Nat.log 2 (Q * Nat.ceil Clock) + L := by
    calc
      padicValNat 2 q ≤ Nat.log 2 q := padicValNat_le_nat_log q
      _ ≤ Nat.log 2 ((Q * Nat.ceil Clock) * 2 ^ L) :=
        Nat.log_mono_right hqbound
      _ = Nat.log 2 (Q * Nat.ceil Clock) + L :=
        stableSegment_nat_log_mul_pow_two _ _ hCpos
  have hwordPrefix : (anchorInteriorWord Q W k base).IsPrefix
      (actualPostPrefixGaps W k) :=
    maximalInteriorPrefix_isPrefix Q base _
  have hwordCap : ∀ g ∈ anchorInteriorWord Q W k base,
      g ≤ L + gap.Cgap + 1 := by
    intro g hg
    exact hcap g (hwordPrefix.mem hg)
  have hstabilization := stabilizationPrefix_span_le Q
    (L + gap.Cgap + 1) base (anchorInteriorWord Q W k base)
    hwordCap
  have hpadic' : padicValNat 2 (base.slope Q).den ≤
      Nat.log 2 (Q * Nat.ceil Clock) + L := by
    simpa only [q] using hpadic
  constructor <;> omega

theorem stableSegment_four_levels_lt_excess_sixteen
    (kappa : ℝ) (hkappa : 0 < kappa)
    (W : WindowSystem) (L Z0 : ℕ) (e : WindowThreshold)
    (hoffset : W.s = Nat.floor (kappa * (L : ℝ)))
    (hZ : (64 : ℝ) ≤ kappa * (Z0 : ℝ))
    (hlarge : e ∈ W.largePairs Z0) :
    (4 * L : ℝ) < W.excess e / 16 := by
  have hmLower : kappa * (L : ℝ) < (W.m : ℝ) := by
    rw [WindowSystem.m, hoffset]
    simpa only [Nat.cast_add, Nat.cast_one] using
      (Nat.lt_floor_add_one (kappa * (L : ℝ)))
  have hZpos : (0 : ℝ) < Z0 := by
    have hkZpos : (0 : ℝ) < kappa * (Z0 : ℝ) :=
      lt_of_lt_of_le (by norm_num) hZ
    nlinarith
  have hmul : kappa * (L : ℝ) * (Z0 : ℝ) <
      (W.m : ℝ) * Z0 :=
    mul_lt_mul_of_pos_right hmLower hZpos
  have hsixtyfour : (64 : ℝ) * L ≤
      kappa * Z0 * L := by
    have := mul_le_mul_of_nonneg_right hZ (Nat.cast_nonneg L)
    nlinarith
  have hexcess : (W.m : ℝ) * Z0 < W.excess e := by
    simpa only [Set.mem_setOf_eq] using hlarge.2
  nlinarith

def StableSegmentAnchorGood (Q : ℕ) (W : WindowSystem) (Z0 : ℕ)
    (Cstep : ℝ) (k : ℕ) (data : AnchorInteriorData) : Prop :=
  data.Valid Q W Z0 k ∧
    ∀ e : WindowThreshold, e.1 = k → LongInteriorPair W Z0 e →
      W.excess e / 16 ≤ data.segment.span ∧
      1 ≤ data.segment.gapCount ∧
      data.segment.gapCount ≤ W.m ∧
      (data.segment.startLine.H : ℝ) ≤
        Cstep * W.X / frequencyCutoff W

theorem stableSegment_anchorGood_construct
    (Q : ℕ) (hQ : 0 < Q) (W : WindowSystem) (L Z0 k : ℕ)
    (Clock : ℝ) (base : AffineLine)
    (hden : W.rational.eta.den = Q)
    (hcutoff : 1 < frequencyCutoff W)
    (hsk : W.s ≤ k) (hk : k ∈ highAnchors W Z0)
    (hfrequent : IsFrequentPrefix W Z0 (initialLongPrefix W k))
    (hoccurrence : IsOccurrenceLine W Z0 (initialLongPrefix W k) base)
    (_hprimitive : Int.gcd base.H base.K = 1)
    (hheight : (base.H : ℝ) ≤ Clock * W.X / frequencyCutoff W)
    (hpadicFour : padicValNat 2 (base.slope Q).den ≤ 4 * L)
    (hbeforeFour : (stabilizationPrefix Q base
      (anchorInteriorWord Q W k base)).span ≤ 4 * L)
    (hfourAll : ∀ e : WindowThreshold, e.1 = k →
      LongInteriorPair W Z0 e → (4 * L : ℝ) < W.excess e / 16)
    (seed : WindowThreshold) (hseedFirst : seed.1 = k)
    (hseed : LongInteriorPair W Z0 seed) :
    StableSegmentAnchorGood Q W Z0 Clock k
      (anchorInteriorData Q W k base) := by
  have hseedAnchor := stableSegment_longInterior_anchorWord Q hQ W Z0 seed base
    hden hcutoff (by simpa only [hseedFirst] using hoccurrence) hseed
  have hseedFour := hfourAll seed hseedFirst hseed
  have hcross : padicValNat 2 (base.slope Q).den ≤
      (anchorInteriorWord Q W k base).span := by
    have hwordLower : W.excess seed / 8 ≤
        (anchorInteriorWord Q W k base).span := by
      simpa only [hseedFirst] using hseedAnchor.2
    have hpadicReal : (padicValNat 2 (base.slope Q).den : ℝ) ≤
        4 * L := by exact_mod_cast hpadicFour
    have hcrossReal : (padicValNat 2 (base.slope Q).den : ℝ) <
        (anchorInteriorWord Q W k base).span := by
      nlinarith
    exact_mod_cast hcrossReal.le
  have hproper : (stabilizationPrefix Q base
      (anchorInteriorWord Q W k base)).span <
      (anchorInteriorWord Q W k base).span := by
    have hwordLower : W.excess seed / 8 ≤
        (anchorInteriorWord Q W k base).span := by
      simpa only [hseedFirst] using hseedAnchor.2
    have hbeforeReal : ((stabilizationPrefix Q base
        (anchorInteriorWord Q W k base)).span : ℝ) ≤ 4 * L := by
      exact_mod_cast hbeforeFour
    have hproperReal : ((stabilizationPrefix Q base
        (anchorInteriorWord Q W k base)).span : ℝ) <
        (anchorInteriorWord Q W k base).span := by
      nlinarith
    exact_mod_cast hproperReal
  have hbaseInterior : classifySlope (base.slope Q) = .interior := by
    simpa only [hseedFirst] using hseedAnchor.1
  have hvalid : (anchorInteriorData Q W k base).Valid Q W Z0 k :=
    anchorInteriorData_valid Q hQ W Z0 k base hsk hk hfrequent
      hoccurrence hbaseInterior hcross hproper
  refine ⟨hvalid, ?_⟩
  intro e heFirst hlong
  have hanchor := stableSegment_longInterior_anchorWord Q hQ W Z0 e base
    hden hcutoff (by simpa only [heFirst] using hoccurrence) hlong
  have hwordLower : W.excess e / 8 ≤
      (anchorInteriorWord Q W k base).span := by
    simpa only [heFirst] using hanchor.2
  have hfour := hfourAll e heFirst hlong
  let data := anchorInteriorData Q W k base
  let before := stabilizationPrefix Q base
    (anchorInteriorWord Q W k base)
  let segment := stabilizedSegment Q base
    (anchorInteriorWord Q W k base)
  have hdecomp : before ++ segment.gaps =
      anchorInteriorWord Q W k base := by
    exact stabilizationPrefix_append_stabilizedGaps Q base
      (anchorInteriorWord Q W k base)
  have hspanEq : (anchorInteriorWord Q W k base).span =
      before.span + segment.span := by
    rw [← hdecomp]
    simp [OddDenominatorSegment.span, GapWord.span]
  have hspanEqReal : ((anchorInteriorWord Q W k base).span : ℝ) =
      before.span + segment.span := by exact_mod_cast hspanEq
  have hbeforeReal : (before.span : ℝ) ≤ 4 * L := by
    exact_mod_cast hbeforeFour
  have hsegmentLower : W.excess e / 16 ≤ (segment.span : ℝ) := by
    nlinarith
  have hexcessPos : 0 < W.excess e := by
    have hlarge := hlong.1.2
    have hnonneg : (0 : ℝ) ≤ W.m * Z0 := by positivity
    linarith
  have hsegmentSpanPos : 0 < segment.span := by
    have hreal : (0 : ℝ) < segment.span := by nlinarith
    exact_mod_cast hreal
  have hsegmentCountPos : 1 ≤ segment.gapCount := by
    have hne : segment.gaps ≠ [] := by
      intro hempty
      simp [OddDenominatorSegment.span, GapWord.span, hempty] at hsegmentSpanPos
    change 1 ≤ segment.gaps.length
    have hlengthPos : 0 < segment.gaps.length :=
      List.length_pos_iff.mpr hne
    omega
  have hsegmentCountLe : segment.gapCount ≤ W.m := by
    rcases hvalid.2.2.2.2.2.1 with ⟨after, hactual⟩
    have hactual' : actualPostPrefixGaps W k =
        before ++ segment.gaps ++ after := by
      simpa only [data, before, segment, anchorInteriorData] using hactual
    have hlength : segment.gaps.length ≤
        (actualPostPrefixGaps W k).length := by
      rw [hactual']
      simp only [List.length_append]
      omega
    exact hlength.trans (actualPostPrefixGaps_length_le W k)
  have hstartHeight : (segment.startLine.H : ℝ) ≤
      Clock * W.X / frequencyCutoff W := by
    have hreduce := stableSegment_primitiveReduction_H_le
      (base.transformWord Q before)
    have hraw : ((base.transformWord Q before).H : ℝ) =
        (base.H : ℝ) := by
      rw [AffineLine.transformWord_H]
    change (((base.transformWord Q before).primitiveReduction.H : ℤ) : ℝ) ≤
      Clock * W.X / frequencyCutoff W
    rw [hraw] at hreduce
    exact hreduce.trans hheight
  change W.excess e / 16 ≤
      (anchorInteriorData Q W k base).segment.span ∧ _
  simpa only [anchorInteriorData, data, before, segment] using
    And.intro hsegmentLower
      (And.intro hsegmentCountPos (And.intro hsegmentCountLe hstartHeight))

/-- Paper label: `lem:stable-segment` (Section 6).  The primitive-step
constant and cutoff are selected at denominator/context level.  For every
compatible family and sufficiently large scale, the selected segment depends
only on the anchor, not on the threshold. -/
theorem lem_stable_segment (context : FixedScaleContext)
    (gap : GapParams context.Q) :
    ∃ Cstep : ℝ, 0 < Cstep ∧ ∃ Zmin : ℕ,
      ∀ Z0 : ℕ, Zmin ≤ Z0 →
        ∀ F : ScaleFamily, F.MatchesContext context →
          ∀ᶠ L : ℕ in atTop,
            ∃ selection : InteriorAnchorSelection,
              ValidInteriorAnchorSelection context.Q (F.system L) Z0 selection ∧
              ∀ e : WindowThreshold, LongInteriorPair (F.system L) Z0 e →
                ∃ data : AnchorInteriorData,
                  selection e.1 = some data ∧
                  data.Valid context.Q (F.system L) Z0 e.1 ∧
                  (F.system L).excess e / 16 ≤ data.segment.span ∧
                  1 ≤ data.segment.gapCount ∧
                  data.segment.gapCount ≤ (F.system L).m ∧
                  (data.segment.startLine.H : ℝ) ≤
                    Cstep * (F.system L).X /
                      frequencyCutoff (F.system L) := by
  classical
  obtain ⟨Cline, Clock, hClock, hlocking⟩ :=
    lem_ap_locking context.Q context.Q_pos
  obtain ⟨CQ, hCQ, hfirstExists⟩ := lem_firstdeep_exists context
  let Cdiscard : ℕ := Nat.log 2 (context.Q * Nat.ceil Clock) +
    2 * (gap.Cgap + 1)
  let Zfirst : ℕ := Nat.ceil
    (2 * context.structural.Caff / context.entropy.kappa)
  let Zdense : ℕ := Nat.ceil (64 / context.entropy.kappa)
  let Zmin : ℕ := max Zfirst Zdense
  refine ⟨Clock, hClock, Zmin, ?_⟩
  intro Z0 hZ0 F hF
  have hZfirst : Zfirst ≤ Z0 := (le_max_left _ _).trans hZ0
  have hZdense : Zdense ≤ Z0 := (le_max_right _ _).trans hZ0
  have hZreal : (64 : ℝ) ≤
      context.entropy.kappa * (Z0 : ℝ) := by
    have hquot : 64 / context.entropy.kappa ≤ (Z0 : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hZdense)
    simpa [mul_comm] using
      (div_le_iff₀ context.entropy.kappa_pos).mp hquot
  have hfirstEvent := hfirstExists Z0
    (by simpa only [Zfirst] using hZfirst) F hF
  have hgapEvent := eventually_rawWindowGap_le context gap F hF
  let lineSlack : ℝ := context.structural.Caff - 2
  have hlineSlack : 0 < lineSlack := by
    dsimp [lineSlack]
    linarith [context.structural.Caff_gt]
  have hnatTop : Tendsto (fun L : ℕ => (L : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlineTop : Tendsto (fun L : ℕ => lineSlack * (L : ℝ))
      atTop atTop := Filter.Tendsto.const_mul_atTop hlineSlack hnatTop
  have hlineEvent : ∀ᶠ L : ℕ in atTop,
      (Cline : ℝ) < lineSlack * (L : ℝ) :=
    hlineTop.eventually_gt_atTop Cline
  filter_upwards [hfirstEvent, hgapEvent, hlineEvent,
    eventually_ge_atTop (max Cdiscard 1)]
      with L hfirstL hgapL hlineL hL
  let W := F.system L
  have hden : W.rational.eta.den = context.Q := by
    change (F.system L).rational.eta.den = context.Q
    rw [F.rational_eq, hF.1]
  have hstruct : W.structural = context.structural := by
    change (F.system L).structural = context.structural
    rw [F.structural_eq, hF.2.1]
  have hentropy : W.entropy = context.entropy := by
    change (F.system L).entropy = context.entropy
    rw [F.entropy_eq, hF.2.2.1]
  have hlevel : W.L = L := F.level_eq L
  have hLdiscard : Cdiscard ≤ L := (le_max_left _ _).trans hL
  have hLone : 1 ≤ L := (le_max_right _ _).trans hL
  have hfrequency : 1 < frequencyCutoff W := by
    unfold frequencyCutoff
    have hX : (1 : ℝ) < W.X := by
      rw [WindowSystem.X, hlevel, dyadicScale]
      exact_mod_cast (one_lt_pow₀ (by norm_num : 1 < (2 : ℕ))
        (Nat.ne_of_gt hLone))
    apply Real.one_lt_rpow hX
    rw [hstruct]
    linarith [context.structural.rho_pos]
  have hfrequencyOne : (1 : ℝ) ≤ frequencyCutoff W := hfrequency.le
  have hoffset : W.s =
      Nat.floor (context.entropy.kappa * (L : ℝ)) := by
    change (F.system L).s = _
    rw [F.offset_eq, hF.2.2.1]
  have candidateExists (k : ℕ)
      (hexists : ∃ seed : WindowThreshold,
        seed.1 = k ∧ LongInteriorPair W Z0 seed) :
      ∃ data : AnchorInteriorData,
        StableSegmentAnchorGood context.Q W Z0 Clock k data := by
    obtain ⟨seed, hseedFirst, hseed⟩ := hexists
    have hk : k ∈ highAnchors W Z0 := by
      rw [highAnchors, Finset.mem_filter]
      refine ⟨?_, seed.2, ?_, ?_⟩
      · simpa only [hseedFirst] using hseed.1.1.1
      · simpa only [hseedFirst] using hseed.1.1.2
      · simpa only [← hseedFirst, Prod.eta, Set.mem_setOf_eq] using
          hseed.1.2
    let p := initialLongPrefix W k
    have hpMem : p ∈ initialPrefixes W Z0 := by
      rw [initialPrefixes, Finset.mem_image]
      exact ⟨k, hk, rfl⟩
    have hpData := hfirstL seed hseed.1
    dsimp only at hpData
    have hpLower : context.structural.Caff * (L : ℝ) < (p.span : ℝ) := by
      have hpLower' := hpData.1
      change W.structural.Caff * (W.L : ℝ) <
        (initialLongPrefix W seed.1).span at hpLower'
      rw [hstruct, hlevel, hseedFirst] at hpLower'
      exact hpLower'
    have hsk : W.s ≤ k := by
      by_contra hnot
      have hpzero : p = [] := by
        dsimp [p, initialLongPrefix]
        simp [WindowSystem.rawWindowGapWord, GapWord.firstPrefixAbove, hnot]
      have hCaffPos : 0 < context.structural.Caff :=
        lt_trans (by norm_num) context.structural.Caff_gt
      rw [hpzero] at hpLower
      simp [GapWord.span] at hpLower
      have hLpos : (0 : ℝ) < L := by exact_mod_cast hLone
      nlinarith
    have hpLong : 2 * W.L + Cline < p.span := by
      have htarget : ((2 * W.L + Cline : ℕ) : ℝ) <
          (p.span : ℝ) := by
        rw [hlevel]
        push_cast
        dsimp [lineSlack] at hlineL
        nlinarith
      exact_mod_cast htarget
    have hfrequent : IsFrequentPrefix W Z0 p := by
      simpa only [p, hseedFirst] using hseed.2.1
    rcases hlocking W hden Z0 p hpMem hpLong hfrequent with
      ⟨base, hoccurrence, hprimitive, hheight⟩
    have hcap : ∀ g ∈ actualPostPrefixGaps W k,
        g ≤ L + gap.Cgap + 1 := by
      intro g hg
      apply hgapL k
      · simpa only [hseedFirst] using hseed.1.1.1
      · exact List.mem_of_mem_drop hg
    have hdiscard := stableSegment_stabilizationPrefix_span_le_four_levels
      context.Q context.Q_pos gap Clock hClock W L k base hlevel
      hprimitive hheight hfrequencyOne
      (by simpa only [Cdiscard] using hLdiscard) hcap
    have hfourAll : ∀ e : WindowThreshold, e.1 = k →
        LongInteriorPair W Z0 e →
        (4 * L : ℝ) < W.excess e / 16 := by
      intro e _heFirst heLong
      exact stableSegment_four_levels_lt_excess_sixteen context.entropy.kappa
        context.entropy.kappa_pos W L Z0 e hoffset hZreal heLong.1
    refine ⟨anchorInteriorData context.Q W k base, ?_⟩
    exact stableSegment_anchorGood_construct context.Q context.Q_pos W L Z0 k Clock
      base hden hfrequency hsk hk hfrequent hoccurrence hprimitive hheight
      hdiscard.1 hdiscard.2 hfourAll seed hseedFirst hseed
  let selection : InteriorAnchorSelection := fun k =>
    if h : ∃ data : AnchorInteriorData,
        StableSegmentAnchorGood context.Q W Z0 Clock k data then
      some (Classical.choose h)
    else none
  refine ⟨selection, ?_, ?_⟩
  · intro k data hselected
    dsimp only [selection] at hselected
    split at hselected
    next hgood =>
      simp only [Option.some.injEq] at hselected
      subst data
      exact (Classical.choose_spec hgood).1
    next hnone => simp at hselected
  · intro e hlong
    have hexists : ∃ data : AnchorInteriorData,
        StableSegmentAnchorGood context.Q W Z0 Clock e.1 data :=
      candidateExists e.1 ⟨e, rfl, hlong⟩
    let data : AnchorInteriorData := Classical.choose hexists
    have hgood : StableSegmentAnchorGood context.Q W Z0 Clock e.1 data :=
      Classical.choose_spec hexists
    have hfacts := hgood.2 e rfl hlong
    refine ⟨data, ?_, hgood.1, hfacts⟩
    dsimp only [selection]
    rw [dif_pos hexists]

/-- Paper label: `lem:primitive-direction` (Section 6). -/
theorem lem_primitive_direction (Q X : ℕ) (hQ : 0 < Q)
    (line : AffineLine) (hprimitive : Int.gcd line.H line.K = 1) :
    line.H.natAbs = (line.slope Q).den / Nat.gcd (line.slope Q).den Q ∧
      (horizontalParameters X line).Finite ∧
      ((horizontalParameters X line).ncard : ℝ) ≤
        1 + 4 * Q * X / (line.slope Q).den := by
  have hden := primitiveDirectionDenominator Q hQ line hprimitive
  refine ⟨hden, ?_⟩
  let C : ℤ := 3 * (X : ℤ) - line.A
  let J : ℤ := -line.H
  let B : ℤ := 4 * (X : ℤ)
  have hJ : J < 0 := by
    dsimp [J]
    exact neg_lt_zero.mpr line.H_pos
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hbound : ∀ t ∈ horizontalParameters X line,
      0 ≤ C + J * t ∧ C + J * t ≤ B := by
    intro t ht
    change -(X : ℤ) ≤ line.A + line.H * t ∧
      line.A + line.H * t ≤ 3 * X at ht
    dsimp [C, J, B]
    constructor <;> linarith
  have hcount := integerAffineIntervalCount
    (horizontalParameters X line) C J B hJ hB hbound
  refine ⟨hcount.1, hcount.2.trans ?_⟩
  have hHreal : (0 : ℝ) < line.H := by exact_mod_cast line.H_pos
  have hqreal : (0 : ℝ) < (line.slope Q).den := by positivity
  have hHnatcast : (line.H.natAbs : ℝ) = (line.H : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos hHreal]
  have hqle_nat : (line.slope Q).den ≤ Q * line.H.natAbs := by
    let q := (line.slope Q).den
    let g := Nat.gcd q Q
    have hgdiv : g ∣ q := Nat.gcd_dvd_left q Q
    have hqeq : q / g * g = q := Nat.div_mul_cancel hgdiv
    have hHg : line.H.natAbs * g = q := by
      rw [hden]
      exact hqeq
    have hgQ : g ≤ Q := Nat.gcd_le_right q hQ
    calc
      (line.slope Q).den = line.H.natAbs * g := by
        simpa [q] using hHg.symm
      _ ≤ line.H.natAbs * Q := Nat.mul_le_mul_left _ hgQ
      _ = Q * line.H.natAbs := Nat.mul_comm _ _
  have hqle : ((line.slope Q).den : ℝ) ≤
      (Q : ℝ) * (line.H : ℝ) := by
    rw [← hHnatcast]
    exact_mod_cast hqle_nat
  have hcross : (4 : ℝ) * X * (line.slope Q).den ≤
      (4 * Q * X) * line.H := by
    have := mul_le_mul_of_nonneg_left hqle
      (show (0 : ℝ) ≤ 4 * X by positivity)
    nlinarith
  have hdiv : (4 : ℝ) * X / line.H ≤
      4 * Q * X / (line.slope Q).den := by
    exact (div_le_div_iff₀ hHreal hqreal).2 hcross
  simpa [C, J, B] using add_le_add_left hdiv 1

/-- Paper label: `lem:denominator-span` (Section 6). -/
theorem lem_denominator_span (Q : ℕ) (hQ : 0 < Q) :
    ∃ cspan : ℝ, 0 < cspan ∧
      ∀ segment : OddDenominatorSegment,
        segment.Valid Q → 0 < segment.gapCount →
        cspan * Real.rpow 2 ((segment.span : ℝ) / segment.gapCount) ≤ segment.q := by
  refine ⟨(1 : ℝ) / 2, by norm_num, ?_⟩
  intro segment hsegment hcount
  rcases hsegment with
    ⟨_hQ, _hpositive, _hprimitive, htrace, _hq_one, _hq_odd, hslopes⟩
  have hlength : 0 < segment.gaps.length := by
    simpa [OddDenominatorSegment.gapCount] using hcount
  let g := segment.gaps.maximum_of_length_pos hlength
  have hgmem : g ∈ segment.gaps :=
    segment.gaps.maximum_of_length_pos_mem hlength
  have hallg : ∀ x ∈ segment.gaps, x ≤ g := by
    intro x hx
    exact segment.gaps.le_maximum_of_length_pos_of_mem hx hlength
  have hsum : segment.gaps.sum ≤ segment.gaps.length * g := by
    simpa using segment.gaps.sum_le_card_nsmul g hallg
  have hsumReal : (segment.gaps.sum : ℝ) ≤
      (segment.gaps.length : ℝ) * g := by
    exact_mod_cast hsum
  have havg : (segment.span : ℝ) / segment.gapCount ≤ (g : ℝ) := by
    rw [OddDenominatorSegment.span, OddDenominatorSegment.gapCount,
      GapWord.span]
    exact (div_le_iff₀
      (by positivity : (0 : ℝ) < segment.gaps.length)).2 (by
        simpa [mul_comm] using hsumReal)
  obtain ⟨r, hr, hget⟩ := List.getElem_of_mem hgmem
  have hμmemTrace :
      (segment.startLine.transformWord Q (segment.gaps.take r)).slope Q ∈
        OddDenominatorSegment.slopeTrace Q segment.startLine segment.gaps := by
    unfold OddDenominatorSegment.slopeTrace
    apply List.mem_map_of_mem
    exact List.mem_range.mpr (by omega)
  have hνmemTrace :
      (segment.startLine.transformWord Q (segment.gaps.take (r + 1))).slope Q ∈
        OddDenominatorSegment.slopeTrace Q segment.startLine segment.gaps := by
    unfold OddDenominatorSegment.slopeTrace
    apply List.mem_map_of_mem
    exact List.mem_range.mpr (by omega)
  have hμmem :
      (segment.startLine.transformWord Q (segment.gaps.take r)).slope Q ∈
        segment.slopes := by
    rw [htrace]
    exact hμmemTrace
  have hνmem :
      (segment.startLine.transformWord Q (segment.gaps.take (r + 1))).slope Q ∈
        segment.slopes := by
    rw [htrace]
    exact hνmemTrace
  let μ := (segment.startLine.transformWord Q (segment.gaps.take r)).slope Q
  let ν :=
    (segment.startLine.transformWord Q (segment.gaps.take (r + 1))).slope Q
  have hμdata := hslopes μ (by simpa [μ] using hμmem)
  have hνdata := hslopes ν (by simpa [ν] using hνmem)
  have htake : segment.gaps.take (r + 1) =
      segment.gaps.take r ++ [g] := by
    rw [← hget]
    simpa only [List.concat_eq_append] using (List.take_concat_get hr).symm
  have hνμ : ν = (2 : ℚ) ^ g * μ - 1 := by
    calc
      ν = (segment.startLine.transformWord Q
          (segment.gaps.take r ++ [g])).slope Q := by
            rw [← htake]
      _ = ((segment.startLine.transformWord Q (segment.gaps.take r)).transformWord
          Q [g]).slope Q := by rw [AffineLine.transformWord_append]
      _ = ((segment.startLine.transformWord Q
          (segment.gaps.take r)).transform Q g).slope Q := rfl
      _ = (2 : ℚ) ^ g * μ - 1 := by
        rw [AffineLine.slope_transform Q hQ]
  have hμlower : (1 : ℚ) / segment.q ≤ μ := by
    have hdenpos : (0 : ℚ) < μ.den := by positivity
    have hnumone : (1 : ℚ) ≤ μ.num := by
      exact_mod_cast (show (1 : ℤ) ≤ μ.num by
        exact (Int.add_one_le_iff).2 (Rat.num_pos.mpr hμdata.1.1))
    calc
      (1 : ℚ) / segment.q = 1 / μ.den := by rw [hμdata.2.1]
      _ ≤ (μ.num : ℚ) / μ.den :=
        (div_le_div_iff_of_pos_right hdenpos).2 hnumone
      _ = μ := Rat.num_div_den μ
  have hpowμ : (2 : ℚ) ^ g * μ < 2 := by
    rw [hνμ] at hνdata
    linarith [hνdata.1.2]
  have hqpos : (0 : ℚ) < segment.q := by positivity
  have hpowdiv : (2 : ℚ) ^ g / segment.q < 2 := by
    calc
      (2 : ℚ) ^ g / segment.q = (2 : ℚ) ^ g * (1 / segment.q) := by ring
      _ ≤ (2 : ℚ) ^ g * μ :=
        mul_le_mul_of_nonneg_left hμlower (by positivity)
      _ < 2 := hpowμ
  have hpowltRat : (2 : ℚ) ^ g < 2 * segment.q :=
    (div_lt_iff₀ hqpos).1 hpowdiv
  have hpowltReal : (2 : ℝ) ^ g < 2 * (segment.q : ℝ) := by
    exact_mod_cast hpowltRat
  have hrpow : Real.rpow 2
      ((segment.span : ℝ) / segment.gapCount) ≤ (2 : ℝ) ^ g := by
    calc
      Real.rpow 2 ((segment.span : ℝ) / segment.gapCount) ≤
          Real.rpow 2 (g : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) havg
      _ = (2 : ℝ) ^ g := Real.rpow_natCast 2 g
  nlinarith

/-- Paper label: `lem:sparse-cover` (Section 6). -/
private theorem forwardEligible_append_discarded (remainder : GapWord)
    (forward : ℕ) (words : List GapWord) :
    forwardEligibleWords remainder forward words ++
      forwardDiscardedWords remainder forward words = words := by
  induction words with
  | nil => rfl
  | cons block rest ih =>
      simp only [forwardEligibleWords, forwardDiscardedWords]
      split_ifs with h
      · simpa using congrArg (List.cons block) ih
      · simp

private theorem forwardDiscarded_span_add_remainder_le
    (remainder : GapWord) (forward cap : ℕ) (words : List GapWord)
    (hcap : ∀ block ∈ words, GapWord.span block ≤ cap)
    (hremainder : GapWord.span remainder ≤ cap) :
    GapWord.span (forwardDiscardedWords remainder forward words).flatten +
        GapWord.span remainder ≤ forward + cap := by
  induction words with
  | nil =>
      simpa [forwardDiscardedWords, GapWord.span] using
        (hremainder.trans (Nat.le_add_left cap forward))
  | cons block rest ih =>
      have hblock : GapWord.span block ≤ cap := hcap block (by simp)
      have hrest : ∀ word ∈ rest, GapWord.span word ≤ cap := by
        intro word hword
        exact hcap word (by simp [hword])
      simp only [forwardDiscardedWords]
      by_cases hsuffix : forward ≤ GapWord.span (rest.flatten ++ remainder)
      · rw [if_pos hsuffix]
        exact ih hrest
      · rw [if_neg hsuffix]
        simp only [List.flatten_cons, GapWord.span, List.sum_append]
        change block.sum + rest.flatten.sum + remainder.sum ≤ forward + cap
        change block.sum ≤ cap at hblock
        have hsuffix' : rest.flatten.sum + remainder.sum < forward := by
          simp only [GapWord.span, List.sum_append] at hsuffix
          omega
        omega

private theorem list_sum_filter_add_filter_not
    {alpha : Type} (p : alpha → Bool)
    (f : alpha → ℕ) (items : List alpha) :
    ((items.filter p).map f).sum +
        ((items.filter fun x => !p x).map f).sum =
      (items.map f).sum := by
  induction items with
  | nil => simp
  | cons x xs ih =>
      cases hx : p x <;> simp [hx] <;> omega

private theorem list_sum_filter_le
    {alpha : Type} (p : alpha → Bool)
    (f : alpha → ℕ) (items : List alpha) :
    ((items.filter p).map f).sum ≤ (items.map f).sum := by
  induction items with
  | nil => simp
  | cons x xs ih =>
      cases hx : p x <;> simp [hx] <;> omega

private theorem list_filter_filter_commute {alpha : Type}
    (items : List alpha) (p q : alpha → Bool) :
    (items.filter p).filter q =
      items.filter fun x => q x && p x := by
  induction items with
  | nil => rfl
  | cons x xs ih =>
      cases hp : p x <;> cases hq : q x <;> simp [hp, hq, ih]

private theorem list_filter_congr_on {alpha : Type}
    (items : List alpha) (p q : alpha → Bool)
    (h : ∀ x ∈ items, p x = q x) :
    items.filter p = items.filter q := by
  induction items with
  | nil => rfl
  | cons x xs ih =>
      have hx := h x (by simp)
      have htail : ∀ y ∈ xs, p y = q y := by
        intro y hy
        exact h y (by simp [hy])
      simp only [List.filter_cons]
      rw [hx.symm]
      cases hp : p x <;> simp [ih htail]

private theorem flatten_span_eq_sum_map_span (items : List GapWord) :
    GapWord.span items.flatten = (items.map GapWord.span).sum := by
  induction items with
  | nil => simp [GapWord.span]
  | cons block rest ih =>
      simp only [List.flatten_cons, GapWord.span, List.sum_append, List.map_cons,
        List.sum_cons]
      simp only [GapWord.span] at ih
      omega

private theorem blocksWithOffsetsFrom_mem_split (offset : ℕ)
    (words : List GapWord) (block : LowGapBlock)
    (hblock : block ∈ blocksWithOffsetsFrom offset words) :
    ∃ before after : List GapWord,
      words = before ++ block.gaps :: after ∧
        block.offset = offset + before.flatten.length := by
  induction words generalizing offset with
  | nil => simp [blocksWithOffsetsFrom] at hblock
  | cons word rest ih =>
      simp only [blocksWithOffsetsFrom, List.mem_cons] at hblock
      rcases hblock with rfl | hblock
      · exact ⟨[], rest, by simp⟩
      · rcases ih (offset + word.length) hblock with
          ⟨before, after, hrest, hoffset⟩
        refine ⟨word :: before, after, ?_, ?_⟩
        · simp [hrest]
        · simp only [List.flatten_cons, List.length_append]
          omega

private theorem blocksWithOffsetsFrom_offset_lower (offset : ℕ)
    (words : List GapWord) (block : LowGapBlock)
    (hblock : block ∈ blocksWithOffsetsFrom offset words) :
    offset ≤ block.offset := by
  rcases blocksWithOffsetsFrom_mem_split offset words block hblock with
    ⟨before, _after, _hwords, hoffset⟩
  omega

private theorem blocksWithOffsetsFrom_nodup (offset : ℕ)
    (words : List GapWord) (hne : ∀ word ∈ words, word ≠ []) :
    (blocksWithOffsetsFrom offset words).Nodup := by
  induction words generalizing offset with
  | nil => simp [blocksWithOffsetsFrom]
  | cons word rest ih =>
      simp only [blocksWithOffsetsFrom, List.nodup_cons]
      constructor
      · intro hmem
        have hlower := blocksWithOffsetsFrom_offset_lower
          (offset + word.length) rest ⟨offset, word⟩ hmem
        have hword : word ≠ [] := hne word (by simp)
        have hlength : 0 < word.length := List.length_pos_iff.mpr hword
        change offset + word.length ≤ offset at hlower
        omega
      · apply ih
        intro tail htail
        exact hne tail (by simp [htail])

private theorem blocksWithOffsetsFrom_occurs
    (segment : OddDenominatorSegment) (words : List GapWord)
    (remainder : GapWord)
    (hconcat : words.flatten ++ remainder = segment.gaps)
    (block : LowGapBlock)
    (hblock : block ∈ blocksWithOffsetsFrom 0 words) :
    LowGapBlock.OccursIn segment block := by
  rcases blocksWithOffsetsFrom_mem_split 0 words block hblock with
    ⟨before, after, hwords, hoffset⟩
  have hsource : segment.gaps =
      before.flatten ++ block.gaps ++ after.flatten ++ remainder := by
    calc
      segment.gaps = words.flatten ++ remainder := hconcat.symm
      _ = (before ++ block.gaps :: after).flatten ++ remainder := by rw [hwords]
      _ = before.flatten ++ block.gaps ++ after.flatten ++ remainder := by
        simp only [List.flatten_append, List.flatten_cons, List.append_assoc]
  constructor
  · have hlength := congrArg List.length hsource
    simp only [List.length_append] at hlength
    omega
  · rw [hsource, hoffset]
    simp

private theorem forwardEligibleWords_eq_nil_of_span_lt
    (remainder : GapWord) (forward : ℕ) (words : List GapWord)
    (hspan : GapWord.span (words.flatten ++ remainder) < forward) :
    forwardEligibleWords remainder forward words = [] := by
  cases words with
  | nil => rfl
  | cons word rest =>
      have hsuffix : GapWord.span (rest.flatten ++ remainder) < forward := by
        simp only [List.flatten_cons, GapWord.span, List.sum_append] at hspan ⊢
        omega
      simp [forwardEligibleWords, Nat.not_le.mpr hsuffix]

/-- The prefix implementation of forward eligibility is exactly the ordered
pointwise filter by the genuine post-block suffix. -/
private theorem forwardEligibleBlocks_eq_filter
    (source initial remainder : GapWord) (forward : ℕ)
    (words : List GapWord)
    (hsource : initial ++ words.flatten ++ remainder = source) :
    blocksWithOffsetsFrom initial.length
        (forwardEligibleWords remainder forward words) =
      (blocksWithOffsetsFrom initial.length words).filter fun block =>
        forward ≤ GapWord.span
          (source.drop (block.offset + block.gaps.length)) := by
  induction words generalizing initial with
  | nil => simp [forwardEligibleWords, blocksWithOffsetsFrom]
  | cons word rest ih =>
      have hsourceTail :
          (initial ++ word) ++ rest.flatten ++ remainder = source := by
        simpa [List.append_assoc] using hsource
      have hsuffix :
          source.drop (initial.length + word.length) =
            rest.flatten ++ remainder := by
        rw [← hsource]
        simp [List.append_assoc]
      have htail := ih (initial ++ word) hsourceTail
      have htail' :
          blocksWithOffsetsFrom (initial.length + word.length)
              (forwardEligibleWords remainder forward rest) =
            (blocksWithOffsetsFrom (initial.length + word.length) rest).filter
              fun block =>
                forward ≤ GapWord.span
                  (source.drop (block.offset + block.gaps.length)) := by
        simpa [List.length_append] using htail
      by_cases hforward :
          forward ≤ GapWord.span (rest.flatten ++ remainder)
      · have hhead :
            forward ≤ GapWord.span
              (source.drop (initial.length + word.length)) := by
          rw [hsuffix]
          exact hforward
        simp [forwardEligibleWords, blocksWithOffsetsFrom, hforward, hhead,
          htail']
      · have hforwardLt :
            GapWord.span (rest.flatten ++ remainder) < forward :=
          Nat.lt_of_not_ge hforward
        have hrestNil := forwardEligibleWords_eq_nil_of_span_lt remainder
          forward rest hforwardLt
        have hhead : ¬ forward ≤ GapWord.span
            (source.drop (initial.length + word.length)) := by
          rw [hsuffix]
          exact hforward
        have htailFilter :
            ((blocksWithOffsetsFrom (initial.length + word.length) rest).filter
              fun block =>
                forward ≤ GapWord.span
                  (source.drop (block.offset + block.gaps.length))) = [] := by
          rw [← htail']
          simp [hrestNil, blocksWithOffsetsFrom]
        simp [forwardEligibleWords, blocksWithOffsetsFrom, hforward, hhead,
          htailFilter]

private theorem selectedBlocks_eq_pointwise_of_bound_pos
    (segment : OddDenominatorSegment) (B : ℝ) (ell Z forward : ℕ)
    (hbound : 0 < Nat.ceil (B * ell)) :
    selectedBlocks segment B ell Z forward =
      pointwiseSelectedBlocks segment B ell Z forward := by
  let decomposition :=
    GapWord.greedyDecompose segment.gaps (Nat.ceil (B * ell))
  have hvalid := GapWord.greedyDecompose_valid segment.gaps
    (Nat.ceil (B * ell)) hbound
  change decomposition.Valid segment.gaps (Nat.ceil (B * ell)) at hvalid
  rcases hvalid with ⟨hconcat, _hgreedy, _hremainder⟩
  have hsource :
      [] ++ decomposition.completed.flatten ++ decomposition.remainder =
        segment.gaps := by
    simpa using hconcat
  have hforward := forwardEligibleBlocks_eq_filter segment.gaps []
    decomposition.remainder forward decomposition.completed hsource
  have hforward' :
      blocksWithOffsetsFrom 0
          (forwardEligibleWords decomposition.remainder forward
            decomposition.completed) =
        (blocksWithOffsetsFrom 0 decomposition.completed).filter fun block =>
          forward ≤ GapWord.span
            (segment.gaps.drop (block.offset + block.gaps.length)) := by
    simpa using hforward
  unfold selectedBlocks pointwiseSelectedBlocks
  change
    ((blocksWithOffsetsFrom 0
        (forwardEligibleWords decomposition.remainder forward
          decomposition.completed)).filter fun block =>
      decide (Z * block.gaps.length ≤ 4 * block.span)) =
    ((blocksWithOffsetsFrom 0 decomposition.completed).filter fun block =>
      decide (Z * block.gaps.length ≤ 4 * block.span ∧
        block.offset + block.gaps.length ≤ segment.gaps.length ∧
        forward ≤ GapWord.span
          (segment.gaps.drop (block.offset + block.gaps.length))))
  rw [hforward', list_filter_filter_commute]
  apply list_filter_congr_on
  intro block hblock
  have hlength := (blocksWithOffsetsFrom_occurs segment
    decomposition.completed decomposition.remainder hconcat block hblock).1
  simp [hlength]

private theorem greedyDecompose_zero (word : GapWord) :
    GapWord.greedyDecompose word 0 = ⟨[], word⟩ := by
  cases word <;> simp [GapWord.greedyDecompose, GapWord.greedyDecomposeAux]

/-- The forward-prefix and pointwise formulations select the same blocks in
the same order, including the degenerate zero-bound case. -/
theorem selectedBlocks_eq_pointwiseSelectedBlocks
    (segment : OddDenominatorSegment) (B : ℝ) (ell Z forward : ℕ) :
    selectedBlocks segment B ell Z forward =
      pointwiseSelectedBlocks segment B ell Z forward := by
  by_cases hbound : 0 < Nat.ceil (B * ell)
  · exact selectedBlocks_eq_pointwise_of_bound_pos segment B ell Z forward hbound
  · have hzero : Nat.ceil (B * ell) = 0 := Nat.eq_zero_of_not_pos hbound
    simp [selectedBlocks, pointwiseSelectedBlocks, hzero, greedyDecompose_zero,
      forwardEligibleWords, blocksWithOffsetsFrom]

private theorem blocksWithOffsetsFrom_filter_span_sum (offset : ℕ)
    (words : List GapWord) (p : GapWord → Bool) :
    (((blocksWithOffsetsFrom offset words).filter fun block => p block.gaps).map
        LowGapBlock.span).sum =
      (((words.filter p).map GapWord.span).sum) := by
  induction words generalizing offset with
  | nil => simp [blocksWithOffsetsFrom]
  | cons word rest ih =>
      cases hp : p word <;>
        simp [blocksWithOffsetsFrom, hp, LowGapBlock.span, ih]

private theorem greedyBlock_span_le_add (bound ell : ℕ) (block : GapWord)
    (hgreedy : GapWord.IsGreedyBlock bound block)
    (hgap : ∀ g ∈ block, g ≤ ell) :
    GapWord.span block ≤ bound + ell := by
  have hne : block ≠ [] := hgreedy.1
  have hlength : 0 < block.length := List.length_pos_iff.mpr hne
  have hprefix := hgreedy.2.2 (block.length - 1) (by omega)
  have hprefix' : block.dropLast.sum < bound := by
    simpa [GapWord.prefixSpan, List.dropLast_eq_take] using hprefix
  have hlast : block.getLast hne ≤ ell :=
    hgap (block.getLast hne) (List.getLast_mem hne)
  have hsplit := congrArg List.sum (List.dropLast_append_getLast hne)
  simp only [List.sum_append, List.sum_singleton] at hsplit
  change block.sum ≤ bound + ell
  omega

private theorem lowForwardWords_cover
    (words : List GapWord) (remainder : GapWord) (forward cap Z totalLength totalSpan : ℕ)
    (hcap : ∀ block ∈ words, GapWord.span block ≤ cap)
    (hremainder : GapWord.span remainder ≤ cap)
    (hlength : words.flatten.length + remainder.length = totalLength)
    (hspan : GapWord.span words.flatten + GapWord.span remainder = totalSpan)
    (hmean : Z * totalLength ≤ totalSpan)
    (hlarge : 4 * (forward + cap) ≤ totalSpan) :
    totalSpan ≤ 2 *
      (((forwardEligibleWords remainder forward words).filter fun block =>
        decide (Z * block.length ≤ 4 * GapWord.span block)).map GapWord.span).sum := by
  let eligible := forwardEligibleWords remainder forward words
  let discarded := forwardDiscardedWords remainder forward words
  let low := eligible.filter fun block =>
    decide (Z * block.length ≤ 4 * GapWord.span block)
  let bad := eligible.filter fun block =>
    !decide (Z * block.length ≤ 4 * GapWord.span block)
  have hpartition := forwardEligible_append_discarded remainder forward words
  change eligible ++ discarded = words at hpartition
  have heligibleMem : ∀ block ∈ eligible, block ∈ words := by
    intro block hblock
    rw [← hpartition]
    exact List.mem_append.mpr (Or.inl hblock)
  have hdiscardCap : ∀ block ∈ discarded, GapWord.span block ≤ cap := by
    intro block hblock
    exact hcap block (by
      rw [← hpartition]
      exact List.mem_append.mpr (Or.inr hblock))
  have htail : GapWord.span discarded.flatten + GapWord.span remainder ≤
      forward + cap := by
    simpa [discarded] using
      (forwardDiscarded_span_add_remainder_le remainder forward cap words hcap hremainder)
  have htailFour : 4 * (GapWord.span discarded.flatten + GapWord.span remainder) ≤
      totalSpan :=
    (Nat.mul_le_mul_left 4 htail).trans hlarge
  have hbadPoint : ∀ block ∈ bad,
      4 * GapWord.span block ≤ Z * block.length := by
    intro block hblock
    have hnot : ¬ Z * block.length ≤ 4 * GapWord.span block := by
      have hp := (List.mem_filter.mp hblock).2
      simpa using hp
    omega
  have hbadScaled : 4 * ((bad.map GapWord.span).sum) ≤
      Z * ((bad.map List.length).sum) := by
    calc
      4 * ((bad.map GapWord.span).sum) =
          (bad.map fun block => 4 * GapWord.span block).sum := by
            rw [List.sum_map_mul_left]
      _ ≤ (bad.map fun block => Z * block.length).sum :=
        List.sum_le_sum hbadPoint
      _ = Z * ((bad.map List.length).sum) := by
        rw [List.sum_map_mul_left]
  have hbadLength : (bad.map List.length).sum ≤ totalLength := by
    calc
      (bad.map List.length).sum ≤ (eligible.map List.length).sum :=
        list_sum_filter_le
          (fun block => !decide (Z * block.length ≤ 4 * GapWord.span block))
          List.length eligible
      _ ≤ (words.map List.length).sum := by
        rw [← List.length_flatten, ← List.length_flatten]
        have hsub : eligible.flatten.length ≤ words.flatten.length := by
          rw [← hpartition, List.flatten_append, List.length_append]
          omega
        exact hsub
      _ ≤ totalLength := by
        rw [← List.length_flatten]
        omega
  have hbadFour : 4 * (bad.map GapWord.span).sum ≤ totalSpan := by
    calc
      4 * (bad.map GapWord.span).sum ≤ Z * (bad.map List.length).sum := hbadScaled
      _ ≤ Z * totalLength := Nat.mul_le_mul_left Z hbadLength
      _ ≤ totalSpan := hmean
  have heligibleSplit :
      (low.map GapWord.span).sum + (bad.map GapWord.span).sum =
        (eligible.map GapWord.span).sum := by
    exact list_sum_filter_add_filter_not
      (fun block => decide (Z * block.length ≤ 4 * GapWord.span block))
      GapWord.span eligible
  have htotalSplit : totalSpan =
      (eligible.map GapWord.span).sum + GapWord.span discarded.flatten +
        GapWord.span remainder := by
    calc
      totalSpan = GapWord.span words.flatten + GapWord.span remainder := hspan.symm
      _ = GapWord.span (eligible.flatten ++ discarded.flatten) +
          GapWord.span remainder := by
        rw [← List.flatten_append, hpartition]
      _ = GapWord.span eligible.flatten + GapWord.span discarded.flatten +
          GapWord.span remainder := by
        simp [GapWord.span]
      _ = (eligible.map GapWord.span).sum + GapWord.span discarded.flatten +
          GapWord.span remainder := by rw [flatten_span_eq_sum_map_span]
  change totalSpan ≤ 2 * (low.map GapWord.span).sum
  omega

theorem lem_sparse_cover (Q : ℕ) (B : ℝ) (hB : 2 < B)
    (segment : OddDenominatorSegment) (_hsegment : segment.Valid Q)
    (ell Z forward : ℕ) (hell : 0 < ell) (_hZ : 0 < Z)
    (hgap : ∀ g ∈ segment.gaps, g ≤ ell)
    (hmean : Z * segment.gapCount ≤ segment.span ∧
      segment.span < 2 * Z * segment.gapCount)
    (hlarge : 4 * (forward + Nat.ceil ((B + 1) * ell)) ≤ segment.span)
    (y : ℝ) (hy0 : 0 ≤ y) (hy : y ≤ 16 * segment.span) :
    ∃ blocks : List LowGapBlock,
      IsLowGapCover segment B ell Z forward blocks ∧
      blocks.Nodup ∧
      (∀ block ∈ blocks, 0 ≤ interiorComponentWeight y blocks block) ∧
      (∀ block ∈ blocks,
        interiorComponentWeight y blocks block ≤
          32 * Nat.ceil ((B + 1) * ell)) ∧
      (blocks.map (fun block => interiorComponentWeight y blocks block)).sum = y := by
  let bound := Nat.ceil (B * ell)
  let cap := Nat.ceil ((B + 1) * ell)
  let decomposition := GapWord.greedyDecompose segment.gaps bound
  let eligible := forwardEligibleWords decomposition.remainder forward
    decomposition.completed
  let discarded := forwardDiscardedWords decomposition.remainder forward
    decomposition.completed
  let blocks :=
    (blocksWithOffsetsFrom 0 eligible).filter fun block =>
      Z * block.gaps.length ≤ 4 * block.span
  have hboundPos : 0 < bound := by
    apply Nat.ceil_pos.mpr
    have hBpos : 0 < B := lt_trans (by norm_num) hB
    positivity
  have hcapEq : cap = bound + ell := by
    dsimp [cap, bound]
    rw [show (B + 1) * (ell : ℝ) = B * ell + ell by ring]
    exact Nat.ceil_add_natCast (by positivity) ell
  have hcapPos : 0 < cap := by omega
  have hvalid := GapWord.greedyDecompose_valid segment.gaps bound hboundPos
  change decomposition.Valid segment.gaps bound at hvalid
  rcases hvalid with ⟨hconcat, hgreedy, hremainder⟩
  have hcompletedGap : ∀ word ∈ decomposition.completed,
      ∀ g ∈ word, g ≤ ell := by
    intro word hword g hg
    apply hgap g
    rw [← hconcat]
    exact List.mem_append.mpr (Or.inl
      (List.mem_flatten.mpr ⟨word, hword, hg⟩))
  have hcompletedCap : ∀ word ∈ decomposition.completed,
      GapWord.span word ≤ cap := by
    intro word hword
    have hadd := greedyBlock_span_le_add bound ell word
      (hgreedy word hword) (hcompletedGap word hword)
    simpa [hcapEq] using hadd
  have hremainderCap : GapWord.span decomposition.remainder ≤ cap := by
    omega
  have hlengthRaw := congrArg List.length hconcat
  have hlength : decomposition.completed.flatten.length +
      decomposition.remainder.length = segment.gapCount := by
    simpa [OddDenominatorSegment.gapCount] using hlengthRaw
  have hspanRaw := congrArg List.sum hconcat
  have hspan : GapWord.span decomposition.completed.flatten +
      GapWord.span decomposition.remainder = segment.span := by
    simpa [OddDenominatorSegment.span, GapWord.span] using hspanRaw
  have hcoverWords := lowForwardWords_cover decomposition.completed
    decomposition.remainder forward cap Z segment.gapCount segment.span
    hcompletedCap hremainderCap hlength hspan hmean.1 (by
      simpa [cap] using hlarge)
  have hpartition := forwardEligible_append_discarded decomposition.remainder
    forward decomposition.completed
  change eligible ++ discarded = decomposition.completed at hpartition
  have heligibleMem : ∀ word ∈ eligible, word ∈ decomposition.completed := by
    intro word hword
    rw [← hpartition]
    exact List.mem_append.mpr (Or.inl hword)
  have heligibleGreedy : ∀ word ∈ eligible,
      GapWord.IsGreedyBlock bound word := by
    intro word hword
    exact hgreedy word (heligibleMem word hword)
  have heligibleNonempty : ∀ word ∈ eligible, word ≠ [] := by
    intro word hword
    exact (heligibleGreedy word hword).1
  have heligibleConcat :
      eligible.flatten ++ (discarded.flatten ++ decomposition.remainder) =
        segment.gaps := by
    calc
      eligible.flatten ++ (discarded.flatten ++ decomposition.remainder) =
          (eligible ++ discarded).flatten ++ decomposition.remainder := by
            simp [List.flatten_append, List.append_assoc]
      _ = decomposition.completed.flatten ++ decomposition.remainder := by
        rw [hpartition]
      _ = segment.gaps := hconcat
  have hblocksNodup : blocks.Nodup := by
    dsimp [blocks]
    exact (blocksWithOffsetsFrom_nodup 0 eligible heligibleNonempty).filter _
  have hblocksSpan : (blocks.map LowGapBlock.span).sum =
      (((eligible.filter fun word =>
        decide (Z * word.length ≤ 4 * GapWord.span word)).map
          GapWord.span).sum) := by
    dsimp [blocks]
    exact blocksWithOffsetsFrom_filter_span_sum 0 eligible
      (fun word => decide (Z * word.length ≤ 4 * GapWord.span word))
  have hcover : segment.span ≤ 2 * (blocks.map LowGapBlock.span).sum := by
    rw [hblocksSpan]
    exact hcoverWords
  have hsegmentSpanPos : 0 < segment.span := by omega
  have hsumPos : 0 < (blocks.map LowGapBlock.span).sum := by omega
  have hselected : blocks = selectedBlocks segment B ell Z forward := by
    rfl
  have hblockData : ∀ block ∈ blocks,
      LowGapBlock.OccursIn segment block ∧
        GapWord.IsGreedyBlock bound block.gaps ∧
        Z * block.gaps.length ≤ 4 * block.span := by
    intro block hblock
    have hmem := List.mem_filter.mp hblock
    have hlow : Z * block.gaps.length ≤ 4 * block.span := by
      simpa using hmem.2
    have hoccurs := blocksWithOffsetsFrom_occurs segment eligible
      (discarded.flatten ++ decomposition.remainder) heligibleConcat block hmem.1
    rcases blocksWithOffsetsFrom_mem_split 0 eligible block hmem.1 with
      ⟨before, after, hwords, _hoffset⟩
    have hword : block.gaps ∈ eligible := by
      rw [hwords]
      simp
    exact ⟨hoccurs, heligibleGreedy block.gaps hword, hlow⟩
  have hcoverCertificate : IsLowGapCover segment B ell Z forward blocks := by
    exact ⟨hselected, hblockData, hcover⟩
  have hdenPos : (0 : ℝ) < (blocks.map LowGapBlock.span).sum := by
    exact_mod_cast hsumPos
  have hcoverReal : (segment.span : ℝ) ≤
      2 * ((blocks.map LowGapBlock.span).sum : ℝ) := by
    exact_mod_cast hcover
  have hyDen : y ≤ 32 * ((blocks.map LowGapBlock.span).sum : ℝ) := by
    nlinarith
  have hweightNonneg : ∀ block ∈ blocks,
      0 ≤ interiorComponentWeight y blocks block := by
    intro block _hblock
    unfold interiorComponentWeight
    exact div_nonneg (mul_nonneg hy0 (by positivity)) hdenPos.le
  have hweightUpper : ∀ block ∈ blocks,
      interiorComponentWeight y blocks block ≤ (32 : ℝ) * cap := by
    intro block hblock
    have hmem := List.mem_filter.mp hblock
    rcases blocksWithOffsetsFrom_mem_split 0 eligible block hmem.1 with
      ⟨before, after, hwords, _hoffset⟩
    have hword : block.gaps ∈ eligible := by
      rw [hwords]
      simp
    have hblockCap : block.span ≤ cap :=
      hcompletedCap block.gaps (heligibleMem block.gaps hword)
    unfold interiorComponentWeight
    have hfirst :
        y * (block.span : ℝ) /
            ((blocks.map LowGapBlock.span).sum : ℝ) ≤
          32 * (block.span : ℝ) := by
      apply (div_le_iff₀ hdenPos).2
      have hmul := mul_le_mul_of_nonneg_right hyDen
        (show (0 : ℝ) ≤ block.span by positivity)
      nlinarith
    exact hfirst.trans (by exact_mod_cast
      (Nat.mul_le_mul_left 32 hblockCap))
  have hcastSpan :
      (blocks.map (fun block => (block.span : ℝ))).sum =
        ((blocks.map LowGapBlock.span).sum : ℝ) := by
    induction blocks with
    | nil => simp
    | cons block rest ih => simp [ih]
  have hsumWeights :
      (blocks.map (fun block =>
        interiorComponentWeight y blocks block)).sum = y := by
    change
      (blocks.map (fun block =>
        y * (block.span : ℝ) /
          ((blocks.map LowGapBlock.span).sum : ℝ))).sum = y
    calc
      _ = (blocks.map (fun block =>
          (y / ((blocks.map LowGapBlock.span).sum : ℝ)) *
            (block.span : ℝ))).sum := by
            apply congrArg List.sum
            apply List.map_congr_left
            intro block _hblock
            ring
      _ = (y / ((blocks.map LowGapBlock.span).sum : ℝ)) *
          (blocks.map (fun block => (block.span : ℝ))).sum := by
            rw [List.sum_map_mul_left]
      _ = (y / ((blocks.map LowGapBlock.span).sum : ℝ)) *
          ((blocks.map LowGapBlock.span).sum : ℝ) := by rw [hcastSpan]
      _ = y := by field_simp
  refine ⟨blocks, hcoverCertificate, hblocksNodup, hweightNonneg, ?_,
    hsumWeights⟩
  simpa [cap] using hweightUpper

/-- Paper label: `lem:signature-entropy` (Section 6). -/
private def compositionShiftEmbedding (n : ℕ) :
    Function.Embedding (Fin (n - 1)) (Fin (n + 1)) :=
  (Fin.succEmb (n - 1)).trans
    (Fin.castLEEmb (Nat.add_le_add_right (Nat.sub_le n 1) 1))

private theorem compositionAsSetEquiv_symm_length (n : ℕ) (hn : 0 < n)
    (s : Finset (Fin (n - 1))) :
    ((compositionAsSetEquiv n).symm s).length = s.card + 1 := by
  let d := (compositionAsSetEquiv n).symm s
  have hboundaries :
      d.boundaries =
        insert 0 (insert (Fin.last n) (s.map (compositionShiftEmbedding n))) := by
    ext i
    dsimp [d, compositionAsSetEquiv]
    change i ∈ ({i : Fin (n + 1) | i = 0 ∨ i = Fin.last n ∨
      ∃ j : Fin (n - 1), ∃ _hj : j ∈ s, i.val = j.val + 1} : Set _).toFinset ↔ _
    simp only [Set.mem_toFinset, Set.mem_setOf_eq, Finset.mem_insert, Finset.mem_map]
    constructor
    · rintro (rfl | rfl | ⟨j, hj, hv⟩)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · right
        right
        exact ⟨j, hj, by
          apply Fin.ext
          simpa [compositionShiftEmbedding] using hv.symm⟩
    · rintro (rfl | rfl | ⟨j, hj, hv⟩)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · right
        right
        exact ⟨j, hj, by
          have hval := congrArg Fin.val hv
          simpa [compositionShiftEmbedding] using hval.symm⟩
  rw [CompositionAsSet.length, hboundaries]
  have hzero :
      (0 : Fin (n + 1)) ∉ s.map (compositionShiftEmbedding n) := by
    simp only [Finset.mem_map]
    rintro ⟨j, _hj, h⟩
    have hval := congrArg Fin.val h
    simp [compositionShiftEmbedding] at hval
  have hlast :
      Fin.last n ∉ s.map (compositionShiftEmbedding n) := by
    simp only [Finset.mem_map]
    rintro ⟨j, _hj, h⟩
    have hval := congrArg Fin.val h
    simp [compositionShiftEmbedding] at hval
    omega
  have hzeroLast : (0 : Fin (n + 1)) ≠ Fin.last n := by
    intro h
    have hval := congrArg Fin.val h
    simp at hval
    omega
  rw [Finset.card_insert_of_notMem]
  · rw [Finset.card_insert_of_notMem hlast, Finset.card_map]
    omega
  · simp [hzero, hzeroLast]

private def compositionCuts {n : ℕ} (c : Composition n) :
    Finset (Fin (n - 1)) :=
  (compositionAsSetEquiv n) ((compositionEquiv n) c)

private theorem compositionCuts_card {n : ℕ} (hn : 0 < n)
    (c : Composition n) :
    (compositionCuts c).card = c.length - 1 := by
  let s := compositionCuts c
  have hinv : (compositionAsSetEquiv n).symm s = (compositionEquiv n) c := by
    exact (compositionAsSetEquiv n).symm_apply_apply ((compositionEquiv n) c)
  have hleft := compositionAsSetEquiv_symm_length n hn s
  rw [hinv] at hleft
  have hleft' : c.length = s.card + 1 := by
    simpa [compositionEquiv] using hleft
  change s.card = c.length - 1
  omega

private theorem compositionCuts_injective {n : ℕ} :
    Function.Injective (compositionCuts : Composition n → Finset (Fin (n - 1))) := by
  exact ((compositionEquiv n).trans (compositionAsSetEquiv n)).injective

private def cutCodeFinset (H rMax : ℕ) : Finset (Finset (Fin H)) :=
  (Finset.Icc 1 rMax).biUnion fun r ↦
    (Finset.univ : Finset (Fin H)).powersetCard (r - 1)

private theorem cutCodeFinset_card (H rMax : ℕ) :
    (cutCodeFinset H rMax).card =
      ∑ r ∈ Finset.Icc 1 rMax, Nat.choose H (r - 1) := by
  have hdisjoint :
      ((Finset.Icc 1 rMax : Finset ℕ) : Set ℕ).PairwiseDisjoint
        (fun r ↦ (Finset.univ : Finset (Fin H)).powersetCard (r - 1)) := by
    intro r hr t ht hrt
    dsimp [Function.onFun]
    rw [Finset.disjoint_left]
    intro s hsr hst
    have hrcard := (Finset.mem_powersetCard.mp hsr).2
    have htcard := (Finset.mem_powersetCard.mp hst).2
    have hrone : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have htone : 1 ≤ t := (Finset.mem_Icc.mp ht).1
    apply hrt
    omega
  rw [cutCodeFinset, Finset.card_biUnion hdisjoint]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

private def paddedComposition (H : ℕ) (w : GapWord)
    (hpos : w.Positive) (hspan : w.span ≤ H) : Composition (H + 1) where
  blocks := w ++ [H + 1 - w.span]
  blocks_pos := by
    intro g hg
    rw [List.mem_append] at hg
    rcases hg with hg | hg
    · exact hpos g hg
    · simp only [List.mem_singleton] at hg
      subst g
      omega
  blocks_sum := by
    change w.sum ≤ H at hspan
    change (w ++ [H + 1 - w.sum]).sum = H + 1
    simp only [List.sum_append, List.sum_singleton]
    omega

private theorem paddedComposition_injective (H : ℕ) :
    Set.InjOn
      (fun x : {w : GapWord // w.Positive ∧ w.span ≤ H} ↦
        paddedComposition H x.1 x.2.1 x.2.2)
      Set.univ := by
  intro u _hu v _hv huv
  apply Subtype.ext
  have hblocks := congrArg Composition.blocks huv
  have hdrop := congrArg List.dropLast hblocks
  simpa [paddedComposition] using hdrop

private def encodingHeight (B : ℝ) (D : ℕ) : ℕ :=
  Nat.ceil ((B + 1) * Nat.ceil (Real.logb 2 (4 * D)))

private theorem encodingCandidate_positive {D Z : ℕ} {B : ℝ}
    {sigma : BlockEncoding} (hsigma : sigma ∈ encodingCandidates D Z B) :
    sigma.gaps.Positive := by
  exact hsigma.1.2.2.2.2

private theorem encodingCandidate_span_le_height {D Z : ℕ} {B : ℝ}
    {sigma : BlockEncoding} (hsigma : sigma ∈ encodingCandidates D Z B) :
    sigma.gaps.span ≤ encodingHeight B D := by
  have hheight : (sigma.h : ℝ) ≤
      (B + 1) * Nat.ceil (Real.logb 2 (4 * D)) := hsigma.2.2.2.2.1
  have hceil :
      (B + 1) * Nat.ceil (Real.logb 2 (4 * D)) ≤
        (encodingHeight B D : ℝ) := by
    exact Nat.le_ceil _
  have hnat : sigma.h ≤ encodingHeight B D := by
    exact_mod_cast hheight.trans hceil
  simpa [BlockEncoding.Valid] using
    (show sigma.gaps.span ≤ encodingHeight B D by
      rw [← hsigma.1.2.2.1]
      exact hnat)

private def encodingPaddedComposition {D Z : ℕ} {B : ℝ}
    (sigma : {sigma : BlockEncoding // sigma ∈ encodingCandidates D Z B}) :
    Composition (encodingHeight B D + 1) :=
  paddedComposition (encodingHeight B D) sigma.1.gaps
    (encodingCandidate_positive sigma.2)
    (encodingCandidate_span_le_height sigma.2)

private def encodingCutCode {D Z : ℕ} {B : ℝ}
    (sigma : {sigma : BlockEncoding // sigma ∈ encodingCandidates D Z B}) :
    Finset (Fin (encodingHeight B D)) :=
  compositionCuts (encodingPaddedComposition sigma)

private theorem encodingCutCode_injective {D Z : ℕ} {B : ℝ} :
    Function.Injective
      (encodingCutCode (D := D) (Z := Z) (B := B)) := by
  intro sigma tau heq
  have hcompositions :
      encodingPaddedComposition sigma = encodingPaddedComposition tau := by
    apply compositionCuts_injective
    exact heq
  let wsigma : {w : GapWord // w.Positive ∧ w.span ≤ encodingHeight B D} :=
    ⟨sigma.1.gaps, encodingCandidate_positive sigma.2,
      encodingCandidate_span_le_height sigma.2⟩
  let wtau : {w : GapWord // w.Positive ∧ w.span ≤ encodingHeight B D} :=
    ⟨tau.1.gaps, encodingCandidate_positive tau.2,
      encodingCandidate_span_le_height tau.2⟩
  have hwords : wsigma = wtau :=
    paddedComposition_injective (encodingHeight B D)
      (Set.mem_univ wsigma) (Set.mem_univ wtau) hcompositions
  have hgaps : sigma.1.gaps = tau.1.gaps := congrArg Subtype.val hwords
  apply Subtype.ext
  apply BlockEncoding.ext
  · exact sigma.2.2.1.trans tau.2.2.1.symm
  · exact sigma.2.2.2.1.trans tau.2.2.2.1.symm
  · rw [sigma.2.1.2.2.1, tau.2.1.2.2.1, hgaps]
  · rw [sigma.2.1.2.2.2.1, tau.2.1.2.2.2.1, hgaps]
  · exact hgaps

private theorem eventually_le_encodingHeight (B cBand : ℝ)
    (hB : 2 < B) (hcBand : 0 < cBand) :
    ∀ᶠ Z : ℕ in atTop, ∀ D : ℕ,
      cBand * (2 : ℝ) ^ Z ≤ D → Z ≤ encodingHeight B D := by
  have hpowers :
      ∀ᶠ n : ℕ in atTop, (1 / cBand : ℝ) ≤ (2 : ℝ) ^ n :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually_ge_atTop _
  obtain ⟨N, hN⟩ := eventually_atTop.mp hpowers
  filter_upwards [eventually_ge_atTop (max (2 * N) 2)] with Z hZ
  intro D hD
  have hNhalf : N ≤ Z / 2 := by omega
  have honeDiv : (1 / cBand : ℝ) ≤ (2 : ℝ) ^ (Z / 2) :=
    (hN N le_rfl).trans (pow_le_pow_right₀ (by norm_num) hNhalf)
  have hone : (1 : ℝ) ≤ cBand * (2 : ℝ) ^ (Z / 2) := by
    have := mul_le_mul_of_nonneg_left honeDiv hcBand.le
    field_simp at this
    exact this
  have hhalfD : (2 : ℝ) ^ (Z / 2) ≤ D := by
    calc
      (2 : ℝ) ^ (Z / 2) ≤
          (cBand * (2 : ℝ) ^ (Z / 2)) * (2 : ℝ) ^ (Z / 2) := by
            calc
              (2 : ℝ) ^ (Z / 2) = 1 * (2 : ℝ) ^ (Z / 2) := by ring
              _ ≤ (cBand * (2 : ℝ) ^ (Z / 2)) * (2 : ℝ) ^ (Z / 2) :=
                mul_le_mul_of_nonneg_right hone (by positivity)
      _ = cBand * (2 : ℝ) ^ (2 * (Z / 2)) := by
        rw [show 2 * (Z / 2) = Z / 2 + Z / 2 by omega, pow_add]
        ring
      _ ≤ cBand * (2 : ℝ) ^ Z := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ (by norm_num) (by omega)) hcBand.le
      _ ≤ D := hD
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le (by positivity) hhalfD
  have hlogD : ((Z / 2 : ℕ) : ℝ) ≤ Real.logb 2 (D : ℝ) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) hDpos]
    simpa [Real.rpow_natCast] using hhalfD
  have hlog4D : ((Z / 2 : ℕ) : ℝ) ≤ Real.logb 2 (4 * D) := by
    have hDle : (D : ℝ) ≤ 4 * D := by nlinarith [hDpos]
    exact hlogD.trans
      (Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hDpos hDle)
  let ell := Nat.ceil (Real.logb 2 (4 * D))
  have hhalfEll : Z / 2 ≤ ell := by
    have hhalfEllReal : ((Z / 2 : ℕ) : ℝ) ≤ (ell : ℝ) := by
      simpa [ell] using hlog4D.trans (Nat.le_ceil (Real.logb 2 (4 * D)))
    exact_mod_cast hhalfEllReal
  have hellPos : 0 < ell := by
    have : 1 ≤ Z / 2 := by omega
    omega
  have hthree : 3 * ell ≤ encodingHeight B D := by
    have hceil : (B + 1) * (ell : ℝ) ≤ (encodingHeight B D : ℝ) := by
      simpa [encodingHeight, ell] using
        (Nat.le_ceil ((B + 1) * (ell : ℝ)))
    have hellReal : (0 : ℝ) < ell := by exact_mod_cast hellPos
    exact_mod_cast (show (3 : ℝ) * ell ≤ encodingHeight B D by
      nlinarith)
  omega

private theorem encodingCutCode_mem {D Z : ℕ} {B : ℝ}
    (hZ : 0 < Z) (hZH : Z ≤ encodingHeight B D)
    (sigma : {sigma : BlockEncoding // sigma ∈ encodingCandidates D Z B}) :
    encodingCutCode sigma ∈
      cutCodeFinset (encodingHeight B D)
        (Nat.floor ((5 / (Z : ℝ)) * (encodingHeight B D + 1))) := by
  let H := encodingHeight B D
  let rMax := Nat.floor ((5 / (Z : ℝ)) * (H + 1))
  have hHspan : sigma.1.h ≤ H := by
    rw [sigma.2.1.2.2.1]
    exact encodingCandidate_span_le_height sigma.2
  have hZreal : (0 : ℝ) < Z := by exact_mod_cast hZ
  have hrbound : (sigma.1.r : ℝ) ≤ 4 * sigma.1.h / Z :=
    sigma.2.2.2.2.2.2
  have hscaled : (sigma.1.r : ℝ) * Z ≤ 4 * sigma.1.h := by
    exact (le_div_iff₀ hZreal).mp hrbound
  have hrMaxReal : ((sigma.1.r + 1 : ℕ) : ℝ) ≤
      (5 / (Z : ℝ)) * (H + 1) := by
    have hZHreal : (Z : ℝ) ≤ H := by exact_mod_cast hZH
    have hhreal : (sigma.1.h : ℝ) ≤ H := by exact_mod_cast hHspan
    rw [div_mul_eq_mul_div]
    rw [le_div_iff₀ hZreal]
    push_cast
    nlinarith
  have hrMaxNat : sigma.1.r + 1 ≤ rMax := by
    exact Nat.le_floor hrMaxReal
  rw [cutCodeFinset, Finset.mem_biUnion]
  refine ⟨sigma.1.r + 1, ?_, ?_⟩
  · exact Finset.mem_Icc.mpr ⟨by omega, hrMaxNat⟩
  · rw [Finset.mem_powersetCard]
    constructor
    · exact Finset.subset_univ _
    · have hcard := compositionCuts_card
          (show 0 < H + 1 by omega) (encodingPaddedComposition sigma)
      have hlength : (encodingPaddedComposition sigma).length = sigma.1.r + 1 := by
        change (sigma.1.gaps ++ [H + 1 - sigma.1.gaps.span]).length = _
        simp [sigma.2.1.2.2.2.1]
      change (compositionCuts (encodingPaddedComposition sigma)).card = _
      rw [hcard, hlength]

theorem lem_signature_entropy (B cBand : ℝ) (hB : 2 < B)
    (hcBand : 0 < cBand) :
    ∃ Zstar : ℕ, ∃ CB : ℝ, 0 < CB ∧ ∀ D Z : ℕ,
      Zstar ≤ Z → cBand * (2 : ℝ) ^ Z ≤ D →
      (encodingCandidates D Z B).Finite ∧
      ((encodingCandidates D Z B).ncard : ℝ) ≤
          CB * (Nat.ceil (Real.logb 2 (4 * D)) : ℝ) ^ 3 *
            Real.rpow 2
              ((B + 1) * Nat.ceil (Real.logb 2 (4 * D)) *
                binaryEntropy (5 / Z)) ∧
      ((encodingCandidates D Z B).ncard : ℝ) *
          Nat.ceil (Real.logb 2 (4 * D)) ≤ Real.sqrt D := by
  let CB : ℝ := 4 * (B + 3) ^ 2
  have hCB : 0 < CB := by
    dsimp [CB]
    positivity
  obtain ⟨Zheight, hheight⟩ := eventually_atTop.mp
    (eventually_le_encodingHeight B cBand hB hcBand)
  obtain ⟨Zquant, hquant⟩ := lem_quant_entropy B cBand CB hB hcBand hCB
  refine ⟨max (max Zheight Zquant) 10, CB, hCB, ?_⟩
  intro D Z hZ hD
  have hZten : 10 ≤ Z := le_trans (le_max_right _ _) hZ
  have hZpos : 0 < Z := by omega
  have hZH : Z ≤ encodingHeight B D :=
    hheight Z (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hZ)) D hD
  let ell := Nat.ceil (Real.logb 2 (4 * D))
  let H := encodingHeight B D
  let alpha : ℝ := 5 / Z
  let rMax := Nat.floor (alpha * (H + 1))
  have hHpos : 0 < H := lt_of_lt_of_le hZpos hZH
  have hHtwo : 2 ≤ H + 1 := by omega
  have halphaPos : 0 < alpha := by
    dsimp [alpha]
    positivity
  have halphaHalf : alpha ≤ (1 : ℝ) / 2 := by
    dsimp [alpha]
    have hZreal : (10 : ℝ) ≤ Z := by exact_mod_cast hZten
    have hZrealPos : (0 : ℝ) < Z := by positivity
    rw [div_le_iff₀ hZrealPos]
    nlinarith
  have halphaNonneg : 0 ≤ alpha := halphaPos.le
  have hargNonneg : 0 ≤ alpha * (H + 1 : ℝ) := by positivity
  have hrMax : (rMax : ℝ) ≤ alpha * (H + 1) := by
    exact Nat.floor_le hargNonneg
  have hrMax' : (rMax : ℝ) ≤ alpha * (((H + 1 : ℕ) : ℝ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hrMax
  have hcomposition :=
    lem_composition_entropy (H + 1) rMax alpha hHtwo halphaPos halphaHalf hrMax'
  let source : Set BlockEncoding := encodingCandidates D Z B
  let code := encodingCutCode (D := D) (Z := Z) (B := B)
  let codes := cutCodeFinset H rMax
  have hcodeMem (sigma : source) : code sigma ∈ codes := by
    simpa [code, codes, H, alpha, rMax] using
      (encodingCutCode_mem hZpos hZH sigma)
  have hcodeInjective : Function.Injective code := by
    simpa [code] using
      (encodingCutCode_injective (D := D) (Z := Z) (B := B))
  have himageFinite : (code '' (Set.univ : Set source)).Finite := by
    apply codes.finite_toSet.subset
    rintro y ⟨sigma, _hsigma, rfl⟩
    exact hcodeMem sigma
  have hunivFinite : (Set.univ : Set source).Finite :=
    himageFinite.of_finite_image (Set.injOn_univ.mpr hcodeInjective)
  letI : Finite source := Set.finite_univ_iff.mp hunivFinite
  letI : Fintype source := Fintype.ofFinite source
  have hcardNat : source.ncard ≤ codes.card := by
    have hle := Fintype.card_le_of_injective
      (fun sigma : source ↦ (⟨code sigma, hcodeMem sigma⟩ : codes))
      (fun _ _ h ↦ hcodeInjective (congrArg Subtype.val h))
    simpa [source, codes, Nat.card_eq_fintype_card] using hle
  have hcodesCard : codes.card =
      ∑ r ∈ Finset.Icc 1 rMax, Nat.choose H (r - 1) := by
    simpa [codes] using cutCodeFinset_card H rMax
  have hcountComposition : (source.ncard : ℝ) ≤
      ((H + 1 : ℕ) : ℝ) ^ 2 *
        Real.rpow 2 (((H + 1 : ℕ) : ℝ) * binaryEntropy alpha) := by
    calc
      (source.ncard : ℝ) ≤ codes.card := by exact_mod_cast hcardNat
      _ = (∑ r ∈ Finset.Icc 1 rMax,
          Nat.choose ((H + 1) - 1) (r - 1) : ℕ) := by
            rw [hcodesCard]
            simp only [Nat.add_sub_cancel]
      _ ≤ ((H + 1 : ℕ) : ℝ) ^ 2 *
          Real.rpow 2 (((H + 1 : ℕ) : ℝ) * binaryEntropy alpha) :=
            hcomposition
  have hellPos : 0 < ell := by
    by_contra hell
    have hellZero : ell = 0 := Nat.eq_zero_of_not_pos hell
    have hHZero : H = 0 := by simp [H, encodingHeight, ell, hellZero]
    omega
  have hellReal : (0 : ℝ) < ell := by exact_mod_cast hellPos
  have hheightLt : (H : ℝ) < (B + 1) * ell + 1 := by
    have hnonneg : 0 ≤ (B + 1) * (ell : ℝ) := by positivity
    simpa [H, encodingHeight, ell] using Nat.ceil_lt_add_one hnonneg
  have hentropyEq :
      binaryEntropy alpha = Real.binEntropy alpha / Real.log 2 := by
    rw [binaryEntropy, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    simp only [Real.negMulLog, Real.logb]
    ring
  have hentropyNonneg : 0 ≤ binaryEntropy alpha := by
    rw [hentropyEq]
    exact div_nonneg
      (Real.binEntropy_nonneg halphaNonneg (halphaHalf.trans (by norm_num)))
      (Real.log_nonneg (by norm_num))
  have hentropyOne : binaryEntropy alpha ≤ 1 := by
    rw [hentropyEq]
    exact (div_le_one (Real.log_pos (by norm_num))).2 Real.binEntropy_le_log_two
  have hpoly : (((H + 1 : ℕ) : ℝ) ^ 2) ≤
      (B + 3) ^ 2 * (ell : ℝ) ^ 2 := by
    have hlinear : ((H + 1 : ℕ) : ℝ) ≤ (B + 3) * ell := by
      push_cast
      have hellOne : (1 : ℝ) ≤ ell := by exact_mod_cast hellPos
      nlinarith
    simpa [mul_pow] using pow_le_pow_left₀ (by positivity) hlinear 2
  have hexponent : (((H + 1 : ℕ) : ℝ) * binaryEntropy alpha) ≤
      (B + 1) * ell * binaryEntropy alpha + 2 := by
    have hHplus : (((H + 1 : ℕ) : ℝ) ≤ (B + 1) * ell + 2) := by
      push_cast
      linarith
    nlinarith
  have hrpow :
      Real.rpow 2 (((H + 1 : ℕ) : ℝ) * binaryEntropy alpha) ≤
        4 * Real.rpow 2 ((B + 1) * ell * binaryEntropy alpha) := by
    calc
      Real.rpow 2 (((H + 1 : ℕ) : ℝ) * binaryEntropy alpha) ≤
          Real.rpow 2 ((B + 1) * ell * binaryEntropy alpha + 2) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent
      _ = 4 * Real.rpow 2 ((B + 1) * ell * binaryEntropy alpha) := by
        change (2 : ℝ) ^ ((B + 1) * ell * binaryEntropy alpha + 2) =
          4 * (2 : ℝ) ^ ((B + 1) * ell * binaryEntropy alpha)
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        norm_num [Real.rpow_natCast]
        ring
  have hcount : ((encodingCandidates D Z B).ncard : ℝ) ≤
      CB * (ell : ℝ) ^ 3 *
        Real.rpow 2 ((B + 1) * ell * binaryEntropy alpha) := by
    have hrpowNonneg :
        0 ≤ Real.rpow 2 ((B + 1) * ell * binaryEntropy alpha) :=
      Real.rpow_nonneg (by norm_num) _
    have hleftNonneg : (0 : ℝ) ≤ (((H + 1 : ℕ) : ℝ) ^ 2) := by positivity
    calc
      ((encodingCandidates D Z B).ncard : ℝ) = (source.ncard : ℝ) := rfl
      _ ≤ (((H + 1 : ℕ) : ℝ) ^ 2) *
          Real.rpow 2 (((H + 1 : ℕ) : ℝ) * binaryEntropy alpha) :=
            hcountComposition
      _ ≤ (((H + 1 : ℕ) : ℝ) ^ 2) *
          (4 * Real.rpow 2 ((B + 1) * ell * binaryEntropy alpha)) :=
            mul_le_mul_of_nonneg_left hrpow hleftNonneg
      _ ≤ ((B + 3) ^ 2 * (ell : ℝ) ^ 2) *
          (4 * Real.rpow 2 ((B + 1) * ell * binaryEntropy alpha)) := by
            exact mul_le_mul_of_nonneg_right hpoly (by positivity)
      _ ≤ CB * (ell : ℝ) ^ 3 *
          Real.rpow 2 ((B + 1) * ell * binaryEntropy alpha) := by
            dsimp [CB]
            have hellOne : (1 : ℝ) ≤ ell := by exact_mod_cast hellPos
            have hepow : (ell : ℝ) ^ 2 ≤ ell ^ 3 := by
              nlinarith [sq_nonneg (ell : ℝ)]
            calc
              (B + 3) ^ 2 * ell ^ 2 *
                  (4 * Real.rpow 2 ((B + 1) * ell * binaryEntropy alpha)) =
                  (4 * (B + 3) ^ 2 *
                    Real.rpow 2 ((B + 1) * ell * binaryEntropy alpha)) * ell ^ 2 := by
                      ring
              _ ≤ (4 * (B + 3) ^ 2 *
                    Real.rpow 2 ((B + 1) * ell * binaryEntropy alpha)) * ell ^ 3 :=
                  mul_le_mul_of_nonneg_left hepow (by positivity)
              _ = 4 * (B + 3) ^ 2 * ell ^ 3 *
                    Real.rpow 2 ((B + 1) * ell * binaryEntropy alpha) := by
                      ring
  constructor
  · exact Set.toFinite _
  constructor
  · simpa [ell, alpha] using hcount
  · have hquantApply := hquant Z D
        (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hZ)) hD
    have hmul := mul_le_mul_of_nonneg_right hcount (by positivity : (0 : ℝ) ≤ ell)
    calc
      ((encodingCandidates D Z B).ncard : ℝ) *
          Nat.ceil (Real.logb 2 (4 * D)) =
          ((encodingCandidates D Z B).ncard : ℝ) * ell := by rfl
      _ ≤ (CB * (ell : ℝ) ^ 3 *
          Real.rpow 2 ((B + 1) * ell * binaryEntropy alpha)) * ell := hmul
      _ = CB * (ell : ℝ) ^ 4 *
          Real.rpow 2 ((B + 1) * ell * binaryEntropy alpha) := by ring
      _ ≤ Real.sqrt D := by simpa [ell, alpha] using hquantApply

/-- Paper label: `lem:word-slope` (Section 6). -/
theorem lem_word_slope (B : ℝ) (hB : 2 < B) (D : ℕ) (hD : 0 < D)
    (w : GapWord)
    (hspan : B * Nat.ceil (Real.logb 2 (4 * D)) ≤ w.span) :
    Set.Subsingleton
      {μ : ℚ | D ≤ μ.den ∧ μ.den < 2 * D ∧
        slopeAfter w μ ∈ Set.Ioo (0 : ℝ) 1} := by
  intro μ hμ ν hν
  by_contra hne
  let ell := Nat.ceil (Real.logb 2 (4 * (D : ℝ)))
  have hell_eq : ell = Nat.clog 2 (4 * D) := by
    dsimp [ell]
    simpa only [Nat.cast_ofNat, Nat.cast_mul] using
      Real.natCeil_logb_natCast 2 (4 * D)
  have hfourD : 4 * D ≤ 2 ^ ell := by
    rw [hell_eq]
    exact Nat.le_pow_clog (by omega) _
  have hellpos : 0 < ell := by
    rw [hell_eq, Nat.lt_clog_iff_pow_lt (by omega)]
    simp
    omega
  have htwoellR : (2 * ell : ℝ) < (w.span : ℝ) := by
    have hmul : (2 : ℝ) * ell < B * ell :=
      mul_lt_mul_of_pos_right hB (by exact_mod_cast hellpos)
    have hspan' : B * (ell : ℝ) ≤ (w.span : ℝ) := by
      simpa [ell] using hspan
    nlinarith
  have htwoell : 2 * ell < w.span := by exact_mod_cast htwoellR
  have hbandpow : (4 * D) ^ 2 ≤ 2 ^ (2 * ell) := by
    calc
      (4 * D) ^ 2 ≤ (2 ^ ell) ^ 2 := Nat.pow_le_pow_left hfourD 2
      _ = 2 ^ (2 * ell) := by
        rw [← pow_mul]
        congr 1
        omega
  have hpowlt : 2 ^ (2 * ell) < 2 ^ w.span := by
    exact Nat.pow_lt_pow_right (by omega) htwoell
  have hdenpowNat : 4 * D ^ 2 < 2 ^ w.span := by
    have hD1 : 1 ≤ D := hD
    calc
      4 * D ^ 2 ≤ (4 * D) ^ 2 := by nlinarith
      _ ≤ 2 ^ (2 * ell) := hbandpow
      _ < 2 ^ w.span := hpowlt
  have hdenpow : (4 : ℝ) * (D : ℝ) ^ 2 < (2 : ℝ) ^ w.span := by
    exact_mod_cast hdenpowNat
  have hdenpos : (0 : ℝ) < 4 * (D : ℝ) ^ 2 := by positivity
  have hrecip : 1 / (2 : ℝ) ^ w.span < 1 / (4 * (D : ℝ) ^ 2) :=
    one_div_lt_one_div_of_lt hdenpos hdenpow
  have hμcyl := lem_word_cylinder w (μ : ℝ) hμ.2.2
  have hνcyl := lem_word_cylinder w (ν : ℝ) hν.2.2
  have hpowpos : (0 : ℝ) < (2 : ℝ) ^ w.span := by positivity
  have hwidth :
      (((wordMultiplier w : ℝ) + 1) / (2 : ℝ) ^ w.span) -
          ((wordMultiplier w : ℝ) / (2 : ℝ) ^ w.span) =
        1 / (2 : ℝ) ^ w.span := by
    field_simp
    ring
  have habs : |(μ : ℝ) - (ν : ℝ)| < 1 / (2 : ℝ) ^ w.span := by
    rw [abs_lt]
    constructor <;> linarith [hμcyl.1, hμcyl.2, hνcyl.1, hνcyl.2, hwidth]
  have hfracne : (μ.num : ℚ) / μ.den ≠ (ν.num : ℚ) / ν.den := by
    intro heq
    apply hne
    rw [← μ.num_div_den, ← ν.num_div_den]
    exact heq
  have hfarey := lem_farey μ.num ν.num μ.den ν.den D
    (Rat.den_pos μ) (Rat.den_pos ν) hμ.2.1 hν.2.1 hfracne
  have hcastdiff :
      ((μ.num : ℝ) / μ.den - (ν.num : ℝ) / ν.den) =
        (μ : ℝ) - (ν : ℝ) := by
    simp only [Rat.cast_def]
  rw [hcastdiff] at hfarey
  linarith

theorem classifySlope_eq_interior_iff (μ : ℚ) :
    classifySlope μ = .interior ↔ μ ∈ Set.Ioo (0 : ℚ) 1 := by
  simp only [classifySlope, Set.mem_Ioo]
  split_ifs with h0 h1 hi
  · simp_all
  · simp_all
  · simp_all
  · simp_all

theorem GapWord.prefixSpan_firstPrefixAbove_le
    (w : GapWord) (bound : ℕ) :
    ∀ r < (w.firstPrefixAbove bound).length,
      (w.firstPrefixAbove bound).prefixSpan r ≤ bound := by
  induction w generalizing bound with
  | nil => simp [firstPrefixAbove]
  | cons g gs ih =>
      simp only [firstPrefixAbove]
      by_cases hbg : bound < g
      · rw [if_pos hbg]
        intro r hr
        have hr0 : r = 0 := by simp at hr; omega
        subst r
        simp [GapWord.prefixSpan]
      · rw [if_neg hbg]
        intro r hr
        have hgle : g ≤ bound := Nat.le_of_not_gt hbg
        cases r with
        | zero => simp [GapWord.prefixSpan]
        | succ r =>
            have hrTail : r < (firstPrefixAbove gs (bound - g)).length := by
              simpa using hr
            have hrec := ih (bound - g) r hrTail
            simp only [GapWord.prefixSpan, List.take_succ_cons, List.sum_cons]
            simp only [GapWord.prefixSpan] at hrec
            omega

theorem IsInteriorTrajectory.tail (Q g : ℕ) (line : AffineLine)
    (gs : GapWord) (h : IsInteriorTrajectory Q line (g :: gs)) :
    IsInteriorTrajectory Q (line.transform Q g) gs := by
  intro r hr
  obtain ⟨state, htrajectory, hinterior⟩ := h (r + 1) (by simpa using hr)
  have hstate := (sharedGapTrajectory_iff_transformWord Q line _ _).mp htrajectory
  refine ⟨(line.transform Q g).transformWord Q (gs.take r),
    (sharedGapTrajectory_iff_transformWord Q (line.transform Q g) _ _).mpr rfl, ?_⟩
  have hstate' : state =
      (line.transform Q g).transformWord Q (gs.take r) := by
    simpa [AffineLine.transformWord] using hstate
  rw [← hstate']
  exact hinterior

theorem interiorWords_comparable (Q : ℕ) (hQ : 0 < Q)
    (u v : AffineLine) (w z : GapWord)
    (hslope : u.slope Q = v.slope Q)
    (hwpos : w.Positive) (hzpos : z.Positive)
    (hw : IsInteriorTrajectory Q u w)
    (hz : IsInteriorTrajectory Q v z) :
    w.IsPrefix z ∨ z.IsPrefix w := by
  induction w generalizing u v z with
  | nil => exact Or.inl List.nil_prefix
  | cons g gs ih =>
      cases z with
      | nil => exact Or.inr List.nil_prefix
      | cons h hs =>
          have hg : 1 ≤ g := hwpos g (by simp)
          have hh : 1 ≤ h := hzpos h (by simp)
          obtain ⟨u0, hu0traj, hu0int⟩ := hw 0 (by simp)
          obtain ⟨ug, hugtraj, hugint⟩ := hw 1 (by simp)
          obtain ⟨vh, hvhtraj, hvhint⟩ := hz 1 (by simp)
          have hu0 : u0 = u :=
            (sharedGapTrajectory_iff_transformWord Q u [] u0).mp hu0traj
          subst u0
          have hug : ug = u.transform Q g := by
            simpa [AffineLine.transformWord] using
              (sharedGapTrajectory_iff_transformWord Q u [g] ug).mp hugtraj
          have hvh : vh = v.transform Q h := by
            simpa [AffineLine.transformWord] using
              (sharedGapTrajectory_iff_transformWord Q v [h] vh).mp hvhtraj
          subst ug
          subst vh
          have hμ : (u.slope Q : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
            have hμq : u.slope Q ∈ Set.Ioo (0 : ℚ) 1 :=
              (classifySlope_eq_interior_iff _).mp hu0int
            exact ⟨by exact_mod_cast hμq.1, by exact_mod_cast hμq.2⟩
          have hgmem : g ∈ {d : ℕ | 1 ≤ d ∧
              (2 : ℝ) ^ d * (u.slope Q : ℝ) - 1 ∈ Set.Ioo (0 : ℝ) 1} := by
            refine ⟨hg, ?_⟩
            have hnextq : (u.transform Q g).slope Q ∈ Set.Ioo (0 : ℚ) 1 :=
              (classifySlope_eq_interior_iff _).mp hugint
            have hnext : ((u.transform Q g).slope Q : ℝ) ∈
                Set.Ioo (0 : ℝ) 1 :=
              ⟨by exact_mod_cast hnextq.1, by exact_mod_cast hnextq.2⟩
            rw [AffineLine.slope_transform Q hQ] at hnext
            exact_mod_cast hnext
          have hhmem : h ∈ {d : ℕ | 1 ≤ d ∧
              (2 : ℝ) ^ d * (u.slope Q : ℝ) - 1 ∈ Set.Ioo (0 : ℝ) 1} := by
            refine ⟨hh, ?_⟩
            have hnextq : (v.transform Q h).slope Q ∈ Set.Ioo (0 : ℚ) 1 :=
              (classifySlope_eq_interior_iff _).mp hvhint
            have hnext : ((v.transform Q h).slope Q : ℝ) ∈
                Set.Ioo (0 : ℝ) 1 :=
              ⟨by exact_mod_cast hnextq.1, by exact_mod_cast hnextq.2⟩
            rw [AffineLine.slope_transform Q hQ] at hnext
            rw [← hslope] at hnext
            exact_mod_cast hnext
          have hgh : g = h := (lem_strict_unique (u.slope Q : ℝ) hμ) hgmem hhmem
          subst h
          have hslope' : (u.transform Q g).slope Q =
              (v.transform Q g).slope Q := by
            rw [AffineLine.slope_transform Q hQ,
              AffineLine.slope_transform Q hQ, hslope]
          have htail := ih (u.transform Q g) (v.transform Q g) hs hslope'
            (by
              intro x hx
              exact hwpos x (by simp [hx]))
            (by
              intro x hx
              exact hzpos x (by simp [hx]))
            (IsInteriorTrajectory.tail Q g u gs hw)
            (IsInteriorTrajectory.tail Q g v hs hz)
          rcases htail with hpre | hpre
          · rcases hpre with ⟨tail, htail⟩
            refine Or.inl ⟨tail, ?_⟩
            simpa using congrArg (List.cons g) htail
          · rcases hpre with ⟨tail, htail⟩
            refine Or.inr ⟨tail, ?_⟩
            simpa using congrArg (List.cons g) htail

theorem crossingInteriorWords_eq (Q bound : ℕ) (hQ : 0 < Q)
    (u v : AffineLine) (w z : GapWord)
    (hslope : u.slope Q = v.slope Q)
    (hwpos : w.Positive) (hzpos : z.Positive)
    (hw : IsInteriorTrajectory Q u w)
    (hz : IsInteriorTrajectory Q v z)
    (hwcross : bound < w.span) (hzcross : bound < z.span)
    (hwminimal : ∀ r < w.length, w.prefixSpan r ≤ bound)
    (hzminimal : ∀ r < z.length, z.prefixSpan r ≤ bound) :
    w = z := by
  rcases interiorWords_comparable Q hQ u v w z hslope hwpos hzpos hw hz with
    hwz | hzw
  · by_contra hne
    have hlen : w.length < z.length :=
      lt_of_le_of_ne hwz.length_le (fun heq =>
        hne (hwz.eq_of_length heq))
    have htake : z.take w.length = w := (List.prefix_iff_eq_take.mp hwz).symm
    have hmin := hzminimal w.length hlen
    rw [GapWord.prefixSpan, htake] at hmin
    exact (Nat.not_lt_of_ge hmin) hwcross
  · by_contra hne
    have hlen : z.length < w.length :=
      lt_of_le_of_ne hzw.length_le (fun heq =>
        hne (hzw.eq_of_length heq).symm)
    have htake : w.take z.length = z := (List.prefix_iff_eq_take.mp hzw).symm
    have hmin := hwminimal z.length hlen
    rw [GapWord.prefixSpan, htake] at hmin
    exact (Nat.not_lt_of_ge hmin) hzcross

theorem primitiveLines_direction_eq_of_slope_eq
    (Q : ℕ) (hQ : 0 < Q) (u v : AffineLine)
    (hu : Int.gcd u.H u.K = 1) (hv : Int.gcd v.H v.K = 1)
    (hslope : u.slope Q = v.slope Q) :
    u.H = v.H ∧ u.K = v.K := by
  have hHnat : u.H.natAbs = v.H.natAbs := by
    rw [primitiveDirectionDenominator Q hQ u hu,
      primitiveDirectionDenominator Q hQ v hv, hslope]
  have huH : (u.H.natAbs : ℤ) = u.H :=
    Int.natAbs_of_nonneg u.H_pos.le
  have hvH : (v.H.natAbs : ℤ) = v.H :=
    Int.natAbs_of_nonneg v.H_pos.le
  have hH : u.H = v.H := by
    calc
      u.H = (u.H.natAbs : ℤ) := huH.symm
      _ = (v.H.natAbs : ℤ) := congrArg (fun n : ℕ => (n : ℤ)) hHnat
      _ = v.H := hvH
  refine ⟨hH, ?_⟩
  have hQ0 : (Q : ℚ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hH0 : (u.H : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt u.H_pos)
  rw [AffineLine.slope, AffineLine.slope, ← hH] at hslope
  field_simp [hQ0, hH0] at hslope
  exact_mod_cast hslope

theorem reconstructed_direction_forward_eq
    (Q Cgap : ℕ) (hQ : 0 < Q) (B Cstep : ℝ) (hB : 2 < B)
    (W : WindowSystem) (Z0 : ℕ) (selection : InteriorAnchorSelection)
    (σ : BlockEncoding)
    (k₁ k₂ : ℕ) (data₁ data₂ : AnchorInteriorData)
    (block₁ block₂ : LowGapBlock)
    (hrec₁ : IsReconstructedOccurrenceLine Q Cgap B Cstep W Z0 selection σ
      k₁ data₁ block₁ (sourceRawLine Q data₁ block₁).canonicalGeometricLine)
    (hrec₂ : IsReconstructedOccurrenceLine Q Cgap B Cstep W Z0 selection σ
      k₂ data₂ block₂ (sourceRawLine Q data₂ block₂).canonicalGeometricLine) :
    (sourceRawLine Q data₁ block₁).H =
        (sourceRawLine Q data₂ block₂).H ∧
      (sourceRawLine Q data₁ block₁).K =
        (sourceRawLine Q data₂ block₂).K ∧
      sourceForwardWord W Cgap data₁ block₁ =
        sourceForwardWord W Cgap data₂ block₂ := by
  rcases hrec₁ with
    ⟨hselected₁, hvalid₁, hfrequent₁, hblock₁, hoccurs₁,
      hoffset₁, hcandidate₁, hD₁, hencoding₁, hprimitive₁,
      hline₁, hstep₁, hrealizes₁, hgeometric₁, hblockTrajectory₁,
      hlower₁, hupper₁, hpositive₁, hinterior₁⟩
  rcases hrec₂ with
    ⟨hselected₂, hvalid₂, hfrequent₂, hblock₂, hoccurs₂,
      hoffset₂, hcandidate₂, hD₂, hencoding₂, hprimitive₂,
      hline₂, hstep₂, hrealizes₂, hgeometric₂, hblockTrajectory₂,
      hlower₂, hupper₂, hpositive₂, hinterior₂⟩
  have hlong : B * Nat.ceil (Real.logb 2 (4 * σ.D)) ≤ σ.gaps.span := by
    rw [← hcandidate₁.1.2.2.1]
    exact hcandidate₁.2.2.2.1
  have hgeometric₁' := hgeometric₁
  have hgeometric₂' := hgeometric₂
  unfold GeometricLineRealizesEncoding at hgeometric₁' hgeometric₂'
  rw [(sourceRawLine Q data₁ block₁).canonicalGeometricLine_slope Q hQ]
    at hgeometric₁'
  rw [(sourceRawLine Q data₂ block₂).canonicalGeometricLine_slope Q hQ]
    at hgeometric₂'
  have hslope : (sourceRawLine Q data₁ block₁).slope Q =
      (sourceRawLine Q data₂ block₂).slope Q :=
    (lem_word_slope B hB σ.D hD₁ σ.gaps hlong)
      hgeometric₁' hgeometric₂'
  obtain ⟨hH, hK⟩ := primitiveLines_direction_eq_of_slope_eq
    Q hQ (sourceRawLine Q data₁ block₁) (sourceRawLine Q data₂ block₂)
    hprimitive₁ hprimitive₂ hslope
  refine ⟨hH, hK, ?_⟩
  have hblockGaps₁ : block₁.gaps = σ.gaps :=
    congrArg BlockEncoding.gaps hencoding₁
  have hblockGaps₂ : block₂.gaps = σ.gaps :=
    congrArg BlockEncoding.gaps hencoding₂
  have hendSlope :
      (sourceBlockEndLine Q data₁ block₁).slope Q =
        (sourceBlockEndLine Q data₂ block₂).slope Q := by
    unfold sourceBlockEndLine
    rw [hblockGaps₁, hblockGaps₂]
    exact AffineLine.transformWord_slope_eq_of_slope_eq Q hQ _ _ _ hslope
  let bound := 2 * W.L + Cgap
  apply crossingInteriorWords_eq Q bound hQ
    (sourceBlockEndLine Q data₁ block₁)
    (sourceBlockEndLine Q data₂ block₂)
    (sourceForwardWord W Cgap data₁ block₁)
    (sourceForwardWord W Cgap data₂ block₂)
    hendSlope hpositive₁ hpositive₂ hinterior₁ hinterior₂
    hlower₁ hlower₂
  · intro r hr
    exact GapWord.prefixSpan_firstPrefixAbove_le
      (sourceForwardSuffix data₁ block₁) bound r hr
  · intro r hr
    exact GapWord.prefixSpan_firstPrefixAbove_le
      (sourceForwardSuffix data₂ block₂) bound r hr

theorem prefix_enumerationGapWord_eq {S : Set ℕ}
    (e : SupportEnumeration S) (i n : ℕ) (word : GapWord)
    (hword : word.IsPrefix (enumerationGapWord e i n)) :
    word = enumerationGapWord e i word.length := by
  have hlen : word.length ≤ n := by
    have := hword.length_le
    simpa [enumerationGapWord] using this
  have hcanonical :
      (enumerationGapWord e i word.length).IsPrefix
        (enumerationGapWord e i n) := by
    rw [show n = word.length + (n - word.length) by omega,
      enumerationGapWord_append]
    exact List.prefix_append _ _
  have hwordTake := List.prefix_iff_eq_take.mp hword
  have hcanonicalTake := List.prefix_iff_eq_take.mp hcanonical
  have hcanonicalLength :
      (enumerationGapWord e i word.length).length = word.length := by
    simp [enumerationGapWord]
  calc
    word = (enumerationGapWord e i n).take word.length := hwordTake
    _ = (enumerationGapWord e i n).take
        (enumerationGapWord e i word.length).length := by
      rw [hcanonicalLength]
    _ = enumerationGapWord e i word.length := hcanonicalTake.symm

theorem drop_enumerationGapWord_eq {S : Set ℕ}
    (e : SupportEnumeration S) (i n offset : ℕ) (hoffset : offset ≤ n) :
    (enumerationGapWord e i n).drop offset =
      enumerationGapWord e (i + offset) (n - offset) := by
  rw [show n = offset + (n - offset) by omega,
    enumerationGapWord_append]
  simp [enumerationGapWord]

theorem actualPoint_intercept_bound
    (Q X x : ℕ) (R : RationalSupport) (hden : R.eta.den = Q)
    (line : AffineLine)
    (hcontains : line.Contains (x : ℤ) (carryInt R x))
    (hx : x ≤ 3 * X) (hX : 1 ≤ X)
    (hinterior : classifySlope (line.slope Q) = .interior) :
    |(line.interceptNumerator : ℝ)| ≤
      8 * (Q : ℝ) * (line.H : ℝ) * X := by
  have hQ : 0 < Q := by
    rw [← hden]
    exact Rat.den_pos R.eta
  have hμ := (classifySlope_eq_interior_iff _).mp hinterior
  have hQr : (0 : ℚ) < Q := by exact_mod_cast hQ
  have hHr : (0 : ℚ) < line.H := by exact_mod_cast line.H_pos
  have hdenQ : (0 : ℚ) < (Q : ℚ) * (line.H : ℚ) :=
    mul_pos hQr hHr
  have hKq : (0 : ℚ) < line.K := by
    rw [AffineLine.slope] at hμ
    exact (div_pos_iff_of_pos_right hdenQ).mp hμ.1
  have hKltq : (line.K : ℚ) < (Q : ℚ) * line.H := by
    rw [AffineLine.slope] at hμ
    exact (div_lt_one hdenQ).mp hμ.2
  have hKnonneg : (0 : ℝ) ≤ line.K := by
    exact_mod_cast hKq.le
  have hKupper : (line.K : ℝ) ≤ (Q : ℝ) * line.H := by
    exact_mod_cast hKltq.le
  have hcarryNonneg : (0 : ℝ) ≤ carryInt R x := by
    exact_mod_cast (prop_carry R).2.1 x
  have hcarryUpper : (carryInt R x : ℝ) ≤ (Q : ℝ) * (x + 2) := by
    have hi := (prop_carry R).2.2.1 x
    rw [hden] at hi
    exact_mod_cast hi
  rcases hcontains with ⟨t, hcoord, hcarry⟩
  have hbInt : line.interceptNumerator =
      line.H * carryInt R x - line.K * (x : ℤ) := by
    unfold AffineLine.interceptNumerator
    rw [hcoord, hcarry]
    ring
  have hbReal : (line.interceptNumerator : ℝ) =
      (line.H : ℝ) * carryInt R x - (line.K : ℝ) * x := by
    exact_mod_cast hbInt
  rw [hbReal]
  have hHnonneg : (0 : ℝ) ≤ line.H := by exact_mod_cast line.H_pos.le
  have hxnonneg : (0 : ℝ) ≤ x := by positivity
  have hQnonneg : (0 : ℝ) ≤ Q := by positivity
  have hXreal : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hxreal : (x : ℝ) ≤ 3 * X := by exact_mod_cast hx
  have habs : |(line.H : ℝ) * carryInt R x - (line.K : ℝ) * x| ≤
      (line.H : ℝ) * carryInt R x + (line.K : ℝ) * x := by
    simpa [abs_of_nonneg (mul_nonneg hHnonneg hcarryNonneg),
      abs_of_nonneg (mul_nonneg hKnonneg hxnonneg)] using
        abs_sub_le ((line.H : ℝ) * carryInt R x) 0 ((line.K : ℝ) * x)
  calc
    |(line.H : ℝ) * carryInt R x - (line.K : ℝ) * x| ≤
        (line.H : ℝ) * carryInt R x + (line.K : ℝ) * x := habs
    _ ≤ (line.H : ℝ) * ((Q : ℝ) * (x + 2)) +
        ((Q : ℝ) * line.H) * x := by gcongr
    _ ≤ 8 * (Q : ℝ) * (line.H : ℝ) * X := by
      nlinarith [mul_nonneg hQnonneg hHnonneg,
        mul_nonneg (mul_nonneg hQnonneg hHnonneg)
          (zero_le_one.trans hXreal)]

theorem selectedBlockFollowWord_eq_enumerationGapWord
    (Q : ℕ) (W : WindowSystem) (Z0 k : ℕ)
    (data : AnchorInteriorData) (hvalid : data.Valid Q W Z0 k)
    (block : LowGapBlock) (hoccurs : LowGapBlock.OccursIn data.segment block)
    (word : GapWord) (hword : word.IsPrefix (sourceForwardSuffix data block)) :
    block.gaps ++ word = enumerationGapWord W.enumeration
      (k - W.s + (initialLongPrefix W k).length + data.before.length +
        block.offset)
      (block.gaps.length + word.length) := by
  let start := k - W.s + (initialLongPrefix W k).length + data.before.length
  have hsegment := data.segmentGaps_eq_enumerationGapWord Q W Z0 k hvalid
  have hoffset : block.offset ≤ data.segment.gaps.length :=
    le_trans (Nat.le_add_right block.offset block.gaps.length) hoccurs.1
  have hdrop : data.segment.gaps.drop block.offset =
      enumerationGapWord W.enumeration (start + block.offset)
        (data.segment.gaps.length - block.offset) := by
    let n := data.segment.gaps.length
    calc
      data.segment.gaps.drop block.offset =
          (enumerationGapWord W.enumeration
            (k - W.s + (initialLongPrefix W k).length + data.before.length)
            n).drop block.offset := by rw [hsegment]
      _ = enumerationGapWord W.enumeration
          (k - W.s + (initialLongPrefix W k).length + data.before.length +
            block.offset) (n - block.offset) :=
        drop_enumerationGapWord_eq W.enumeration _ n block.offset hoffset
      _ = enumerationGapWord W.enumeration (start + block.offset)
          (data.segment.gaps.length - block.offset) := by rfl
  have hsplit : data.segment.gaps.drop block.offset =
      block.gaps ++ data.segment.gaps.drop (block.offset + block.gaps.length) := by
    calc
      data.segment.gaps.drop block.offset =
          (data.segment.gaps.drop block.offset).take block.gaps.length ++
            (data.segment.gaps.drop block.offset).drop block.gaps.length :=
        (List.take_append_drop _ _).symm
      _ = block.gaps ++
          data.segment.gaps.drop (block.offset + block.gaps.length) := by
        rw [hoccurs.2, List.drop_drop]
  have hprefix : (block.gaps ++ word).IsPrefix
      (data.segment.gaps.drop block.offset) := by
    rcases hword with ⟨tail, htail⟩
    refine ⟨tail, ?_⟩
    rw [hsplit]
    simp only [List.append_assoc]
    rw [htail]
    rfl
  rw [hdrop] at hprefix
  simpa [start, Nat.add_assoc] using
    prefix_enumerationGapWord_eq W.enumeration
      (start + block.offset) (data.segment.gaps.length - block.offset)
      (block.gaps ++ word) hprefix

theorem sourceBlockEnd_forward_contains
    (Q : ℕ) (W : WindowSystem) (Z0 k : ℕ)
    (hden : W.rational.eta.den = Q)
    (data : AnchorInteriorData) (hvalid : data.Valid Q W Z0 k)
    (block : LowGapBlock) (hoccurs : LowGapBlock.OccursIn data.segment block)
    (t : ℤ) (hparameter : IsOriginalSourceParameter Q W k data block t)
    (word : GapWord) (hword : word.IsPrefix (sourceForwardSuffix data block)) :
    ((sourceBlockEndLine Q data block).transformWord Q word).Contains
      (W.enumeration.a
        (k - W.s + (initialLongPrefix W k).length + data.before.length +
          block.offset + block.gaps.length + word.length))
      (carryInt W.rational (W.enumeration.a
        (k - W.s + (initialLongPrefix W k).length + data.before.length +
          block.offset + block.gaps.length + word.length))) := by
  let i := k - W.s + (initialLongPrefix W k).length + data.before.length +
    block.offset
  have hstart : (sourceRawLine Q data block).Contains
      (W.enumeration.a i) (carryInt W.rational (W.enumeration.a i)) := by
    rcases hparameter with ⟨hx, hr, ht⟩
    have hi : k - W.s + sourceWindowOffset W k data block = i := by
      unfold sourceWindowOffset
      dsimp [i]
      omega
    change (W.enumeration.a (k - W.s + sourceWindowOffset W k data block) : ℤ) =
        (sourceRawLine Q data block).A + (sourceRawLine Q data block).H * t at hx
    change carryInt W.rational
        (W.enumeration.a (k - W.s + sourceWindowOffset W k data block)) =
          (sourceRawLine Q data block).C + (sourceRawLine Q data block).K * t at hr
    refine ⟨t, ?_, ?_⟩
    · rw [← hi]
      exact hx
    · rw [← hi]
      exact hr
  have hwordEnum := selectedBlockFollowWord_eq_enumerationGapWord
    Q W Z0 k data hvalid block hoccurs word hword
  have hpoint := (sourceRawLine Q data block).transformWord_contains_enumerationGapWord
    Q W.rational hden W.enumeration i (block.gaps.length + word.length) hstart
  rw [← hwordEnum, AffineLine.transformWord_append] at hpoint
  simpa [i, sourceBlockEndLine, Nat.add_assoc] using hpoint

theorem sourceEndpointIndex_le_succ
    (Q : ℕ) (W : WindowSystem) (Z0 k : ℕ)
    (data : AnchorInteriorData) (hvalid : data.Valid Q W Z0 k)
    (block : LowGapBlock) (hoccurs : LowGapBlock.OccursIn data.segment block)
    (word : GapWord) (hword : word.IsPrefix (sourceForwardSuffix data block)) :
    k - W.s + (initialLongPrefix W k).length + data.before.length +
        block.offset + block.gaps.length + word.length ≤ k + 1 := by
  have hwordLen : word.length ≤ (sourceForwardSuffix data block).length :=
    hword.length_le
  have hblockEnd : block.offset + block.gaps.length ≤
      data.segment.gaps.length := hoccurs.1
  have hsourceSuffixLen : (sourceForwardSuffix data block).length =
      data.segment.gaps.length - (block.offset + block.gaps.length) := by
    simp [sourceForwardSuffix]
  rw [hsourceSuffixLen] at hwordLen
  obtain ⟨after, hactual⟩ := hvalid.2.2.2.2.2.1
  have hbeforeSegment : data.before.length + data.segment.gaps.length ≤
      (actualPostPrefixGaps W k).length := by
    rw [hactual]
    simp
  have hinitialPrefix : (initialLongPrefix W k).IsPrefix
      (W.rawWindowGapWord k) := GapWord.firstPrefixAbove_isPrefix _ _
  have hpLen : (initialLongPrefix W k).length ≤
      (W.rawWindowGapWord k).length := hinitialPrefix.length_le
  have hactualLen : (actualPostPrefixGaps W k).length =
      (W.rawWindowGapWord k).length - (initialLongPrefix W k).length := by
    simp [actualPostPrefixGaps]
  have hrawLen : (W.rawWindowGapWord k).length ≤ W.m :=
    rawWindowGapWord_length_le W k
  rw [hactualLen] at hbeforeSegment
  have hsk : W.s ≤ k := hvalid.1
  rw [WindowSystem.m] at hrawLen
  omega

theorem sourceEndpointCoordinate_le_threeX
    (Q Cgap : ℕ) (W : WindowSystem) (Z0 k : ℕ)
    (data : AnchorInteriorData) (hvalid : data.Valid Q W Z0 k)
    (block : LowGapBlock) (hoccurs : LowGapBlock.OccursIn data.segment block)
    (word : GapWord) (hword : word.IsPrefix (sourceForwardSuffix data block))
    (hgap : supportGap W.enumeration k ≤ W.L + Cgap + 1)
    (hscale : W.L + Cgap + 1 ≤ W.X) :
    W.enumeration.a
        (k - W.s + (initialLongPrefix W k).length + data.before.length +
          block.offset + block.gaps.length + word.length) ≤ 3 * W.X := by
  classical
  let j := k - W.s + (initialLongPrefix W k).length + data.before.length +
    block.offset + block.gaps.length + word.length
  have hj : j ≤ k + 1 := by
    exact sourceEndpointIndex_le_succ Q W Z0 k data hvalid block hoccurs
      word hword
  have hmono : W.enumeration.a j ≤ W.enumeration.a (k + 1) :=
    W.enumeration.strictMono.monotone hj
  have hkAnchor : k ∈ W.anchors := by
    have hhigh := hvalid.2.1
    rw [highAnchors, Finset.mem_filter] at hhigh
    exact hhigh.1
  have hkUpper : W.enumeration.a k ≤ 2 * W.X :=
    (Finset.mem_filter.mp hkAnchor).2.2
  have hnext : W.enumeration.a (k + 1) =
      W.enumeration.a k + supportGap W.enumeration k := by
    simp only [supportGap]
    exact (Nat.add_sub_of_le
      (W.enumeration.strictMono (Nat.lt_succ_self k)).le).symm
  dsimp [j] at hmono
  rw [hnext] at hmono
  omega

theorem AffineLine.transformWord_direction_eq
    (Q : ℕ) (u v : AffineLine) (word : GapWord)
    (hH : u.H = v.H) (hK : u.K = v.K) :
    (u.transformWord Q word).H = (v.transformWord Q word).H ∧
      (u.transformWord Q word).K = (v.transformWord Q word).K := by
  induction word generalizing u v with
  | nil => exact ⟨hH, hK⟩
  | cons g gs ih =>
      simp only [AffineLine.transformWord]
      apply ih
      · simpa [AffineLine.transform] using hH
      · simp only [AffineLine.transform]
        rw [hH, hK]

theorem IsInteriorTrajectory.start_interior
    (Q : ℕ) (line : AffineLine) (word : GapWord)
    (h : IsInteriorTrajectory Q line word) :
    classifySlope (line.slope Q) = .interior := by
  obtain ⟨state, htrajectory, hinterior⟩ := h 0 (by simp)
  have hstate := (sharedGapTrajectory_iff_transformWord Q line [] state).mp
    htrajectory
  rw [hstate] at hinterior
  simpa [AffineLine.transformWord] using hinterior

theorem IsInteriorTrajectory.end_interior
    (Q : ℕ) (line : AffineLine) (word : GapWord)
    (h : IsInteriorTrajectory Q line word) :
    classifySlope ((line.transformWord Q word).slope Q) = .interior := by
  obtain ⟨state, htrajectory, hinterior⟩ := h word.length (by simp)
  have hstate := (sharedGapTrajectory_iff_transformWord Q line
    (word.take word.length) state).mp htrajectory
  rw [hstate] at hinterior
  simpa using hinterior

theorem supportGap_mem_rawWindowGapWord
    (W : WindowSystem) (k : ℕ) (hsk : W.s ≤ k) :
    supportGap W.enumeration k ∈ W.rawWindowGapWord k := by
  rw [WindowSystem.rawWindowGapWord, dif_pos hsk]
  simp only [WindowSystem.window, windowGapWord, List.mem_map, List.mem_range]
  refine ⟨W.s, ?_, ?_⟩
  · simp
  · congr 1
    omega

theorem two_mul_le_two_pow (L : ℕ) (hL : 1 ≤ L) :
    2 * L ≤ 2 ^ L := by
  induction L with
  | zero => omega
  | succ L ih =>
      by_cases hL0 : L = 0
      · subst L
        norm_num
      · have hLpos : 1 ≤ L := by omega
        have hrec := ih hLpos
        rw [pow_succ]
        nlinarith

theorem frequencyCutoff_tendsto (context : FixedScaleContext)
    (F : ScaleFamily) (hF : F.MatchesContext context) :
    Tendsto (fun L : ℕ => frequencyCutoff (F.system L)) atTop atTop := by
  have hXtop : Tendsto (fun L : ℕ => ((F.system L).X : ℝ)) atTop atTop := by
    simpa [WindowSystem.X, F.level_eq, dyadicScale] using
      (tendsto_pow_atTop_atTop_of_one_lt (r := (2 : ℝ)) (by norm_num))
  have hexponent : 0 < (1 : ℝ) / 2 + context.structural.rho := by
    linarith [context.structural.rho_pos]
  have hpow := (tendsto_rpow_atTop hexponent).comp hXtop
  apply hpow.congr'
  filter_upwards [] with L
  unfold frequencyCutoff
  rw [F.structural_eq L, hF.2.1]
  rfl

theorem eventually_scale_dominates_gap (Cgap : ℕ) (F : ScaleFamily) :
    ∀ᶠ L : ℕ in atTop,
      (F.system L).L + Cgap + 1 ≤ (F.system L).X := by
  filter_upwards [eventually_ge_atTop (max 1 (Cgap + 1))] with L hL
  have hLone : 1 ≤ L := (le_max_left _ _).trans hL
  have hLC : Cgap + 1 ≤ L := (le_max_right _ _).trans hL
  rw [F.level_eq, WindowSystem.X, F.level_eq, dyadicScale]
  have htwo := two_mul_le_two_pow L hLone
  omega

theorem reconstructed_endpoint_intercept_bounds
    (Q Cgap : ℕ) (B Cstep : ℝ) (W : WindowSystem) (Z0 k : ℕ)
    (selection : InteriorAnchorSelection) (σ : BlockEncoding)
    (data : AnchorInteriorData) (block : LowGapBlock)
    (hden : W.rational.eta.den = Q)
    (hgap : ∀ j : ℕ, j ∈ W.anchors →
      ∀ g ∈ W.rawWindowGapWord j, g ≤ W.L + Cgap + 1)
    (hscale : W.L + Cgap + 1 ≤ W.X)
    (hrec : IsReconstructedOccurrenceLine Q Cgap B Cstep W Z0 selection σ
      k data block (sourceRawLine Q data block).canonicalGeometricLine)
    (t : ℤ) (hparameter : IsOriginalSourceParameter Q W k data block t) :
    |((sourceBlockEndLine Q data block).interceptNumerator : ℝ)| ≤
        8 * (Q : ℝ) * ((sourceBlockEndLine Q data block).H : ℝ) * W.X ∧
      |(((sourceBlockEndLine Q data block).transformWord Q
          (sourceForwardWord W Cgap data block)).interceptNumerator : ℝ)| ≤
        8 * (Q : ℝ) *
          (((sourceBlockEndLine Q data block).transformWord Q
            (sourceForwardWord W Cgap data block)).H : ℝ) * W.X := by
  classical
  rcases hrec with
    ⟨_hselected, hvalid, _hfrequent, _hblock, hoccurs, _hoffset,
      _hcandidate, _hD, _hencoding, _hprimitive, _hline, _hstep,
      _hrealizes, _hgeometric, _hblockTrajectory, _hlower, _hupper,
      _hpositive, hinterior⟩
  let word := sourceForwardWord W Cgap data block
  have hword : word.IsPrefix (sourceForwardSuffix data block) := by
    exact GapWord.firstPrefixAbove_isPrefix _ _
  have hkAnchor : k ∈ W.anchors := by
    have hhigh := hvalid.2.1
    rw [highAnchors, Finset.mem_filter] at hhigh
    exact hhigh.1
  have hgapAt : supportGap W.enumeration k ≤ W.L + Cgap + 1 :=
    hgap k hkAnchor _ (supportGap_mem_rawWindowGapWord W k hvalid.1)
  have hXone : 1 ≤ W.X := by
    rw [WindowSystem.X, dyadicScale]
    exact Left.one_le_pow_of_le (by norm_num : (1 : ℕ) ≤ 2) W.L
  have hendContains := sourceBlockEnd_forward_contains Q W Z0 k hden
    data hvalid block hoccurs t hparameter [] List.nil_prefix
  have hendCoord := sourceEndpointCoordinate_le_threeX Q Cgap W Z0 k
    data hvalid block hoccurs [] List.nil_prefix hgapAt hscale
  have hfinalContains := sourceBlockEnd_forward_contains Q W Z0 k hden
    data hvalid block hoccurs t hparameter word hword
  have hfinalCoord := sourceEndpointCoordinate_le_threeX Q Cgap W Z0 k
    data hvalid block hoccurs word hword hgapAt hscale
  have hstartInterior := IsInteriorTrajectory.start_interior Q
    (sourceBlockEndLine Q data block) word hinterior
  have hendInterior := IsInteriorTrajectory.end_interior Q
    (sourceBlockEndLine Q data block) word hinterior
  constructor
  · simpa [word, AffineLine.transformWord] using
      actualPoint_intercept_bound Q W.X
        (W.enumeration.a
          (k - W.s + (initialLongPrefix W k).length + data.before.length +
            block.offset + block.gaps.length + [].length))
        W.rational hden (sourceBlockEndLine Q data block)
        (by simpa [AffineLine.transformWord] using hendContains)
        hendCoord hXone hstartInterior
  · exact actualPoint_intercept_bound Q W.X
      (W.enumeration.a
        (k - W.s + (initialLongPrefix W k).length + data.before.length +
          block.offset + block.gaps.length + word.length))
      W.rational hden
      ((sourceBlockEndLine Q data block).transformWord Q word)
      hfinalContains hfinalCoord hXone hendInterior

theorem intercept_eq_of_long_transform
    (Q X : ℕ) (Cstep frequency : ℝ) (u v : AffineLine) (word : GapWord)
    (hQ : 0 < Q) (hCstep : 0 < Cstep) (hX : 0 < X)
    (hfrequency : 16 * (Q : ℝ) * Cstep < frequency)
    (hH : u.H = v.H) (hK : u.K = v.K)
    (hstep : (u.H : ℝ) ≤ Cstep * X / frequency)
    (hspan : (X : ℝ) ^ 2 < (2 : ℝ) ^ word.span)
    (huBound : |((u.transformWord Q word).interceptNumerator : ℝ)| ≤
      8 * (Q : ℝ) * (u.H : ℝ) * X)
    (hvBound : |((v.transformWord Q word).interceptNumerator : ℝ)| ≤
      8 * (Q : ℝ) * (u.H : ℝ) * X) :
    u.interceptNumerator = v.interceptNumerator := by
  by_contra hne
  let δ : ℤ := u.interceptNumerator - v.interceptNumerator
  have hδne : δ ≠ 0 := sub_ne_zero.mpr hne
  have hδabsInt : (1 : ℤ) ≤ |δ| := by
    exact Int.add_one_le_iff.mpr (abs_pos.mpr hδne)
  have hδabs : (1 : ℝ) ≤ |(δ : ℝ)| := by
    exact_mod_cast hδabsInt
  have hmonoInt := AffineLine.interceptDifference_transformWord
    Q u v word hH hK
  have hmonoReal :
      ((u.transformWord Q word).interceptNumerator : ℝ) -
          ((v.transformWord Q word).interceptNumerator : ℝ) =
        (2 : ℝ) ^ word.span * (δ : ℝ) := by
    exact_mod_cast hmonoInt
  have hpowPos : (0 : ℝ) < (2 : ℝ) ^ word.span := by positivity
  have hpowLeDiff : (2 : ℝ) ^ word.span ≤
      |((u.transformWord Q word).interceptNumerator : ℝ) -
        ((v.transformWord Q word).interceptNumerator : ℝ)| := by
    rw [hmonoReal, abs_mul, abs_of_pos hpowPos]
    nlinarith
  have hdiffUpper :
      |((u.transformWord Q word).interceptNumerator : ℝ) -
          ((v.transformWord Q word).interceptNumerator : ℝ)| ≤
        16 * (Q : ℝ) * (u.H : ℝ) * X := by
    calc
      |((u.transformWord Q word).interceptNumerator : ℝ) -
          ((v.transformWord Q word).interceptNumerator : ℝ)| ≤
          |((u.transformWord Q word).interceptNumerator : ℝ)| +
            |((v.transformWord Q word).interceptNumerator : ℝ)| :=
        abs_sub _ _
      _ ≤ 16 * (Q : ℝ) * (u.H : ℝ) * X := by
        nlinarith
  have hfrequencyPos : 0 < frequency := by
    have hQC : 0 < 16 * (Q : ℝ) * Cstep := by positivity
    linarith
  have hHfrequency : (u.H : ℝ) * frequency ≤ Cstep * X := by
    exact (le_div_iff₀ hfrequencyPos).mp hstep
  have hQreal : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hXreal : (0 : ℝ) < X := by exact_mod_cast hX
  have hHreal : (0 : ℝ) < u.H := by exact_mod_cast u.H_pos
  have hpowUpper : (2 : ℝ) ^ word.span ≤
      16 * (Q : ℝ) * (u.H : ℝ) * X :=
    hpowLeDiff.trans hdiffUpper
  have hmulUpper : (2 : ℝ) ^ word.span * frequency ≤
      (16 * (Q : ℝ) * Cstep) * (X : ℝ) ^ 2 := by
    calc
      (2 : ℝ) ^ word.span * frequency ≤
          (16 * (Q : ℝ) * (u.H : ℝ) * X) * frequency := by
        exact mul_le_mul_of_nonneg_right hpowUpper hfrequencyPos.le
      _ = (16 * (Q : ℝ) * X) * ((u.H : ℝ) * frequency) := by ring
      _ ≤ (16 * (Q : ℝ) * X) * (Cstep * X) := by
        exact mul_le_mul_of_nonneg_left hHfrequency (by positivity)
      _ = (16 * (Q : ℝ) * Cstep) * (X : ℝ) ^ 2 := by ring
  have hconstantPos : 0 < 16 * (Q : ℝ) * Cstep := by positivity
  have hpowRealPos : 0 < (2 : ℝ) ^ word.span := by positivity
  have hmulLower₁ :
      (X : ℝ) ^ 2 * (16 * (Q : ℝ) * Cstep) <
        (2 : ℝ) ^ word.span * (16 * (Q : ℝ) * Cstep) :=
    mul_lt_mul_of_pos_right hspan hconstantPos
  have hmulLower₂ :
      (2 : ℝ) ^ word.span * (16 * (Q : ℝ) * Cstep) <
        (2 : ℝ) ^ word.span * frequency :=
    mul_lt_mul_of_pos_left hfrequency hpowRealPos
  have hmulLower :
      (16 * (Q : ℝ) * Cstep) * (X : ℝ) ^ 2 <
        (2 : ℝ) ^ word.span * frequency := by
    rw [mul_comm (16 * (Q : ℝ) * Cstep) ((X : ℝ) ^ 2)]
    exact hmulLower₁.trans hmulLower₂
  linarith

theorem forward_span_power (Cgap : ℕ) (W : WindowSystem)
    (word : GapWord) (hspan : 2 * W.L + Cgap < word.span) :
    (W.X : ℝ) ^ 2 < (2 : ℝ) ^ word.span := by
  have hexponent : 2 * W.L < word.span := by omega
  have hnat : 2 ^ (2 * W.L) < 2 ^ word.span :=
    Nat.pow_lt_pow_right (by omega) hexponent
  have hreal : (2 : ℝ) ^ (2 * W.L) < (2 : ℝ) ^ word.span := by
    exact_mod_cast hnat
  rw [WindowSystem.X, dyadicScale, Nat.cast_pow, Nat.cast_ofNat]
  convert hreal using 1
  ring

theorem AffineLine.canonicalGeometricLine_eq_of_primitive_direction_intercept
    (u v : AffineLine) (hu : Int.gcd u.H u.K = 1)
    (hv : Int.gcd v.H v.K = 1) (hH : u.H = v.H) (hK : u.K = v.K)
    (hb : u.interceptNumerator = v.interceptNumerator) :
    u.canonicalGeometricLine = v.canonicalGeometricLine := by
  unfold AffineLine.canonicalGeometricLine AffineLine.primitiveHorizontalInt
    AffineLine.primitiveVertical AffineLine.directionGCD
  simp only [hu, hv]
  congr 1
  · simpa using congrArg Int.natAbs hH
  · simpa using hK
  · simpa using hb

/-- Paper label: `lem:line-unique` (Section 6). -/
theorem lem_line_unique (context : FixedScaleContext)
    (gap : GapParams context.Q) (Cstep : ℝ) (hCstep : 0 < Cstep) :
    ∃ Zmin : ℕ,
      ∀ Z0 : ℕ, Zmin ≤ Z0 →
        ∀ F : ScaleFamily, F.MatchesContext context →
          ∀ᶠ L : ℕ in atTop,
            ∀ selection : InteriorAnchorSelection,
              ValidInteriorAnchorSelection context.Q (F.system L) Z0 selection →
                ∀ σ : BlockEncoding,
                  σ ∈ encodingCandidates σ.D σ.Z context.structural.B →
                    0 < σ.D →
                      Set.Subsingleton
                        (spatialCanonicalLines context.Q gap.Cgap
                          context.structural.B Cstep (F.system L) Z0
                          selection σ) := by
  classical
  refine ⟨0, ?_⟩
  intro Z0 _hZ0 F hF
  have hfrequencyTop := frequencyCutoff_tendsto context F hF
  have hfrequencyEventually : ∀ᶠ L : ℕ in atTop,
      16 * (context.Q : ℝ) * Cstep < frequencyCutoff (F.system L) := by
    filter_upwards [tendsto_atTop.1 hfrequencyTop
      (16 * (context.Q : ℝ) * Cstep + 1)] with L hL
    linarith
  filter_upwards [eventually_rawWindowGap_le context gap F hF,
    eventually_scale_dominates_gap gap.Cgap F,
    hfrequencyEventually] with L hgapL hscaleL hfrequencyL
  intro selection _hselection σ _hσ _hD
  rintro line₁ ⟨k₁, data₁, block₁, hsource₁, hselected₁, hline₁⟩
    line₂ ⟨k₂, data₂, block₂, hsource₂, hselected₂, hline₂⟩
  change IsSpatialEncodingSource context.Q gap.Cgap context.structural.B
    Cstep (F.system L) Z0 selection σ (k₁, block₁) at hsource₁
  change IsSpatialEncodingSource context.Q gap.Cgap context.structural.B
    Cstep (F.system L) Z0 selection σ (k₂, block₂) at hsource₂
  rcases hsource₁ with ⟨data₁', t₁, hrec₁', hparameter₁'⟩
  rcases hsource₂ with ⟨data₂', t₂, hrec₂', hparameter₂'⟩
  have hdata₁ : data₁' = data₁ := by
    apply Option.some.inj
    exact hrec₁'.1.symm.trans hselected₁
  have hdata₂ : data₂' = data₂ := by
    apply Option.some.inj
    exact hrec₂'.1.symm.trans hselected₂
  subst data₁'
  subst data₂'
  have hrec₁ := hrec₁'
  have hrec₂ := hrec₂'
  have hparameter₁ := hparameter₁'
  have hparameter₂ := hparameter₂'
  obtain ⟨hrawH, hrawK, hword⟩ := reconstructed_direction_forward_eq
    context.Q gap.Cgap context.Q_pos context.structural.B Cstep
      context.structural.B_gt (F.system L) Z0 selection σ
      k₁ k₂ data₁ data₂ block₁ block₂ hrec₁ hrec₂
  have hden : (F.system L).rational.eta.den = context.Q := by
    rw [F.rational_eq]
    exact hF.1
  have hgapW : ∀ j : ℕ, j ∈ (F.system L).anchors →
      ∀ g ∈ (F.system L).rawWindowGapWord j,
        g ≤ (F.system L).L + gap.Cgap + 1 := by
    intro j hj g hg
    rw [F.level_eq]
    exact hgapL j hj g hg
  have hbounds₁ := reconstructed_endpoint_intercept_bounds
    context.Q gap.Cgap context.structural.B Cstep (F.system L) Z0 k₁
      selection σ data₁ block₁ hden hgapW hscaleL hrec₁ t₁ hparameter₁
  have hbounds₂ := reconstructed_endpoint_intercept_bounds
    context.Q gap.Cgap context.structural.B Cstep (F.system L) Z0 k₂
      selection σ data₂ block₂ hden hgapW hscaleL hrec₂ t₂ hparameter₂
  rcases hrec₁' with
    ⟨_hselectedRec₁, _hvalid₁, _hfrequent₁, _hblock₁, _hoccurs₁,
      _hoffset₁, _hcandidate₁, _hD₁, hencoding₁, hprimitive₁,
      _hlineRec₁, hstep₁, _hrealizes₁, _hgeometric₁,
      _hblockTrajectory₁, hlower₁, _hupper₁, _hpositive₁, _hinterior₁⟩
  rcases hrec₂' with
    ⟨_hselectedRec₂, _hvalid₂, _hfrequent₂, _hblock₂, _hoccurs₂,
      _hoffset₂, _hcandidate₂, _hD₂, hencoding₂, hprimitive₂,
      _hlineRec₂, _hstep₂, _hrealizes₂, _hgeometric₂,
      _hblockTrajectory₂, _hlower₂, _hupper₂, _hpositive₂, _hinterior₂⟩
  have hblockGaps₁ : block₁.gaps = σ.gaps :=
    congrArg BlockEncoding.gaps hencoding₁
  have hblockGaps₂ : block₂.gaps = σ.gaps :=
    congrArg BlockEncoding.gaps hencoding₂
  have hendH : (sourceBlockEndLine context.Q data₁ block₁).H =
      (sourceBlockEndLine context.Q data₂ block₂).H := by
    unfold sourceBlockEndLine
    rw [hblockGaps₁, hblockGaps₂]
    exact (AffineLine.transformWord_direction_eq context.Q
      (sourceRawLine context.Q data₁ block₁)
      (sourceRawLine context.Q data₂ block₂) σ.gaps hrawH hrawK).1
  have hendK : (sourceBlockEndLine context.Q data₁ block₁).K =
      (sourceBlockEndLine context.Q data₂ block₂).K := by
    unfold sourceBlockEndLine
    rw [hblockGaps₁, hblockGaps₂]
    exact (AffineLine.transformWord_direction_eq context.Q
      (sourceRawLine context.Q data₁ block₁)
      (sourceRawLine context.Q data₂ block₂) σ.gaps hrawH hrawK).2
  have hcanonHInt :
      ((sourceRawLine context.Q data₁ block₁).canonicalGeometricLine.H : ℤ) =
        (sourceRawLine context.Q data₁ block₁).H := by
    rw [(sourceRawLine context.Q data₁ block₁).canonicalGeometricLine_H_cast]
    simp [AffineLine.primitiveHorizontalInt, AffineLine.directionGCD,
      hprimitive₁]
  have hcanonHReal :
      ((sourceRawLine context.Q data₁ block₁).canonicalGeometricLine.H : ℝ) =
        ((sourceRawLine context.Q data₁ block₁).H : ℝ) := by
    exact_mod_cast hcanonHInt
  have hrawStep : ((sourceRawLine context.Q data₁ block₁).H : ℝ) ≤
      Cstep * (F.system L).X / frequencyCutoff (F.system L) := by
    rw [← hcanonHReal]
    exact hstep₁
  have hendRawH : (sourceBlockEndLine context.Q data₁ block₁).H =
      (sourceRawLine context.Q data₁ block₁).H := by
    exact AffineLine.transformWord_H context.Q _ _
  have hendStep : ((sourceBlockEndLine context.Q data₁ block₁).H : ℝ) ≤
      Cstep * (F.system L).X / frequencyCutoff (F.system L) := by
    rw [hendRawH]
    exact hrawStep
  have huBound :
      |(((sourceBlockEndLine context.Q data₁ block₁).transformWord context.Q
          (sourceForwardWord (F.system L) gap.Cgap data₁ block₁)).interceptNumerator : ℝ)| ≤
        8 * (context.Q : ℝ) *
          ((sourceBlockEndLine context.Q data₁ block₁).H : ℝ) *
            (F.system L).X := by
    simpa only [AffineLine.transformWord_H] using hbounds₁.2
  have hvBound :
      |(((sourceBlockEndLine context.Q data₂ block₂).transformWord context.Q
          (sourceForwardWord (F.system L) gap.Cgap data₁ block₁)).interceptNumerator : ℝ)| ≤
        8 * (context.Q : ℝ) *
          ((sourceBlockEndLine context.Q data₁ block₁).H : ℝ) *
            (F.system L).X := by
    rw [hword, hendH]
    simpa only [AffineLine.transformWord_H] using hbounds₂.2
  have hspanPower : ((F.system L).X : ℝ) ^ 2 <
      (2 : ℝ) ^ (sourceForwardWord (F.system L) gap.Cgap data₁ block₁).span :=
    forward_span_power gap.Cgap (F.system L)
      (sourceForwardWord (F.system L) gap.Cgap data₁ block₁) hlower₁
  have hXpos : 0 < (F.system L).X := by
    rw [WindowSystem.X, dyadicScale]
    positivity
  have hendIntercept :
      (sourceBlockEndLine context.Q data₁ block₁).interceptNumerator =
        (sourceBlockEndLine context.Q data₂ block₂).interceptNumerator := by
    apply intercept_eq_of_long_transform context.Q (F.system L).X
      Cstep (frequencyCutoff (F.system L))
      (sourceBlockEndLine context.Q data₁ block₁)
      (sourceBlockEndLine context.Q data₂ block₂)
      (sourceForwardWord (F.system L) gap.Cgap data₁ block₁)
      context.Q_pos hCstep hXpos hfrequencyL hendH hendK hendStep
      hspanPower huBound hvBound
  have hblockMono :
      (sourceBlockEndLine context.Q data₁ block₁).interceptNumerator -
          (sourceBlockEndLine context.Q data₂ block₂).interceptNumerator =
        (2 : ℤ) ^ σ.gaps.span *
          ((sourceRawLine context.Q data₁ block₁).interceptNumerator -
            (sourceRawLine context.Q data₂ block₂).interceptNumerator) := by
    unfold sourceBlockEndLine
    rw [hblockGaps₁, hblockGaps₂]
    exact AffineLine.interceptDifference_transformWord context.Q
      (sourceRawLine context.Q data₁ block₁)
      (sourceRawLine context.Q data₂ block₂) σ.gaps hrawH hrawK
  have hrawIntercept :
      (sourceRawLine context.Q data₁ block₁).interceptNumerator =
        (sourceRawLine context.Q data₂ block₂).interceptNumerator := by
    have hproduct : (2 : ℤ) ^ σ.gaps.span *
        ((sourceRawLine context.Q data₁ block₁).interceptNumerator -
          (sourceRawLine context.Q data₂ block₂).interceptNumerator) = 0 := by
      rw [← hblockMono, hendIntercept]
      simp
    have hpowNe : (2 : ℤ) ^ σ.gaps.span ≠ 0 := pow_ne_zero _ (by norm_num)
    exact sub_eq_zero.mp ((mul_eq_zero.mp hproduct).resolve_left hpowNe)
  have hcanonical :
      (sourceRawLine context.Q data₁ block₁).canonicalGeometricLine =
        (sourceRawLine context.Q data₂ block₂).canonicalGeometricLine :=
    AffineLine.canonicalGeometricLine_eq_of_primitive_direction_intercept
      _ _ hprimitive₁ hprimitive₂ hrawH hrawK hrawIntercept
  calc
    line₁ = (sourceRawLine context.Q data₁ block₁).canonicalGeometricLine := hline₁.symm
    _ = (sourceRawLine context.Q data₂ block₂).canonicalGeometricLine := hcanonical
    _ = line₂ := hline₂

/-- Paper label: `lem:source-fibre` (Section 6).

The remaining proof uses: `lem_line_unique`; the primitive raw-line
converse to `AffineLine.contains_canonicalGeometricLine`; equality of raw and
canonical normalized slopes in the primitive case; and finite-cardinality
transport through `spatialSourceCode_injective`.  None of these facts is
encoded as an assumption in the source data. -/
theorem lem_source_fibre (context : FixedScaleContext)
    (gap : GapParams context.Q) (Cstep : ℝ) (hCstep : 0 < Cstep) :
    ∃ Zmin : ℕ,
      ∀ Z0 : ℕ, Zmin ≤ Z0 →
        ∀ F : ScaleFamily, F.MatchesContext context →
          ∀ᶠ L : ℕ in atTop,
            ∀ selection : InteriorAnchorSelection,
              ValidInteriorAnchorSelection context.Q (F.system L) Z0 selection →
                ∀ σ : BlockEncoding,
                  σ ∈ encodingCandidates σ.D σ.Z context.structural.B →
                    0 < σ.D →
                      (spatialPreimage context.Q gap.Cgap
                          context.structural.B Cstep (F.system L) Z0
                          selection σ).Finite ∧
                        ((spatialPreimage context.Q gap.Cgap
                            context.structural.B Cstep (F.system L) Z0
                            selection σ).ncard : ℝ) ≤
                          (context.Q : ℝ) * (Cstep + 4) *
                            (F.system L).m * (F.system L).X / σ.D := by
  classical
  obtain ⟨Zmin, hline⟩ := lem_line_unique context gap Cstep hCstep
  refine ⟨Zmin, ?_⟩
  intro Z0 hZ0 F hF
  filter_upwards [hline Z0 hZ0 F hF] with L hlineL
  intro selection hselection σ hσ hD
  let W := F.system L
  let S := spatialPreimage context.Q gap.Cgap context.structural.B
    Cstep W Z0 selection σ
  have hsubsingleton := hlineL selection hselection σ hσ hD
  by_cases hSne : S.Nonempty
  · rcases hSne with ⟨⟨k₀, block₀⟩, hsource₀⟩
    have hsource₀' := hsource₀
    change IsSpatialEncodingSource context.Q gap.Cgap
      context.structural.B Cstep W Z0 selection σ (k₀, block₀) at hsource₀'
    rcases hsource₀' with ⟨data₀, t₀, hrec₀, hparameter₀⟩
    rcases hrec₀ with
      ⟨hselected₀, hvalid₀, hfrequent₀, hblock₀, hoccurs₀,
        hoffset₀, hcandidate₀, hD₀, hencoding₀, hprimitive₀,
        hline₀, hstep₀, hrealizes₀, hgeometric₀, hblockTrajectory₀,
        hlower₀, hupper₀, hpositive₀, hinterior₀⟩
    let base := sourceRawLine context.Q data₀ block₀
    have hbaseMem : base.canonicalGeometricLine ∈
        spatialCanonicalLines context.Q gap.Cgap context.structural.B
          Cstep W Z0 selection σ := by
      exact ⟨k₀, data₀, block₀, hsource₀, hselected₀, rfl⟩
    let P : Set ℤ := horizontalParameters W.X base
    let J : Set ℕ := Set.Iio W.m
    let parameterCode : ℤ × ℕ → Option (ℕ × ℕ) := fun tj =>
      some ((base.A + base.H * tj.1).toNat, tj.2)
    let envelope : Set (Option (ℕ × ℕ)) := parameterCode '' (P ×ˢ J)
    have hPfinite : P.Finite := by
      exact (lem_primitive_direction context.Q W.X context.Q_pos base
        hprimitive₀).2.1
    have hPJfinite : (P ×ˢ J).Finite :=
      hPfinite.prod (Set.finite_Iio W.m)
    have henvelopeFinite : envelope.Finite := hPJfinite.image parameterCode
    have himageSubset : spatialSourceCode W selection '' S ⊆ envelope := by
      rintro _ ⟨⟨k, block⟩, hsource, rfl⟩
      have hsource' := hsource
      change IsSpatialEncodingSource context.Q gap.Cgap
        context.structural.B Cstep W Z0 selection σ (k, block) at hsource'
      rcases hsource' with ⟨data, tsource, hrec, hparameter⟩
      rcases hrec with
        ⟨hselected, hvalid, hfrequent, hblock, hoccurs,
          hoffset, hcandidate, hDsource, hencoding, hprimitive,
          hline, hstep, hrealizes, hgeometric, hblockTrajectory,
          hlower, hupper, hpositive, hinterior⟩
      have hlineMem : (sourceRawLine context.Q data block).canonicalGeometricLine ∈
          spatialCanonicalLines context.Q gap.Cgap context.structural.B
            Cstep W Z0 selection σ :=
        ⟨k, data, block, hsource, hselected, rfl⟩
      have hlineEq : base.canonicalGeometricLine =
          (sourceRawLine context.Q data block).canonicalGeometricLine :=
        hsubsingleton hbaseMem hlineMem
      have hxOwn := sourceCoordinate_on_canonicalLine context.Q W k data block
        tsource hparameter
      have hxBase : base.canonicalGeometricLine.Contains
          (sourceCoordinate W k data block : ℤ)
          (carryInt W.rational (sourceCoordinate W k data block)) := by
        rw [hlineEq]
        exact hxOwn
      obtain ⟨t, hxt, hrt⟩ :=
        base.contains_of_canonicalGeometricLine_of_primitive hprimitive₀
          (sourceCoordinate W k data block : ℤ)
          (carryInt W.rational (sourceCoordinate W k data block)) hxBase
      have hsourceCorridor :=
        originalSourceParameter_mem_corridor context.Q W k data block
          tsource hparameter
      have hxsource := hparameter.1
      change -(W.X : ℤ) ≤
          (sourceRawLine context.Q data block).A +
              (sourceRawLine context.Q data block).H * tsource ∧
        (sourceRawLine context.Q data block).A +
              (sourceRawLine context.Q data block).H * tsource ≤
            3 * W.X at hsourceCorridor
      rw [← hxsource] at hsourceCorridor
      have htP : t ∈ P := by
        change -(W.X : ℤ) ≤ base.A + base.H * t ∧
          base.A + base.H * t ≤ 3 * W.X
        rw [← hxt]
        exact hsourceCorridor
      have htJ : sourceWindowOffset W k data block ∈ J := hoffset
      refine ⟨(t, sourceWindowOffset W k data block), ⟨htP, htJ⟩, ?_⟩
      have htoNat : (base.A + base.H * t).toNat =
          sourceCoordinate W k data block := by
        rw [← hxt]
        simp
      rw [spatialSourceCode_of_selected W selection k block data hselected]
      simp [parameterCode, htoNat]
    have hcodeImageFinite : (spatialSourceCode W selection '' S).Finite :=
      henvelopeFinite.subset himageSubset
    have hinjective := spatialSourceCode_injective context.Q gap.Cgap
      context.structural.B Cstep W Z0 selection σ
    have hSfinite : S.Finite :=
      Set.Finite.of_finite_image hcodeImageFinite hinjective
    refine ⟨hSfinite, ?_⟩
    have hcardImage : S.ncard =
        (spatialSourceCode W selection '' S).ncard :=
      hinjective.ncard_image.symm
    have hcardSubset :
        (spatialSourceCode W selection '' S).ncard ≤ envelope.ncard :=
      Set.ncard_le_ncard himageSubset henvelopeFinite
    have hcardEnvelope : envelope.ncard ≤ (P ×ˢ J).ncard := by
      exact Set.ncard_image_le hPJfinite
    have hcardNat : S.ncard ≤ P.ncard * W.m := by
      rw [hcardImage]
      calc
        (spatialSourceCode W selection '' S).ncard ≤ envelope.ncard := hcardSubset
        _ ≤ (P ×ˢ J).ncard := hcardEnvelope
        _ = P.ncard * J.ncard := Set.ncard_prod
        _ = P.ncard * W.m := by rw [Set.ncard_Iio_nat]
    have hcardReal : (S.ncard : ℝ) ≤ (P.ncard : ℝ) * W.m := by
      exact_mod_cast hcardNat
    have hPbound := (lem_primitive_direction context.Q W.X context.Q_pos base
      hprimitive₀).2.2
    have hdenBand : σ.D ≤ (base.slope context.Q).den := hrealizes₀.1
    have hHden := (lem_primitive_direction context.Q W.X context.Q_pos base
      hprimitive₀).1
    have hgcdLe : Nat.gcd (base.slope context.Q).den context.Q ≤ context.Q :=
      Nat.gcd_le_right _ context.Q_pos
    have hgcdDvd : Nat.gcd (base.slope context.Q).den context.Q ∣
        (base.slope context.Q).den := Nat.gcd_dvd_left _ _
    have hdenStepNat : (base.slope context.Q).den ≤
        base.H.natAbs * context.Q := by
      calc
        (base.slope context.Q).den =
            (base.slope context.Q).den /
                Nat.gcd (base.slope context.Q).den context.Q *
              Nat.gcd (base.slope context.Q).den context.Q :=
          (Nat.div_mul_cancel hgcdDvd).symm
        _ ≤ (base.slope context.Q).den /
                Nat.gcd (base.slope context.Q).den context.Q * context.Q :=
          Nat.mul_le_mul_left _ hgcdLe
        _ = base.H.natAbs * context.Q := by rw [hHden]
    have hprimitiveBase : Int.gcd base.H base.K = 1 := hprimitive₀
    have hcanonHInt : (base.canonicalGeometricLine.H : ℤ) = base.H := by
      rw [base.canonicalGeometricLine_H_cast]
      simp only [AffineLine.primitiveHorizontalInt,
        AffineLine.directionGCD, hprimitiveBase]
      norm_num
    have hcanonHReal : (base.canonicalGeometricLine.H : ℝ) = (base.H : ℝ) := by
      exact_mod_cast hcanonHInt
    have hXone : (1 : ℝ) ≤ W.X := by
      rw [WindowSystem.X, dyadicScale]
      exact_mod_cast Nat.one_le_two_pow
    have hfrequencyOne : (1 : ℝ) ≤ frequencyCutoff W := by
      unfold frequencyCutoff
      exact Real.one_le_rpow hXone (by
        have := W.structural.rho_pos
        linarith)
    have hfrequencyPos : (0 : ℝ) < frequencyCutoff W :=
      lt_of_lt_of_le zero_lt_one hfrequencyOne
    have hstepBase : (base.H : ℝ) ≤ Cstep * W.X := by
      rw [← hcanonHReal]
      refine hstep₀.trans ?_
      rw [div_le_iff₀ hfrequencyPos]
      have hnonneg : 0 ≤ Cstep * (W.X : ℝ) := by positivity
      nlinarith
    have hHnatReal : (base.H.natAbs : ℝ) = (base.H : ℝ) := by
      have hHnatInt : (base.H.natAbs : ℤ) = base.H :=
        Int.natAbs_of_nonneg base.H_pos.le
      calc
        (base.H.natAbs : ℝ) = ((base.H.natAbs : ℤ) : ℝ) := by norm_num
        _ = (base.H : ℝ) := by rw [hHnatInt]
    have hdenStepReal : ((base.slope context.Q).den : ℝ) ≤
        (context.Q : ℝ) * Cstep * W.X := by
      have hcast : ((base.slope context.Q).den : ℝ) ≤
          (base.H.natAbs : ℝ) * context.Q := by exact_mod_cast hdenStepNat
      rw [hHnatReal] at hcast
      nlinarith [show (0 : ℝ) ≤ context.Q by positivity]
    have hDStep : (σ.D : ℝ) ≤ (context.Q : ℝ) * Cstep * W.X := by
      have hDden : (σ.D : ℝ) ≤ ((base.slope context.Q).den : ℝ) := by
        exact_mod_cast hdenBand
      exact hDden.trans hdenStepReal
    have hDreal : (0 : ℝ) < σ.D := by exact_mod_cast hD
    have hDdenReal : (σ.D : ℝ) ≤ (base.slope context.Q).den := by
      exact_mod_cast hdenBand
    have hfourFraction :
        4 * (context.Q : ℝ) * W.X / (base.slope context.Q).den ≤
          4 * (context.Q : ℝ) * W.X / σ.D := by
      exact div_le_div_of_nonneg_left (by positivity) hDreal hDdenReal
    have honeFraction : (1 : ℝ) ≤
        (context.Q : ℝ) * Cstep * W.X / σ.D := by
      rw [le_div_iff₀ hDreal]
      simpa [one_mul] using hDStep
    have hPfinal : (P.ncard : ℝ) ≤
        (context.Q : ℝ) * (Cstep + 4) * W.X / σ.D := by
      calc
        (P.ncard : ℝ) ≤ 1 +
            4 * (context.Q : ℝ) * W.X /
              (base.slope context.Q).den := hPbound
        _ ≤ (context.Q : ℝ) * Cstep * W.X / σ.D +
            4 * (context.Q : ℝ) * W.X / σ.D :=
          add_le_add honeFraction hfourFraction
        _ = (context.Q : ℝ) * (Cstep + 4) * W.X / σ.D := by ring
    have hmnonneg : (0 : ℝ) ≤ W.m := by positivity
    calc
      (S.ncard : ℝ) ≤ (P.ncard : ℝ) * W.m := hcardReal
      _ ≤ ((context.Q : ℝ) * (Cstep + 4) * W.X / σ.D) * W.m :=
        mul_le_mul_of_nonneg_right hPfinal hmnonneg
      _ = (context.Q : ℝ) * (Cstep + 4) * W.m * W.X / σ.D := by ring
  · have hSempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hSne
    have hemptyResult : S.Finite ∧
        (S.ncard : ℝ) ≤ (context.Q : ℝ) * (Cstep + 4) *
          W.m * W.X / σ.D := by
      rw [hSempty]
      constructor
      · exact Set.finite_empty
      · simp
        positivity
    simpa [S, W] using hemptyResult

/-- Largest power of two not exceeding a positive natural number.  At zero
the definition takes the harmless default value `1`; all uses in the strict
cone decomposition carry a positivity proof. -/
def dyadicFloorBand (n : ℕ) : ℕ := 2 ^ Nat.log 2 n

@[simp] theorem dyadicFloorBand_pos (n : ℕ) : 0 < dyadicFloorBand n := by
  simp [dyadicFloorBand]

theorem dyadicFloorBand_isPow (n : ℕ) :
    ∃ k : ℕ, dyadicFloorBand n = 2 ^ k := by
  exact ⟨Nat.log 2 n, rfl⟩

theorem dyadicFloorBand_le {n : ℕ} (hn : 0 < n) :
    dyadicFloorBand n ≤ n := by
  exact Nat.pow_log_le_self 2 hn.ne'

theorem dyadicFloorBand_lt_two_mul (n : ℕ) :
    n < 2 * dyadicFloorBand n := by
  simpa [dyadicFloorBand, pow_succ, Nat.mul_comm] using
    (Nat.lt_pow_succ_log_self (by omega : 1 < 2) n)

/-- Dyadic lower band of the integer average gap. -/
def meanGapBand (span count : ℕ) : ℕ :=
  dyadicFloorBand (span / count)

theorem meanGapBand_bounds {span count : ℕ}
    (hcount : 0 < count) (hcountSpan : count ≤ span) :
    0 < meanGapBand span count ∧
      meanGapBand span count * count ≤ span ∧
      span < 2 * meanGapBand span count * count := by
  have hquotPos : 0 < span / count := Nat.div_pos hcountSpan hcount
  have hlower := dyadicFloorBand_le hquotPos
  have hupper := dyadicFloorBand_lt_two_mul (span / count)
  refine ⟨dyadicFloorBand_pos _, ?_, ?_⟩
  · exact (Nat.le_div_iff_mul_le hcount).mp hlower
  · exact (Nat.div_lt_iff_lt_mul hcount).mp hupper

/-- A segment whose span carries a fixed fraction of the parent excess has
mean-gap band strictly beyond the cutoff scale. -/
theorem meanGapBand_above_cutoff
    {span count m Z Z0 : ℕ} {y : ℝ}
    (hm : 0 < m) (hcount : count ≤ m)
    (hy : (m : ℝ) * Z0 < y) (hspan : y / 16 ≤ span)
    (hmeanUpper : span < 2 * Z * count) :
    (Z0 : ℝ) / 32 < Z := by
  have hcountReal : (count : ℝ) ≤ m := by exact_mod_cast hcount
  have hspanReal : (span : ℝ) < 2 * Z * count := by exact_mod_cast hmeanUpper
  have hcoef : (0 : ℝ) ≤ 2 * Z := by positivity
  have hcountScaled : (2 : ℝ) * Z * count ≤ 2 * Z * m :=
    mul_le_mul_of_nonneg_left hcountReal hcoef
  have hmReal : (0 : ℝ) < m := by positivity
  nlinarith

/-- Combining denominator--span with the dyadic denominator band gives the
lower band used by the signature-entropy estimate. -/
theorem denominatorBand_lower
    {span count q D Z : ℕ} {cspan : ℝ}
    (hcspan : 0 < cspan)
    (hZavg : (Z : ℝ) ≤ (span : ℝ) / count)
    (hden : cspan * Real.rpow 2 ((span : ℝ) / count) ≤ q)
    (hqband : q < 2 * D) :
    cspan / 2 * (2 : ℝ) ^ Z ≤ D := by
  have hrpow : Real.rpow 2 (Z : ℝ) ≤
      Real.rpow 2 ((span : ℝ) / count) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hZavg
  have hpow : (2 : ℝ) ^ Z ≤
      Real.rpow 2 ((span : ℝ) / count) := by
    simpa [Real.rpow_natCast] using hrpow
  have hscaled := mul_le_mul_of_nonneg_left hpow hcspan.le
  have hqbandReal : (q : ℝ) < 2 * D := by exact_mod_cast hqband
  nlinarith

/-- Every gap on a fixed odd-denominator segment is short enough for the
logarithmic greedy scale associated with any dyadic band containing that
denominator. -/
theorem OddDenominatorSegment.gap_le_logBand
    (Q D : ℕ) (hQ : 0 < Q)
    (segment : OddDenominatorSegment) (hsegment : segment.Valid Q)
    (hqband : segment.q < 2 * D) :
    ∀ g ∈ segment.gaps,
      g ≤ Nat.ceil (Real.logb 2 (4 * D)) := by
  intro g hg
  rcases hsegment with
    ⟨_hQ, _hpositive, _hprimitive, htrace, _hq_one, _hq_odd, hslopes⟩
  obtain ⟨r, hr, hget⟩ := List.getElem_of_mem hg
  have hμmemTrace :
      (segment.startLine.transformWord Q (segment.gaps.take r)).slope Q ∈
        OddDenominatorSegment.slopeTrace Q segment.startLine segment.gaps := by
    unfold OddDenominatorSegment.slopeTrace
    apply List.mem_map_of_mem
    exact List.mem_range.mpr (by omega)
  have hνmemTrace :
      (segment.startLine.transformWord Q (segment.gaps.take (r + 1))).slope Q ∈
        OddDenominatorSegment.slopeTrace Q segment.startLine segment.gaps := by
    unfold OddDenominatorSegment.slopeTrace
    apply List.mem_map_of_mem
    exact List.mem_range.mpr (by omega)
  have hμmem :
      (segment.startLine.transformWord Q (segment.gaps.take r)).slope Q ∈
        segment.slopes := by
    rw [htrace]
    exact hμmemTrace
  have hνmem :
      (segment.startLine.transformWord Q (segment.gaps.take (r + 1))).slope Q ∈
        segment.slopes := by
    rw [htrace]
    exact hνmemTrace
  let μ := (segment.startLine.transformWord Q (segment.gaps.take r)).slope Q
  let ν :=
    (segment.startLine.transformWord Q (segment.gaps.take (r + 1))).slope Q
  have hμdata := hslopes μ (by simpa [μ] using hμmem)
  have hνdata := hslopes ν (by simpa [ν] using hνmem)
  have htake : segment.gaps.take (r + 1) =
      segment.gaps.take r ++ [g] := by
    rw [← hget]
    simpa only [List.concat_eq_append] using (List.take_concat_get hr).symm
  have hνμ : ν = (2 : ℚ) ^ g * μ - 1 := by
    calc
      ν = (segment.startLine.transformWord Q
          (segment.gaps.take r ++ [g])).slope Q := by rw [← htake]
      _ = ((segment.startLine.transformWord Q (segment.gaps.take r)).transformWord
          Q [g]).slope Q := by rw [AffineLine.transformWord_append]
      _ = ((segment.startLine.transformWord Q
          (segment.gaps.take r)).transform Q g).slope Q := rfl
      _ = (2 : ℚ) ^ g * μ - 1 := by
        rw [AffineLine.slope_transform Q hQ]
  have hμlower : (1 : ℚ) / segment.q ≤ μ := by
    have hdenpos : (0 : ℚ) < μ.den := by positivity
    have hnumone : (1 : ℚ) ≤ μ.num := by
      exact_mod_cast (show (1 : ℤ) ≤ μ.num by
        exact (Int.add_one_le_iff).2 (Rat.num_pos.mpr hμdata.1.1))
    calc
      (1 : ℚ) / segment.q = 1 / μ.den := by rw [hμdata.2.1]
      _ ≤ (μ.num : ℚ) / μ.den :=
        (div_le_div_iff_of_pos_right hdenpos).2 hnumone
      _ = μ := Rat.num_div_den μ
  have hpowμ : (2 : ℚ) ^ g * μ < 2 := by
    rw [hνμ] at hνdata
    linarith [hνdata.1.2]
  have hqpos : (0 : ℚ) < segment.q := by positivity
  have hpowdiv : (2 : ℚ) ^ g / segment.q < 2 := by
    calc
      (2 : ℚ) ^ g / segment.q = (2 : ℚ) ^ g * (1 / segment.q) := by ring
      _ ≤ (2 : ℚ) ^ g * μ :=
        mul_le_mul_of_nonneg_left hμlower (by positivity)
      _ < 2 := hpowμ
  have hpowltRat : (2 : ℚ) ^ g < 2 * segment.q :=
    (div_lt_iff₀ hqpos).1 hpowdiv
  have hpowlt : 2 ^ g < 4 * D := by
    have hpowltNat : 2 ^ g < 2 * segment.q := by exact_mod_cast hpowltRat
    omega
  have hellEq : Nat.ceil (Real.logb 2 (4 * D)) = Nat.clog 2 (4 * D) := by
    simpa only [Nat.cast_ofNat, Nat.cast_mul] using
      Real.natCeil_logb_natCast 2 (4 * D)
  rw [hellEq]
  exact ((Nat.lt_clog_iff_pow_lt (by omega)).2 hpowlt).le

/-- Every genuine selected block start retains the original integer parameter
of the affine support run.  The strict offset bound keeps that point inside
the enlarged dyadic corridor. -/
theorem exists_originalSourceParameter
    (Q : ℕ) (W : WindowSystem) (Z0 k : ℕ)
    (hden : W.rational.eta.den = Q)
    (data : AnchorInteriorData) (hvalid : data.Valid Q W Z0 k)
    (block : LowGapBlock) (hoccurs : LowGapBlock.OccursIn data.segment block)
    (hoffset : sourceWindowOffset W k data block < W.m) :
    ∃ t : ℤ, IsOriginalSourceParameter Q W k data block t := by
  classical
  let i := k - W.s + (initialLongPrefix W k).length + data.before.length
  have hstart := data.segmentStart_contains_actual Q W Z0 k hden hvalid
  rcases hstart with ⟨t, hx, hr⟩
  have hsegment := data.segmentGaps_eq_enumerationGapWord Q W Z0 k hvalid
  have hoffsetSegment : block.offset ≤ data.segment.gaps.length :=
    le_trans (Nat.le_add_right block.offset block.gaps.length) hoccurs.1
  have htakePrefix : (data.segment.gaps.take block.offset).IsPrefix
      (enumerationGapWord W.enumeration i data.segment.gaps.length) := by
    rw [← hsegment]
    exact List.take_prefix _ _
  have htakeLen : (data.segment.gaps.take block.offset).length = block.offset := by
    simp [hoffsetSegment]
  have htake : data.segment.gaps.take block.offset =
      enumerationGapWord W.enumeration i block.offset := by
    have := prefix_enumerationGapWord_eq W.enumeration i
      data.segment.gaps.length (data.segment.gaps.take block.offset) htakePrefix
    simpa [htakeLen] using this
  have hpoint := data.segment.startLine.transformWord_parameter_enumerationGapWord
    Q W.rational hden W.enumeration i block.offset t hx hr
  rw [← htake] at hpoint
  have hindex : i + block.offset =
      k - W.s + sourceWindowOffset W k data block := by
    unfold sourceWindowOffset
    dsimp [i]
    omega
  have hindexLe : k - W.s + sourceWindowOffset W k data block ≤ k := by
    rw [WindowSystem.m] at hoffset
    have hsk : W.s ≤ k := hvalid.1
    omega
  have hkAnchor : k ∈ W.anchors := by
    have hhigh := hvalid.2.1
    rw [highAnchors, Finset.mem_filter] at hhigh
    exact hhigh.1
  have hxUpper : sourceCoordinate W k data block ≤ 2 * W.X := by
    unfold sourceCoordinate
    calc
      W.enumeration.a (k - W.s + sourceWindowOffset W k data block) ≤
          W.enumeration.a k := W.enumeration.strictMono.monotone hindexLe
      _ ≤ 2 * W.X := (Finset.mem_filter.mp hkAnchor).2.2
  refine ⟨t, ?_, ?_, ?_⟩
  · unfold sourceCoordinate sourceRawLine
    rw [← hindex]
    exact hpoint.1
  · unfold sourceCoordinate sourceRawLine
    rw [← hindex]
    exact hpoint.2
  · change -(W.X : ℤ) ≤ (sourceRawLine Q data block).A +
        (sourceRawLine Q data block).H * t ∧
      (sourceRawLine Q data block).A +
        (sourceRawLine Q data block).H * t ≤ 3 * W.X
    have hxEq : (sourceRawLine Q data block).A +
        (sourceRawLine Q data block).H * t =
          (sourceCoordinate W k data block : ℤ) := by
      symm
      unfold sourceCoordinate sourceRawLine
      rw [← hindex]
      exact hpoint.1
    rw [hxEq]
    constructor
    · have hneg : -(W.X : ℤ) ≤ 0 := neg_nonpos.mpr (by positivity)
      exact hneg.trans (by positivity)
    · exact_mod_cast (hxUpper.trans (by omega : 2 * W.X ≤ 3 * W.X))

local instance affineLineCountableForStrict : Countable AffineLine := by
  let code : AffineLine → ℤ × ℤ × ℤ × ℤ := fun line =>
    (line.A, line.C, line.H, line.K)
  exact (show Function.Injective code from by
    intro line₁ line₂ h
    cases line₁
    cases line₂
    simp only [code, Prod.mk.injEq] at h
    simp_all).countable

private theorem measurableSet_exists_le_countable_strict {α β : Type*}
    [Countable α] [MeasurableSpace β] (f : β → ℝ) (hf : Measurable f)
    (P : α → Prop) (c : α → ℝ) :
    MeasurableSet {x | ∃ a, P a ∧ f x ≤ c a} := by
  classical
  rw [show {x | ∃ a, P a ∧ f x ≤ c a} =
      ⋃ a, if P a then {x | f x ≤ c a} else ∅ by
    ext x
    simp]
  exact MeasurableSet.iUnion fun a => by
    by_cases ha : P a
    · simpa [ha] using measurableSet_le hf measurable_const
    · simp [ha]

private theorem measurableSet_windowThreshold_of_sections_strict
    (E : Set WindowThreshold)
    (hsection : ∀ k : ℕ, MeasurableSet {T : ℝ | (k, T) ∈ E}) :
    MeasurableSet E := by
  rw [show E = ⋃ k : ℕ, Set.prod {k} {T : ℝ | (k, T) ∈ E} by
    ext e
    rcases e with ⟨k, T⟩
    rw [Set.mem_iUnion]
    change (k, T) ∈ E ↔
      ∃ i : ℕ, (k, T) ∈ Set.prod {i} {u : ℝ | (i, u) ∈ E}
    constructor
    · intro h
      exact ⟨k, ⟨by simp, h⟩⟩
    · rintro ⟨i, hi⟩
      have hik : k = i := hi.1
      subst i
      exact hi.2]
  exact MeasurableSet.iUnion fun k =>
    (MeasurableSet.singleton k).prod (hsection k)

theorem measurableSet_largePairs_strict (W : WindowSystem) (Z0 : ℕ) :
    MeasurableSet (W.largePairs Z0) := by
  exact W.measurableSet_pairSet.inter
    (measurableSet_lt
      (measurable_const : Measurable
        (fun _ : WindowThreshold => (W.m : ℝ) * Z0))
      W.measurable_excess)

private theorem measurableSet_longInteriorPair_section_strict
    (W : WindowSystem) (Z0 k : ℕ) :
    MeasurableSet {T : ℝ | LongInteriorPair W Z0 (k, T)} := by
  classical
  have hlargeSection :
      MeasurableSet {T : ℝ | (k, T) ∈ W.largePairs Z0} :=
    (measurableSet_largePairs_strict W Z0).preimage measurable_prodMk_left
  let P : AffineLine × GapWord → Prop := fun lg =>
    IsActualInitialContinuation W Z0 (k, 0) lg.1 lg.2 ∧
      IsInteriorTrajectory W.rational.eta.den lg.1 lg.2
  have hexists : MeasurableSet
      {T : ℝ | ∃ lg : AffineLine × GapWord,
        P lg ∧ W.excess (k, T) / 8 ≤ (lg.2.span : ℝ)} := by
    apply measurableSet_exists_le_countable_strict
    exact W.measurable_excess.comp measurable_prodMk_left |>.div_const 8
  by_cases hfreq : IsFrequentPrefix W Z0 (initialLongPrefix W k)
  · have heq : {T : ℝ | LongInteriorPair W Z0 (k, T)} =
        {T | (k, T) ∈ W.largePairs Z0 ∧
          ∃ lg : AffineLine × GapWord,
            P lg ∧ W.excess (k, T) / 8 ≤ (lg.2.span : ℝ)} := by
      ext T
      change
        ((k, T) ∈ W.largePairs Z0 ∧
          IsFrequentPrefix W Z0 (initialLongPrefix W k) ∧
          ∃ line gaps,
            IsActualInitialContinuation W Z0 (k, T) line gaps ∧
            IsInteriorTrajectory W.rational.eta.den line gaps ∧
            W.excess (k, T) / 8 ≤ (gaps.span : ℝ)) ↔ _
      have hactual : ∀ line gaps,
          IsActualInitialContinuation W Z0 (k, T) line gaps ↔
            IsActualInitialContinuation W Z0 (k, 0) line gaps := by
        intro line gaps
        rfl
      simp only [hfreq, true_and, hactual, P]
      constructor <;> aesop
    rw [heq]
    exact hlargeSection.inter hexists
  · have heq : {T : ℝ | LongInteriorPair W Z0 (k, T)} = ∅ := by
      ext T
      constructor
      · intro h
        exact (hfreq h.2.1).elim
      · intro h
        exact h.elim
    rw [heq]
    exact MeasurableSet.empty

theorem measurableSet_interiorPairs_strict (W : WindowSystem) (Z0 : ℕ) :
    MeasurableSet (interiorPairs W Z0) := by
  apply measurableSet_windowThreshold_of_sections_strict
  intro k
  exact measurableSet_longInteriorPair_section_strict W Z0 k

theorem interiorPairs_subset_pairSet (W : WindowSystem) (Z0 : ℕ) :
    interiorPairs W Z0 ⊆ W.pairSet := by
  intro e he
  exact he.1.1

/-- Dyadic denominator band fixed by the anchor's selected segment. -/
def selectedDenominatorBand (selection : InteriorAnchorSelection) (k : ℕ) : ℕ :=
  match selection k with
  | none => 1
  | some data => dyadicFloorBand data.segment.q

/-- Dyadic lower band of the selected segment's integer average gap. -/
def selectedMeanGapBand (selection : InteriorAnchorSelection) (k : ℕ) : ℕ :=
  match selection k with
  | none => 1
  | some data => meanGapBand data.segment.span data.segment.gapCount

def selectedLogLength (selection : InteriorAnchorSelection) (k : ℕ) : ℕ :=
  Nat.ceil (Real.logb 2 (4 * selectedDenominatorBand selection k))

def selectedForwardLength (W : WindowSystem) (gap : GapParams W.rational.eta.den)
    (_k : ℕ) : ℕ :=
  reconstructionForwardLength W gap.Cgap

/-- The deterministic threshold-independent block list attached to an anchor.
Unselected anchors carry the empty list. -/
def selectedInteriorBlocks (W : WindowSystem)
    (selection : InteriorAnchorSelection) (gap : GapParams W.rational.eta.den)
    (k : ℕ) : List LowGapBlock :=
  match selection k with
  | none => []
  | some data => selectedBlocks data.segment W.structural.B
      (selectedLogLength selection k) (selectedMeanGapBand selection k)
      (selectedForwardLength W gap k)

@[simp] theorem selectedDenominatorBand_pos
    (selection : InteriorAnchorSelection) (k : ℕ) :
    0 < selectedDenominatorBand selection k := by
  simp only [selectedDenominatorBand]
  split <;> simp

@[simp] theorem selectedMeanGapBand_pos
    (selection : InteriorAnchorSelection) (k : ℕ) :
    0 < selectedMeanGapBand selection k := by
  simp only [selectedMeanGapBand]
  split <;> simp [meanGapBand]

@[simp] theorem selectedLogLength_eq
    (selection : InteriorAnchorSelection) (k : ℕ) :
    selectedLogLength selection k =
      Nat.ceil (Real.logb 2 (4 * selectedDenominatorBand selection k)) := rfl

@[simp] theorem selectedForwardLength_eq
    (W : WindowSystem) (gap : GapParams W.rational.eta.den) (k : ℕ) :
    selectedForwardLength W gap k = reconstructionForwardLength W gap.Cgap := rfl

theorem selectedInteriorBlocks_eq_of_selected
    (W : WindowSystem) (selection : InteriorAnchorSelection)
    (gap : GapParams W.rational.eta.den) (k : ℕ)
    (data : AnchorInteriorData) (hselected : selection k = some data) :
    selectedInteriorBlocks W selection gap k =
      selectedBlocks data.segment W.structural.B
        (selectedLogLength selection k) (selectedMeanGapBand selection k)
        (selectedForwardLength W gap k) := by
  simp [selectedInteriorBlocks, hselected]

/-- Once the selected segment has enough span to pay for the forward reserve
and final greedy remainder, its deterministic anchor-level blocks form the
nonnegative sparse cover used in the strict mass refinement. -/
theorem selectedInteriorBlocks_sparseCover
    (Q : ℕ) (hQ : 0 < Q) (W : WindowSystem) (Z0 : ℕ)
    (selection : InteriorAnchorSelection)
    (gap : GapParams W.rational.eta.den) (e : WindowThreshold)
    (data : AnchorInteriorData) (hselected : selection e.1 = some data)
    (hvalid : data.Valid Q W Z0 e.1)
    (hspan : W.excess e / 16 ≤ data.segment.span)
    (hcount : 1 ≤ data.segment.gapCount)
    (hlarge :
      4 * (selectedForwardLength W gap e.1 +
        Nat.ceil ((W.structural.B + 1) * selectedLogLength selection e.1)) ≤
          data.segment.span) :
    let blocks := selectedInteriorBlocks W selection gap e.1
    IsLowGapCover data.segment W.structural.B
        (selectedLogLength selection e.1)
        (selectedMeanGapBand selection e.1)
        (selectedForwardLength W gap e.1) blocks ∧
      blocks.Nodup ∧
      (∀ block ∈ blocks,
        0 ≤ interiorComponentWeight (W.excess e) blocks block) ∧
      (∀ block ∈ blocks,
        interiorComponentWeight (W.excess e) blocks block ≤
          32 * Nat.ceil ((W.structural.B + 1) *
            selectedLogLength selection e.1)) ∧
      (blocks.map (fun block =>
        interiorComponentWeight (W.excess e) blocks block)).sum = W.excess e := by
  let D := selectedDenominatorBand selection e.1
  let Z := selectedMeanGapBand selection e.1
  let ell := selectedLogLength selection e.1
  let forward := selectedForwardLength W gap e.1
  let blocks := selectedInteriorBlocks W selection gap e.1
  have hsegment : data.segment.Valid Q := hvalid.2.2.2.2.1
  have hqpos : 0 < data.segment.q :=
    lt_trans (by omega) hsegment.2.2.2.2.1
  have hD : D = dyadicFloorBand data.segment.q := by
    simp [D, selectedDenominatorBand, hselected]
  have hDpos : 0 < D := by simp [D]
  have hqband : data.segment.q < 2 * D := by
    rw [hD]
    exact dyadicFloorBand_lt_two_mul _
  have hcountPos : 0 < data.segment.gapCount := by omega
  have hcountSpan : data.segment.gapCount ≤ data.segment.span := by
    rw [OddDenominatorSegment.gapCount, OddDenominatorSegment.span,
      GapWord.span]
    exact List.length_le_sum_of_one_le data.segment.gaps fun g hg =>
      hsegment.2.1 g hg
  have hmean : Z * data.segment.gapCount ≤ data.segment.span ∧
      data.segment.span < 2 * Z * data.segment.gapCount := by
    have hm := meanGapBand_bounds hcountPos hcountSpan
    simpa [Z, selectedMeanGapBand, hselected] using hm.2
  have hell : ell = Nat.ceil (Real.logb 2 (4 * D)) := by
    simp [ell, D]
  have hellPos : 0 < ell := by
    have hellEq : Nat.ceil (Real.logb 2 (4 * D)) = Nat.clog 2 (4 * D) := by
      simpa only [Nat.cast_ofNat, Nat.cast_mul] using
        Real.natCeil_logb_natCast 2 (4 * D)
    rw [hell, hellEq, Nat.lt_clog_iff_pow_lt (by omega)]
    simp
    omega
  have hgap : ∀ g ∈ data.segment.gaps, g ≤ ell := by
    rw [hell]
    exact data.segment.gap_le_logBand Q D hQ hsegment hqband
  have hy0 : 0 ≤ W.excess e := by
    unfold WindowSystem.excess
    positivity
  have hyUpper : W.excess e ≤ 16 * data.segment.span := by
    nlinarith
  obtain ⟨result, hcover, hnodup, hnonneg, hbound, hsum⟩ :=
    lem_sparse_cover Q W.structural.B W.structural.B_gt data.segment hsegment
      ell Z forward hellPos (by simp [Z]) hgap hmean
      (by simpa [ell, forward] using hlarge) (W.excess e) hy0 hyUpper
  have hdet : blocks = selectedBlocks data.segment W.structural.B ell Z forward := by
    simpa [blocks, ell, Z, forward] using
      selectedInteriorBlocks_eq_of_selected W selection gap e.1 data hselected
  have hresult : result = blocks := hcover.1.trans hdet.symm
  subst result
  exact ⟨hcover, hnodup, hnonneg, hbound, hsum⟩

theorem OddDenominatorSegment.startSlope_den_eq
    (Q : ℕ) (segment : OddDenominatorSegment) (hsegment : segment.Valid Q) :
    (segment.startLine.slope Q).den = segment.q := by
  have hmem : segment.startLine.slope Q ∈ segment.slopes := by
    rw [hsegment.2.2.2.1]
    unfold OddDenominatorSegment.slopeTrace
    have hz := List.mem_map_of_mem
      (f := fun r =>
        (segment.startLine.transformWord Q (segment.gaps.take r)).slope Q)
      (a := 0) (List.mem_range.mpr (by simp : 0 < segment.gaps.length + 1))
    simpa [AffineLine.transformWord] using hz
  exact (hsegment.2.2.2.2.2.2 _ hmem).2.1

theorem primitive_slope_den_le_Q_mul_H
    (Q : ℕ) (hQ : 0 < Q) (line : AffineLine)
    (hprimitive : Int.gcd line.H line.K = 1) :
    (line.slope Q).den ≤ Q * line.H.natAbs := by
  let q := (line.slope Q).den
  let g := Nat.gcd q Q
  have hformula := primitiveDirectionDenominator Q hQ line hprimitive
  have hgdvd : g ∣ q := Nat.gcd_dvd_left q Q
  have hgQ : g ≤ Q := Nat.gcd_le_right q hQ
  calc
    (line.slope Q).den = q := rfl
    _ = (q / g) * g := (Nat.div_mul_cancel hgdvd).symm
    _ = line.H.natAbs * g := by rw [hformula]
    _ ≤ line.H.natAbs * Q := Nat.mul_le_mul_left _ hgQ
    _ = Q * line.H.natAbs := Nat.mul_comm _ _

/-- The stabilized primitive-step bound forces the dyadic logarithmic block
length below the forward-gap allowance once the frequency cutoff dominates
the fixed denominator-level constant. -/
theorem selectedLogLength_le_of_step
    (Q Cgap : ℕ) (hQ : 0 < Q) (Cstep : ℝ)
    (W : WindowSystem) (Z0 k : ℕ) (selection : InteriorAnchorSelection)
    (data : AnchorInteriorData) (hselected : selection k = some data)
    (hvalid : data.Valid Q W Z0 k)
    (hstep : (data.segment.startLine.H : ℝ) ≤
      Cstep * W.X / frequencyCutoff W)
    (hfrequency : 4 * (Q : ℝ) * Cstep ≤ frequencyCutoff W) :
    selectedLogLength selection k ≤ W.L + Cgap := by
  let D := selectedDenominatorBand selection k
  have hsegment : data.segment.Valid Q := hvalid.2.2.2.2.1
  have hqpos : 0 < data.segment.q :=
    lt_trans (by omega) hsegment.2.2.2.2.1
  have hD : D = dyadicFloorBand data.segment.q := by
    simp [D, selectedDenominatorBand, hselected]
  have hDleq : D ≤ data.segment.q := by
    rw [hD]
    exact dyadicFloorBand_le hqpos
  have hprimitive : Int.gcd data.segment.startLine.H
      data.segment.startLine.K = 1 := hsegment.2.2.1
  have hdenEq := data.segment.startSlope_den_eq Q hsegment
  have hqHnat : data.segment.q ≤ Q * data.segment.startLine.H.natAbs := by
    rw [← hdenEq]
    exact primitive_slope_den_le_Q_mul_H Q hQ data.segment.startLine hprimitive
  have hHcast : (data.segment.startLine.H.natAbs : ℝ) =
      (data.segment.startLine.H : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos]
    exact_mod_cast data.segment.startLine.H_pos
  have hqH' : (data.segment.q : ℝ) ≤
      ((Q * data.segment.startLine.H.natAbs : ℕ) : ℝ) := by
    exact_mod_cast hqHnat
  have hqH : (data.segment.q : ℝ) ≤
      (Q : ℝ) * data.segment.startLine.H := by
    simpa [hHcast] using hqH'
  have hfreqPos : 0 < frequencyCutoff W := by
    unfold frequencyCutoff
    apply Real.rpow_pos_of_pos
    rw [WindowSystem.X, dyadicScale]
    positivity
  have hXnonneg : (0 : ℝ) ≤ W.X := by positivity
  have hscaledFrequency :
      4 * (Q : ℝ) * Cstep * W.X ≤ W.X * frequencyCutoff W := by
    nlinarith [mul_le_mul_of_nonneg_right hfrequency hXnonneg]
  have hratio :
      4 * (Q : ℝ) * (Cstep * W.X / frequencyCutoff W) ≤ W.X := by
    rw [show 4 * (Q : ℝ) * (Cstep * W.X / frequencyCutoff W) =
      (4 * Q * Cstep * W.X) / frequencyCutoff W by ring]
    exact (div_le_iff₀ hfreqPos).2 (by nlinarith)
  have hfourDReal : (4 * D : ℕ) ≤ W.X := by
    have hDqReal : (D : ℝ) ≤ data.segment.q := by exact_mod_cast hDleq
    have hchain : (4 : ℝ) * D ≤ W.X := by
      calc
        (4 : ℝ) * D ≤ 4 * data.segment.q :=
          mul_le_mul_of_nonneg_left hDqReal (by norm_num)
        _ ≤ 4 * ((Q : ℝ) * data.segment.startLine.H) :=
          mul_le_mul_of_nonneg_left hqH (by norm_num)
        _ ≤ 4 * (Q : ℝ) * (Cstep * W.X / frequencyCutoff W) := by
          nlinarith [mul_le_mul_of_nonneg_left hstep
            (show (0 : ℝ) ≤ 4 * Q by positivity)]
        _ ≤ W.X := hratio
    exact_mod_cast hchain
  have hfourDpow : 4 * D ≤ 2 ^ (W.L + Cgap) := by
    calc
      4 * D ≤ W.X := hfourDReal
      _ = 2 ^ W.L := rfl
      _ ≤ 2 ^ (W.L + Cgap) := Nat.pow_le_pow_right (by omega) (by omega)
  have hellEq : selectedLogLength selection k = Nat.clog 2 (4 * D) := by
    rw [selectedLogLength]
    have hDdef : selectedDenominatorBand selection k = D := rfl
    rw [hDdef]
    simpa only [Nat.cast_ofNat, Nat.cast_mul] using
      Real.natCeil_logb_natCast 2 (4 * D)
  rw [hellEq, Nat.clog_le_iff_le_pow (by omega)]
  exact hfourDpow

/-- An odd primitive horizontal direction remains primitive after one raw
shared-gap transformation. -/
theorem AffineLine.transform_primitive_of_odd_horizontal
    (Q g : ℕ) (line : AffineLine)
    (hprimitive : Int.gcd line.H line.K = 1)
    (hodd : Odd line.H.natAbs) :
    Int.gcd (line.transform Q g).H (line.transform Q g).K = 1 := by
  have hHK : Nat.Coprime line.H.natAbs line.K.natAbs := hprimitive
  have hHpow : Nat.Coprime line.H.natAbs (2 ^ g) :=
    hodd.coprime_two_right.pow_right g
  have hHmul : Nat.Coprime line.H.natAbs (2 ^ g * line.K.natAbs) :=
    hHpow.mul_right hHK
  have hmulGcd : Int.gcd line.H ((2 : ℤ) ^ g * line.K) = 1 := by
    rw [Int.gcd_def]
    simpa [Int.natAbs_mul, Int.natAbs_pow] using hHmul
  change Int.gcd line.H ((2 : ℤ) ^ g * line.K - (Q : ℤ) * line.H) = 1
  calc
    Int.gcd line.H ((2 : ℤ) ^ g * line.K - (Q : ℤ) * line.H) =
        Int.gcd ((2 : ℤ) ^ g * line.K - (Q : ℤ) * line.H) line.H :=
      Int.gcd_comm _ _
    _ = Int.gcd ((2 : ℤ) ^ g * line.K) line.H :=
      Int.gcd_sub_mul_right_left line.H ((2 : ℤ) ^ g * line.K) Q
    _ = Int.gcd line.H ((2 : ℤ) ^ g * line.K) := Int.gcd_comm _ _
    _ = 1 := hmulGcd

/-- Primitivity persists along every prefix of a fixed odd-horizontal raw
direction. -/
theorem AffineLine.transformWord_primitive_of_odd_horizontal
    (Q : ℕ) (line : AffineLine) (word : GapWord)
    (hprimitive : Int.gcd line.H line.K = 1)
    (hodd : Odd line.H.natAbs) :
    Int.gcd (line.transformWord Q word).H
      (line.transformWord Q word).K = 1 := by
  induction word generalizing line with
  | nil => exact hprimitive
  | cons g gs ih =>
      simp only [AffineLine.transformWord]
      apply ih (line.transform Q g)
      · exact line.transform_primitive_of_odd_horizontal Q g hprimitive hodd
      · simpa [AffineLine.transform] using hodd

/-- The primitive horizontal step of a valid fixed odd-denominator segment is
itself odd. -/
theorem OddDenominatorSegment.startLine_horizontal_odd
    (Q : ℕ) (segment : OddDenominatorSegment)
    (hsegment : segment.Valid Q) : Odd segment.startLine.H.natAbs := by
  have hden := segment.startSlope_den_eq Q hsegment
  have hformula := primitiveDirectionDenominator Q hsegment.1 segment.startLine
    hsegment.2.2.1
  let d := Nat.gcd segment.q Q
  have hdvd : d ∣ segment.q := Nat.gcd_dvd_left segment.q Q
  have hquotDvd : segment.q / d ∣ segment.q := by
    refine ⟨d, ?_⟩
    exact (Nat.div_mul_cancel hdvd).symm
  have hquotOdd : Odd (segment.q / d) :=
    Odd.of_dvd_nat hsegment.2.2.2.2.2.1 hquotDvd
  rw [hformula, hden]
  exact hquotOdd

/-- Every raw prefix direction in a valid fixed odd-denominator segment is
primitive. -/
theorem OddDenominatorSegment.prefixLine_primitive
    (Q : ℕ) (segment : OddDenominatorSegment)
    (hsegment : segment.Valid Q) (r : ℕ) :
    Int.gcd (segment.startLine.transformWord Q (segment.gaps.take r)).H
      (segment.startLine.transformWord Q (segment.gaps.take r)).K = 1 := by
  exact segment.startLine.transformWord_primitive_of_odd_horizontal Q
    (segment.gaps.take r) hsegment.2.2.1
      (segment.startLine_horizontal_odd Q hsegment)

/-- The slope datum attached to every genuine prefix of a valid segment. -/
theorem OddDenominatorSegment.prefixSlope_data
    (Q : ℕ) (segment : OddDenominatorSegment)
    (hsegment : segment.Valid Q) (r : ℕ) (hr : r ≤ segment.gaps.length) :
    let μ := (segment.startLine.transformWord Q (segment.gaps.take r)).slope Q
    μ ∈ Set.Ioo (0 : ℚ) 1 ∧ μ.den = segment.q ∧ Odd μ.num := by
  have htrace :
      (segment.startLine.transformWord Q (segment.gaps.take r)).slope Q ∈
        OddDenominatorSegment.slopeTrace Q segment.startLine segment.gaps := by
    unfold OddDenominatorSegment.slopeTrace
    exact List.mem_map_of_mem (List.mem_range.mpr (by omega))
  have hmem :
      (segment.startLine.transformWord Q (segment.gaps.take r)).slope Q ∈
        segment.slopes := by
    rw [hsegment.2.2.2.1]
    exact htrace
  exact hsegment.2.2.2.2.2.2 _ hmem

/-- A valid fixed odd-denominator segment is an interior trajectory at every
prefix. -/
theorem OddDenominatorSegment.interiorTrajectory
    (Q : ℕ) (segment : OddDenominatorSegment)
    (hsegment : segment.Valid Q) :
    IsInteriorTrajectory Q segment.startLine segment.gaps := by
  rw [isInteriorTrajectory_iff_transformWord]
  intro r hr
  exact (classifySlope_eq_interior_iff _).2
    (segment.prefixSlope_data Q hsegment r hr).1

/-- The deterministic forward reconstruction word remains on the actual
interior trajectory after its selected block. -/
theorem sourceForwardWord_interior
    (Q Cgap : ℕ) (W : WindowSystem) (data : AnchorInteriorData)
    (hsegment : data.segment.Valid Q) (block : LowGapBlock)
    (hoccurs : LowGapBlock.OccursIn data.segment block) :
    IsInteriorTrajectory Q (sourceBlockEndLine Q data block)
      (sourceForwardWord W Cgap data block) := by
  have hfull := data.segment.interiorTrajectory Q hsegment
  have hdecomp : data.segment.gaps.take block.offset ++ block.gaps ++
      sourceForwardSuffix data block = data.segment.gaps := by
    unfold sourceForwardSuffix
    calc
      data.segment.gaps.take block.offset ++ block.gaps ++
          data.segment.gaps.drop (block.offset + block.gaps.length) =
        data.segment.gaps.take block.offset ++
          ((data.segment.gaps.drop block.offset).take block.gaps.length ++
            (data.segment.gaps.drop block.offset).drop block.gaps.length) := by
              rw [hoccurs.2]
              simp [List.drop_drop, List.append_assoc]
      _ = data.segment.gaps.take block.offset ++
          data.segment.gaps.drop block.offset := by rw [List.take_append_drop]
      _ = data.segment.gaps := List.take_append_drop _ _
  have hdecomp' : data.segment.gaps.take block.offset ++
      (block.gaps ++ sourceForwardSuffix data block) = data.segment.gaps := by
    simpa [List.append_assoc] using hdecomp
  rw [← hdecomp', isInteriorTrajectory_append_iff] at hfull
  have hafterPrefix := hfull.2
  rw [isInteriorTrajectory_append_iff] at hafterPrefix
  have hafterBlock : IsInteriorTrajectory Q (sourceBlockEndLine Q data block)
      (sourceForwardSuffix data block) := by
    simpa [sourceRawLine, sourceBlockEndLine] using hafterPrefix.2
  have hprefix := GapWord.firstPrefixAbove_isPrefix
    (sourceForwardSuffix data block) (2 * W.L + Cgap)
  rcases hprefix with ⟨rest, hrest⟩
  rw [← hrest, isInteriorTrajectory_append_iff] at hafterBlock
  exact hafterBlock.1

/-- The retained forward reserve gives the exact lower and upper reconstruction
span bounds and preserves positivity. -/
theorem sourceForwardWord_spec
    (Q Cgap : ℕ) (W : WindowSystem) (data : AnchorInteriorData)
    (hsegment : data.segment.Valid Q) (block : LowGapBlock)
    (hforward : reconstructionForwardLength W Cgap ≤
      (sourceForwardSuffix data block).span)
    (hell : ∀ g ∈ data.segment.gaps, g ≤ W.L + Cgap)
    (hL : 1 ≤ W.L) :
    2 * W.L + Cgap < (sourceForwardWord W Cgap data block).span ∧
      (sourceForwardWord W Cgap data block).span ≤
        reconstructionForwardLength W Cgap ∧
      (sourceForwardWord W Cgap data block).Positive := by
  let suffix := sourceForwardSuffix data block
  let bound := 2 * W.L + Cgap
  have hcross : bound < suffix.span := by
    have : bound < reconstructionForwardLength W Cgap := by
      unfold bound reconstructionForwardLength
      omega
    exact this.trans_le hforward
  have hgapSuffix : ∀ g ∈ suffix, g ≤ W.L + Cgap := by
    intro g hg
    apply hell g
    exact List.mem_of_mem_drop hg
  refine ⟨?_, ?_, ?_⟩
  · exact GapWord.lt_span_firstPrefixAbove_of_lt_span suffix bound hcross
  · have hupper :=
      GapWord.span_firstPrefixAbove_le_add suffix bound (W.L + Cgap) hgapSuffix
    have hsum : bound + (W.L + Cgap) = reconstructionForwardLength W Cgap := by
      unfold bound reconstructionForwardLength
      omega
    change (suffix.firstPrefixAbove bound).span ≤ reconstructionForwardLength W Cgap
    rw [← hsum]
    exact hupper
  · apply GapWord.firstPrefixAbove_positive suffix bound
    intro g hg
    exact hsegment.2.1 g (List.mem_of_mem_drop hg)

/-- Membership in the deterministic selected-block list exposes all four
semantic properties used by reconstruction. -/
theorem selectedBlocks_mem_spec
    (segment : OddDenominatorSegment) (B : ℝ) (ell Z forward : ℕ)
    (block : LowGapBlock)
    (hblock : block ∈ selectedBlocks segment B ell Z forward) :
    LowGapBlock.OccursIn segment block ∧
      GapWord.IsGreedyBlock (Nat.ceil (B * ell)) block.gaps ∧
      Z * block.gaps.length ≤ 4 * block.span ∧
      forward ≤ GapWord.span
        (segment.gaps.drop (block.offset + block.gaps.length)) := by
  rw [selectedBlocks_eq_pointwiseSelectedBlocks] at hblock
  change block ∈
    ((blocksWithOffsetsFrom 0
      (GapWord.greedyDecompose segment.gaps
        (Nat.ceil (B * ell))).completed).filter fun block =>
          Z * block.gaps.length ≤ 4 * block.span ∧
          block.offset + block.gaps.length ≤ segment.gaps.length ∧
          forward ≤ GapWord.span
            (segment.gaps.drop (block.offset + block.gaps.length))) at hblock
  have hbound : 0 < Nat.ceil (B * ell) := by
    by_contra hzero
    have hboundZero : Nat.ceil (B * ell) = 0 := Nat.eq_zero_of_not_pos hzero
    rw [hboundZero] at hblock
    rw [greedyDecompose_zero] at hblock
    simp [blocksWithOffsetsFrom] at hblock
  have hfilter := List.mem_filter.mp hblock
  have hpred :
      Z * block.gaps.length ≤ 4 * block.span ∧
        block.offset + block.gaps.length ≤ segment.gaps.length ∧
        forward ≤ GapWord.span
          (segment.gaps.drop (block.offset + block.gaps.length)) :=
    of_decide_eq_true hfilter.2
  have hvalid := GapWord.greedyDecompose_valid segment.gaps
    (Nat.ceil (B * ell)) hbound
  have hwordMem : block.gaps ∈
      (GapWord.greedyDecompose segment.gaps (Nat.ceil (B * ell))).completed := by
    rcases blocksWithOffsetsFrom_mem_split 0
        (GapWord.greedyDecompose segment.gaps (Nat.ceil (B * ell))).completed
        block hfilter.1 with ⟨before, after, hwords, _⟩
    rw [hwords]
    simp
  refine ⟨?_, hvalid.2.1 block.gaps hwordMem, hpred.1, hpred.2.2⟩
  · exact blocksWithOffsetsFrom_occurs segment
      (GapWord.greedyDecompose segment.gaps (Nat.ceil (B * ell))).completed
      (GapWord.greedyDecompose segment.gaps (Nat.ceil (B * ell))).remainder
      hvalid.1 block hfilter.1

/-- A completed greedy block has the paper's real upper span bound, without
losing a ceiling unit. -/
theorem greedyBlock_span_le_real
    (B : ℝ) (ell : ℕ) (block : GapWord)
    (hgreedy : GapWord.IsGreedyBlock (Nat.ceil (B * ell)) block)
    (hgap : ∀ g ∈ block, g ≤ ell) :
    (block.span : ℝ) ≤ (B + 1) * ell := by
  have hne : block ≠ [] := hgreedy.1
  have hlength : 0 < block.length := List.length_pos_iff.mpr hne
  have hprefixNat : block.dropLast.sum < Nat.ceil (B * ell) := by
    simpa [GapWord.prefixSpan, List.dropLast_eq_take] using
      hgreedy.2.2 (block.length - 1) (by omega)
  have hprefixReal : (block.dropLast.sum : ℝ) < B * ell :=
    (Nat.lt_ceil.mp hprefixNat)
  have hlastNat : block.getLast hne ≤ ell :=
    hgap (block.getLast hne) (List.getLast_mem hne)
  have hlastReal : (block.getLast hne : ℝ) ≤ ell := by exact_mod_cast hlastNat
  have hsplitNat := congrArg List.sum (List.dropLast_append_getLast hne)
  simp only [List.sum_append, List.sum_singleton] at hsplitNat
  have hsplitReal : (block.span : ℝ) =
      block.dropLast.sum + block.getLast hne := by
    exact_mod_cast hsplitNat.symm
  rw [hsplitReal]
  nlinarith

/-- The concrete block encoding of a selected low-gap greedy block lies in the
candidate set for its two dyadic bands. -/
theorem encodeBlock_mem_encodingCandidates
    (B : ℝ) (D Z ell : ℕ) (block : LowGapBlock)
    (hDpow : ∃ d : ℕ, D = 2 ^ d) (hZpow : ∃ z : ℕ, Z = 2 ^ z)
    (hell : ell = Nat.ceil (Real.logb 2 (4 * D)))
    (hgreedy : GapWord.IsGreedyBlock (Nat.ceil (B * ell)) block.gaps)
    (hgap : ∀ g ∈ block.gaps, g ≤ ell)
    (hlow : Z * block.gaps.length ≤ 4 * block.span)
    (hpositive : block.gaps.Positive) :
    encodeBlock D Z block ∈ encodingCandidates D Z B := by
  have hZpos : 0 < Z := by
    rcases hZpow with ⟨z, rfl⟩
    positivity
  have hlower : B * ell ≤ (block.span : ℝ) := by
    calc
      B * ell ≤ Nat.ceil (B * ell) := Nat.le_ceil _
      _ ≤ block.span := by exact_mod_cast hgreedy.2.1
  have hupper : (block.span : ℝ) ≤ (B + 1) * ell :=
    greedyBlock_span_le_real B ell block.gaps hgreedy hgap
  have hlowReal : (block.gaps.length : ℝ) ≤ 4 * block.span / Z := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < Z)]
    have hcast : (Z : ℝ) * block.gaps.length ≤ 4 * block.span := by
      exact_mod_cast hlow
    nlinarith
  refine ⟨?_, rfl, rfl, ?_, ?_, hlowReal⟩
  · exact ⟨hDpow, hZpow, rfl, rfl, hpositive⟩
  · simpa [encodeBlock, LowGapBlock.span, hell] using hlower
  · simpa [encodeBlock, LowGapBlock.span, hell] using hupper

/-- A gap belonging to an occurring block belongs to its ambient segment. -/
theorem LowGapBlock.mem_segment
    (segment : OddDenominatorSegment) (block : LowGapBlock)
    (hoccurs : block.OccursIn segment) {g : ℕ} (hg : g ∈ block.gaps) :
    g ∈ segment.gaps := by
  have htake : g ∈ (segment.gaps.drop block.offset).take block.gaps.length := by
    rw [hoccurs.2]
    exact hg
  exact List.mem_of_mem_drop (List.mem_of_mem_take htake)

/-- The start of a nonempty selected block has a strict order-window offset. -/
theorem sourceWindowOffset_lt
    (Q : ℕ) (W : WindowSystem) (Z0 k : ℕ)
    (data : AnchorInteriorData) (hvalid : data.Valid Q W Z0 k)
    (block : LowGapBlock) (hoccurs : block.OccursIn data.segment)
    (hne : block.gaps ≠ []) :
    sourceWindowOffset W k data block < W.m := by
  have hindex := sourceEndpointIndex_le_succ Q W Z0 k data hvalid block
    hoccurs [] List.nil_prefix
  have hlen : 0 < block.gaps.length := List.length_pos_iff.mpr hne
  rw [WindowSystem.m]
  unfold sourceWindowOffset
  have hsk := hvalid.1
  simp only [List.length_nil, Nat.add_zero] at hindex
  omega

/-- The stable primitive-step bound transfers unchanged to the canonical line
at the start of every selected block. -/
theorem sourceRawLine_step
    (Q : ℕ) (W : WindowSystem) (data : AnchorInteriorData) (Cstep : ℝ)
    (hsegment : data.segment.Valid Q) (block : LowGapBlock)
    (hstep : (data.segment.startLine.H : ℝ) ≤
      Cstep * W.X / frequencyCutoff W) :
    ((sourceRawLine Q data block).canonicalGeometricLine.H : ℝ) ≤
      Cstep * W.X / frequencyCutoff W := by
  have hprimitive := data.segment.prefixLine_primitive Q hsegment block.offset
  have hprimitiveRaw : Int.gcd (sourceRawLine Q data block).H
      (sourceRawLine Q data block).K = 1 := by
    simpa [sourceRawLine] using hprimitive
  have hcanonical :
      ((sourceRawLine Q data block).canonicalGeometricLine.H : ℤ) =
        (sourceRawLine Q data block).H := by
    rw [(sourceRawLine Q data block).canonicalGeometricLine_H_cast]
    simp [AffineLine.primitiveHorizontalInt, AffineLine.directionGCD, hprimitiveRaw]
  have hcanonicalReal :
      ((sourceRawLine Q data block).canonicalGeometricLine.H : ℝ) =
        ((sourceRawLine Q data block).H : ℝ) := by exact_mod_cast hcanonical
  rw [hcanonicalReal]
  simpa [sourceRawLine, AffineLine.transformWord_H] using hstep

/-- A genuine selected block realizes its encoding on both the raw affine line
and its canonical geometric line. -/
theorem sourceBlock_realizes
    (Q D Z : ℕ) (hQ : 0 < Q) (data : AnchorInteriorData)
    (hsegment : data.segment.Valid Q) (block : LowGapBlock)
    (hoccurs : block.OccursIn data.segment)
    (hDle : D ≤ data.segment.q) (hqD : data.segment.q < 2 * D) :
    LineRealizesEncoding Q (sourceRawLine Q data block) (encodeBlock D Z block) ∧
      GeometricLineRealizesEncoding Q
        (sourceRawLine Q data block).canonicalGeometricLine
        (encodeBlock D Z block) ∧
      SharedGapTrajectory Q (sourceRawLine Q data block) block.gaps
        (sourceBlockEndLine Q data block) := by
  have hoffset : block.offset ≤ data.segment.gaps.length :=
    le_trans (Nat.le_add_right block.offset block.gaps.length) hoccurs.1
  have hrawData := data.segment.prefixSlope_data Q hsegment block.offset hoffset
  have hrawDen : ((sourceRawLine Q data block).slope Q).den = data.segment.q := by
    simpa [sourceRawLine] using hrawData.2.1
  have htrajectory : SharedGapTrajectory Q (sourceRawLine Q data block) block.gaps
      (sourceBlockEndLine Q data block) := by
    rw [sharedGapTrajectory_iff_transformWord]
    rfl
  have htakeEnd : data.segment.gaps.take (block.offset + block.gaps.length) =
      data.segment.gaps.take block.offset ++ block.gaps := by
    calc
      data.segment.gaps.take (block.offset + block.gaps.length) =
          data.segment.gaps.take block.offset ++
            (data.segment.gaps.drop block.offset).take block.gaps.length :=
        List.take_add
      _ = data.segment.gaps.take block.offset ++ block.gaps := by rw [hoccurs.2]
  have hendData := data.segment.prefixSlope_data Q hsegment
    (block.offset + block.gaps.length) hoccurs.1
  have hendSlope :
      (sourceBlockEndLine Q data block).slope Q =
        (data.segment.startLine.transformWord Q
          (data.segment.gaps.take (block.offset + block.gaps.length))).slope Q := by
    unfold sourceBlockEndLine sourceRawLine
    rw [htakeEnd, AffineLine.transformWord_append]
  have hendInteriorRat : (sourceBlockEndLine Q data block).slope Q ∈
      Set.Ioo (0 : ℚ) 1 := by
    rw [hendSlope]
    exact hendData.1
  have hendInteriorReal : ((sourceBlockEndLine Q data block).slope Q : ℝ) ∈
      Set.Ioo (0 : ℝ) 1 := by
    exact ⟨by exact_mod_cast hendInteriorRat.1, by exact_mod_cast hendInteriorRat.2⟩
  have hcanonicalSlope :=
    (sourceRawLine Q data block).canonicalGeometricLine_slope Q hQ
  have hslopeAfter :
      slopeAfter block.gaps
          ((sourceRawLine Q data block).canonicalGeometricLine.slope Q : ℝ) =
        ((sourceBlockEndLine Q data block).slope Q : ℝ) := by
    rw [hcanonicalSlope]
    exact (AffineLine.transformWord_slope_real Q hQ
      (sourceRawLine Q data block) block.gaps).symm
  refine ⟨?_, ?_, htrajectory⟩
  · exact ⟨by simpa [encodeBlock, hrawDen] using hDle,
      by simpa [encodeBlock, hrawDen] using hqD,
      ⟨sourceBlockEndLine Q data block, htrajectory⟩⟩
  · refine ⟨?_, ?_, ?_⟩
    · simpa [encodeBlock, hcanonicalSlope, hrawDen] using hDle
    · simpa [encodeBlock, hcanonicalSlope, hrawDen] using hqD
    · change slopeAfter block.gaps
        ((sourceRawLine Q data block).canonicalGeometricLine.slope Q : ℝ) ∈
          Set.Ioo (0 : ℝ) 1
      rw [hslopeAfter]
      exact hendInteriorReal

/-- Every genuine deterministic selected block, with the eventual logarithmic
cap and stable step bound, constructs the full spatial source required by the
interior fibre argument. -/
theorem selectedBlock_isSpatialEncodingSource
    (Q Cgap : ℕ) (hQ : 0 < Q) (W : WindowSystem) (Z0 k : ℕ)
    (selection : InteriorAnchorSelection) (data : AnchorInteriorData)
    (Cstep : ℝ) (block : LowGapBlock)
    (hden : W.rational.eta.den = Q)
    (hselected : selection k = some data)
    (hvalid : data.Valid Q W Z0 k)
    (hstep : (data.segment.startLine.H : ℝ) ≤
      Cstep * W.X / frequencyCutoff W)
    (hellCap : selectedLogLength selection k ≤ W.L + Cgap)
    (hL : 1 ≤ W.L)
    (hblock : block ∈ selectedBlocks data.segment W.structural.B
      (selectedLogLength selection k) (selectedMeanGapBand selection k)
      (reconstructionForwardLength W Cgap)) :
    IsSpatialEncodingSource Q Cgap W.structural.B Cstep W Z0 selection
      (encodeBlock (selectedDenominatorBand selection k)
        (selectedMeanGapBand selection k) block) (k, block) := by
  let D := selectedDenominatorBand selection k
  let Z := selectedMeanGapBand selection k
  let ell := selectedLogLength selection k
  have hsegment : data.segment.Valid Q := hvalid.2.2.2.2.1
  have hqpos : 0 < data.segment.q := lt_trans (by omega) hsegment.2.2.2.2.1
  have hD : D = dyadicFloorBand data.segment.q := by
    simp [D, selectedDenominatorBand, hselected]
  have hZ : Z = meanGapBand data.segment.span data.segment.gapCount := by
    simp [Z, selectedMeanGapBand, hselected]
  have hDle : D ≤ data.segment.q := by
    rw [hD]
    exact dyadicFloorBand_le hqpos
  have hqD : data.segment.q < 2 * D := by
    rw [hD]
    exact dyadicFloorBand_lt_two_mul _
  have hell : ell = Nat.ceil (Real.logb 2 (4 * D)) := by rfl
  have hgapEll : ∀ g ∈ data.segment.gaps, g ≤ ell := by
    rw [hell]
    exact data.segment.gap_le_logBand Q D hQ hsegment hqD
  have hspec := selectedBlocks_mem_spec data.segment W.structural.B ell Z
    (reconstructionForwardLength W Cgap) block (by simpa [ell, Z] using hblock)
  rcases hspec with ⟨hoccurs, hgreedy, hlow, hforward⟩
  have hblockPositive : block.gaps.Positive := by
    intro g hg
    exact hsegment.2.1 g (block.mem_segment data.segment hoccurs hg)
  have hblockGap : ∀ g ∈ block.gaps, g ≤ ell := by
    intro g hg
    exact hgapEll g (block.mem_segment data.segment hoccurs hg)
  have hDpow : ∃ d : ℕ, D = 2 ^ d := by
    rw [hD]
    exact dyadicFloorBand_isPow _
  have hZpow : ∃ z : ℕ, Z = 2 ^ z := by
    rw [hZ]
    unfold meanGapBand
    exact dyadicFloorBand_isPow _
  have hcandidate : encodeBlock D Z block ∈ encodingCandidates D Z W.structural.B :=
    encodeBlock_mem_encodingCandidates W.structural.B D Z ell block hDpow
      hZpow hell hgreedy hblockGap hlow hblockPositive
  have hoffset : sourceWindowOffset W k data block < W.m :=
    sourceWindowOffset_lt Q W Z0 k data hvalid block hoccurs hgreedy.1
  have hprimitive : Int.gcd (sourceRawLine Q data block).H
      (sourceRawLine Q data block).K = 1 := by
    simpa [sourceRawLine] using
      data.segment.prefixLine_primitive Q hsegment block.offset
  have hcanonicalStep := sourceRawLine_step Q W data Cstep hsegment block hstep
  obtain ⟨hlineRealizes, hgeometricRealizes, hblockTrajectory⟩ :=
    sourceBlock_realizes Q D Z hQ data hsegment block hoccurs hDle hqD
  have hgapCap : ∀ g ∈ data.segment.gaps, g ≤ W.L + Cgap := by
    intro g hg
    exact (hgapEll g hg).trans (by simpa [ell] using hellCap)
  obtain ⟨hforwardLower, hforwardUpper, hforwardPositive⟩ :=
    sourceForwardWord_spec Q Cgap W data hsegment block hforward hgapCap hL
  have hforwardInterior :=
    sourceForwardWord_interior Q Cgap W data hsegment block hoccurs
  obtain ⟨t, hparameter⟩ := exists_originalSourceParameter Q W Z0 k hden data
    hvalid block hoccurs hoffset
  refine ⟨data, t, ?_, hparameter⟩
  refine ⟨hselected, hvalid, hvalid.2.2.1, ?_, hoccurs, hoffset, ?_, ?_, ?_,
    hprimitive, rfl, hcanonicalStep, ?_, ?_, hblockTrajectory,
    hforwardLower, hforwardUpper, hforwardPositive, hforwardInterior⟩
  · simpa [ell, Z, encodingLogLength, encodeBlock] using hblock
  · simpa [D, Z, encodeBlock] using hcandidate
  · simp [encodeBlock]
  · rfl
  · simpa [D, Z] using hlineRealizes
  · simpa [D, Z] using hgeometricRealizes

/-- Certified real mass of the long-interior parent family. -/
def interiorPairsMass (W : WindowSystem) (Z0 : ℕ) : ℝ :=
  finiteWindowMass W (interiorPairs W Z0)
    (interiorPairs_subset_pairSet W Z0)

/-- The tail of a nonnegative real geometric series, written as an indicator
on all natural-number exponents. -/
theorem tsum_geometric_indicator_ge
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    (∑' i : ℕ, if n ≤ i then r ^ i else 0) = r ^ n * (1 - r)⁻¹ := by
  have hsummable : Summable (fun i : ℕ ↦ if n ≤ i then r ^ i else 0) := by
    refine ((summable_geometric_of_lt_one hr0 hr1).indicator
      {i : ℕ | n ≤ i}).congr ?_
    intro i
    simp [Set.indicator_apply]
  have hprefix :
      (∑ i ∈ Finset.range n, if n ≤ i then r ^ i else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp only [Finset.mem_range] at hi
    simp [Nat.not_le.mpr hi]
  rw [← hsummable.sum_add_tsum_nat_add n, hprefix, zero_add]
  simp only [Nat.le_add_left, if_true, pow_add]
  rw [tsum_mul_right, tsum_geometric_of_lt_one hr0 hr1, mul_comm]

/-- Any finite collection of distinct exponents lying above `n` is bounded by
the full geometric tail beginning at `n`. -/
theorem finset_geometric_tail_le
    (s : Finset ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ)
    (hmin : ∀ i ∈ s, n ≤ i) :
    (∑ i ∈ s, r ^ i) ≤ r ^ n * (1 - r)⁻¹ := by
  have hsummable : Summable (fun i : ℕ ↦ if n ≤ i then r ^ i else 0) := by
    refine ((summable_geometric_of_lt_one hr0 hr1).indicator
      {i : ℕ | n ≤ i}).congr ?_
    intro i
    simp [Set.indicator_apply]
  calc
    (∑ i ∈ s, r ^ i) = ∑ i ∈ s, (if n ≤ i then r ^ i else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [hmin i hi]
    _ ≤ ∑' i : ℕ, (if n ≤ i then r ^ i else 0) := by
      exact hsummable.sum_le_tsum s (fun i _ ↦ by positivity)
    _ = r ^ n * (1 - r)⁻¹ := tsum_geometric_indicator_ge hr0 hr1 n

/-- Reindexing version of `finset_geometric_tail_le`.  It is useful when the
objects being summed are bands, while `exponent` extracts their dyadic
exponents. -/
theorem finset_geometric_tail_le_of_inj
    { α : Type* } [DecidableEq α] (s : Finset α) (exponent : α → ℕ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ)
    (hinj : Set.InjOn exponent s)
    (hmin : ∀ a ∈ s, n ≤ exponent a) :
    (∑ a ∈ s, r ^ exponent a) ≤ r ^ n * (1 - r)⁻¹ := by
  calc
    (∑ a ∈ s, r ^ exponent a) =
        ∑ i ∈ s.image exponent, r ^ i :=
      (Finset.sum_image hinj).symm
    _ ≤ r ^ n * (1 - r)⁻¹ := by
      apply finset_geometric_tail_le (s.image exponent) hr0 hr1 n
      intro i hi
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
      exact hmin a ha

/-- Weighted outer-band form.  If the contribution of band `i` is bounded by
`C * r^i`, summing any finite collection above `n` costs one geometric-tail
factor. -/
theorem finset_weighted_geometric_tail_le
    (s : Finset ℕ) (weight : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ)
    (hmin : ∀ i ∈ s, n ≤ i)
    (hweight : ∀ i ∈ s, weight i ≤ C * r ^ i) :
    (∑ i ∈ s, weight i) ≤ C * (r ^ n * (1 - r)⁻¹) := by
  calc
    (∑ i ∈ s, weight i) ≤ ∑ i ∈ s, C * r ^ i :=
      Finset.sum_le_sum hweight
    _ = C * ∑ i ∈ s, r ^ i := by
      rw [Finset.mul_sum]
    _ ≤ C * (r ^ n * (1 - r)⁻¹) :=
      mul_le_mul_of_nonneg_left
        (finset_geometric_tail_le s hr0 hr1 n hmin) hC

/-- Ratio associated with the weight `D⁻¹ᐚ²` when `D = 2^d`. -/
def strictMassRatio : ℝ := (√2)⁻¹

theorem strictMassRatio_nonneg : 0 ≤ strictMassRatio := by
  unfold strictMassRatio
  positivity

theorem strictMassRatio_pos : 0 < strictMassRatio := by
  unfold strictMassRatio
  positivity

theorem strictMassRatio_lt_one : strictMassRatio < 1 := by
  unfold strictMassRatio
  exact (inv_lt_one₀ (Real.sqrt_pos.2 (by norm_num))).2 Real.one_lt_sqrt_two

theorem strictMassRatio_le_one : strictMassRatio ≤ 1 :=
  strictMassRatio_lt_one.le

theorem strictMassRatio_sq : strictMassRatio ^ 2 = (1 : ℝ) / 2 := by
  unfold strictMassRatio
  rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- Ratio for the second (`Z`) geometric summation.  Its square is the
denominator ratio, so it absorbs the floor in `Z / 2`. -/
def strictMassOuterRatio : ℝ := √strictMassRatio

theorem strictMassOuterRatio_nonneg : 0 ≤ strictMassOuterRatio := by
  unfold strictMassOuterRatio
  exact Real.sqrt_nonneg _

theorem strictMassOuterRatio_pos : 0 < strictMassOuterRatio := by
  unfold strictMassOuterRatio
  exact Real.sqrt_pos.2 strictMassRatio_pos

theorem strictMassOuterRatio_lt_one : strictMassOuterRatio < 1 := by
  unfold strictMassOuterRatio
  calc
    √strictMassRatio < √(1 : ℝ) :=
      Real.sqrt_lt_sqrt strictMassRatio_nonneg strictMassRatio_lt_one
    _ = 1 := Real.sqrt_one

theorem strictMassOuterRatio_le_one : strictMassOuterRatio ≤ 1 :=
  strictMassOuterRatio_lt_one.le

theorem strictMassOuterRatio_sq :
    strictMassOuterRatio ^ 2 = strictMassRatio := by
  unfold strictMassOuterRatio
  exact Real.sq_sqrt strictMassRatio_nonneg

theorem strictMassOuterRatio_fourth :
    strictMassOuterRatio ^ 4 = (1 : ℝ) / 2 := by
  calc
    strictMassOuterRatio ^ 4 = (strictMassOuterRatio ^ 2) ^ 2 := by
      ring
    _ = strictMassRatio ^ 2 := by rw [strictMassOuterRatio_sq]
    _ = (1 : ℝ) / 2 := strictMassRatio_sq

/-- The floor in `Z / 2` costs only one fixed outer-ratio factor. -/
theorem strictMassRatio_pow_div_two_le_outer (Z : ℕ) :
    strictMassRatio ^ (Z / 2) ≤
      strictMassOuterRatio⁻¹ * strictMassOuterRatio ^ Z := by
  apply (le_inv_mul_iff₀ strictMassOuterRatio_pos).2
  calc
    strictMassOuterRatio * strictMassRatio ^ (Z / 2) =
        strictMassOuterRatio ^ (2 * (Z / 2) + 1) := by
      rw [pow_add, pow_mul, strictMassOuterRatio_sq, pow_one]
      ring
    _ ≤ strictMassOuterRatio ^ Z :=
      pow_le_pow_of_le_one strictMassOuterRatio_nonneg
        strictMassOuterRatio_le_one (by omega)

/-- Four outer-ratio powers equal one factor `1/2`; hence the lower cutoff
`Z₀/32` produces the advertised exponent `Z₀/128`. -/
theorem strictMassOuterRatio_pow_div32_le (Z₀ : ℕ) :
    strictMassOuterRatio ^ (Z₀ / 32) ≤
      ((1 : ℝ) / 2) ^ (Z₀ / 128) := by
  calc
    strictMassOuterRatio ^ (Z₀ / 32) ≤
        strictMassOuterRatio ^ (4 * (Z₀ / 128)) :=
      pow_le_pow_of_le_one strictMassOuterRatio_nonneg
        strictMassOuterRatio_le_one (by omega)
    _ = ((1 : ℝ) / 2) ^ (Z₀ / 128) := by
      rw [pow_mul, strictMassOuterRatio_fourth]

theorem sqrt_two_pow (d : ℕ) :
    √((2 : ℝ) ^ d) = (√2) ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]

/-- Exact conversion from a dyadic denominator to a geometric weight. -/
theorem inv_sqrt_nat_two_pow (d : ℕ) :
    1 / √(((2 ^ d : ℕ) : ℝ)) = strictMassRatio ^ d := by
  rw [Nat.cast_pow, Nat.cast_ofNat, sqrt_two_pow]
  simp [strictMassRatio, div_eq_mul_inv]

/-- Single-layer denominator-band estimate.  It is the directly composable
form for one fixed mean-gap band `Z`: use `n = Z / 2`. -/
theorem dyadicExponentBandTail
    (exponents : Finset ℕ) (n : ℕ)
    (hmin : ∀ d ∈ exponents, n ≤ d) :
    (∑ d ∈ exponents, 1 / √(((2 ^ d : ℕ) : ℝ))) ≤
      strictMassRatio ^ n * (1 - strictMassRatio)⁻¹ := by
  simp_rw [inv_sqrt_nat_two_pow]
  exact finset_geometric_tail_le exponents strictMassRatio_nonneg
    strictMassRatio_lt_one n hmin

/-- The constant left after summing a single denominator band. -/
def strictMassTailConstant : ℝ := (1 - strictMassRatio)⁻¹

theorem strictMassTailConstant_pos : 0 < strictMassTailConstant := by
  unfold strictMassTailConstant
  exact inv_pos.mpr (sub_pos.mpr strictMassRatio_lt_one)

/-- Explicit cutoff tail used by the final strict-mass estimate. -/
def strictMassTail (Z₀ : ℕ) : ℝ :=
  strictMassTailConstant * ((1 : ℝ) / 2) ^ (Z₀ / 128)

theorem strictMassTail_nonneg (Z₀ : ℕ) : 0 ≤ strictMassTail Z₀ := by
  unfold strictMassTail
  exact mul_nonneg strictMassTailConstant_pos.le (pow_nonneg (by norm_num) _)

theorem strictMassTail_tendsto_zero :
    Tendsto strictMassTail atTop (𝓝 0) := by
  change Tendsto
    (fun Z₀ : ℕ ↦ strictMassTailConstant * ((1 : ℝ) / 2) ^ (Z₀ / 128))
    atTop (𝓝 0)
  have hdiv : Tendsto (fun Z₀ : ℕ ↦ Z₀ / 128) atTop atTop :=
    Nat.tendsto_div_const_atTop (by norm_num)
  have hpow : Tendsto (fun n : ℕ ↦ ((1 : ℝ) / 2) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hconst :
      Tendsto (fun _ : ℕ ↦ strictMassTailConstant) atTop
        (𝓝 strictMassTailConstant) :=
    tendsto_const_nhds
  simpa only [Function.comp_apply, mul_zero] using
    hconst.mul (hpow.comp hdiv)

/-- Dividing first by `64` leaves at least twice the exponent obtained by
dividing by `128`; this is the bookkeeping behind the paper's `Z₀/128`
decay. -/
theorem twice_div_128_le_div_64 (Z₀ : ℕ) :
    2 * (Z₀ / 128) ≤ Z₀ / 64 := by
  omega

theorem strictMassRatio_pow_div64_le (Z₀ : ℕ) :
    strictMassRatio ^ (Z₀ / 64) ≤
      ((1 : ℝ) / 2) ^ (Z₀ / 128) := by
  calc
    strictMassRatio ^ (Z₀ / 64) ≤
        strictMassRatio ^ (2 * (Z₀ / 128)) :=
      pow_le_pow_of_le_one strictMassRatio_nonneg strictMassRatio_le_one
        (twice_div_128_le_div_64 Z₀)
    _ = ((1 : ℝ) / 2) ^ (Z₀ / 128) := by
      rw [pow_mul, strictMassRatio_sq]

/-- A one-layer dyadic family whose exponent is eventually at least
`Z₀/64` already contributes at most the explicit `Z₀/128` tail. -/
theorem dyadicExponentBandTail_le_strictMassTail
    (exponents : Finset ℕ) (Z₀ : ℕ)
    (hmin : ∀ d ∈ exponents, Z₀ / 64 ≤ d) :
    (∑ d ∈ exponents, 1 / √(((2 ^ d : ℕ) : ℝ))) ≤
      strictMassTail Z₀ := by
  calc
    (∑ d ∈ exponents, 1 / √(((2 ^ d : ℕ) : ℝ))) ≤
        strictMassRatio ^ (Z₀ / 64) * strictMassTailConstant := by
      simpa only [strictMassTailConstant] using
        dyadicExponentBandTail exponents (Z₀ / 64) hmin
    _ ≤ ((1 : ℝ) / 2) ^ (Z₀ / 128) * strictMassTailConstant := by
      exact mul_le_mul_of_nonneg_right (strictMassRatio_pow_div64_le Z₀)
        strictMassTailConstant_pos.le
    _ = strictMassTail Z₀ := by
      simp only [strictMassTail]
      ring

/-- Two-layer tail in the representation used by the interior band sum.

`keys` stores `(D,Z)`.  The witness `exponent` records `D = 2^d`; within a
fixed `Z`-fiber this makes `exponent` injective automatically.  The only
analytic lower bound needed here is `Z/2 ≤ d`.  In the application it follows,
for all sufficiently large `Z`, from the stronger manuscript estimate
`cBand * 2^Z ≤ D`.
-/
theorem finite_dyadic_band_pair_tail
    (keys : Finset (ℕ × ℕ)) (exponent : ℕ × ℕ → ℕ) (Z₀ : ℕ)
    (hdyadic : ∀ key ∈ keys, key.1 = 2 ^ exponent key)
    (hcutoff : ∀ key ∈ keys, Z₀ / 32 ≤ key.2)
    (hlower : ∀ key ∈ keys, key.2 / 2 ≤ exponent key) :
    (∑ key ∈ keys, 1 / √((key.1 : ℝ))) ≤
      strictMassOuterRatio⁻¹ * (1 - strictMassOuterRatio)⁻¹ *
        strictMassTail Z₀ := by
  let zBands : Finset ℕ := keys.image Prod.snd
  let fiberWeight : ℕ → ℝ := fun Z ↦
    ∑ key ∈ keys with key.2 = Z, 1 / √((key.1 : ℝ))
  have hratioInv : 0 ≤ strictMassOuterRatio⁻¹ :=
    inv_nonneg.mpr strictMassOuterRatio_nonneg
  have houterTailInv : 0 ≤ (1 - strictMassOuterRatio)⁻¹ :=
    inv_nonneg.mpr (sub_nonneg.mpr strictMassOuterRatio_le_one)
  have hsingleConstant :
      0 ≤ strictMassOuterRatio⁻¹ * strictMassTailConstant :=
    mul_nonneg hratioInv strictMassTailConstant_pos.le
  have hfiber (Z : ℕ) (hZ : Z ∈ zBands) :
      fiberWeight Z ≤
        (strictMassOuterRatio⁻¹ * strictMassTailConstant) *
          strictMassOuterRatio ^ Z := by
    let fiber : Finset (ℕ × ℕ) := keys.filter fun key ↦ key.2 = Z
    have hinj : Set.InjOn exponent fiber := by
      intro a ha b hb hab
      have ha' := Finset.mem_filter.mp ha
      have hb' := Finset.mem_filter.mp hb
      apply Prod.ext
      · rw [hdyadic a ha'.1, hdyadic b hb'.1, hab]
      · exact ha'.2.trans hb'.2.symm
    have hmin : ∀ key ∈ fiber, Z / 2 ≤ exponent key := by
      intro key hkey
      have hkey' := Finset.mem_filter.mp hkey
      simpa only [hkey'.2] using hlower key hkey'.1
    have hrewrite :
        fiberWeight Z = ∑ key ∈ fiber, strictMassRatio ^ exponent key := by
      apply Finset.sum_congr rfl
      intro key hkey
      have hkey' := Finset.mem_filter.mp hkey
      rw [hdyadic key hkey'.1, inv_sqrt_nat_two_pow]
    rw [hrewrite]
    calc
      (∑ key ∈ fiber, strictMassRatio ^ exponent key) ≤
          strictMassRatio ^ (Z / 2) * strictMassTailConstant := by
        simpa only [strictMassTailConstant] using
          finset_geometric_tail_le_of_inj fiber exponent
            strictMassRatio_nonneg strictMassRatio_lt_one (Z / 2) hinj hmin
      _ ≤
          (strictMassOuterRatio⁻¹ * strictMassOuterRatio ^ Z) *
            strictMassTailConstant :=
        mul_le_mul_of_nonneg_right
          (strictMassRatio_pow_div_two_le_outer Z)
          strictMassTailConstant_pos.le
      _ = (strictMassOuterRatio⁻¹ * strictMassTailConstant) *
          strictMassOuterRatio ^ Z := by ring
  have hzMin : ∀ Z ∈ zBands, Z₀ / 32 ≤ Z := by
    intro Z hZ
    obtain ⟨key, hkey, rfl⟩ := Finset.mem_image.mp hZ
    exact hcutoff key hkey
  calc
    (∑ key ∈ keys, 1 / √((key.1 : ℝ))) =
        ∑ Z ∈ zBands, fiberWeight Z := by
      symm
      exact Finset.sum_fiberwise_of_maps_to
        (s := keys) (t := zBands) (g := Prod.snd) (M := ℝ)
        (fun key hkey ↦ Finset.mem_image_of_mem Prod.snd hkey)
        (fun key ↦ 1 / √((key.1 : ℝ)))
    _ ≤ (strictMassOuterRatio⁻¹ * strictMassTailConstant) *
        (strictMassOuterRatio ^ (Z₀ / 32) *
          (1 - strictMassOuterRatio)⁻¹) :=
      finset_weighted_geometric_tail_le zBands fiberWeight
        (strictMassOuterRatio⁻¹ * strictMassTailConstant) hsingleConstant
        strictMassOuterRatio_nonneg strictMassOuterRatio_lt_one (Z₀ / 32)
        hzMin hfiber
    _ ≤ (strictMassOuterRatio⁻¹ * strictMassTailConstant) *
        (((1 : ℝ) / 2) ^ (Z₀ / 128) *
          (1 - strictMassOuterRatio)⁻¹) := by
      apply mul_le_mul_of_nonneg_left _ hsingleConstant
      exact mul_le_mul_of_nonneg_right
        (strictMassOuterRatio_pow_div32_le Z₀) houterTailInv
    _ = strictMassOuterRatio⁻¹ * (1 - strictMassOuterRatio)⁻¹ *
        strictMassTail Z₀ := by
      rw [strictMassTail]
      ac_rfl

/-- For every fixed positive band constant, the manuscript lower bound
`cBand * 2^Z ≤ 2^d` eventually implies the deliberately weaker exponent
bound `Z/2 ≤ d` used by `finite_dyadic_band_pair_tail`. -/
theorem exists_dyadic_exponent_cutoff (cBand : ℝ) (hcBand : 0 < cBand) :
    ∃ Zc : ℕ, ∀ {Z d : ℕ}, Zc ≤ Z →
      cBand * (2 : ℝ) ^ Z ≤ (2 : ℝ) ^ d → Z / 2 ≤ d := by
  obtain ⟨K, hK⟩ :=
    pow_unbounded_of_one_lt cBand⁻¹ (by norm_num : (1 : ℝ) < 2)
  refine ⟨2 * K, ?_⟩
  intro Z d hZ hband
  have hpow : (2 : ℝ) ^ Z ≤ (2 : ℝ) ^ (K + d) := by
    calc
      (2 : ℝ) ^ Z ≤ cBand⁻¹ * (2 : ℝ) ^ d :=
        (le_inv_mul_iff₀ hcBand).2 hband
      _ ≤ (2 : ℝ) ^ K * (2 : ℝ) ^ d :=
        mul_le_mul_of_nonneg_right hK.le (by positivity)
      _ = (2 : ℝ) ^ (K + d) := by rw [pow_add]
  have hZd : Z ≤ K + d :=
    (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hpow
  omega

/-- Direct arbitrary-`cBand` wrapper for finite `(D,Z)` band keys.  The
returned `Zc` depends only on `cBand`, not on the key set, `Z₀`, or the
support. -/
theorem exists_finite_dyadic_band_pair_tail_of_lower
    (cBand : ℝ) (hcBand : 0 < cBand) :
    ∃ Zc : ℕ, ∀ (keys : Finset (ℕ × ℕ))
      (exponent : ℕ × ℕ → ℕ) (Z₀ : ℕ),
      (∀ key ∈ keys, key.1 = 2 ^ exponent key) →
      (∀ key ∈ keys, Z₀ / 32 ≤ key.2) →
      (∀ key ∈ keys, Zc ≤ key.2) →
      (∀ key ∈ keys,
        cBand * (2 : ℝ) ^ key.2 ≤ (key.1 : ℝ)) →
      (∑ key ∈ keys, 1 / √((key.1 : ℝ))) ≤
        strictMassOuterRatio⁻¹ * (1 - strictMassOuterRatio)⁻¹ *
          strictMassTail Z₀ := by
  obtain ⟨Zc, hZc⟩ := exists_dyadic_exponent_cutoff cBand hcBand
  refine ⟨Zc, ?_⟩
  intro keys exponent Z₀ hdyadic hcutoff hlarge hband
  apply finite_dyadic_band_pair_tail keys exponent Z₀ hdyadic hcutoff
  intro key hkey
  apply hZc (hlarge key hkey)
  have h := hband key hkey
  rw [hdyadic key hkey, Nat.cast_pow, Nat.cast_ofNat] at h
  exact h


def strictCoverLinearConstant (B : ℝ) : ℕ :=
  64 * (5 + 2 * Nat.ceil (B + 1))

def strictCoverCutoff (B kappa : ℝ) : ℕ :=
  Nat.ceil (strictCoverLinearConstant B / kappa) + 1

theorem selectedCoverReserve_le_segment
    (W : WindowSystem) (gap : GapParams W.rational.eta.den)
    (selection : InteriorAnchorSelection) (e : WindowThreshold)
    (data : AnchorInteriorData) (Z0 : ℕ) (kappa : ℝ)
    (hkappa : 0 < kappa)
    (hlevel : max 1 gap.Cgap ≤ W.L)
    (hcutoff : strictCoverCutoff W.structural.B kappa ≤ Z0)
    (hm : kappa * W.L < W.m)
    (hlargePair : (W.m : ℝ) * Z0 < W.excess e)
    (hspan : W.excess e / 16 ≤ data.segment.span)
    (hell : selectedLogLength selection e.1 ≤ W.L + gap.Cgap) :
    4 * (selectedForwardLength W gap e.1 +
      Nat.ceil ((W.structural.B + 1) * selectedLogLength selection e.1)) ≤
        data.segment.span := by
  let C := Nat.ceil (W.structural.B + 1)
  let A := selectedForwardLength W gap e.1 +
    Nat.ceil ((W.structural.B + 1) * selectedLogLength selection e.1)
  let K := strictCoverLinearConstant W.structural.B
  have hLone : 1 ≤ W.L := (le_max_left _ _).trans hlevel
  have hgapL : gap.Cgap ≤ W.L := (le_max_right _ _).trans hlevel
  have hCbound : W.structural.B + 1 ≤ (C : ℝ) := by
    exact Nat.le_ceil _
  have hcap : Nat.ceil ((W.structural.B + 1) *
      selectedLogLength selection e.1) ≤ C * selectedLogLength selection e.1 := by
    rw [Nat.ceil_le]
    have hellNonneg : (0 : ℝ) ≤ selectedLogLength selection e.1 := by positivity
    have hmul := mul_le_mul_of_nonneg_right hCbound hellNonneg
    exact_mod_cast hmul
  have hforward : selectedForwardLength W gap e.1 ≤ 5 * W.L := by
    simp only [selectedForwardLength, reconstructionForwardLength]
    omega
  have hellTwo : selectedLogLength selection e.1 ≤ 2 * W.L := by omega
  have hALinear : A ≤ (5 + 2 * C) * W.L := by
    dsimp [A]
    calc
      selectedForwardLength W gap e.1 +
          Nat.ceil ((W.structural.B + 1) * selectedLogLength selection e.1) ≤
          5 * W.L + C * selectedLogLength selection e.1 :=
        Nat.add_le_add hforward hcap
      _ ≤ 5 * W.L + C * (2 * W.L) :=
        Nat.add_le_add_left (Nat.mul_le_mul_left C hellTwo) _
      _ = (5 + 2 * C) * W.L := by ring
  have hKLinear : 64 * A ≤ K * W.L := by
    calc
      64 * A ≤ 64 * ((5 + 2 * C) * W.L) :=
        Nat.mul_le_mul_left 64 hALinear
      _ = K * W.L := by
        simp [K, strictCoverLinearConstant, C]
        ring
  have hKappaCutoff : (K : ℝ) < kappa * strictCoverCutoff W.structural.B kappa := by
    have hcutoffEq : strictCoverCutoff W.structural.B kappa =
        Nat.ceil ((K : ℝ) / kappa) + 1 := by
      simp [strictCoverCutoff, K]
    have hquot : (K : ℝ) / kappa < strictCoverCutoff W.structural.B kappa := by
      rw [hcutoffEq]
      have hle : (K : ℝ) / kappa ≤
          Nat.ceil ((K : ℝ) / kappa) := Nat.le_ceil _
      have hsucc : ((Nat.ceil ((K : ℝ) / kappa) : ℕ) : ℝ) <
          ((Nat.ceil ((K : ℝ) / kappa) + 1 : ℕ) : ℝ) := by
        exact_mod_cast (Nat.lt_succ_self (Nat.ceil ((K : ℝ) / kappa)))
      exact hle.trans_lt hsucc
    simpa only [mul_comm] using (div_lt_iff₀ hkappa).1 hquot
  have hKZ : (K : ℝ) < kappa * Z0 := by
    have hcutoffReal : (strictCoverCutoff W.structural.B kappa : ℝ) ≤ Z0 := by
      exact_mod_cast hcutoff
    nlinarith [mul_le_mul_of_nonneg_left hcutoffReal hkappa.le]
  have hLpos : (0 : ℝ) < W.L := by exact_mod_cast hLone
  have hKL : (K : ℝ) * W.L < kappa * Z0 * W.L :=
    mul_lt_mul_of_pos_right hKZ hLpos
  have hmZ : kappa * Z0 * W.L < (W.m : ℝ) * Z0 := by
    have hZpos : (0 : ℝ) < Z0 := by
      have hcutoffPos : 0 < strictCoverCutoff W.structural.B kappa := by
        simp [strictCoverCutoff]
      exact_mod_cast lt_of_lt_of_le hcutoffPos hcutoff
    nlinarith [mul_lt_mul_of_pos_right hm hZpos]
  have h64A : (64 * A : ℕ) < W.m * Z0 := by
    have h64AReal : ((64 * A : ℕ) : ℝ) < ((W.m * Z0 : ℕ) : ℝ) := by
      calc
        ((64 * A : ℕ) : ℝ) ≤ ((K * W.L : ℕ) : ℝ) := by exact_mod_cast hKLinear
        _ < kappa * Z0 * W.L := by simpa using hKL
        _ < (W.m : ℝ) * Z0 := hmZ
        _ = ((W.m * Z0 : ℕ) : ℝ) := by norm_num
    exact_mod_cast h64AReal
  have hmassSpan : ((W.m * Z0 : ℕ) : ℝ) < 16 * data.segment.span := by
    have hspan16 : W.excess e ≤ 16 * (data.segment.span : ℝ) := by
      nlinarith
    calc
      ((W.m * Z0 : ℕ) : ℝ) = (W.m : ℝ) * Z0 := by norm_num
      _ < W.excess e := hlargePair
      _ ≤ 16 * (data.segment.span : ℝ) := hspan16
  have h64ASpan : 64 * A < 16 * data.segment.span := by
    have hmassSpanNat : W.m * Z0 < 16 * data.segment.span := by
      exact_mod_cast hmassSpan
    omega
  dsimp [A] at h64ASpan ⊢
  omega

/-- A concrete finite, nonnegative refinement of each interior pair.  The
certificate lives in the interior layer because its actual anchor selection
and deterministic block decomposition are produced by the Section 6
argument, before the exact parent partition is assembled. -/
structure InteriorRefinement (W : WindowSystem) (Z0 : ℕ) where
  /-- The stabilized segment actually selected at each spatial anchor. -/
  selection : InteriorAnchorSelection
  selection_valid :
    ValidInteriorAnchorSelection W.rational.eta.den W Z0 selection
  /-- Denominator-level gap data and the affine step constant are fixed for
  the whole refinement, rather than chosen separately by a block. -/
  gap : GapParams W.rational.eta.den
  Cstep : ℝ
  Cstep_pos : 0 < Cstep
  /-- Anchor-level parameters used by the deterministic greedy rule. -/
  ell : ℕ → ℕ
  meanGap : ℕ → ℕ
  forward : ℕ → ℕ
  denominatorBand : ℕ → ℕ
  blocks : ℕ → List LowGapBlock
  denominatorBand_pos : ∀ k, 0 < denominatorBand k
  meanGap_pos : ∀ k, 0 < meanGap k
  ell_eq : ∀ k,
    ell k = Nat.ceil (Real.logb 2 (4 * denominatorBand k))
  forward_eq : ∀ k,
    forward k = reconstructionForwardLength W gap.Cgap
  /-- Every interior pair is backed by the actual selected segment at its
  anchor, and its block list is exactly the threshold-independent greedy
  selection from that segment. -/
  selected_data : ∀ e, e ∈ interiorPairs W Z0 →
    ∃ data : AnchorInteriorData,
      selection e.1 = some data ∧
      data.Valid W.rational.eta.den W Z0 e.1 ∧
      blocks e.1 = selectedBlocks data.segment W.structural.B
        (ell e.1) (meanGap e.1) (forward e.1)
  blocks_nodup : ∀ k, (blocks k).Nodup
  /-- Each retained block is a genuine spatial source of its actual encoding.
  This is the bridge from the anchor-level refinement to line uniqueness and
  the source-fibre estimate. -/
  source_valid : ∀ e, e ∈ interiorPairs W Z0 →
    ∀ block ∈ blocks e.1,
      IsSpatialEncodingSource W.rational.eta.den gap.Cgap
        W.structural.B Cstep W Z0 selection
        (encodeBlock (denominatorBand e.1) (meanGap e.1) block)
        (e.1, block)
  labels : WindowThreshold → Finset LowGapBlock
  weight : WindowThreshold → LowGapBlock → ℝ
  labels_eq : ∀ e, e ∈ interiorPairs W Z0 →
    labels e = (blocks e.1).toFinset
  weight_eq : ∀ e, e ∈ interiorPairs W Z0 → ∀ b ∈ labels e,
    weight e b = interiorComponentWeight (W.excess e) (blocks e.1) b
  weight_nonneg : ∀ e b, 0 ≤ weight e b
  sums_to_excess : ∀ e, e ∈ interiorPairs W Z0 →
    (∑ b ∈ labels e, weight e b) = W.excess e
  outside_zero : ∀ e, e ∉ interiorPairs W Z0 → labels e = ∅

structure InteriorRefinementUniformFacts {W : WindowSystem} {Z0 : ℕ}
    (refinement : InteriorRefinement W Z0) (cBand Cstep : ℝ)
    (Cgap : ℕ) : Prop where
  cBand_pos : 0 < cBand
  Cstep_eq : refinement.Cstep = Cstep
  gap_Cgap_eq : refinement.gap.Cgap = Cgap
  selected_quantitative : ∀ e ∈ interiorPairs W Z0,
    ∃ data : AnchorInteriorData,
      refinement.selection e.1 = some data ∧
      data.Valid W.rational.eta.den W Z0 e.1 ∧
      W.excess e / 16 ≤ data.segment.span ∧
      1 ≤ data.segment.gapCount ∧
      data.segment.gapCount ≤ W.m ∧
      (data.segment.startLine.H : ℝ) ≤
        refinement.Cstep * W.X / frequencyCutoff W
  component_bound : ∀ e ∈ interiorPairs W Z0,
    ∀ block ∈ refinement.blocks e.1,
      interiorComponentWeight (W.excess e) (refinement.blocks e.1) block ≤
        32 * Nat.ceil ((W.structural.B + 1) * refinement.ell e.1)
  component_sum : ∀ e ∈ interiorPairs W Z0,
    (refinement.blocks e.1 |>.map fun block =>
      interiorComponentWeight (W.excess e) (refinement.blocks e.1) block).sum =
        W.excess e
  meanGap_cutoff : ∀ e ∈ interiorPairs W Z0,
    (Z0 : ℝ) / 32 < refinement.meanGap e.1
  denominator_lower : ∀ e ∈ interiorPairs W Z0,
    cBand * (2 : ℝ) ^ (refinement.meanGap e.1) ≤
      refinement.denominatorBand e.1
  denominator_isPow : ∀ k, ∃ d : ℕ, refinement.denominatorBand k = 2 ^ d
  meanGap_isPow : ∀ k, ∃ z : ℕ, refinement.meanGap k = 2 ^ z
  candidate : ∀ e ∈ interiorPairs W Z0,
    ∀ block ∈ refinement.blocks e.1,
      encodeBlock (refinement.denominatorBand e.1)
          (refinement.meanGap e.1) block ∈
        encodingCandidates (refinement.denominatorBand e.1)
          (refinement.meanGap e.1) W.structural.B

theorem interiorRefinement_exists_of_stable
    (Q : ℕ) (hQ : 0 < Q) (W : WindowSystem) (Z0 : ℕ)
    (gap : GapParams W.rational.eta.den) (Cstep : ℝ) (hCstep : 0 < Cstep)
    (selection : InteriorAnchorSelection)
    (hden : W.rational.eta.den = Q)
    (hselection : ValidInteriorAnchorSelection Q W Z0 selection)
    (hstable : ∀ e : WindowThreshold, LongInteriorPair W Z0 e →
      ∃ data : AnchorInteriorData,
        selection e.1 = some data ∧ data.Valid Q W Z0 e.1 ∧
        W.excess e / 16 ≤ data.segment.span ∧
        1 ≤ data.segment.gapCount ∧
        data.segment.gapCount ≤ W.m ∧
        (data.segment.startLine.H : ℝ) ≤
          Cstep * W.X / frequencyCutoff W)
    (hfrequency : 4 * (Q : ℝ) * Cstep ≤ frequencyCutoff W)
    (hlevel : max 1 gap.Cgap ≤ W.L)
    (hcutoff : strictCoverCutoff W.structural.B W.entropy.kappa ≤ Z0)
    (hm : W.entropy.kappa * W.L < W.m)
    (cspan : ℝ) (hcspan : 0 < cspan)
    (hdenSpan : ∀ segment : OddDenominatorSegment,
      segment.Valid Q → 0 < segment.gapCount →
      cspan * Real.rpow 2
        ((segment.span : ℝ) / segment.gapCount) ≤ segment.q) :
    ∃ refinement : InteriorRefinement W Z0,
      InteriorRefinementUniformFacts refinement (cspan / 2) Cstep gap.Cgap := by
  classical
  let ActiveAnchor : ℕ → Prop := fun k =>
    ∃ e : WindowThreshold, e.1 = k ∧ LongInteriorPair W Z0 e
  let trimmed : InteriorAnchorSelection := fun k =>
    if h : ActiveAnchor k then selection k else none
  have htrimmed_of_long (e : WindowThreshold)
      (he : LongInteriorPair W Z0 e) : trimmed e.1 = selection e.1 := by
    dsimp only [trimmed]
    split
    next => rfl
    next h => exact (h ⟨e, rfl, he⟩).elim
  have htrimmed_valid :
      ValidInteriorAnchorSelection Q W Z0 trimmed := by
    intro k data hdata
    by_cases hk : ActiveAnchor k
    · have horiginal : selection k = some data := by
        simpa [trimmed, hk] using hdata
      exact hselection k data horiginal
    · simp [trimmed, hk] at hdata
  have hstableTrimmed (e : WindowThreshold)
      (he : LongInteriorPair W Z0 e) :
      ∃ data : AnchorInteriorData,
        trimmed e.1 = some data ∧ data.Valid Q W Z0 e.1 ∧
        W.excess e / 16 ≤ data.segment.span ∧
        1 ≤ data.segment.gapCount ∧
        data.segment.gapCount ≤ W.m ∧
        (data.segment.startLine.H : ℝ) ≤
          Cstep * W.X / frequencyCutoff W := by
    rcases hstable e he with ⟨data, hselected, hrest⟩
    exact ⟨data, (htrimmed_of_long e he).trans hselected, hrest⟩
  let blocks : ℕ → List LowGapBlock :=
    selectedInteriorBlocks W trimmed gap
  have pairSpec (e : WindowThreshold) (he : e ∈ interiorPairs W Z0) :
      ∃ data : AnchorInteriorData,
        trimmed e.1 = some data ∧
        data.Valid Q W Z0 e.1 ∧
        W.excess e / 16 ≤ data.segment.span ∧
        1 ≤ data.segment.gapCount ∧
        data.segment.gapCount ≤ W.m ∧
        (data.segment.startLine.H : ℝ) ≤
          Cstep * W.X / frequencyCutoff W ∧
        (blocks e.1).Nodup ∧
        (∀ block ∈ blocks e.1,
          0 ≤ interiorComponentWeight (W.excess e) (blocks e.1) block) ∧
        (∀ block ∈ blocks e.1,
          interiorComponentWeight (W.excess e) (blocks e.1) block ≤
            32 * Nat.ceil ((W.structural.B + 1) *
              selectedLogLength trimmed e.1)) ∧
        ((blocks e.1).map (fun block =>
          interiorComponentWeight (W.excess e) (blocks e.1) block)).sum =
            W.excess e ∧
        (Z0 : ℝ) / 32 < selectedMeanGapBand trimmed e.1 ∧
        (cspan / 2) * (2 : ℝ) ^
            (selectedMeanGapBand trimmed e.1) ≤
          selectedDenominatorBand trimmed e.1 := by
    change LongInteriorPair W Z0 e at he
    rcases hstableTrimmed e he with
      ⟨data, hselected, hvalid, hspan, hcount, hcountLe, hstep⟩
    have hell : selectedLogLength trimmed e.1 ≤ W.L + gap.Cgap :=
      selectedLogLength_le_of_step Q gap.Cgap hQ Cstep W Z0 e.1 trimmed
        data hselected hvalid hstep hfrequency
    have hreserve :
        4 * (selectedForwardLength W gap e.1 +
          Nat.ceil ((W.structural.B + 1) * selectedLogLength trimmed e.1)) ≤
            data.segment.span :=
      selectedCoverReserve_le_segment W gap trimmed e data Z0
        W.entropy.kappa W.entropy.kappa_pos hlevel hcutoff hm he.1.2
        hspan hell
    have hsparse := selectedInteriorBlocks_sparseCover Q hQ W Z0 trimmed gap e
      data hselected hvalid hspan hcount hreserve
    dsimp only at hsparse
    have hblocksEq : blocks e.1 = selectedInteriorBlocks W trimmed gap e.1 := rfl
    rw [hblocksEq]
    let Z := selectedMeanGapBand trimmed e.1
    let D := selectedDenominatorBand trimmed e.1
    have hsegment : data.segment.Valid Q := hvalid.2.2.2.2.1
    have hcountPos : 0 < data.segment.gapCount := by omega
    have hcountSpan : data.segment.gapCount ≤ data.segment.span := by
      rw [OddDenominatorSegment.gapCount, OddDenominatorSegment.span,
        GapWord.span]
      exact List.length_le_sum_of_one_le data.segment.gaps fun g hg =>
        hsegment.2.1 g hg
    have hmean := meanGapBand_bounds hcountPos hcountSpan
    have hZeq : Z = meanGapBand data.segment.span data.segment.gapCount := by
      simp [Z, selectedMeanGapBand, hselected]
    have hmeanLower : Z * data.segment.gapCount ≤ data.segment.span := by
      simpa only [hZeq] using hmean.2.1
    have hmeanUpper : data.segment.span <
        2 * Z * data.segment.gapCount := by
      simpa only [hZeq] using hmean.2.2
    have hZcut : (Z0 : ℝ) / 32 < Z :=
      meanGapBand_above_cutoff (m := W.m) (Z0 := Z0)
        (y := W.excess e) (Z := Z) (by simp [WindowSystem.m]) hcountLe
        he.1.2 hspan hmeanUpper
    have hDeq : D = dyadicFloorBand data.segment.q := by
      simp [D, selectedDenominatorBand, hselected]
    have hqband : data.segment.q < 2 * D := by
      rw [hDeq]
      exact dyadicFloorBand_lt_two_mul _
    have hZavg : (Z : ℝ) ≤
        (data.segment.span : ℝ) / data.segment.gapCount := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < data.segment.gapCount)]
      exact_mod_cast hmeanLower
    have hDlower := denominatorBand_lower
      (cspan := cspan) (Z := Z) (D := D)
      hcspan hZavg (hdenSpan data.segment hsegment hcountPos) hqband
    refine ⟨data, hselected, hvalid, hspan, hcount, hcountLe, hstep,
      hsparse.2.1, hsparse.2.2.1, hsparse.2.2.2.1, hsparse.2.2.2.2,
      ?_, ?_⟩
    · simpa only [Z] using hZcut
    · simpa only [D, Z] using hDlower
  have hblocks_nodup : ∀ k, (blocks k).Nodup := by
    intro k
    by_cases hk : ActiveAnchor k
    · rcases hk with ⟨e, heFirst, he⟩
      have heMem : e ∈ interiorPairs W Z0 := by exact he
      rcases pairSpec e heMem with ⟨data, hselected, hvalid, hspan,
        hcount, hcountLe, hstep, hnodup, hrest⟩
      simpa only [heFirst] using hnodup
    · simp [blocks, selectedInteriorBlocks, trimmed, hk]
  let labels : WindowThreshold → Finset LowGapBlock := fun e =>
    if e ∈ interiorPairs W Z0 then (blocks e.1).toFinset else ∅
  let weight : WindowThreshold → LowGapBlock → ℝ := fun e block =>
    interiorComponentWeight (W.excess e) (blocks e.1) block
  let refinement : InteriorRefinement W Z0 :=
    { selection := trimmed
      selection_valid := by simpa only [hden] using htrimmed_valid
      gap := gap
      Cstep := Cstep
      Cstep_pos := hCstep
      ell := selectedLogLength trimmed
      meanGap := selectedMeanGapBand trimmed
      forward := selectedForwardLength W gap
      denominatorBand := selectedDenominatorBand trimmed
      blocks := blocks
      denominatorBand_pos := selectedDenominatorBand_pos trimmed
      meanGap_pos := selectedMeanGapBand_pos trimmed
      ell_eq := selectedLogLength_eq trimmed
      forward_eq := selectedForwardLength_eq W gap
      selected_data := by
        intro e he
        rcases pairSpec e he with ⟨data, hselected, hvalid, hrest⟩
        refine ⟨data, hselected, by simpa only [hden] using hvalid, ?_⟩
        exact selectedInteriorBlocks_eq_of_selected W trimmed gap e.1 data
          hselected
      blocks_nodup := hblocks_nodup
      source_valid := by
        intro e he block hblock
        rcases pairSpec e he with ⟨data, hselected, hvalid, hspan, hcount,
          hcountLe, hstep, hrest⟩
        have heLong : LongInteriorPair W Z0 e := he
        have hell : selectedLogLength trimmed e.1 ≤ W.L + gap.Cgap :=
          selectedLogLength_le_of_step Q gap.Cgap hQ Cstep W Z0 e.1 trimmed
            data hselected hvalid hstep hfrequency
        have hblock' : block ∈ selectedBlocks data.segment W.structural.B
            (selectedLogLength trimmed e.1) (selectedMeanGapBand trimmed e.1)
            (reconstructionForwardLength W gap.Cgap) := by
          have hblocksEq := selectedInteriorBlocks_eq_of_selected W trimmed gap
            e.1 data hselected
          change block ∈ selectedInteriorBlocks W trimmed gap e.1 at hblock
          rw [hblocksEq] at hblock
          simpa only [selectedForwardLength_eq] using hblock
        simpa only [hden] using
          selectedBlock_isSpatialEncodingSource Q gap.Cgap hQ W Z0 e.1
            trimmed data Cstep block hden hselected hvalid hstep hell
            (le_max_left _ _ |>.trans hlevel) hblock'
      labels := labels
      weight := weight
      labels_eq := by
        intro e he
        simp [labels, he]
      weight_eq := by
        intro e he block hblock
        rfl
      weight_nonneg := by
        intro e block
        dsimp only [weight]
        unfold interiorComponentWeight
        have hexcess : 0 ≤ W.excess e := by
          unfold WindowSystem.excess
          positivity
        positivity
      sums_to_excess := by
        intro e he
        rcases pairSpec e he with ⟨data, hselected, hvalid, hspan, hcount,
          hcountLe, hstep, hnodup, hnonneg, hbound, hsum, hrest⟩
        dsimp only [labels, weight]
        rw [if_pos he]
        rw [List.sum_toFinset _ hnodup]
        exact hsum
      outside_zero := by
        intro e he
        simp [labels, he] }
  refine ⟨refinement, ?_⟩
  refine {
    cBand_pos := div_pos hcspan (by norm_num)
    Cstep_eq := rfl
    gap_Cgap_eq := rfl
    selected_quantitative := ?_
    component_bound := ?_
    component_sum := ?_
    meanGap_cutoff := ?_
    denominator_lower := ?_
    denominator_isPow := ?_
    meanGap_isPow := ?_
    candidate := ?_ }
  · intro e he
    rcases pairSpec e he with ⟨data, hselected, hvalid, hspan, hcount,
      hcountLe, hstep, hrest⟩
    exact ⟨data, hselected, by simpa only [hden] using hvalid,
      hspan, hcount, hcountLe, hstep⟩
  · intro e he block hblock
    rcases pairSpec e he with ⟨data, hselected, hvalid, hspan, hcount,
      hcountLe, hstep, hnodup, hnonneg, hbound, hsum, hZcut, hDlower⟩
    exact hbound block hblock
  · intro e he
    rcases pairSpec e he with ⟨data, hselected, hvalid, hspan, hcount,
      hcountLe, hstep, hnodup, hnonneg, hbound, hsum, hZcut, hDlower⟩
    exact hsum
  · intro e he
    rcases pairSpec e he with ⟨data, hselected, hvalid, hspan, hcount,
      hcountLe, hstep, hnodup, hnonneg, hbound, hsum, hZcut, hDlower⟩
    exact hZcut
  · intro e he
    rcases pairSpec e he with ⟨data, hselected, hvalid, hspan, hcount,
      hcountLe, hstep, hnodup, hnonneg, hbound, hsum, hZcut, hDlower⟩
    exact hDlower
  · intro k
    simp only [refinement]
    unfold selectedDenominatorBand
    split
    · exact ⟨0, by simp⟩
    · exact dyadicFloorBand_isPow _
  · intro k
    simp only [refinement]
    unfold selectedMeanGapBand meanGapBand
    split
    · exact ⟨0, by simp⟩
    · exact dyadicFloorBand_isPow _
  · intro e he block hblock
    have hsource := refinement.source_valid e he block hblock
    rcases hsource with ⟨data, t, hreconstructed, hparameter⟩
    exact hreconstructed.2.2.2.2.2.2.1

theorem eventually_exists_interiorRefinement_certificate
    (context : FixedScaleContext) :
    ∃ gap : GapParams context.Q, ∃ Cstep : ℝ, 0 < Cstep ∧
      ∃ Zmin : ℕ, ∃ cBand : ℝ, 0 < cBand ∧
        ∀ Z0 : ℕ, Zmin ≤ Z0 →
          ∀ F : ScaleFamily, F.MatchesContext context →
            ∀ᶠ L : ℕ in atTop,
              ∃ refinement : InteriorRefinement (F.system L) Z0,
                InteriorRefinementUniformFacts refinement cBand Cstep gap.Cgap := by
  obtain ⟨gap⟩ := gapParams_exists context.Q context.Q_pos
  obtain ⟨Cstep, hCstep, Zstable, hstable⟩ :=
    lem_stable_segment context gap
  obtain ⟨cspan, hcspan, hdenSpan⟩ :=
    lem_denominator_span context.Q context.Q_pos
  let Zmin := max Zstable
    (strictCoverCutoff context.structural.B context.entropy.kappa)
  refine ⟨gap, Cstep, hCstep, Zmin, cspan / 2,
    div_pos hcspan (by norm_num), ?_⟩
  intro Z0 hZ0 F hF
  have hZstable : Zstable ≤ Z0 :=
    (le_max_left Zstable
      (strictCoverCutoff context.structural.B context.entropy.kappa)).trans hZ0
  have hZcover :
      strictCoverCutoff context.structural.B context.entropy.kappa ≤ Z0 :=
    (le_max_right Zstable
      (strictCoverCutoff context.structural.B context.entropy.kappa)).trans hZ0
  have hstableEvent := hstable Z0 hZstable F hF
  have hfrequencyTop := frequencyCutoff_tendsto context F hF
  have hfrequencyEvent : ∀ᶠ L : ℕ in atTop,
      4 * (context.Q : ℝ) * Cstep ≤ frequencyCutoff (F.system L) := by
    filter_upwards [tendsto_atTop.1 hfrequencyTop
      (4 * (context.Q : ℝ) * Cstep + 1)] with L hL
    linarith
  filter_upwards [hstableEvent, hfrequencyEvent,
      eventually_ge_atTop (max 1 gap.Cgap)] with
      L hselection hfrequency hlevel
  rcases hselection with ⟨selection, hselectionValid, hstableSelection⟩
  have hden : (F.system L).rational.eta.den = context.Q := by
    rw [F.rational_eq]
    exact hF.1
  let gapW : GapParams (F.system L).rational.eta.den :=
    { Cgap := gap.Cgap
      x0 := gap.x0
      bound := by
        intro R hR
        exact gap.bound R (hR.trans hden) }
  have hlevelW : max 1 gapW.Cgap ≤ (F.system L).L := by
    rw [F.level_eq]
    exact hlevel
  have hcutoffW :
      strictCoverCutoff (F.system L).structural.B
          (F.system L).entropy.kappa ≤ Z0 := by
    rw [F.structural_eq, hF.2.1, F.entropy_eq, hF.2.2.1]
    exact hZcover
  have hoffset : (F.system L).s =
      Nat.floor (context.entropy.kappa * (L : ℝ)) := by
    rw [F.offset_eq, hF.2.2.1]
  have hmContext : context.entropy.kappa * (L : ℝ) <
      ((F.system L).m : ℝ) := by
    rw [WindowSystem.m, hoffset]
    simpa only [Nat.cast_add, Nat.cast_one] using
      (Nat.lt_floor_add_one (context.entropy.kappa * (L : ℝ)))
  have hmW : (F.system L).entropy.kappa * (F.system L).L <
      (F.system L).m := by
    rw [F.entropy_eq, hF.2.2.1, F.level_eq]
    exact hmContext
  exact interiorRefinement_exists_of_stable context.Q context.Q_pos
    (F.system L) Z0 gapW Cstep hCstep selection hden hselectionValid
    hstableSelection hfrequency hlevelW hcutoffW hmW cspan hcspan hdenSpan

/-- Refined interior mass with counting over finite labels inside the same
window-threshold integral. -/
def refinedInteriorMass {W : WindowSystem} {Z0 : ℕ}
    (refinement : InteriorRefinement W Z0) : ℝ≥0∞ :=
  ∫⁻ e in interiorPairs W Z0,
    ENNReal.ofReal
      (∑ b ∈ (refinement.blocks e.1).toFinset,
        interiorComponentWeight (W.excess e) (refinement.blocks e.1) b)
    ∂windowThresholdMeasure

theorem refinedInteriorMass_eq_mass_strict {W : WindowSystem} {Z0 : ℕ}
    (refinement : InteriorRefinement W Z0) :
    refinedInteriorMass refinement = mass (interiorPairs W Z0) W.excess := by
  unfold refinedInteriorMass mass
  apply setLIntegral_congr_fun (measurableSet_interiorPairs_strict W Z0)
  intro e he
  apply congrArg ENNReal.ofReal
  have hsum := refinement.sums_to_excess e he
  calc
    (∑ b ∈ (refinement.blocks e.1).toFinset,
        interiorComponentWeight (W.excess e) (refinement.blocks e.1) b) =
        ∑ b ∈ refinement.labels e, refinement.weight e b := by
          rw [refinement.labels_eq e he]
          apply Finset.sum_congr rfl
          intro b hb
          symm
          apply refinement.weight_eq e he b
          simpa [refinement.labels_eq e he] using hb
    _ = W.excess e := hsum

theorem lintegral_anchorCharge_pairSet
    (W : WindowSystem) (charge : ℕ → ℝ)
    (hcharge : ∀ k ∈ W.anchors, 0 ≤ charge k) :
    (∫⁻ e in W.pairSet, ENNReal.ofReal (charge e.1)
        ∂windowThresholdMeasure) =
      ENNReal.ofReal
        ((∑ k ∈ W.anchors, charge k) * thresholdLength W) := by
  rw [WindowSystem.pairSet_eq_prod]
  unfold windowThresholdMeasure
  change (∫⁻ e : WindowThreshold,
      ENNReal.ofReal (charge e.1) ∂
        (Measure.count.prod volume).restrict
          (Set.prod (W.anchors : Set ℕ) W.thresholds)) = _
  have hmeasure :
      (Measure.count.prod volume).restrict
          (Set.prod (W.anchors : Set ℕ) W.thresholds) =
        (Measure.count.restrict (W.anchors : Set ℕ)).prod
          (volume.restrict W.thresholds) :=
    (Measure.prod_restrict (μ := Measure.count) (ν := volume)
      (W.anchors : Set ℕ) W.thresholds).symm
  rw [hmeasure, MeasureTheory.lintegral_prod_symm]
  · have hsum :
        (∑ k ∈ W.anchors, ENNReal.ofReal (charge k)) =
          ENNReal.ofReal (∑ k ∈ W.anchors, charge k) := by
      symm
      apply ENNReal.ofReal_sum_of_nonneg
      intro k hk
      exact hcharge k hk
    simp_rw [MeasureTheory.lintegral_finset]
    simp
    have hsumNonneg : 0 ≤ ∑ k ∈ W.anchors, charge k :=
      Finset.sum_nonneg fun k hk => hcharge k hk
    have hlength : 0 ≤ thresholdLength W := by
      unfold thresholdLength
      exact mul_nonneg W.structural.cI_pos.le (Nat.cast_nonneg _)
    rw [hsum, WindowSystem.thresholds, thresholdInterval, Real.volume_Icc]
    have hdiff :
        2 * (W.L : ℝ) + W.structural.C0 + W.structural.cI * W.L -
            (2 * (W.L : ℝ) + W.structural.C0) = thresholdLength W := by
      unfold thresholdLength
      ring
    rw [hdiff]
    rw [← ENNReal.ofReal_mul hsumNonneg]
  · exact ((measurable_of_countable charge).comp measurable_fst).ennreal_ofReal.aemeasurable

theorem mass_le_anchorCharge
    (W : WindowSystem) (E : Set WindowThreshold) (hE : E ⊆ W.pairSet)
    (charge : ℕ → ℝ) (hcharge : ∀ k ∈ W.anchors, 0 ≤ charge k)
    (hbound : ∀ e ∈ E, W.excess e ≤ charge e.1) :
    mass E W.excess ≤
      ENNReal.ofReal
        ((∑ k ∈ W.anchors, charge k) * thresholdLength W) := by
  unfold mass
  calc
    (∫⁻ e in E, ENNReal.ofReal (W.excess e) ∂windowThresholdMeasure) ≤
        ∫⁻ e in E, ENNReal.ofReal (charge e.1) ∂windowThresholdMeasure := by
      apply setLIntegral_mono
      · exact ((measurable_of_countable charge).comp measurable_fst).ennreal_ofReal
      · intro e he
        exact ENNReal.ofReal_le_ofReal (hbound e he)
    _ ≤ ∫⁻ e in W.pairSet,
        ENNReal.ofReal (charge e.1) ∂windowThresholdMeasure :=
      lintegral_mono_set hE
    _ = ENNReal.ofReal
        ((∑ k ∈ W.anchors, charge k) * thresholdLength W) :=
      lintegral_anchorCharge_pairSet W charge hcharge

def refinementAnchorCharge {W : WindowSystem} {Z0 : ℕ}
    (refinement : InteriorRefinement W Z0)
    (blockBound : ℕ → LowGapBlock → ℝ) (k : ℕ) : ℝ :=
  ∑ b ∈ (refinement.blocks k).toFinset, blockBound k b

theorem interiorPairsMass_le_refinementAnchorCharge
    {W : WindowSystem} {Z0 : ℕ}
    (refinement : InteriorRefinement W Z0)
    (blockBound : ℕ → LowGapBlock → ℝ)
    (hboundNonneg : ∀ k b, 0 ≤ blockBound k b)
    (hcomponentSum : ∀ e, e ∈ interiorPairs W Z0 →
      (refinement.blocks e.1 |>.map fun b =>
        interiorComponentWeight (W.excess e) (refinement.blocks e.1) b).sum =
          W.excess e)
    (hcomponentBound : ∀ e, e ∈ interiorPairs W Z0 →
      ∀ b ∈ refinement.blocks e.1,
        interiorComponentWeight (W.excess e) (refinement.blocks e.1) b ≤
          blockBound e.1 b) :
    interiorPairsMass W Z0 ≤
      (∑ k ∈ W.anchors, refinementAnchorCharge refinement blockBound k) *
        thresholdLength W := by
  let charge := refinementAnchorCharge refinement blockBound
  have hcharge : ∀ k ∈ W.anchors, 0 ≤ charge k := by
    intro k _hk
    apply Finset.sum_nonneg
    intro b hb
    exact hboundNonneg k b
  have hpoint : ∀ e ∈ interiorPairs W Z0, W.excess e ≤ charge e.1 := by
    intro e he
    rw [← hcomponentSum e he]
    have hlist := List.sum_toFinset
      (fun b => interiorComponentWeight (W.excess e) (refinement.blocks e.1) b)
      (refinement.blocks_nodup e.1)
    rw [← hlist]
    apply Finset.sum_le_sum
    intro b hb
    apply hcomponentBound e he b
    simpa using hb
  have hmass := mass_le_anchorCharge W (interiorPairs W Z0)
    (interiorPairs_subset_pairSet W Z0) charge hcharge hpoint
  have hleftTop : mass (interiorPairs W Z0) W.excess ≠ ⊤ :=
    (finiteMassOfSubset W (interiorPairs W Z0)
      (interiorPairs_subset_pairSet W Z0)).ne_top
  have hsumNonneg : 0 ≤
      (∑ k ∈ W.anchors, refinementAnchorCharge refinement blockBound k) := by
    apply Finset.sum_nonneg
    intro k hk
    exact hcharge k hk
  have hlength : 0 ≤ thresholdLength W := by
    unfold thresholdLength
    exact mul_nonneg W.structural.cI_pos.le (Nat.cast_nonneg _)
  have hrightNonneg : 0 ≤
      (∑ k ∈ W.anchors, refinementAnchorCharge refinement blockBound k) *
        thresholdLength W := mul_nonneg hsumNonneg hlength
  have hrightTop : ENNReal.ofReal
      ((∑ k ∈ W.anchors, refinementAnchorCharge refinement blockBound k) *
        thresholdLength W) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hto := (ENNReal.toReal_le_toReal hleftTop hrightTop).2 hmass
  change (mass (interiorPairs W Z0) W.excess).toReal ≤ _
  simpa [interiorPairsMass, ENNReal.toReal_ofReal hrightNonneg] using hto

theorem finite_ncard_real_le_card_mul_of_bounded_fibres
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Set α) (t : Set β) (hs : s.Finite) (ht : t.Finite)
    (f : α → β) (M : ℝ) (_hM : 0 ≤ M)
    (hmap : ∀ x ∈ s, f x ∈ t)
    (hfibre : ∀ y ∈ t, (s ∩ f ⁻¹' {y}).Finite)
    (hbound : ∀ y ∈ t, ((s ∩ f ⁻¹' {y}).ncard : ℝ) ≤ M) :
    (s.ncard : ℝ) ≤ (t.ncard : ℝ) * M := by
  classical
  let fibres : β → Finset α := fun y =>
    if hy : y ∈ t then (hfibre y hy).toFinset else ∅
  have hsub : hs.toFinset ⊆ ht.toFinset.biUnion fibres := by
    intro x hx
    have hxs : x ∈ s := hs.mem_toFinset.mp hx
    have hfx : f x ∈ t := hmap x hxs
    rw [Finset.mem_biUnion]
    refine ⟨f x, ht.mem_toFinset.mpr hfx, ?_⟩
    simp only [fibres, dif_pos hfx]
    apply (hfibre (f x) hfx).mem_toFinset.mpr
    exact ⟨hxs, rfl⟩
  have hcardNat : hs.toFinset.card ≤
      (ht.toFinset.biUnion fibres).card := Finset.card_le_card hsub
  calc
    (s.ncard : ℝ) = (hs.toFinset.card : ℝ) := by
      rw [Set.ncard_eq_toFinset_card s hs]
    _ ≤ ((ht.toFinset.biUnion fibres).card : ℕ) := by exact_mod_cast hcardNat
    _ ≤ (∑ y ∈ ht.toFinset, (fibres y).card : ℕ) := by
      exact_mod_cast (Finset.card_biUnion_le (s := ht.toFinset) (t := fibres))
    _ = ∑ y ∈ ht.toFinset, ((fibres y).card : ℝ) := by norm_num
    _ ≤ ∑ _y ∈ ht.toFinset, M := by
      apply Finset.sum_le_sum
      intro y hy
      have hyt : y ∈ t := ht.mem_toFinset.mp hy
      simp only [fibres, dif_pos hyt]
      rw [← Set.ncard_eq_toFinset_card (s ∩ f ⁻¹' {y}) (hfibre y hyt)]
      exact hbound y hyt
    _ = (ht.toFinset.card : ℝ) * M := by simp
    _ = (t.ncard : ℝ) * M := by rw [Set.ncard_eq_toFinset_card t ht]

noncomputable def interiorAnchorFinset (W : WindowSystem) (Z0 : ℕ) : Finset ℕ :=
  by
    classical
    exact W.anchors.filter fun k => ∃ T : ℝ, (k, T) ∈ interiorPairs W Z0

noncomputable def refinementSourceFinset {W : WindowSystem} {Z0 : ℕ}
    (refinement : InteriorRefinement W Z0) : Finset (ℕ × LowGapBlock) :=
  by
    classical
    exact (interiorAnchorFinset W Z0).biUnion fun k =>
      (refinement.blocks k).toFinset.image fun b => (k, b)

noncomputable def refinementSourceBandFinset {W : WindowSystem} {Z0 : ℕ}
    (refinement : InteriorRefinement W Z0) (D Z : ℕ) :
    Finset (ℕ × LowGapBlock) :=
  by
    classical
    exact (refinementSourceFinset refinement).filter fun kb =>
      refinement.denominatorBand kb.1 = D ∧ refinement.meanGap kb.1 = Z

theorem mem_refinementSourceFinset_iff
    {W : WindowSystem} {Z0 : ℕ} (refinement : InteriorRefinement W Z0)
    (kb : ℕ × LowGapBlock) :
    kb ∈ refinementSourceFinset refinement ↔
      kb.1 ∈ interiorAnchorFinset W Z0 ∧ kb.2 ∈ refinement.blocks kb.1 := by
  classical
  constructor
  · intro hkb
    rw [refinementSourceFinset, Finset.mem_biUnion] at hkb
    rcases hkb with ⟨k, hk, hkb⟩
    rw [Finset.mem_image] at hkb
    rcases hkb with ⟨b, hb, hpair⟩
    have hkEq : k = kb.1 := congrArg Prod.fst hpair
    have hbEq : b = kb.2 := congrArg Prod.snd hpair
    subst k
    subst b
    exact ⟨hk, by simpa using hb⟩
  · rintro ⟨hk, hb⟩
    rw [refinementSourceFinset, Finset.mem_biUnion]
    refine ⟨kb.1, hk, ?_⟩
    rw [Finset.mem_image]
    exact ⟨kb.2, by simpa using hb, Prod.ext rfl rfl⟩

theorem refinementSourceBand_card_real_le
    {W : WindowSystem} {Z0 D Z : ℕ} (M : ℝ) (hM : 0 ≤ M)
    (refinement : InteriorRefinement W Z0)
    (hcandidates : (encodingCandidates D Z W.structural.B).Finite)
    (hfibres : ∀ σ ∈ encodingCandidates D Z W.structural.B,
      (spatialPreimage W.rational.eta.den refinement.gap.Cgap
          W.structural.B refinement.Cstep W Z0 refinement.selection σ).Finite ∧
        ((spatialPreimage W.rational.eta.den refinement.gap.Cgap
          W.structural.B refinement.Cstep W Z0 refinement.selection σ).ncard : ℝ) ≤ M) :
    ((refinementSourceBandFinset refinement D Z).card : ℝ) ≤
      ((encodingCandidates D Z W.structural.B).ncard : ℝ) * M := by
  classical
  let s : Set (ℕ × LowGapBlock) :=
    (refinementSourceBandFinset refinement D Z : Finset (ℕ × LowGapBlock))
  let t : Set BlockEncoding := encodingCandidates D Z W.structural.B
  let f : (ℕ × LowGapBlock) → BlockEncoding := fun kb => encodeBlock D Z kb.2
  have hs : s.Finite := (refinementSourceBandFinset refinement D Z).finite_toSet
  have hmap : ∀ kb ∈ s, f kb ∈ t := by
    intro kb hkb
    change kb ∈ refinementSourceBandFinset refinement D Z at hkb
    rw [refinementSourceBandFinset, Finset.mem_filter] at hkb
    rcases hkb with ⟨hsourceFinset, hD, hZ⟩
    have hsourceData := (mem_refinementSourceFinset_iff refinement kb).mp hsourceFinset
    rw [interiorAnchorFinset, Finset.mem_filter] at hsourceData
    rcases hsourceData with ⟨⟨_hkAnchor, T, he⟩, hb⟩
    have hsource := refinement.source_valid (kb.1, T) he kb.2 hb
    change IsSpatialEncodingSource W.rational.eta.den refinement.gap.Cgap
      W.structural.B refinement.Cstep W Z0 refinement.selection
        (encodeBlock (refinement.denominatorBand kb.1)
          (refinement.meanGap kb.1) kb.2) kb at hsource
    rcases hsource with ⟨sourceData, tsource, hrec, hparameter⟩
    change encodeBlock D Z kb.2 ∈ encodingCandidates D Z W.structural.B
    simpa [hD, hZ, encodeBlock] using hrec.2.2.2.2.2.2.1
  have hfibreSubset : ∀ σ ∈ t, (s ∩ f ⁻¹' {σ}) ⊆
      spatialPreimage W.rational.eta.den refinement.gap.Cgap
        W.structural.B refinement.Cstep W Z0 refinement.selection σ := by
    intro σ hσ kb hkb
    rcases hkb with ⟨hkbS, hencode⟩
    change kb ∈ refinementSourceBandFinset refinement D Z at hkbS
    rw [refinementSourceBandFinset, Finset.mem_filter] at hkbS
    rcases hkbS with ⟨hsourceFinset, hD, hZ⟩
    have hsourceData := (mem_refinementSourceFinset_iff refinement kb).mp hsourceFinset
    rw [interiorAnchorFinset, Finset.mem_filter] at hsourceData
    rcases hsourceData with ⟨⟨_hkAnchor, T, he⟩, hb⟩
    have hsource := refinement.source_valid (kb.1, T) he kb.2 hb
    change IsSpatialEncodingSource W.rational.eta.den refinement.gap.Cgap
      W.structural.B refinement.Cstep W Z0 refinement.selection
        (encodeBlock (refinement.denominatorBand kb.1)
          (refinement.meanGap kb.1) kb.2) kb at hsource
    change IsSpatialEncodingSource W.rational.eta.den refinement.gap.Cgap
      W.structural.B refinement.Cstep W Z0 refinement.selection σ kb
    have hencode' : encodeBlock D Z kb.2 = σ := by simpa [f] using hencode
    simpa [hD, hZ, hencode'] using hsource
  have hfibreFinite : ∀ σ ∈ t, (s ∩ f ⁻¹' {σ}).Finite := by
    intro σ hσ
    exact (hfibres σ hσ).1.subset (hfibreSubset σ hσ)
  have hfibreBound : ∀ σ ∈ t, ((s ∩ f ⁻¹' {σ}).ncard : ℝ) ≤ M := by
    intro σ hσ
    calc
      ((s ∩ f ⁻¹' {σ}).ncard : ℝ) ≤
          ((spatialPreimage W.rational.eta.den refinement.gap.Cgap
            W.structural.B refinement.Cstep W Z0 refinement.selection σ).ncard : ℝ) := by
        exact_mod_cast Set.ncard_le_ncard (hfibreSubset σ hσ) (hfibres σ hσ).1
      _ ≤ M := (hfibres σ hσ).2
  have hcard := finite_ncard_real_le_card_mul_of_bounded_fibres
    s t hs hcandidates f M hM hmap hfibreFinite hfibreBound
  simpa [s, t] using hcard

def strictAnchorBlockCap {W : WindowSystem} {Z0 : ℕ}
    (refinement : InteriorRefinement W Z0) (k : ℕ) : ℝ :=
  32 * Nat.ceil ((W.structural.B + 1) * refinement.ell k)

def strictBandBlockCap (W : WindowSystem) (D : ℕ) : ℝ :=
  32 * Nat.ceil ((W.structural.B + 1) *
    Nat.ceil (Real.logb 2 (4 * D)))

noncomputable def refinementBandKeys {W : WindowSystem} {Z0 : ℕ}
    (refinement : InteriorRefinement W Z0) : Finset (ℕ × ℕ) :=
  (refinementSourceFinset refinement).image fun kb =>
    (refinement.denominatorBand kb.1, refinement.meanGap kb.1)

theorem interiorAnchorFinset_subset_anchors (W : WindowSystem) (Z0 : ℕ) :
    interiorAnchorFinset W Z0 ⊆ W.anchors := by
  classical
  intro k hk
  rw [interiorAnchorFinset, Finset.mem_filter] at hk
  exact hk.1

theorem sum_refinementSourceFinset
    {W : WindowSystem} {Z0 : ℕ} (refinement : InteriorRefinement W Z0)
    (f : ℕ × LowGapBlock → ℝ) :
    (∑ kb ∈ refinementSourceFinset refinement, f kb) =
      ∑ k ∈ interiorAnchorFinset W Z0,
        ∑ b ∈ (refinement.blocks k).toFinset, f (k, b) := by
  classical
  have hdisjoint : Set.PairwiseDisjoint
      (interiorAnchorFinset W Z0 : Set ℕ)
      (fun k => (refinement.blocks k).toFinset.image fun b => (k, b)) := by
    intro k hk k' hk' hne
    change Disjoint
      ((refinement.blocks k).toFinset.image fun b => (k, b))
      ((refinement.blocks k').toFinset.image fun b => (k', b))
    rw [Finset.disjoint_left]
    intro kb hkb hkb'
    rcases Finset.mem_image.mp hkb with ⟨b, hb, rfl⟩
    rcases Finset.mem_image.mp hkb' with ⟨b', hb', hpair⟩
    have hfirst := congrArg Prod.fst hpair
    exact hne (by simpa using hfirst.symm)
  rw [refinementSourceFinset, Finset.sum_biUnion hdisjoint]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_image]
  intro b hb b' hb' hpair
  exact congrArg Prod.snd hpair

theorem anchorCharge_sum_eq_sourceCap_sum
    {W : WindowSystem} {Z0 : ℕ} (refinement : InteriorRefinement W Z0) :
    (∑ k ∈ W.anchors,
        refinementAnchorCharge refinement
          (fun k _ => if k ∈ interiorAnchorFinset W Z0 then
            strictAnchorBlockCap refinement k else 0) k) =
      ∑ kb ∈ refinementSourceFinset refinement,
        strictAnchorBlockCap refinement kb.1 := by
  classical
  let I := interiorAnchorFinset W Z0
  let cap : ℕ → ℝ := strictAnchorBlockCap refinement
  have hsubset : I ⊆ W.anchors := interiorAnchorFinset_subset_anchors W Z0
  have houter :
      (∑ k ∈ W.anchors,
          refinementAnchorCharge refinement
            (fun k _ => if k ∈ I then cap k else 0) k) =
        ∑ k ∈ I, ∑ b ∈ (refinement.blocks k).toFinset, cap k := by
    calc
      (∑ k ∈ W.anchors,
          refinementAnchorCharge refinement
            (fun k _ => if k ∈ I then cap k else 0) k) =
          ∑ k ∈ W.anchors,
            if k ∈ I then
              ∑ b ∈ (refinement.blocks k).toFinset, cap k
            else 0 := by
              apply Finset.sum_congr rfl
              intro k hk
              by_cases hkI : k ∈ I <;>
                simp [refinementAnchorCharge, hkI]
      _ = ∑ k ∈ I, ∑ b ∈ (refinement.blocks k).toFinset, cap k := by
        calc
          (∑ k ∈ W.anchors,
              if k ∈ I then
                ∑ b ∈ (refinement.blocks k).toFinset, cap k
              else 0) =
              ∑ k ∈ I,
                if k ∈ I then
                  ∑ b ∈ (refinement.blocks k).toFinset, cap k
                else 0 := by
                  symm
                  apply Finset.sum_subset hsubset
                  intro k hkAnchor hkNotI
                  simp [hkNotI]
          _ = ∑ k ∈ I,
              ∑ b ∈ (refinement.blocks k).toFinset, cap k := by
                apply Finset.sum_congr rfl
                intro k hkI
                simp [hkI]
  rw [houter]
  rw [sum_refinementSourceFinset refinement]

theorem sourceCap_sum_eq_bandCap_sum
    {W : WindowSystem} {Z0 : ℕ} (refinement : InteriorRefinement W Z0) :
    (∑ kb ∈ refinementSourceFinset refinement,
        strictAnchorBlockCap refinement kb.1) =
      ∑ key ∈ refinementBandKeys refinement,
        ((refinementSourceBandFinset refinement key.1 key.2).card : ℝ) *
          strictBandBlockCap W key.1 := by
  classical
  let source := refinementSourceFinset refinement
  let key : (ℕ × LowGapBlock) → ℕ × ℕ := fun kb =>
    (refinement.denominatorBand kb.1, refinement.meanGap kb.1)
  let keys := refinementBandKeys refinement
  have hmaps : ∀ kb ∈ source, key kb ∈ keys := by
    intro kb hkb
    exact Finset.mem_image.mpr ⟨kb, hkb, rfl⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to hmaps
    (fun kb => strictAnchorBlockCap refinement kb.1)
  rw [← hfiber]
  have hbandFinset : ∀ keyValue : ℕ × ℕ,
      refinementSourceBandFinset refinement keyValue.1 keyValue.2 =
        source.filter fun kb => key kb = keyValue := by
    intro keyValue
    ext kb
    simp [refinementSourceBandFinset, source, key, Prod.ext_iff]
  change (∑ keyValue ∈ keys,
      ∑ kb ∈ source with key kb = keyValue,
        strictAnchorBlockCap refinement kb.1) =
    ∑ keyValue ∈ keys,
      ((refinementSourceBandFinset refinement
        keyValue.1 keyValue.2).card : ℝ) *
        strictBandBlockCap W keyValue.1
  apply Finset.sum_congr rfl
  intro keyValue hkeyValue
  rw [hbandFinset keyValue]
  calc
    (∑ kb ∈ source with key kb = keyValue,
        strictAnchorBlockCap refinement kb.1) =
        ∑ _kb ∈ source.filter (fun kb => key kb = keyValue),
          strictBandBlockCap W keyValue.1 := by
            apply Finset.sum_congr rfl
            intro kb hkb
            have hkey : key kb = keyValue := (Finset.mem_filter.mp hkb).2
            have hD : refinement.denominatorBand kb.1 = keyValue.1 :=
              congrArg Prod.fst hkey
            simp only [strictAnchorBlockCap, strictBandBlockCap]
            rw [refinement.ell_eq kb.1, hD]
    _ = ((source.filter fun kb => key kb = keyValue).card : ℝ) *
          strictBandBlockCap W keyValue.1 := by simp

theorem strictLogLength_pos {D : ℕ} (hD : 0 < D) :
    0 < Nat.ceil (Real.logb 2 (4 * D)) := by
  have hellEq : Nat.ceil (Real.logb 2 (4 * D)) =
      Nat.clog 2 (4 * D) := by
    simpa only [Nat.cast_ofNat, Nat.cast_mul] using
      Real.natCeil_logb_natCast 2 (4 * D)
  rw [hellEq, Nat.lt_clog_iff_pow_lt (by omega)]
  simp
  omega

theorem strictBandBlockCap_le (W : WindowSystem) {D : ℕ} (hD : 0 < D) :
    strictBandBlockCap W D ≤
      32 * (W.structural.B + 2) *
        Nat.ceil (Real.logb 2 (4 * D)) := by
  let ell := Nat.ceil (Real.logb 2 (4 * D))
  have hellPos : 0 < ell := strictLogLength_pos hD
  have hBnonneg : 0 ≤ W.structural.B + 1 := by
    linarith [W.structural.B_gt]
  have hargNonneg : 0 ≤ (W.structural.B + 1) * (ell : ℝ) :=
    mul_nonneg hBnonneg (Nat.cast_nonneg _)
  have hceil : (Nat.ceil ((W.structural.B + 1) * (ell : ℝ)) : ℝ) ≤
      (W.structural.B + 2) * ell := by
    have hlt := Nat.ceil_lt_add_one hargNonneg
    have hone : (1 : ℝ) ≤ ell := by exact_mod_cast hellPos
    nlinarith
  unfold strictBandBlockCap
  change 32 * (Nat.ceil ((W.structural.B + 1) * (ell : ℝ)) : ℝ) ≤
    32 * (W.structural.B + 2) * ell
  nlinarith

theorem fixedBandCharge_le_sqrt
    {W : WindowSystem} {Z0 D Z : ℕ} (hD : 0 < D)
    (refinement : InteriorRefinement W Z0)
    (hcandidates : (encodingCandidates D Z W.structural.B).Finite)
    (hentropy :
      ((encodingCandidates D Z W.structural.B).ncard : ℝ) *
        Nat.ceil (Real.logb 2 (4 * D)) ≤ Real.sqrt D)
    (hfibres : ∀ σ ∈ encodingCandidates D Z W.structural.B,
      (spatialPreimage W.rational.eta.den refinement.gap.Cgap
          W.structural.B refinement.Cstep W Z0 refinement.selection σ).Finite ∧
        ((spatialPreimage W.rational.eta.den refinement.gap.Cgap
          W.structural.B refinement.Cstep W Z0 refinement.selection σ).ncard : ℝ) ≤
          (W.rational.eta.den : ℝ) * (refinement.Cstep + 4) * W.m * W.X / D) :
    ((refinementSourceBandFinset refinement D Z).card : ℝ) *
        strictBandBlockCap W D ≤
      32 * (W.structural.B + 2) *
        ((W.rational.eta.den : ℝ) * (refinement.Cstep + 4) * W.m * W.X) /
          Real.sqrt D := by
  let ell : ℝ := Nat.ceil (Real.logb 2 (4 * D))
  let N : ℝ := (encodingCandidates D Z W.structural.B).ncard
  let C : ℝ :=
    (W.rational.eta.den : ℝ) * (refinement.Cstep + 4) * W.m * W.X
  let K : ℝ := 32 * (W.structural.B + 2) * C
  have hC : 0 ≤ C := by
    dsimp [C]
    have hstep : 0 ≤ refinement.Cstep + 4 := by
      linarith [refinement.Cstep_pos]
    positivity
  have hK : 0 ≤ K := by
    dsimp [K]
    have hB : 0 ≤ W.structural.B + 2 := by
      linarith [W.structural.B_gt]
    positivity
  have hDreal : (0 : ℝ) < D := by positivity
  have hsqrtPos : 0 < Real.sqrt D := Real.sqrt_pos.2 hDreal
  have hcard : ((refinementSourceBandFinset refinement D Z).card : ℝ) ≤
      N * (C / D) := by
    apply refinementSourceBand_card_real_le (C / D)
      (div_nonneg hC hDreal.le) refinement hcandidates
    intro σ hσ
    simpa [C] using hfibres σ hσ
  have hcap : strictBandBlockCap W D ≤
      32 * (W.structural.B + 2) * ell := by
    simpa [ell] using strictBandBlockCap_le W hD
  have hcapNonneg : 0 ≤ strictBandBlockCap W D := by
    unfold strictBandBlockCap
    positivity
  have hNnonneg : 0 ≤ N := by
    dsimp [N]
    positivity
  have hellNonneg : 0 ≤ ell := by
    dsimp [ell]
    positivity
  have hupperNonneg : 0 ≤ 32 * (W.structural.B + 2) * ell := by
    have hB : 0 ≤ W.structural.B + 2 := by
      linarith [W.structural.B_gt]
    positivity
  have hNell : N * ell ≤ Real.sqrt D := by
    simpa [N, ell] using hentropy
  have hsq : Real.sqrt D * Real.sqrt D = (D : ℝ) := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ D by positivity)]
  calc
    ((refinementSourceBandFinset refinement D Z).card : ℝ) *
          strictBandBlockCap W D ≤
        (N * (C / D)) * (32 * (W.structural.B + 2) * ell) := by
      exact mul_le_mul hcard hcap hcapNonneg
        (mul_nonneg hNnonneg (div_nonneg hC hDreal.le))
    _ = K * (N * ell) / D := by
      dsimp [K]
      ring
    _ ≤ K * Real.sqrt D / D := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hNell hK) hDreal.le
    _ = K / Real.sqrt D := by
      calc
        K * Real.sqrt D / (D : ℝ) =
            K * Real.sqrt D / (Real.sqrt D * Real.sqrt D) := by
          exact congrArg (fun x : ℝ => K * Real.sqrt D / x) hsq.symm
        _ = K / Real.sqrt D := by field_simp
    _ = 32 * (W.structural.B + 2) *
        ((W.rational.eta.den : ℝ) * (refinement.Cstep + 4) * W.m * W.X) /
          Real.sqrt D := by rfl

theorem InteriorRefinement.component_sum_eq
    {W : WindowSystem} {Z0 : ℕ} (refinement : InteriorRefinement W Z0)
    (e : WindowThreshold) (he : e ∈ interiorPairs W Z0) :
    (refinement.blocks e.1 |>.map fun b =>
      interiorComponentWeight (W.excess e) (refinement.blocks e.1) b).sum =
        W.excess e := by
  rw [← List.sum_toFinset _ (refinement.blocks_nodup e.1)]
  have hsum := refinement.sums_to_excess e he
  calc
    (∑ b ∈ (refinement.blocks e.1).toFinset,
        interiorComponentWeight (W.excess e) (refinement.blocks e.1) b) =
        ∑ b ∈ refinement.labels e, refinement.weight e b := by
      rw [refinement.labels_eq e he]
      apply Finset.sum_congr rfl
      intro b hb
      symm
      apply refinement.weight_eq e he b
      simpa [refinement.labels_eq e he] using hb
    _ = W.excess e := hsum

theorem interiorPairsMass_le_bandCharge
    {W : WindowSystem} {Z0 : ℕ}
    (refinement : InteriorRefinement W Z0)
    (hcomponentCap : ∀ e, e ∈ interiorPairs W Z0 →
      ∀ b ∈ refinement.blocks e.1,
        interiorComponentWeight (W.excess e) (refinement.blocks e.1) b ≤
          strictAnchorBlockCap refinement e.1) :
    interiorPairsMass W Z0 ≤
      (∑ key ∈ refinementBandKeys refinement,
        ((refinementSourceBandFinset refinement key.1 key.2).card : ℝ) *
          strictBandBlockCap W key.1) * thresholdLength W := by
  classical
  let I := interiorAnchorFinset W Z0
  let blockBound : ℕ → LowGapBlock → ℝ := fun k _ =>
    if k ∈ I then strictAnchorBlockCap refinement k else 0
  have hblockNonneg : ∀ k b, 0 ≤ blockBound k b := by
    intro k b
    dsimp [blockBound]
    split
    · unfold strictAnchorBlockCap
      positivity
    · positivity
  have hcomponentBound : ∀ e, e ∈ interiorPairs W Z0 →
      ∀ b ∈ refinement.blocks e.1,
        interiorComponentWeight (W.excess e) (refinement.blocks e.1) b ≤
          blockBound e.1 b := by
    intro e he b hb
    have hpair : e ∈ W.pairSet := interiorPairs_subset_pairSet W Z0 he
    have hanchor : e.1 ∈ W.anchors := by
      simpa [WindowSystem.pairSet_eq_prod] using hpair.1
    have hI : e.1 ∈ I := by
      change e.1 ∈ interiorAnchorFinset W Z0
      rw [interiorAnchorFinset, Finset.mem_filter]
      exact ⟨hanchor, ⟨e.2, he⟩⟩
    simpa [blockBound, hI] using hcomponentCap e he b hb
  have hmass := interiorPairsMass_le_refinementAnchorCharge refinement blockBound
    hblockNonneg (refinement.component_sum_eq) hcomponentBound
  have hanchorEq := anchorCharge_sum_eq_sourceCap_sum refinement
  have hbandEq := sourceCap_sum_eq_bandCap_sum refinement
  simpa [blockBound, I, hanchorEq, hbandEq] using hmass

def strictInteriorConstant {W : WindowSystem} {Z0 : ℕ}
    (refinement : InteriorRefinement W Z0) : ℝ :=
  32 * (W.structural.B + 2) *
    (W.rational.eta.den : ℝ) * (refinement.Cstep + 4)

theorem bandCharge_sum_le_reciprocalSqrt
    {W : WindowSystem} {Z0 : ℕ}
    (refinement : InteriorRefinement W Z0)
    (hentropy : ∀ key ∈ refinementBandKeys refinement,
      (encodingCandidates key.1 key.2 W.structural.B).Finite ∧
        ((encodingCandidates key.1 key.2 W.structural.B).ncard : ℝ) *
          Nat.ceil (Real.logb 2 (4 * key.1)) ≤ Real.sqrt key.1)
    (hfibres : ∀ key ∈ refinementBandKeys refinement,
      ∀ σ ∈ encodingCandidates key.1 key.2 W.structural.B,
        (spatialPreimage W.rational.eta.den refinement.gap.Cgap
            W.structural.B refinement.Cstep W Z0 refinement.selection σ).Finite ∧
          ((spatialPreimage W.rational.eta.den refinement.gap.Cgap
            W.structural.B refinement.Cstep W Z0 refinement.selection σ).ncard : ℝ) ≤
            (W.rational.eta.den : ℝ) * (refinement.Cstep + 4) *
              W.m * W.X / key.1) :
    (∑ key ∈ refinementBandKeys refinement,
        ((refinementSourceBandFinset refinement key.1 key.2).card : ℝ) *
          strictBandBlockCap W key.1) ≤
      strictInteriorConstant refinement * W.m * W.X *
        ∑ key ∈ refinementBandKeys refinement, 1 / Real.sqrt key.1 := by
  have hsum : (∑ key ∈ refinementBandKeys refinement,
      ((refinementSourceBandFinset refinement key.1 key.2).card : ℝ) *
        strictBandBlockCap W key.1) ≤
      ∑ key ∈ refinementBandKeys refinement,
        strictInteriorConstant refinement * W.m * W.X *
          (1 / Real.sqrt key.1) := by
    apply Finset.sum_le_sum
    intro key hkey
    have hD : 0 < key.1 := by
      rcases Finset.mem_image.mp hkey with ⟨kb, hkb, hkeyEq⟩
      have hpos := refinement.denominatorBand_pos kb.1
      have hDvalue : refinement.denominatorBand kb.1 = key.1 :=
        congrArg Prod.fst hkeyEq
      rw [← hDvalue]
      exact hpos
    have hfixed := fixedBandCharge_le_sqrt hD refinement
      (hentropy key hkey).1 (hentropy key hkey).2 (hfibres key hkey)
    calc
      ((refinementSourceBandFinset refinement key.1 key.2).card : ℝ) *
          strictBandBlockCap W key.1 ≤
        32 * (W.structural.B + 2) *
          ((W.rational.eta.den : ℝ) * (refinement.Cstep + 4) * W.m * W.X) /
            Real.sqrt key.1 := hfixed
      _ = strictInteriorConstant refinement * W.m * W.X *
          (1 / Real.sqrt key.1) := by
        unfold strictInteriorConstant
        ring
  calc
    (∑ key ∈ refinementBandKeys refinement,
        ((refinementSourceBandFinset refinement key.1 key.2).card : ℝ) *
          strictBandBlockCap W key.1) ≤
      ∑ key ∈ refinementBandKeys refinement,
        strictInteriorConstant refinement * W.m * W.X *
          (1 / Real.sqrt key.1) := hsum
    _ = strictInteriorConstant refinement * W.m * W.X *
        ∑ key ∈ refinementBandKeys refinement, 1 / Real.sqrt key.1 := by
      rw [Finset.mul_sum]

theorem bandEntropy_of_key_bounds
    {W : WindowSystem} {Z0 Zstar : ℕ} {cBand : ℝ}
    (refinement : InteriorRefinement W Z0)
    (hsignature : ∀ D Z : ℕ,
      Zstar ≤ Z → cBand * (2 : ℝ) ^ Z ≤ D →
        (encodingCandidates D Z W.structural.B).Finite ∧
          ((encodingCandidates D Z W.structural.B).ncard : ℝ) *
            Nat.ceil (Real.logb 2 (4 * D)) ≤ Real.sqrt D)
    (hZ : ∀ key ∈ refinementBandKeys refinement, Zstar ≤ key.2)
    (hD : ∀ key ∈ refinementBandKeys refinement,
      cBand * (2 : ℝ) ^ key.2 ≤ key.1) :
    ∀ key ∈ refinementBandKeys refinement,
      (encodingCandidates key.1 key.2 W.structural.B).Finite ∧
        ((encodingCandidates key.1 key.2 W.structural.B).ncard : ℝ) *
          Nat.ceil (Real.logb 2 (4 * key.1)) ≤ Real.sqrt key.1 := by
  intro key hkey
  have h := hsignature key.1 key.2 (hZ key hkey) (hD key hkey)
  exact h

theorem bandKeys_property_of_pairs
    {W : WindowSystem} {Z0 : ℕ}
    (refinement : InteriorRefinement W Z0) (P : ℕ → ℕ → Prop)
    (hP : ∀ e ∈ interiorPairs W Z0,
      P (refinement.denominatorBand e.1) (refinement.meanGap e.1)) :
    ∀ key ∈ refinementBandKeys refinement, P key.1 key.2 := by
  classical
  intro key hkey
  rcases Finset.mem_image.mp hkey with ⟨kb, hsource, hkeyEq⟩
  have hsourceData := (mem_refinementSourceFinset_iff refinement kb).mp hsource
  have hkInterior := hsourceData.1
  rw [interiorAnchorFinset, Finset.mem_filter] at hkInterior
  rcases hkInterior.2 with ⟨T, he⟩
  have hp := hP (kb.1, T) he
  have hD : refinement.denominatorBand kb.1 = key.1 :=
    congrArg Prod.fst hkeyEq
  have hZ : refinement.meanGap kb.1 = key.2 :=
    congrArg Prod.snd hkeyEq
  simpa [hD, hZ] using hp

def strictBandExponent (key : ℕ × ℕ) : ℕ := Nat.log 2 key.1

theorem bandKey_isPow
    {W : WindowSystem} {Z0 : ℕ}
    (refinement : InteriorRefinement W Z0)
    (key : ℕ × ℕ) (hkey : key ∈ refinementBandKeys refinement) :
    (∃ d : ℕ, key.1 = 2 ^ d) ∧ (∃ z : ℕ, key.2 = 2 ^ z) := by
  classical
  rcases Finset.mem_image.mp hkey with ⟨kb, hsource, hkeyEq⟩
  have hsourceData := (mem_refinementSourceFinset_iff refinement kb).mp hsource
  have hkInterior := hsourceData.1
  rw [interiorAnchorFinset, Finset.mem_filter] at hkInterior
  rcases hkInterior.2 with ⟨T, he⟩
  have hspatial := refinement.source_valid (kb.1, T) he kb.2 hsourceData.2
  change IsSpatialEncodingSource W.rational.eta.den refinement.gap.Cgap
    W.structural.B refinement.Cstep W Z0 refinement.selection
      (encodeBlock (refinement.denominatorBand kb.1)
        (refinement.meanGap kb.1) kb.2) kb at hspatial
  rcases hspatial with ⟨data, t, hrec, hparameter⟩
  have hcandidate := hrec.2.2.2.2.2.2.1
  have hvalidEncoding :
      (encodeBlock (refinement.denominatorBand kb.1)
        (refinement.meanGap kb.1) kb.2).Valid := hcandidate.1
  have hDpow : ∃ d : ℕ, refinement.denominatorBand kb.1 = 2 ^ d := by
    simpa [encodeBlock] using hvalidEncoding.1
  have hZpow : ∃ z : ℕ, refinement.meanGap kb.1 = 2 ^ z := by
    simpa [encodeBlock] using hvalidEncoding.2.1
  have hD : refinement.denominatorBand kb.1 = key.1 :=
    congrArg Prod.fst hkeyEq
  have hZ : refinement.meanGap kb.1 = key.2 :=
    congrArg Prod.snd hkeyEq
  simpa [hD, hZ] using And.intro hDpow hZpow

theorem bandKey_eq_two_pow_strictBandExponent
    {W : WindowSystem} {Z0 : ℕ}
    (refinement : InteriorRefinement W Z0)
    (key : ℕ × ℕ) (hkey : key ∈ refinementBandKeys refinement) :
    key.1 = 2 ^ strictBandExponent key := by
  rcases (bandKey_isPow refinement key hkey).1 with ⟨d, hd⟩
  have hlog : Nat.log 2 key.1 = d := by
    calc
      Nat.log 2 key.1 = Nat.log 2 (2 ^ d) := congrArg (Nat.log 2) hd
      _ = d := Nat.log_pow (by omega : 1 < 2) d
  calc
    key.1 = 2 ^ d := hd
    _ = 2 ^ strictBandExponent key := by rw [strictBandExponent, hlog]

theorem realMeanGapCutoff_implies_nat
    {Z0 Z : ℕ} (h : (Z0 : ℝ) / 32 < Z) : Z0 / 32 ≤ Z := by
  have hfloor : ((Z0 / 32 : ℕ) : ℝ) ≤ (Z0 : ℝ) / 32 :=
    Nat.cast_div_le
  exact_mod_cast (hfloor.trans h.le)

theorem bandFibres_of_globalSourceFibre
    {W : WindowSystem} {Z0 : ℕ}
    (refinement : InteriorRefinement W Z0)
    (hsource : ∀ selection : InteriorAnchorSelection,
      ValidInteriorAnchorSelection W.rational.eta.den W Z0 selection →
        ∀ σ : BlockEncoding,
          σ ∈ encodingCandidates σ.D σ.Z W.structural.B →
            0 < σ.D →
              (spatialPreimage W.rational.eta.den refinement.gap.Cgap
                  W.structural.B refinement.Cstep W Z0 selection σ).Finite ∧
                ((spatialPreimage W.rational.eta.den refinement.gap.Cgap
                  W.structural.B refinement.Cstep W Z0 selection σ).ncard : ℝ) ≤
                    (W.rational.eta.den : ℝ) * (refinement.Cstep + 4) *
                      W.m * W.X / σ.D) :
    ∀ key ∈ refinementBandKeys refinement,
      ∀ σ ∈ encodingCandidates key.1 key.2 W.structural.B,
        (spatialPreimage W.rational.eta.den refinement.gap.Cgap
            W.structural.B refinement.Cstep W Z0 refinement.selection σ).Finite ∧
          ((spatialPreimage W.rational.eta.den refinement.gap.Cgap
            W.structural.B refinement.Cstep W Z0 refinement.selection σ).ncard : ℝ) ≤
              (W.rational.eta.den : ℝ) * (refinement.Cstep + 4) *
                W.m * W.X / key.1 := by
  intro key hkey σ hσ
  have hσD : σ.D = key.1 := hσ.2.1
  have hσZ : σ.Z = key.2 := hσ.2.2.1
  have hσOwn : σ ∈ encodingCandidates σ.D σ.Z W.structural.B := by
    simpa [hσD, hσZ] using hσ
  have hDpos : 0 < σ.D := by
    rw [hσD]
    rcases Finset.mem_image.mp hkey with ⟨kb, hkb, hkeyEq⟩
    have hkeyD : refinement.denominatorBand kb.1 = key.1 :=
      congrArg Prod.fst hkeyEq
    rw [← hkeyD]
    exact refinement.denominatorBand_pos kb.1
  have h := hsource refinement.selection refinement.selection_valid σ hσOwn hDpos
  simpa [hσD] using h

theorem interiorPairsMass_le_tail
    {W : WindowSystem} {Z0 : ℕ}
    (refinement : InteriorRefinement W Z0)
    (hcomponentCap : ∀ e, e ∈ interiorPairs W Z0 →
      ∀ b ∈ refinement.blocks e.1,
        interiorComponentWeight (W.excess e) (refinement.blocks e.1) b ≤
          strictAnchorBlockCap refinement e.1)
    (hentropy : ∀ key ∈ refinementBandKeys refinement,
      (encodingCandidates key.1 key.2 W.structural.B).Finite ∧
        ((encodingCandidates key.1 key.2 W.structural.B).ncard : ℝ) *
          Nat.ceil (Real.logb 2 (4 * key.1)) ≤ Real.sqrt key.1)
    (hfibres : ∀ key ∈ refinementBandKeys refinement,
      ∀ σ ∈ encodingCandidates key.1 key.2 W.structural.B,
        (spatialPreimage W.rational.eta.den refinement.gap.Cgap
            W.structural.B refinement.Cstep W Z0 refinement.selection σ).Finite ∧
          ((spatialPreimage W.rational.eta.den refinement.gap.Cgap
            W.structural.B refinement.Cstep W Z0 refinement.selection σ).ncard : ℝ) ≤
              (W.rational.eta.den : ℝ) * (refinement.Cstep + 4) *
                W.m * W.X / key.1)
    (tail : ℝ) (htail :
      (∑ key ∈ refinementBandKeys refinement, 1 / Real.sqrt key.1) ≤ tail) :
    interiorPairsMass W Z0 ≤
      strictInteriorConstant refinement * tail * W.m * W.X * thresholdLength W := by
  have hmass := interiorPairsMass_le_bandCharge refinement hcomponentCap
  have hbands := bandCharge_sum_le_reciprocalSqrt refinement hentropy hfibres
  have hconstantNonneg : 0 ≤ strictInteriorConstant refinement := by
    unfold strictInteriorConstant
    have hB : 0 ≤ W.structural.B + 2 := by linarith [W.structural.B_gt]
    have hstep : 0 ≤ refinement.Cstep + 4 := by linarith [refinement.Cstep_pos]
    positivity
  have hmXNonneg : 0 ≤ strictInteriorConstant refinement * W.m * W.X := by
    exact mul_nonneg
      (mul_nonneg hconstantNonneg (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have hbandTail :
      (∑ key ∈ refinementBandKeys refinement,
        ((refinementSourceBandFinset refinement key.1 key.2).card : ℝ) *
          strictBandBlockCap W key.1) ≤
        strictInteriorConstant refinement * W.m * W.X * tail :=
    hbands.trans (mul_le_mul_of_nonneg_left htail hmXNonneg)
  have hlength : 0 ≤ thresholdLength W := by
    unfold thresholdLength
    exact mul_nonneg W.structural.cI_pos.le (Nat.cast_nonneg _)
  calc
    interiorPairsMass W Z0 ≤
        (∑ key ∈ refinementBandKeys refinement,
          ((refinementSourceBandFinset refinement key.1 key.2).card : ℝ) *
            strictBandBlockCap W key.1) * thresholdLength W := hmass
    _ ≤ (strictInteriorConstant refinement * W.m * W.X * tail) *
        thresholdLength W := mul_le_mul_of_nonneg_right hbandTail hlength
    _ = strictInteriorConstant refinement * tail * W.m * W.X *
        thresholdLength W := by ring
def strictBandPairTail (Z0 : ℕ) : ℝ :=
  strictMassOuterRatio⁻¹ * (1 - strictMassOuterRatio)⁻¹ * strictMassTail Z0

theorem strictBandPairTail_nonneg (Z0 : ℕ) : 0 ≤ strictBandPairTail Z0 := by
  unfold strictBandPairTail
  have houterInv : 0 ≤ strictMassOuterRatio⁻¹ :=
    inv_nonneg.mpr strictMassOuterRatio_nonneg
  have htailInv : 0 ≤ (1 - strictMassOuterRatio)⁻¹ :=
    inv_nonneg.mpr (sub_nonneg.mpr strictMassOuterRatio_le_one)
  exact mul_nonneg (mul_nonneg houterInv htailInv) (strictMassTail_nonneg Z0)

theorem strictBandPairTail_tendsto_zero :
    Tendsto strictBandPairTail atTop (𝓝 0) := by
  let C : ℝ := strictMassOuterRatio⁻¹ * (1 - strictMassOuterRatio)⁻¹
  have hconst : Tendsto (fun _ : ℕ => C) atTop (𝓝 C) := tendsto_const_nhds
  have h := hconst.mul strictMassTail_tendsto_zero
  change Tendsto (fun Z0 : ℕ =>
    strictMassOuterRatio⁻¹ * (1 - strictMassOuterRatio)⁻¹ *
      strictMassTail Z0) atTop (𝓝 0)
  simpa [C] using h
/-- Paper label: `thm:strict-mass` (Section 6).  A denominator-level cutoff
and one nonnegative coefficient function tending to zero are selected before
the compatible rational-support family.  At every cutoff beyond that fixed
threshold, all sufficiently large scales simultaneously carry an actual
interior refinement certificate and obey the strict interior mass bound. -/
theorem thm_strict_mass (context : FixedScaleContext) :
    ∃ Zmin : ℕ, ∃ ηQ : ℕ → ℝ, (∀ Z0, 0 ≤ ηQ Z0) ∧
      Tendsto ηQ atTop (𝓝 0) ∧
      ∀ Z0 : ℕ, Zmin ≤ Z0 →
        ∀ F : ScaleFamily, F.MatchesContext context →
          ∀ᶠ L : ℕ in atTop,
            ∃ _refinement : InteriorRefinement (F.system L) Z0,
              interiorPairsMass (F.system L) Z0 ≤
                ηQ Z0 * (F.system L).m * (F.system L).X *
                  thresholdLength (F.system L) := by
  obtain ⟨gap, Cstep, hCstep, Zcertificate, cBand, hcBand, hcertificate⟩ :=
    eventually_exists_interiorRefinement_certificate context
  obtain ⟨Zstar, CB, hCB, hsignature⟩ :=
    lem_signature_entropy context.structural.B cBand
      context.structural.B_gt hcBand
  obtain ⟨Ztail, htail⟩ :=
    exists_finite_dyadic_band_pair_tail_of_lower cBand hcBand
  obtain ⟨Zsource, hsource⟩ :=
    lem_source_fibre context gap Cstep hCstep
  let Zband := max Zstar Ztail
  let Zmin := max Zcertificate (max Zsource (32 * Zband))
  let Cmass : ℝ :=
    32 * (context.structural.B + 2) * (context.Q : ℝ) * (Cstep + 4)
  let ηQ : ℕ → ℝ := fun Z0 => Cmass * strictBandPairTail Z0
  have hCmass : 0 ≤ Cmass := by
    dsimp [Cmass]
    have hB : 0 ≤ context.structural.B + 2 := by
      linarith [context.structural.B_gt]
    have hstep : 0 ≤ Cstep + 4 := by linarith
    positivity
  have hηNonneg : ∀ Z0, 0 ≤ ηQ Z0 := by
    intro Z0
    exact mul_nonneg hCmass (strictBandPairTail_nonneg Z0)
  have hηTendsto : Tendsto ηQ atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℕ => Cmass) atTop (𝓝 Cmass) :=
      tendsto_const_nhds
    simpa [ηQ] using hconst.mul strictBandPairTail_tendsto_zero
  refine ⟨Zmin, ηQ, hηNonneg, hηTendsto, ?_⟩
  intro Z0 hZ0 F hF
  have hZcertificate : Zcertificate ≤ Z0 :=
    (le_max_left Zcertificate (max Zsource (32 * Zband))).trans hZ0
  have hZsource : Zsource ≤ Z0 :=
    (le_trans (le_max_left Zsource (32 * Zband))
      (le_max_right Zcertificate (max Zsource (32 * Zband)))).trans hZ0
  have hZbandScale : 32 * Zband ≤ Z0 :=
    (le_trans (le_max_right Zsource (32 * Zband))
      (le_max_right Zcertificate (max Zsource (32 * Zband)))).trans hZ0
  have hZbandBase : Zband ≤ Z0 / 32 := by
    exact (Nat.le_div_iff_mul_le (by omega : 0 < 32)).2
      (by simpa [Nat.mul_comm] using hZbandScale)
  filter_upwards [hcertificate Z0 hZcertificate F hF,
      hsource Z0 hZsource F hF] with L hcertificateL hsourceL
  rcases hcertificateL with ⟨refinement, hfacts⟩
  refine ⟨refinement, ?_⟩
  let W := F.system L
  have hstructural : W.structural = context.structural := by
    dsimp [W]
    rw [F.structural_eq, hF.2.1]
  have hdenominator : W.rational.eta.den = context.Q := by
    dsimp [W]
    rw [F.rational_eq]
    exact hF.1
  have hcomponentCap : ∀ e, e ∈ interiorPairs W Z0 →
      ∀ b ∈ refinement.blocks e.1,
        interiorComponentWeight (W.excess e) (refinement.blocks e.1) b ≤
          strictAnchorBlockCap refinement e.1 := by
    intro e he b hb
    simpa [strictAnchorBlockCap] using hfacts.component_bound e he b hb
  have hmeanKey : ∀ key ∈ refinementBandKeys refinement,
      (Z0 : ℝ) / 32 < key.2 :=
    bandKeys_property_of_pairs refinement
      (fun _ Z => (Z0 : ℝ) / 32 < Z)
      (by
        intro e he
        exact hfacts.meanGap_cutoff e he)
  have hdenKey : ∀ key ∈ refinementBandKeys refinement,
      cBand * (2 : ℝ) ^ key.2 ≤ key.1 :=
    bandKeys_property_of_pairs refinement
      (fun D Z => cBand * (2 : ℝ) ^ Z ≤ D)
      (by
        intro e he
        exact hfacts.denominator_lower e he)
  have hcutoffKey : ∀ key ∈ refinementBandKeys refinement,
      Z0 / 32 ≤ key.2 := by
    intro key hkey
    exact realMeanGapCutoff_implies_nat (hmeanKey key hkey)
  have hZstarKey : ∀ key ∈ refinementBandKeys refinement,
      Zstar ≤ key.2 := by
    intro key hkey
    exact (le_max_left Zstar Ztail).trans
      (hZbandBase.trans (hcutoffKey key hkey))
  have hZtailKey : ∀ key ∈ refinementBandKeys refinement,
      Ztail ≤ key.2 := by
    intro key hkey
    exact (le_max_right Zstar Ztail).trans
      (hZbandBase.trans (hcutoffKey key hkey))
  have hsignatureW : ∀ D Z : ℕ,
      Zstar ≤ Z → cBand * (2 : ℝ) ^ Z ≤ D →
        (encodingCandidates D Z W.structural.B).Finite ∧
          ((encodingCandidates D Z W.structural.B).ncard : ℝ) *
            Nat.ceil (Real.logb 2 (4 * D)) ≤ Real.sqrt D := by
    intro D Z hZ hD
    have h := hsignature D Z hZ hD
    rw [hstructural]
    exact ⟨h.1, h.2.2⟩
  have hentropy := bandEntropy_of_key_bounds refinement hsignatureW
    hZstarKey hdenKey
  have hsourceForRefinement :
      ∀ selection : InteriorAnchorSelection,
        ValidInteriorAnchorSelection W.rational.eta.den W Z0 selection →
          ∀ σ : BlockEncoding,
            σ ∈ encodingCandidates σ.D σ.Z W.structural.B →
              0 < σ.D →
                (spatialPreimage W.rational.eta.den refinement.gap.Cgap
                    W.structural.B refinement.Cstep W Z0 selection σ).Finite ∧
                  ((spatialPreimage W.rational.eta.den refinement.gap.Cgap
                    W.structural.B refinement.Cstep W Z0 selection σ).ncard : ℝ) ≤
                      (W.rational.eta.den : ℝ) * (refinement.Cstep + 4) *
                        W.m * W.X / σ.D := by
    intro selection hselection σ hσ hσD
    have hselectionContext :
        ValidInteriorAnchorSelection context.Q W Z0 selection := by
      simpa [hdenominator] using hselection
    have hσContext :
        σ ∈ encodingCandidates σ.D σ.Z context.structural.B := by
      simpa [hstructural] using hσ
    have h := hsourceL selection hselectionContext σ hσContext hσD
    simpa [hdenominator, hstructural, hfacts.gap_Cgap_eq,
      hfacts.Cstep_eq] using h
  have hfibres := bandFibres_of_globalSourceFibre refinement
    hsourceForRefinement
  have hdyadic : ∀ key ∈ refinementBandKeys refinement,
      key.1 = 2 ^ strictBandExponent key :=
    bandKey_eq_two_pow_strictBandExponent refinement
  have htailBound :
      (∑ key ∈ refinementBandKeys refinement, 1 / Real.sqrt key.1) ≤
        strictBandPairTail Z0 := by
    exact htail (refinementBandKeys refinement) strictBandExponent Z0
      hdyadic hcutoffKey hZtailKey hdenKey
  have hmass := interiorPairsMass_le_tail refinement hcomponentCap
    hentropy hfibres (strictBandPairTail Z0) htailBound
  have hconstant : strictInteriorConstant refinement = Cmass := by
    unfold strictInteriorConstant
    dsimp [Cmass]
    rw [hfacts.Cstep_eq, hstructural, hdenominator]
  simpa [W, hconstant, ηQ] using hmass

end Erdos260

/-! Source module: Erdos260/Exterior.lean -/

/-!
# Long-exterior contribution

This module corresponds to Section 7 of the manuscript.
-/

noncomputable section

open Filter MeasureTheory Set Topology Asymptotics
open scoped BigOperators ENNReal List

namespace Erdos260

/-- Exact distance from a real number to `[0,1]`. -/
def distanceToUnitInterval (μ : ℝ) : ℝ :=
  if μ < 0 then -μ else if 1 < μ then μ - 1 else 0

/-- The four first-exit tags. -/
inductive ExitTag
  | initialExterior
  | direct
  | boundaryZero
  | boundaryOne
  deriving DecidableEq, Repr

instance : Fintype ExitTag where
  elems := {.initialExterior, .direct, .boundaryZero, .boundaryOne}
  complete := by
    intro tag
    cases tag <;> simp

/-- Deterministic first-exit record from Appendix B. -/
@[ext] structure FirstExitRecord where
  interiorGaps : ℕ
  tag : ExitTag
  boundaryOnes : ℕ
  exitGap : ℕ
  deriving DecidableEq, Repr

namespace FirstExitRecord

def initialExterior : FirstExitRecord := ⟨0, .initialExterior, 0, 0⟩

/-- Region immediately before the first exterior state, encoded with the four
tags used in Appendix B.  The exterior case is unreachable for a certified
first exit and is mapped to `direct` so that this helper remains total. -/
def tagOfPreExitRegion : SlopeRegion → ExitTag
  | .interior => .direct
  | .boundaryZero => .boundaryZero
  | .boundaryOne => .boundaryOne
  | .exterior => .direct

/-- The deterministic record extracted from a concrete initial trajectory.
`before` is the exact word from the post-prefix occurrence line up to the
first exterior state. -/
def ofFirstExit (Q : ℕ) (base : AffineLine) (before : GapWord) :
    FirstExitRecord :=
  if _h : before = [] then initialExterior else
    { interiorGaps :=
        ((List.range before.length).filter fun r =>
          classifySlope
            ((base.transformWord Q (before.take r)).slope Q) = .interior).length
      tag := tagOfPreExitRegion
        (classifySlope
          ((base.transformWord Q before.dropLast).slope Q))
      boundaryOnes :=
        ((List.range before.length).filter fun r =>
          classifySlope
            ((base.transformWord Q (before.take r)).slope Q) =
              .boundaryOne).length
      exitGap := before.getLastD 0 }

@[simp] theorem ofFirstExit_nil (Q : ℕ) (base : AffineLine) :
    ofFirstExit Q base [] = initialExterior := by
  simp [ofFirstExit]

def Valid (m L Cgap : ℕ) (record : FirstExitRecord) : Prop :=
  record.interiorGaps ≤ m ∧ record.boundaryOnes ≤ m ∧
    (record.tag = .initialExterior → record = initialExterior) ∧
    (record.tag ≠ .initialExterior →
      1 ≤ record.exitGap ∧ record.exitGap ≤ L + Cgap + 1) ∧
    (record.tag = .boundaryOne → 2 ≤ record.exitGap)

/-- A record describes the actual first exterior state of the anchored suffix.
The pre-exit word and all line states are tied to the same occurrence and the
record is definitionally the deterministic value returned by `ofFirstExit`. -/
def DescribesFirstExit (W : WindowSystem) (Z0 : ℕ) (e : WindowThreshold)
    (record : FirstExitRecord) (line : AffineLine)
    (continuation : GapWord) : Prop :=
  ∃ base finish : AffineLine, ∃ before after : GapWord,
    IsOccurrenceLine W Z0 (initialLongPrefix W e.1) base ∧
      actualPostPrefixGaps W e.1 = before ++ continuation ++ after ∧
      SharedGapTrajectory W.rational.eta.den base before line ∧
      SharedGapTrajectory W.rational.eta.den line continuation finish ∧
      classifySlope (line.slope W.rational.eta.den) = .exterior ∧
      (∀ r < before.length, ∃ state : AffineLine,
        SharedGapTrajectory W.rational.eta.den base (before.take r) state ∧
          classifySlope (state.slope W.rational.eta.den) ≠ .exterior) ∧
      record = ofFirstExit W.rational.eta.den base before

end FirstExitRecord

/-- Enlarged admissible carry corridor at one scale. -/
def InAdmissibleCarryRegion (Q X : ℕ) (x r : ℤ) : Prop :=
  -(X : ℤ) ≤ x ∧ x ≤ 3 * X ∧ 0 ≤ r ∧ r ≤ (Q : ℤ) * (x + 2)

/-- Original integer parameters whose points are admissible before and after a
fixed shared continuation.  No primitive reparameterization is performed. -/
def admissibleOriginalParameters (Q X : ℕ) (line : AffineLine)
    (word : GapWord) : Set ℤ :=
  {t |
    InAdmissibleCarryRegion Q X
      (line.A + line.H * t) (line.C + line.K * t) ∧
    let finish := line.transformWord Q word
    InAdmissibleCarryRegion Q X
      (finish.A + finish.H * t) (finish.C + finish.K * t)}

/-- Exterior-prefix exponent `δ_ext`. -/
def exteriorPrefixExponent (p : EntropyParams) : ℝ :=
  (p.structural.Gamma + 1) *
    binaryEntropy (p.kappa / (p.structural.Gamma + 1))

/-- Paper label: `lem:off-amplify` (Section 7). -/
theorem lem_off_amplify (μ : ℝ) (g : ℕ) (hg : 1 ≤ g)
    (hμ : μ ∉ Set.Icc (0 : ℝ) 1) :
    (2 : ℝ) ^ g * distanceToUnitInterval μ ≤
      distanceToUnitInterval ((2 : ℝ) ^ g * μ - 1) := by
  have hpow0 : 0 < (2 : ℝ) ^ g := pow_pos (by norm_num) _
  have hpow2 : (2 : ℝ) ≤ (2 : ℝ) ^ g := by
    simpa using (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hg)
  by_cases hneg : μ < 0
  · have hnext : (2 : ℝ) ^ g * μ - 1 < 0 := by
      nlinarith [mul_neg_of_pos_of_neg hpow0 hneg]
    rw [distanceToUnitInterval, if_pos hneg]
    rw [distanceToUnitInterval, if_pos hnext]
    linarith
  · have hnonneg : 0 ≤ μ := le_of_not_gt hneg
    have hgt : 1 < μ := by
      by_contra hnot
      exact hμ ⟨hnonneg, le_of_not_gt hnot⟩
    have hnext : 1 < (2 : ℝ) ^ g * μ - 1 := by
      nlinarith [mul_le_mul_of_nonneg_right hpow2 hnonneg]
    rw [distanceToUnitInterval, if_neg hneg, if_pos hgt]
    rw [distanceToUnitInterval, if_neg (not_lt_of_ge (le_trans (by norm_num) hnext.le)),
      if_pos hnext]
    nlinarith

theorem classifySlope_exterior_not_mem (μ : ℚ)
    (h : classifySlope μ = .exterior) :
    (μ : ℝ) ∉ Set.Icc (0 : ℝ) 1 := by
  intro hmem
  have hmemQ : μ ∈ Set.Icc (0 : ℚ) 1 := by
    exact ⟨by exact_mod_cast hmem.1, by exact_mod_cast hmem.2⟩
  rcases hmemQ with ⟨hμ0, hμ1⟩
  unfold classifySlope at h
  by_cases h0 : μ = 0
  · simp [h0] at h
  by_cases h1 : μ = 1
  · simp [h1] at h
  have hinterior : 0 < μ ∧ μ < 1 :=
    ⟨lt_of_le_of_ne hμ0 (Ne.symm h0), lt_of_le_of_ne hμ1 h1⟩
  simp [h0, h1, hinterior] at h

/-- For a fixed transition word, changing the raw occurrence-line
parameterization without changing its normalized slope leaves the deterministic
first-exit record unchanged. -/
theorem FirstExitRecord.ofFirstExit_eq_of_slope_eq (Q : ℕ) (hQ : 0 < Q)
    (left right : AffineLine) (before : GapWord)
    (hslope : left.slope Q = right.slope Q) :
    FirstExitRecord.ofFirstExit Q left before =
      FirstExitRecord.ofFirstExit Q right before := by
  by_cases hnil : before = []
  · subst before
    simp [FirstExitRecord.ofFirstExit]
  · rw [FirstExitRecord.ofFirstExit, dif_neg hnil,
      FirstExitRecord.ofFirstExit, dif_neg hnil]
    have hstate (r : ℕ) :
        classifySlope ((left.transformWord Q (before.take r)).slope Q) =
          classifySlope ((right.transformWord Q (before.take r)).slope Q) :=
      congrArg classifySlope
        (AffineLine.transformWord_slope_eq_of_slope_eq Q hQ left right
          (before.take r) hslope)
    have hlast :
        classifySlope ((left.transformWord Q before.dropLast).slope Q) =
          classifySlope ((right.transformWord Q before.dropLast).slope Q) :=
      congrArg classifySlope
        (AffineLine.transformWord_slope_eq_of_slope_eq Q hQ left right
          before.dropLast hslope)
    simp_rw [hstate]
    rw [hlast]

/-- A shared-gap trajectory has no hidden choice: its terminal line is the
iterated affine transform of its initial line. -/
theorem sharedGapTrajectory_iff_eq_transformWord (Q : ℕ)
    (line finish : AffineLine) (word : GapWord) :
    SharedGapTrajectory Q line word finish ↔
      finish = line.transformWord Q word := by
  constructor
  · intro h
    induction h with
    | nil => rfl
    | cons line next finish g gs hnext htail ih =>
        subst next
        simpa only [AffineLine.transformWord] using ih
  · intro h
    subst finish
    induction word generalizing line with
    | nil => exact SharedGapTrajectory.nil line
    | cons g gs ih =>
        exact SharedGapTrajectory.cons line (line.transform Q g)
          ((line.transform Q g).transformWord Q gs) g gs rfl
          (ih (line.transform Q g))

/-! ### Deterministic reconstruction of the first-exit word

The polynomial first-exit record is useful in the exterior fibre count only
because, once the initial occurrence line is fixed, it reconstructs the
whole transition word.  The next lemmas make that assertion explicit rather
than treating it as an informal property of the record. -/

private def preExitRegionCount (Q : ℕ) (base : AffineLine)
    (word : GapWord) (region : SlopeRegion) : ℕ :=
  (List.range word.length).countP fun r =>
    classifySlope ((base.transformWord Q (word.take r)).slope Q) = region

private theorem countP_congr_of_mem {α : Type*} (l : List α)
    (p q : α → Bool) (h : ∀ x ∈ l, p x = q x) :
    l.countP p = l.countP q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      rw [List.countP_cons, List.countP_cons, h a (by simp)]
      exact congrArg (fun n => n + if q a = true then 1 else 0)
        (ih fun x hx => h x (by simp [hx]))

@[simp] private theorem preExitRegionCount_cons (Q g : ℕ)
    (base : AffineLine) (word : GapWord) (region : SlopeRegion) :
    preExitRegionCount Q base (g :: word) region =
      (if classifySlope (base.slope Q) = region then 1 else 0) +
        preExitRegionCount Q (base.transform Q g) word region := by
  unfold preExitRegionCount
  rw [List.length_cons, List.range_succ_eq_map, List.countP_cons,
    List.countP_map]
  have htail := countP_congr_of_mem (List.range word.length)
    ((fun r => decide
      (classifySlope
        ((base.transformWord Q ((g :: word).take r)).slope Q) = region)) ∘
      Nat.succ)
    (fun r => decide
      (classifySlope
        (((base.transform Q g).transformWord Q (word.take r)).slope Q) =
          region))
    (by
      intro r hr
      simp only [Function.comp_apply, List.take_succ_cons,
        AffineLine.transformWord])
  rw [htail]
  simp only [List.take_zero, AffineLine.transformWord, decide_eq_true_eq]
  omega

private def IsFirstExitWord (Q : ℕ) (base : AffineLine)
    (word : GapWord) : Prop :=
  word.Positive ∧
    (∀ r < word.length,
      classifySlope ((base.transformWord Q (word.take r)).slope Q) ≠
        .exterior) ∧
    classifySlope ((base.transformWord Q word).slope Q) = .exterior

private theorem classifySlope_interior_iff (μ : ℚ) :
    classifySlope μ = .interior ↔ 0 < μ ∧ μ < 1 := by
  unfold classifySlope
  by_cases h0 : μ = 0
  · simp [h0]
  by_cases h1 : μ = 1
  · simp [h1]
  simp [h0, h1]

private theorem classifySlope_boundaryZero_iff (μ : ℚ) :
    classifySlope μ = .boundaryZero ↔ μ = 0 := by
  constructor
  · intro h
    by_contra h0
    unfold classifySlope at h
    rw [if_neg h0] at h
    by_cases h1 : μ = 1
    · rw [if_pos h1] at h
      contradiction
    · rw [if_neg h1] at h
      by_cases hi : 0 < μ ∧ μ < 1
      · rw [if_pos hi] at h
        contradiction
      · rw [if_neg hi] at h
        contradiction
  · rintro rfl
    simp [classifySlope]

private theorem classifySlope_boundaryOne_iff (μ : ℚ) :
    classifySlope μ = .boundaryOne ↔ μ = 1 := by
  constructor
  · intro h
    by_contra h1
    unfold classifySlope at h
    by_cases h0 : μ = 0
    · simp [h0] at h
    simp only [h0, h1, if_false] at h
    split at h <;> contradiction
  · rintro rfl
    simp [classifySlope]

private theorem classifySlope_ne_exterior_iff (μ : ℚ) :
    classifySlope μ ≠ .exterior ↔ 0 ≤ μ ∧ μ ≤ 1 := by
  constructor
  · intro h
    cases hregion : classifySlope μ with
    | interior =>
        have hi := (classifySlope_interior_iff μ).mp hregion
        exact ⟨hi.1.le, hi.2.le⟩
    | boundaryZero =>
        rw [(classifySlope_boundaryZero_iff μ).mp hregion]
        norm_num
    | boundaryOne =>
        rw [(classifySlope_boundaryOne_iff μ).mp hregion]
        norm_num
    | exterior => exact (h hregion).elim
  · rintro ⟨h0, h1⟩ hext
    apply classifySlope_exterior_not_mem μ hext
    exact ⟨by exact_mod_cast h0, by exact_mod_cast h1⟩

private theorem IsFirstExitWord.tail {Q g : ℕ} {base : AffineLine}
    {word : GapWord} (h : IsFirstExitWord Q base (g :: word)) :
    IsFirstExitWord Q (base.transform Q g) word := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact h.1 x (by simp [hx])
  · intro r hr
    have hproper := h.2.1 (r + 1) (by simp; omega)
    simpa only [List.take_succ_cons, AffineLine.transformWord] using hproper
  · simpa only [AffineLine.transformWord] using h.2.2

private theorem IsFirstExitWord.base_nonexterior {Q : ℕ}
    {base : AffineLine} {word : GapWord} (hword : word ≠ [])
    (h : IsFirstExitWord Q base word) :
    classifySlope (base.slope Q) ≠ .exterior := by
  have hlen : 0 < word.length := List.length_pos_iff.mpr hword
  simpa only [List.take_zero, AffineLine.transformWord] using h.2.1 0 hlen

private theorem IsFirstExitWord.head_positive {Q g : ℕ}
    {base : AffineLine} {word : GapWord}
    (h : IsFirstExitWord Q base (g :: word)) : 1 ≤ g := by
  exact h.1 g (by simp)

private theorem transform_boundaryZero_exterior (Q g : ℕ) (hQ : 0 < Q)
    (base : AffineLine)
    (hbase : classifySlope (base.slope Q) = .boundaryZero) :
    classifySlope ((base.transform Q g).slope Q) = .exterior := by
  have hslope : base.slope Q = 0 :=
    (classifySlope_boundaryZero_iff _).mp hbase
  rw [AffineLine.slope_transform Q hQ, hslope]
  norm_num [classifySlope]

private theorem transform_boundaryOne_of_nonexterior (Q g : ℕ)
    (hQ : 0 < Q) (base : AffineLine) (hg : 1 ≤ g)
    (hbase : classifySlope (base.slope Q) = .boundaryOne)
    (hnext : classifySlope ((base.transform Q g).slope Q) ≠ .exterior) :
    g = 1 ∧
      classifySlope ((base.transform Q g).slope Q) = .boundaryOne := by
  have hslope : base.slope Q = 1 :=
    (classifySlope_boundaryOne_iff _).mp hbase
  have hbounds := (classifySlope_ne_exterior_iff _).mp hnext
  have hformula := AffineLine.slope_transform Q hQ base g
  have hg_one : g = 1 := by
    by_contra hne
    have hg_two : 2 ≤ g := by omega
    have hpow : (2 : ℚ) ^ 2 ≤ (2 : ℚ) ^ g :=
      pow_le_pow_right₀ (by norm_num) hg_two
    rw [hslope] at hformula
    norm_num at hformula
    nlinarith
  subst g
  refine ⟨rfl, ?_⟩
  rw [AffineLine.slope_transform Q hQ, hslope]
  norm_num [classifySlope]

private theorem firstExit_boundaryZero_singleton (Q : ℕ) (hQ : 0 < Q)
    (base : AffineLine) (word : GapWord)
    (hbase : classifySlope (base.slope Q) = .boundaryZero)
    (hword : IsFirstExitWord Q base word) :
    ∃ g : ℕ, word = [g] := by
  cases word with
  | nil =>
      have := hword.2.2
      simp only [AffineLine.transformWord] at this
      rw [hbase] at this
      contradiction
  | cons g gs =>
      refine ⟨g, ?_⟩
      by_contra hne
      have hgs : gs ≠ [] := by
        intro hnil
        subst gs
        exact hne rfl
      have hproper :
          classifySlope ((base.transform Q g).slope Q) ≠ .exterior := by
        have hlt : 1 < (g :: gs).length := by
          simp only [List.length_cons]
          exact Nat.succ_lt_succ (List.length_pos_iff.mpr hgs)
        simpa only [List.take_succ_cons, List.take_zero,
          AffineLine.transformWord] using hword.2.1 1 hlt
      exact hproper (transform_boundaryZero_exterior Q g hQ base hbase)

private theorem firstExit_boundaryOne_all_states (Q : ℕ) (hQ : 0 < Q) :
    ∀ (base : AffineLine) (word : GapWord),
      classifySlope (base.slope Q) = .boundaryOne →
      IsFirstExitWord Q base word →
      ∀ r < word.length,
        classifySlope ((base.transformWord Q (word.take r)).slope Q) =
          .boundaryOne := by
  intro base word
  induction word generalizing base with
  | nil => simp
  | cons g gs ih =>
      intro hbase hword r hr
      cases r with
      | zero => simpa only [List.take_zero, AffineLine.transformWord] using hbase
      | succ r =>
          have hrTail : r < gs.length := by simpa using hr
          have hgs : gs ≠ [] := List.ne_nil_of_length_pos (lt_of_le_of_lt
            (Nat.zero_le r) hrTail)
          have hnextNonexterior :
              classifySlope ((base.transform Q g).slope Q) ≠ .exterior := by
            have hlt : 1 < (g :: gs).length := by
              simp only [List.length_cons]
              exact Nat.succ_lt_succ (List.length_pos_iff.mpr hgs)
            simpa only [List.take_succ_cons, List.take_zero,
              AffineLine.transformWord] using hword.2.1 1 hlt
          have hnext := transform_boundaryOne_of_nonexterior Q g hQ base
            hword.head_positive hbase hnextNonexterior
          simpa only [List.take_succ_cons, AffineLine.transformWord] using
            ih (base.transform Q g) hnext.2 hword.tail r hrTail

private theorem firstExit_boundaryOne_head_eq_one (Q : ℕ) (hQ : 0 < Q)
    (base : AffineLine) (g : ℕ) (tail : GapWord)
    (htail : tail ≠ [])
    (hbase : classifySlope (base.slope Q) = .boundaryOne)
    (hword : IsFirstExitWord Q base (g :: tail)) : g = 1 := by
  have hnextNonexterior :
      classifySlope ((base.transform Q g).slope Q) ≠ .exterior := by
    have hlt : 1 < (g :: tail).length := by
      simp only [List.length_cons]
      exact Nat.succ_lt_succ (List.length_pos_iff.mpr htail)
    simpa only [List.take_succ_cons, List.take_zero,
      AffineLine.transformWord] using hword.2.1 1 hlt
  exact (transform_boundaryOne_of_nonexterior Q g hQ base
    hword.head_positive hbase hnextNonexterior).1

private theorem preExitRegionCount_interior_eq_zero_of_boundary
    (Q : ℕ) (hQ : 0 < Q) (base : AffineLine) (word : GapWord)
    (hbase : classifySlope (base.slope Q) = .boundaryZero ∨
      classifySlope (base.slope Q) = .boundaryOne)
    (hword : IsFirstExitWord Q base word) :
    preExitRegionCount Q base word .interior = 0 := by
  have hall : ∀ r < word.length,
      classifySlope ((base.transformWord Q (word.take r)).slope Q) ≠
        .interior := by
    rcases hbase with hzero | hone
    · obtain ⟨g, rfl⟩ :=
        firstExit_boundaryZero_singleton Q hQ base word hzero hword
      intro r hr
      have hr0 : r = 0 := by simp at hr; omega
      subst r
      simp only [List.take_zero, AffineLine.transformWord]
      rw [hzero]
      decide
    · intro r hr
      rw [firstExit_boundaryOne_all_states Q hQ base word hone hword r hr]
      decide
  rw [preExitRegionCount, List.countP_eq_zero]
  intro r hr
  have hrlt : r < word.length := List.mem_range.mp hr
  simp only [decide_eq_true_eq]
  exact hall r hrlt

private theorem firstExit_boundary_tag (Q : ℕ) (hQ : 0 < Q)
    (base : AffineLine) (word : GapWord) (hwordNonempty : word ≠ [])
    (hword : IsFirstExitWord Q base word) :
    (classifySlope (base.slope Q) = .boundaryZero →
        (FirstExitRecord.ofFirstExit Q base word).tag = .boundaryZero) ∧
      (classifySlope (base.slope Q) = .boundaryOne →
        (FirstExitRecord.ofFirstExit Q base word).tag = .boundaryOne) := by
  constructor
  · intro hzero
    obtain ⟨g, rfl⟩ :=
      firstExit_boundaryZero_singleton Q hQ base word hzero hword
    rw [FirstExitRecord.ofFirstExit, dif_neg (by simp)]
    change FirstExitRecord.tagOfPreExitRegion
      (classifySlope ((base.transformWord Q [g].dropLast).slope Q)) =
        .boundaryZero
    simp only [List.dropLast, AffineLine.transformWord]
    rw [hzero]
    rfl
  · intro hone
    have hlastIndex : word.length - 1 < word.length := by
      exact Nat.sub_lt (List.length_pos_iff.mpr hwordNonempty) (by omega)
    have hlast := firstExit_boundaryOne_all_states Q hQ base word hone hword
      (word.length - 1) hlastIndex
    have hdrop : classifySlope
        ((base.transformWord Q word.dropLast).slope Q) = .boundaryOne := by
      simpa only [List.dropLast_eq_take] using hlast
    simp [FirstExitRecord.ofFirstExit, hwordNonempty,
      FirstExitRecord.tagOfPreExitRegion, hdrop]

private theorem FirstExitRecord.ofFirstExit_interiorGaps (Q : ℕ)
    (base : AffineLine) (word : GapWord) (hword : word ≠ []) :
    (FirstExitRecord.ofFirstExit Q base word).interiorGaps =
      preExitRegionCount Q base word .interior := by
  rw [FirstExitRecord.ofFirstExit, dif_neg hword]
  change (List.filter _ (List.range word.length)).length = _
  rw [← List.countP_eq_length_filter]
  rfl

private theorem FirstExitRecord.ofFirstExit_boundaryOnes (Q : ℕ)
    (base : AffineLine) (word : GapWord) (hword : word ≠ []) :
    (FirstExitRecord.ofFirstExit Q base word).boundaryOnes =
      preExitRegionCount Q base word .boundaryOne := by
  rw [FirstExitRecord.ofFirstExit, dif_neg hword]
  change (List.filter _ (List.range word.length)).length = _
  rw [← List.countP_eq_length_filter]
  rfl

private theorem FirstExitRecord.ofFirstExit_tag_cons (Q g : ℕ)
    (base : AffineLine) (tail : GapWord) (htail : tail ≠ []) :
    (FirstExitRecord.ofFirstExit Q base (g :: tail)).tag =
      (FirstExitRecord.ofFirstExit Q (base.transform Q g) tail).tag := by
  cases tail with
  | nil => exact (htail rfl).elim
  | cons x xs =>
      simp [FirstExitRecord.ofFirstExit, AffineLine.transformWord]

private theorem FirstExitRecord.ofFirstExit_exitGap_cons (Q g : ℕ)
    (base : AffineLine) (tail : GapWord) (htail : tail ≠ []) :
    (FirstExitRecord.ofFirstExit Q base (g :: tail)).exitGap =
      (FirstExitRecord.ofFirstExit Q (base.transform Q g) tail).exitGap := by
  cases tail with
  | nil => exact (htail rfl).elim
  | cons x xs => simp [FirstExitRecord.ofFirstExit]

private theorem FirstExitRecord.tail_eq_of_cons_record_eq (Q g : ℕ)
    (base : AffineLine) (left right : GapWord)
    (hleft : left ≠ []) (hright : right ≠ [])
    (hrecord : FirstExitRecord.ofFirstExit Q base (g :: left) =
      FirstExitRecord.ofFirstExit Q base (g :: right)) :
    FirstExitRecord.ofFirstExit Q (base.transform Q g) left =
      FirstExitRecord.ofFirstExit Q (base.transform Q g) right := by
  apply FirstExitRecord.ext
  · have hfield := congrArg FirstExitRecord.interiorGaps hrecord
    rw [FirstExitRecord.ofFirstExit_interiorGaps Q base _ (by simp),
      FirstExitRecord.ofFirstExit_interiorGaps Q base _ (by simp),
      preExitRegionCount_cons, preExitRegionCount_cons] at hfield
    rw [FirstExitRecord.ofFirstExit_interiorGaps Q (base.transform Q g) left
      hleft, FirstExitRecord.ofFirstExit_interiorGaps Q (base.transform Q g)
      right hright]
    omega
  · simpa only [FirstExitRecord.ofFirstExit_tag_cons Q g base left hleft,
      FirstExitRecord.ofFirstExit_tag_cons Q g base right hright] using
      congrArg FirstExitRecord.tag hrecord
  · have hfield := congrArg FirstExitRecord.boundaryOnes hrecord
    rw [FirstExitRecord.ofFirstExit_boundaryOnes Q base _ (by simp),
      FirstExitRecord.ofFirstExit_boundaryOnes Q base _ (by simp),
      preExitRegionCount_cons, preExitRegionCount_cons] at hfield
    rw [FirstExitRecord.ofFirstExit_boundaryOnes Q (base.transform Q g) left
      hleft, FirstExitRecord.ofFirstExit_boundaryOnes Q (base.transform Q g)
      right hright]
    omega
  · simpa only [FirstExitRecord.ofFirstExit_exitGap_cons Q g base left hleft,
      FirstExitRecord.ofFirstExit_exitGap_cons Q g base right hright] using
      congrArg FirstExitRecord.exitGap hrecord

private theorem positive_gap_eq_of_same_nonexterior_region
    (Q : ℕ) (hQ : 0 < Q) (base : AffineLine) (g h : ℕ)
    (hg : 1 ≤ g) (hh : 1 ≤ h)
    (hbase : classifySlope (base.slope Q) = .interior)
    (region : SlopeRegion) (hregion : region ≠ .exterior)
    (hgRegion : classifySlope ((base.transform Q g).slope Q) = region)
    (hhRegion : classifySlope ((base.transform Q h).slope Q) = region) :
    g = h := by
  have hbaseIrat := (classifySlope_interior_iff _).mp hbase
  have hbaseIreal : (base.slope Q : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
    exact ⟨by exact_mod_cast hbaseIrat.1, by exact_mod_cast hbaseIrat.2⟩
  cases region with
  | interior =>
      apply lem_strict_unique (base.slope Q : ℝ) hbaseIreal
      · refine ⟨hg, ?_⟩
        have hnextRat := (classifySlope_interior_iff _).mp hgRegion
        have hnextReal :
            (((base.transform Q g).slope Q : ℚ) : ℝ) ∈ Set.Ioo 0 1 := by
          exact ⟨by exact_mod_cast hnextRat.1,
            by exact_mod_cast hnextRat.2⟩
        simpa only [AffineLine.transform_slope_real Q g hQ base] using hnextReal
      · refine ⟨hh, ?_⟩
        have hnextRat := (classifySlope_interior_iff _).mp hhRegion
        have hnextReal :
            (((base.transform Q h).slope Q : ℚ) : ℝ) ∈ Set.Ioo 0 1 := by
          exact ⟨by exact_mod_cast hnextRat.1,
            by exact_mod_cast hnextRat.2⟩
        simpa only [AffineLine.transform_slope_real Q h hQ base] using hnextReal
  | boundaryZero =>
      have hgSlope : (base.transform Q g).slope Q = 0 :=
        (classifySlope_boundaryZero_iff _).mp hgRegion
      have hhSlope : (base.transform Q h).slope Q = 0 :=
        (classifySlope_boundaryZero_iff _).mp hhRegion
      have hgFormula := AffineLine.slope_transform Q hQ base g
      have hhFormula := AffineLine.slope_transform Q hQ base h
      have hpows : (2 : ℚ) ^ g = (2 : ℚ) ^ h := by
        nlinarith [hbaseIrat.1]
      have hpowsNat : (2 : ℕ) ^ g = 2 ^ h := by exact_mod_cast hpows
      exact Nat.pow_right_injective (by norm_num) hpowsNat
  | boundaryOne =>
      have hgSlope : (base.transform Q g).slope Q = 1 :=
        (classifySlope_boundaryOne_iff _).mp hgRegion
      have hhSlope : (base.transform Q h).slope Q = 1 :=
        (classifySlope_boundaryOne_iff _).mp hhRegion
      have hgFormula := AffineLine.slope_transform Q hQ base g
      have hhFormula := AffineLine.slope_transform Q hQ base h
      have hpows : (2 : ℚ) ^ g = (2 : ℚ) ^ h := by
        nlinarith [hbaseIrat.1]
      have hpowsNat : (2 : ℕ) ^ g = 2 ^ h := by exact_mod_cast hpows
      exact Nat.pow_right_injective (by norm_num) hpowsNat
  | exterior => exact (hregion rfl).elim

private theorem preExitRegionCount_pos_of_base_region (Q : ℕ)
    (base : AffineLine) (word : GapWord) (region : SlopeRegion)
    (hword : word ≠ []) (hbase : classifySlope (base.slope Q) = region) :
    0 < preExitRegionCount Q base word region := by
  cases word with
  | nil => exact (hword rfl).elim
  | cons g tail =>
      rw [preExitRegionCount_cons, hbase]
      simp

private theorem FirstExitRecord.ofFirstExit_tag_singleton (Q g : ℕ)
    (base : AffineLine) :
    (FirstExitRecord.ofFirstExit Q base [g]).tag =
      FirstExitRecord.tagOfPreExitRegion (classifySlope (base.slope Q)) := by
  rw [FirstExitRecord.ofFirstExit, dif_neg (by simp)]
  rfl

private theorem IsFirstExitWord.next_nonexterior {Q g : ℕ}
    {base : AffineLine} {tail : GapWord} (htail : tail ≠ [])
    (hword : IsFirstExitWord Q base (g :: tail)) :
    classifySlope ((base.transform Q g).slope Q) ≠ .exterior := by
  have hlt : 1 < (g :: tail).length := by
    simp only [List.length_cons]
    exact Nat.succ_lt_succ (List.length_pos_iff.mpr htail)
  simpa only [List.take_succ_cons, List.take_zero,
    AffineLine.transformWord] using hword.2.1 1 hlt

private theorem singleton_record_ne_long_firstExit (Q : ℕ) (hQ : 0 < Q)
    (base : AffineLine) (g h : ℕ) (tail : GapWord) (htail : tail ≠ [])
    (hsingle : IsFirstExitWord Q base [g])
    (hlong : IsFirstExitWord Q base (h :: tail)) :
    FirstExitRecord.ofFirstExit Q base [g] ≠
      FirstExitRecord.ofFirstExit Q base (h :: tail) := by
  intro hrecord
  have hbaseNon := hsingle.base_nonexterior (by simp)
  cases hbaseRegion : classifySlope (base.slope Q) with
  | exterior => exact hbaseNon hbaseRegion
  | boundaryZero =>
      obtain ⟨x, hshape⟩ := firstExit_boundaryZero_singleton Q hQ base
        (h :: tail) hbaseRegion hlong
      have : tail = [] := by simpa using congrArg List.tail hshape
      exact htail this
  | boundaryOne =>
      have hnext := transform_boundaryOne_of_nonexterior Q h hQ base
        hlong.head_positive hbaseRegion (hlong.next_nonexterior htail)
      have hleftCount :
          (FirstExitRecord.ofFirstExit Q base [g]).boundaryOnes = 1 := by
        rw [FirstExitRecord.ofFirstExit_boundaryOnes Q base [g] (by simp),
          preExitRegionCount_cons, hbaseRegion]
        simp [preExitRegionCount]
      have htailPositive : 0 < preExitRegionCount Q (base.transform Q h)
          tail .boundaryOne :=
        preExitRegionCount_pos_of_base_region Q (base.transform Q h) tail
          .boundaryOne htail hnext.2
      have hrightCount : 2 ≤
          (FirstExitRecord.ofFirstExit Q base (h :: tail)).boundaryOnes := by
        rw [FirstExitRecord.ofFirstExit_boundaryOnes Q base (h :: tail)
          (by simp), preExitRegionCount_cons, hbaseRegion]
        simpa [Nat.add_comm] using Nat.succ_le_succ htailPositive
      have hfield := congrArg FirstExitRecord.boundaryOnes hrecord
      omega
  | interior =>
      have hnextNon := hlong.next_nonexterior htail
      cases hnextRegion : classifySlope ((base.transform Q h).slope Q) with
      | exterior => exact hnextNon hnextRegion
      | interior =>
          have hleftCount :
              (FirstExitRecord.ofFirstExit Q base [g]).interiorGaps = 1 := by
            rw [FirstExitRecord.ofFirstExit_interiorGaps Q base [g] (by simp),
              preExitRegionCount_cons, hbaseRegion]
            simp [preExitRegionCount]
          have htailPositive : 0 < preExitRegionCount Q (base.transform Q h)
              tail .interior :=
            preExitRegionCount_pos_of_base_region Q (base.transform Q h) tail
              .interior htail hnextRegion
          have hrightCount : 2 ≤
              (FirstExitRecord.ofFirstExit Q base (h :: tail)).interiorGaps := by
            rw [FirstExitRecord.ofFirstExit_interiorGaps Q base (h :: tail)
              (by simp), preExitRegionCount_cons, hbaseRegion]
            simpa [Nat.add_comm] using Nat.succ_le_succ htailPositive
          have hfield := congrArg FirstExitRecord.interiorGaps hrecord
          omega
      | boundaryZero =>
          have hleftTag : (FirstExitRecord.ofFirstExit Q base [g]).tag =
              .direct := by
            rw [FirstExitRecord.ofFirstExit_tag_singleton, hbaseRegion]
            rfl
          have htailTag := (firstExit_boundary_tag Q hQ (base.transform Q h)
            tail htail hlong.tail).1 hnextRegion
          have hrightTag :
              (FirstExitRecord.ofFirstExit Q base (h :: tail)).tag =
                .boundaryZero := by
            rw [FirstExitRecord.ofFirstExit_tag_cons Q h base tail htail]
            exact htailTag
          have hfield := congrArg FirstExitRecord.tag hrecord
          rw [hleftTag, hrightTag] at hfield
          contradiction
      | boundaryOne =>
          have hleftTag : (FirstExitRecord.ofFirstExit Q base [g]).tag =
              .direct := by
            rw [FirstExitRecord.ofFirstExit_tag_singleton, hbaseRegion]
            rfl
          have htailTag := (firstExit_boundary_tag Q hQ (base.transform Q h)
            tail htail hlong.tail).2 hnextRegion
          have hrightTag :
              (FirstExitRecord.ofFirstExit Q base (h :: tail)).tag =
                .boundaryOne := by
            rw [FirstExitRecord.ofFirstExit_tag_cons Q h base tail htail]
            exact htailTag
          have hfield := congrArg FirstExitRecord.tag hrecord
          rw [hleftTag, hrightTag] at hfield
          contradiction

private theorem firstExit_next_region_eq_of_record_eq
    (Q : ℕ) (hQ : 0 < Q) (base : AffineLine) (g h : ℕ)
    (left right : GapWord) (hleft : left ≠ []) (hright : right ≠ [])
    (hbase : classifySlope (base.slope Q) = .interior)
    (hleftWord : IsFirstExitWord Q base (g :: left))
    (hrightWord : IsFirstExitWord Q base (h :: right))
    (hrecord : FirstExitRecord.ofFirstExit Q base (g :: left) =
      FirstExitRecord.ofFirstExit Q base (h :: right)) :
    classifySlope ((base.transform Q g).slope Q) =
      classifySlope ((base.transform Q h).slope Q) := by
  let leftRegion := classifySlope ((base.transform Q g).slope Q)
  let rightRegion := classifySlope ((base.transform Q h).slope Q)
  have hleftNon : leftRegion ≠ .exterior := hleftWord.next_nonexterior hleft
  have hrightNon : rightRegion ≠ .exterior := hrightWord.next_nonexterior hright
  have hcounts :
      preExitRegionCount Q (base.transform Q g) left .interior =
        preExitRegionCount Q (base.transform Q h) right .interior := by
    have hfield := congrArg FirstExitRecord.interiorGaps hrecord
    rw [FirstExitRecord.ofFirstExit_interiorGaps Q base (g :: left)
        (by simp),
      FirstExitRecord.ofFirstExit_interiorGaps Q base (h :: right)
        (by simp),
      preExitRegionCount_cons, preExitRegionCount_cons, hbase] at hfield
    omega
  by_cases hleftInterior : leftRegion = .interior
  · have hleftPos : 0 <
        preExitRegionCount Q (base.transform Q g) left .interior :=
      preExitRegionCount_pos_of_base_region Q (base.transform Q g) left
        .interior hleft hleftInterior
    by_contra hne
    have hrightBoundary : rightRegion = .boundaryZero ∨
        rightRegion = .boundaryOne := by
      cases hrightRegion : rightRegion with
      | interior => exact (hne (hleftInterior.trans hrightRegion.symm)).elim
      | boundaryZero => exact Or.inl rfl
      | boundaryOne => exact Or.inr rfl
      | exterior => exact (hrightNon hrightRegion).elim
    have hrightZero :
        preExitRegionCount Q (base.transform Q h) right .interior = 0 :=
      preExitRegionCount_interior_eq_zero_of_boundary Q hQ
        (base.transform Q h) right hrightBoundary hrightWord.tail
    omega
  · have hleftBoundary : leftRegion = .boundaryZero ∨
        leftRegion = .boundaryOne := by
      cases hleftRegion : leftRegion with
      | interior => exact (hleftInterior hleftRegion).elim
      | boundaryZero => exact Or.inl rfl
      | boundaryOne => exact Or.inr rfl
      | exterior => exact (hleftNon hleftRegion).elim
    by_cases hrightInterior : rightRegion = .interior
    · have hrightPos : 0 <
          preExitRegionCount Q (base.transform Q h) right .interior :=
        preExitRegionCount_pos_of_base_region Q (base.transform Q h) right
          .interior hright hrightInterior
      have hleftZero :
          preExitRegionCount Q (base.transform Q g) left .interior = 0 :=
        preExitRegionCount_interior_eq_zero_of_boundary Q hQ
          (base.transform Q g) left hleftBoundary hleftWord.tail
      omega
    · have hrightBoundary : rightRegion = .boundaryZero ∨
          rightRegion = .boundaryOne := by
        cases hrightRegion : rightRegion with
        | interior => exact (hrightInterior hrightRegion).elim
        | boundaryZero => exact Or.inl rfl
        | boundaryOne => exact Or.inr rfl
        | exterior => exact (hrightNon hrightRegion).elim
      rcases hleftBoundary with hleftZero | hleftOne
      · rcases hrightBoundary with hrightZero | hrightOne
        · exact hleftZero.trans hrightZero.symm
        · have hleftTag := (firstExit_boundary_tag Q hQ
            (base.transform Q g) left hleft hleftWord.tail).1 hleftZero
          have hrightTag := (firstExit_boundary_tag Q hQ
            (base.transform Q h) right hright hrightWord.tail).2 hrightOne
          have hfield := congrArg FirstExitRecord.tag hrecord
          rw [FirstExitRecord.ofFirstExit_tag_cons Q g base left hleft,
            FirstExitRecord.ofFirstExit_tag_cons Q h base right hright,
            hleftTag, hrightTag] at hfield
          contradiction
      · rcases hrightBoundary with hrightZero | hrightOne
        · have hleftTag := (firstExit_boundary_tag Q hQ
            (base.transform Q g) left hleft hleftWord.tail).2 hleftOne
          have hrightTag := (firstExit_boundary_tag Q hQ
            (base.transform Q h) right hright hrightWord.tail).1 hrightZero
          have hfield := congrArg FirstExitRecord.tag hrecord
          rw [FirstExitRecord.ofFirstExit_tag_cons Q g base left hleft,
            FirstExitRecord.ofFirstExit_tag_cons Q h base right hright,
            hleftTag, hrightTag] at hfield
          contradiction
        · exact hleftOne.trans hrightOne.symm

/-- Once the initial occurrence line is fixed, the polynomial first-exit
record reconstructs the complete positive transition word. -/
private theorem FirstExitRecord.ofFirstExit_injective_on_firstExit
    (Q : ℕ) (hQ : 0 < Q) (base : AffineLine)
    (left right : GapWord) (hleft : IsFirstExitWord Q base left)
    (hright : IsFirstExitWord Q base right)
    (hrecord : FirstExitRecord.ofFirstExit Q base left =
      FirstExitRecord.ofFirstExit Q base right) :
    left = right := by
  induction left generalizing base right with
  | nil =>
      cases right with
      | nil => rfl
      | cons h tail =>
          have hbaseExterior : classifySlope (base.slope Q) = .exterior := by
            simpa only [AffineLine.transformWord] using hleft.2.2
          have hbaseNon := hright.base_nonexterior (by simp)
          exact (hbaseNon hbaseExterior).elim
  | cons g left ih =>
      cases right with
      | nil =>
          have hbaseNon := hleft.base_nonexterior (by simp)
          have hbaseExterior : classifySlope (base.slope Q) = .exterior := by
            simpa only [AffineLine.transformWord] using hright.2.2
          exact (hbaseNon hbaseExterior).elim
      | cons h right =>
          by_cases hleftTail : left = []
          · subst left
            by_cases hrightTail : right = []
            · subst right
              have hfield := congrArg FirstExitRecord.exitGap hrecord
              have hgh : g = h := by
                simpa [FirstExitRecord.ofFirstExit] using hfield
              subst h
              rfl
            · exact (singleton_record_ne_long_firstExit Q hQ base g h right
                hrightTail hleft hright hrecord).elim
          · by_cases hrightTail : right = []
            · subst right
              exact (singleton_record_ne_long_firstExit Q hQ base h g left
                hleftTail hright hleft hrecord.symm).elim
            · have hbaseNon := hleft.base_nonexterior (by simp)
              have hhead : g = h := by
                cases hbaseRegion : classifySlope (base.slope Q) with
                | exterior => exact (hbaseNon hbaseRegion).elim
                | boundaryZero =>
                    obtain ⟨x, hshape⟩ := firstExit_boundaryZero_singleton Q
                      hQ base (g :: left) hbaseRegion hleft
                    have : left = [] := by simpa using congrArg List.tail hshape
                    exact (hleftTail this).elim
                | boundaryOne =>
                    have hg := firstExit_boundaryOne_head_eq_one Q hQ base g
                      left hleftTail hbaseRegion hleft
                    have hh := firstExit_boundaryOne_head_eq_one Q hQ base h
                      right hrightTail hbaseRegion hright
                    omega
                | interior =>
                    have hregion := firstExit_next_region_eq_of_record_eq Q hQ
                      base g h left right hleftTail hrightTail hbaseRegion
                      hleft hright hrecord
                    apply positive_gap_eq_of_same_nonexterior_region Q hQ base
                      g h hleft.head_positive hright.head_positive hbaseRegion
                      (classifySlope ((base.transform Q g).slope Q))
                      (hleft.next_nonexterior hleftTail)
                    · rfl
                    · exact hregion.symm ▸ rfl
              subst h
              have htailRecord :=
                FirstExitRecord.tail_eq_of_cons_record_eq Q g base left right
                  hleftTail hrightTail hrecord
              have htail := ih (base.transform Q g) right hleft.tail
                hright.tail htailRecord
              rw [htail]
/-- The stronger affine-locking witness produces the unique deterministic
record consumed by the exterior encoding. -/
theorem FirstExitRecord.exists_describes_of_actual
    (W : WindowSystem) (Z0 : ℕ) (e : WindowThreshold)
    (line : AffineLine) (continuation : GapWord)
    (hactual : IsActualFirstExteriorContinuation W Z0 e line continuation) :
    ∃ record : FirstExitRecord,
      FirstExitRecord.DescribesFirstExit W Z0 e record line continuation := by
  rcases hactual with
    ⟨base, finish, before, after, hbase, hsuffix, hbefore,
      hfirst, hexterior, hcontinuation⟩
  refine ⟨FirstExitRecord.ofFirstExit W.rational.eta.den base before, ?_⟩
  refine ⟨base, finish, before, after, hbase, hsuffix, hbefore,
    hcontinuation, hexterior, ?_, rfl⟩
  intro r hr
  let state := base.transformWord W.rational.eta.den (before.take r)
  have htrajectory : SharedGapTrajectory W.rational.eta.den base
      (before.take r) state :=
    (sharedGapTrajectory_iff_eq_transformWord _ _ _ _).2 rfl
  exact ⟨state, htrajectory, hfirst r hr state htrajectory⟩

private theorem getLastD_mem_of_ne_nil {α : Type*} (word : List α)
    (default : α) (hword : word ≠ []) : word.getLastD default ∈ word := by
  cases word with
  | nil => exact (hword rfl).elim
  | cons a tail =>
      simpa only [List.getLastD_cons] using
        (List.getLastD_mem_cons (l := tail) (a := a))

private theorem dropLast_append_getLastD {α : Type*} (word : List α)
    (default : α) (hword : word ≠ []) :
    word.dropLast ++ [word.getLastD default] = word := by
  cases word with
  | nil => exact (hword rfl).elim
  | cons a tail =>
      have hcons : a :: tail ≠ [] := by simp
      rw [List.getLastD_cons, ← List.getLast_eq_getLastD hcons]
      exact List.dropLast_append_getLast hcons

/-- The deterministic first-exit record satisfies all finite ranges used in
the polynomial record count.  The `+1` is forced by the possible endpoint
`x = 2X`, for which `Nat.log 2 x = L + 1`. -/
theorem FirstExitRecord.ofFirstExit_valid
    (Q m L Cgap : ℕ) (hQ : 0 < Q) (base line : AffineLine)
    (before : GapWord)
    (htrajectory : SharedGapTrajectory Q base before line)
    (hexterior : classifySlope (line.slope Q) = .exterior)
    (hlength : before.length ≤ m) (hpositive : before.Positive)
    (hgap : ∀ g ∈ before, g ≤ L + Cgap + 1) :
    (FirstExitRecord.ofFirstExit Q base before).Valid m L Cgap := by
  by_cases hnil : before = []
  · subst before
    simp [FirstExitRecord.ofFirstExit, FirstExitRecord.initialExterior,
      FirstExitRecord.Valid]
  rw [FirstExitRecord.ofFirstExit, dif_neg hnil]
  have hinteriorCount :
      ((List.range before.length).filter fun r =>
        classifySlope ((base.transformWord Q (before.take r)).slope Q) =
          .interior).length ≤ m :=
    (List.length_filter_le _ _).trans (by simpa using hlength)
  have hboundaryCount :
      ((List.range before.length).filter fun r =>
        classifySlope ((base.transformWord Q (before.take r)).slope Q) =
          .boundaryOne).length ≤ m :=
    (List.length_filter_le _ _).trans (by simpa using hlength)
  have hlastMem : before.getLastD 0 ∈ before :=
    getLastD_mem_of_ne_nil before 0 hnil
  have hlastPos : 1 ≤ before.getLastD 0 :=
    hpositive _ hlastMem
  have hlastBound : before.getLastD 0 ≤ L + Cgap + 1 :=
    hgap _ hlastMem
  have htagNotInitial :
      FirstExitRecord.tagOfPreExitRegion
          (classifySlope ((base.transformWord Q before.dropLast).slope Q)) ≠
        .initialExterior := by
    cases classifySlope ((base.transformWord Q before.dropLast).slope Q) <;>
      simp [FirstExitRecord.tagOfPreExitRegion]
  have hboundaryExit :
      FirstExitRecord.tagOfPreExitRegion
            (classifySlope ((base.transformWord Q before.dropLast).slope Q)) =
          .boundaryOne →
        2 ≤ before.getLastD 0 := by
    intro htag
    have hpre :
        classifySlope ((base.transformWord Q before.dropLast).slope Q) =
          .boundaryOne := by
      cases hregion :
          classifySlope ((base.transformWord Q before.dropLast).slope Q) <;>
        simp [FirstExitRecord.tagOfPreExitRegion, hregion] at htag
      rfl
    by_contra hnot
    have hlast : before.getLastD 0 = 1 := by omega
    have hlineEq :
        line = (base.transformWord Q before.dropLast).transform Q
          (before.getLastD 0) := by
      have hterminal :=
        (sharedGapTrajectory_iff_eq_transformWord Q base line before).1
          htrajectory
      rw [← dropLast_append_getLastD before 0 hnil,
        AffineLine.transformWord_append] at hterminal
      simpa only [AffineLine.transformWord] using hterminal
    have hpreSlope :
        (base.transformWord Q before.dropLast).slope Q = 1 := by
      unfold classifySlope at hpre
      by_cases hzero :
          (base.transformWord Q before.dropLast).slope Q = 0
      · simp [hzero] at hpre
      rw [if_neg hzero] at hpre
      by_cases hone :
          (base.transformWord Q before.dropLast).slope Q = 1
      · exact hone
      rw [if_neg hone] at hpre
      split at hpre <;> contradiction
    have hnextSlope :
        ((base.transformWord Q before.dropLast).transform Q 1).slope Q = 1 := by
      rw [AffineLine.slope_transform Q hQ, hpreSlope]
      norm_num
    have hnextClass :
        classifySlope
            (((base.transformWord Q before.dropLast).transform Q 1).slope Q) =
          .boundaryOne := by
      simp [hnextSlope, classifySlope]
    rw [hlineEq, hlast, hnextClass] at hexterior
    contradiction
  refine ⟨hinteriorCount, hboundaryCount, ?_, ?_, hboundaryExit⟩
  · intro htag
    exact (htagNotInitial htag).elim
  · intro _htag
    exact ⟨hlastPos, hlastBound⟩

def validFirstExitRecords (m L Cgap : ℕ) : Set FirstExitRecord :=
  {record | record.Valid m L Cgap}

private def firstExitRecordCoordinates (record : FirstExitRecord) :
    ℕ × (ExitTag × (ℕ × ℕ)) :=
  (record.interiorGaps, (record.tag, (record.boundaryOnes, record.exitGap)))

private theorem firstExitRecordCoordinates_injective :
    Function.Injective firstExitRecordCoordinates := by
  intro a b h
  rcases a with ⟨ai, atag, ab, ae⟩
  rcases b with ⟨bi, bt, bb, be⟩
  simp only [firstExitRecordCoordinates] at h
  cases h
  rfl

/-- The first-exit records form a polynomial-size finite family. -/
theorem validFirstExitRecords_finite_and_ncard_le (m L Cgap : ℕ) :
    (validFirstExitRecords m L Cgap).Finite ∧
      (validFirstExitRecords m L Cgap).ncard ≤
        (m + 1) * 4 * (m + 1) * (L + Cgap + 2) := by
  let box : Set (ℕ × (ExitTag × (ℕ × ℕ))) :=
    Set.Iic m ×ˢ
      (Set.univ ×ˢ (Set.Iic m ×ˢ Set.Iic (L + Cgap + 1)))
  have hboxFinite : box.Finite := by
    exact (Set.finite_Iic m).prod
      (Set.finite_univ.prod
        ((Set.finite_Iic m).prod (Set.finite_Iic (L + Cgap + 1))))
  have hmaps : Set.MapsTo firstExitRecordCoordinates
      (validFirstExitRecords m L Cgap) box := by
    intro record hrecord
    change record.Valid m L Cgap at hrecord
    have hexit : record.exitGap ≤ L + Cgap + 1 := by
      by_cases hinitial : record.tag = .initialExterior
      · have hrecordEq := hrecord.2.2.1 hinitial
        rw [hrecordEq]
        simp [FirstExitRecord.initialExterior]
      · exact (hrecord.2.2.2.1 hinitial).2
    exact ⟨hrecord.1, Set.mem_univ _, hrecord.2.1, hexit⟩
  have himageFinite :
      (firstExitRecordCoordinates ''
        validFirstExitRecords m L Cgap).Finite := by
    apply hboxFinite.subset
    rintro _ ⟨record, hrecord, rfl⟩
    exact hmaps hrecord
  have hfinite : (validFirstExitRecords m L Cgap).Finite :=
    Set.Finite.of_finite_image himageFinite
      (firstExitRecordCoordinates_injective.injOn)
  refine ⟨hfinite, ?_⟩
  calc
    (validFirstExitRecords m L Cgap).ncard =
        (firstExitRecordCoordinates ''
          validFirstExitRecords m L Cgap).ncard := by
      symm
      exact Set.ncard_image_of_injective _ firstExitRecordCoordinates_injective
    _ ≤ box.ncard := by
      apply Set.ncard_le_ncard _ hboxFinite
      rintro _ ⟨record, hrecord, rfl⟩
      exact hmaps hrecord
    _ = (m + 1) * 4 * (m + 1) * (L + Cgap + 2) := by
      have hcardExit : Fintype.card ExitTag = 4 := by decide
      have hnatCardExit : Nat.card ExitTag = 4 := by
        simpa [Nat.card_eq_fintype_card] using hcardExit
      have hpair :
          (Set.Iic (m, L + Cgap + 1) : Set (ℕ × ℕ)).ncard =
            (m + 1) * (L + Cgap + 2) := by
        rw [show (Set.Iic (m, L + Cgap + 1) : Set (ℕ × ℕ)) =
            Set.Iic m ×ˢ Set.Iic (L + Cgap + 1) by rfl,
          Set.ncard_prod, Set.ncard_Iic_nat, Set.ncard_Iic_nat]
      dsimp [box]
      rw [Set.ncard_prod, Set.ncard_Iic_nat, Set.ncard_prod,
        Set.ncard_univ, hnatCardExit, hpair]
      ring

theorem distanceToUnitInterval_pos_of_not_mem (μ : ℝ)
    (hμ : μ ∉ Set.Icc (0 : ℝ) 1) :
    0 < distanceToUnitInterval μ := by
  by_cases hneg : μ < 0
  · rw [distanceToUnitInterval, if_pos hneg]
    linarith
  · have hnonneg : 0 ≤ μ := le_of_not_gt hneg
    have hgt : 1 < μ := by
      by_contra hnot
      exact hμ ⟨hnonneg, le_of_not_gt hnot⟩
    rw [distanceToUnitInterval, if_neg hneg, if_pos hgt]
    linarith

theorem not_mem_unitInterval_of_distance_pos (μ : ℝ)
    (hμ : 0 < distanceToUnitInterval μ) :
    μ ∉ Set.Icc (0 : ℝ) 1 := by
  intro hmem
  rw [distanceToUnitInterval, if_neg (not_lt_of_ge hmem.1),
    if_neg (not_lt_of_ge hmem.2)] at hμ
  linarith

theorem classifySlope_exterior_of_not_mem (μ : ℚ)
    (hμ : (μ : ℝ) ∉ Set.Icc (0 : ℝ) 1) :
    classifySlope μ = .exterior := by
  unfold classifySlope
  by_cases hzero : μ = 0
  · subst μ
    exact (hμ (by norm_num)).elim
  rw [if_neg hzero]
  by_cases hone : μ = 1
  · subst μ
    exact (hμ (by norm_num)).elim
  rw [if_neg hone]
  by_cases hinterior : 0 < μ ∧ μ < 1
  · exfalso
    apply hμ
    exact ⟨by exact_mod_cast hinterior.1.le,
      by exact_mod_cast hinterior.2.le⟩
  · simp [hinterior]

theorem distance_amplify_word (μ : ℝ) (word : GapWord)
    (hword : word.Positive) (hμ : μ ∉ Set.Icc (0 : ℝ) 1) :
    (2 : ℝ) ^ word.span * distanceToUnitInterval μ ≤
      distanceToUnitInterval (slopeAfter word μ) := by
  induction word generalizing μ with
  | nil => simp [GapWord.span, slopeAfter]
  | cons g gs ih =>
      have hg : 1 ≤ g := hword g (by simp)
      have hgs : GapWord.Positive gs := by
        intro x hx
        exact hword x (by simp [hx])
      let next := (2 : ℝ) ^ g * μ - 1
      have hstep :
          (2 : ℝ) ^ g * distanceToUnitInterval μ ≤
            distanceToUnitInterval next := by
        exact lem_off_amplify μ g hg hμ
      have hnextPos : 0 < distanceToUnitInterval next := by
        have hleft : 0 < (2 : ℝ) ^ g * distanceToUnitInterval μ :=
          mul_pos (by positivity) (distanceToUnitInterval_pos_of_not_mem μ hμ)
        exact lt_of_lt_of_le hleft hstep
      have hnext : next ∉ Set.Icc (0 : ℝ) 1 :=
        not_mem_unitInterval_of_distance_pos next hnextPos
      have htail := ih next hgs hnext
      calc
        (2 : ℝ) ^ GapWord.span (g :: gs) * distanceToUnitInterval μ =
            (2 : ℝ) ^ GapWord.span gs *
              ((2 : ℝ) ^ g * distanceToUnitInterval μ) := by
          simp only [GapWord.span, List.sum_cons, pow_add]
          ring
        _ ≤ (2 : ℝ) ^ GapWord.span gs * distanceToUnitInterval next := by
          exact mul_le_mul_of_nonneg_left hstep (by positivity)
        _ ≤ distanceToUnitInterval (slopeAfter gs next) := htail
        _ = distanceToUnitInterval (slopeAfter (g :: gs) μ) := rfl

theorem exterior_rational_distance_lower (Q : ℕ) (hQ : 0 < Q)
    (line : AffineLine)
    (hexterior : classifySlope (line.slope Q) = .exterior) :
    (1 : ℝ) ≤ (Q : ℝ) * (line.H : ℝ) *
      distanceToUnitInterval (line.slope Q : ℝ) := by
  have hout := classifySlope_exterior_not_mem (line.slope Q) hexterior
  have hQrQ : (0 : ℚ) < Q := by exact_mod_cast hQ
  have hHrQ : (0 : ℚ) < line.H := by exact_mod_cast line.H_pos
  have hdenQ : (0 : ℚ) < (Q : ℚ) * line.H := mul_pos hQrQ hHrQ
  have hQrR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hHrR : (0 : ℝ) < line.H := by exact_mod_cast line.H_pos
  by_cases hneg : (line.slope Q : ℝ) < 0
  · have hnegQ : line.slope Q < 0 := by exact_mod_cast hneg
    have hKQ : (line.K : ℚ) < 0 := by
      rw [AffineLine.slope] at hnegQ
      rcases (div_neg_iff.mp hnegQ) with hbad | hgood
      · exact (not_lt_of_ge hdenQ.le hbad.2).elim
      · exact hgood.1
    have hKneg : line.K < 0 := by exact_mod_cast hKQ
    have hK : line.K ≤ -1 := by omega
    have hid :
        (Q : ℝ) * (line.H : ℝ) *
            distanceToUnitInterval (line.slope Q : ℝ) =
          -(line.K : ℝ) := by
      rw [distanceToUnitInterval, if_pos hneg, AffineLine.slope]
      push_cast
      field_simp [ne_of_gt hQrR, ne_of_gt hHrR]
    rw [hid]
    have hfinal : (1 : ℤ) ≤ -line.K := by omega
    exact_mod_cast hfinal
  · have hnonneg : (0 : ℝ) ≤ line.slope Q := le_of_not_gt hneg
    have hgt : (1 : ℝ) < line.slope Q := by
      by_contra hnot
      exact hout ⟨hnonneg, le_of_not_gt hnot⟩
    have hgtQ : (1 : ℚ) < line.slope Q := by exact_mod_cast hgt
    have hKQ : (Q : ℚ) * line.H < line.K := by
      rw [AffineLine.slope] at hgtQ
      simpa using (lt_div_iff₀ hdenQ).mp hgtQ
    have hK : (Q : ℤ) * line.H + 1 ≤ line.K := by exact_mod_cast hKQ
    have hid :
        (Q : ℝ) * (line.H : ℝ) *
            distanceToUnitInterval (line.slope Q : ℝ) =
          (line.K : ℝ) - (Q : ℝ) * line.H := by
      rw [distanceToUnitInterval, if_neg hneg, if_pos hgt,
        AffineLine.slope]
      push_cast
      field_simp [ne_of_gt hQrR, ne_of_gt hHrR]
    rw [hid]
    have hfinal : (1 : ℤ) ≤ line.K - (Q : ℤ) * line.H := by omega
    exact_mod_cast hfinal

/-- A finite set of integer parameters whose values under a decreasing affine
map lie in an interval of length `B` has the expected spacing bound. -/
private theorem affineIntegerParameterCount
    (S : Set ℤ) (C J B : ℤ) (hJ : J < 0) (hB : 0 ≤ B)
    (hbound : ∀ t ∈ S, 0 ≤ C + J * t ∧ C + J * t ≤ B) :
    S.Finite ∧
      (S.ncard : ℝ) ≤ 1 + (B : ℝ) / (-(J : ℝ)) := by
  let f : ℤ → ℤ := fun t => C + J * t
  have himage : f '' S ⊆ Set.Icc 0 B := by
    rintro y ⟨t, ht, rfl⟩
    exact hbound t ht
  have hfimage : (f '' S).Finite :=
    (Set.finite_Icc 0 B).subset himage
  have hinj : Set.InjOn f S := by
    intro x _ y _ hxy
    dsimp [f] at hxy
    apply mul_left_cancel₀ (ne_of_lt hJ)
    exact add_left_cancel hxy
  have hfinite : S.Finite :=
    Set.Finite.of_finite_image hfimage hinj
  refine ⟨hfinite, ?_⟩
  by_cases hempty : S = ∅
  · rw [hempty, Set.ncard_empty]
    have hBreal : (0 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
    have hJreal : (0 : ℝ) < -(J : ℝ) := by
      exact_mod_cast (neg_pos.mpr hJ)
    have hquot : (0 : ℝ) ≤ (B : ℝ) / (-(J : ℝ)) := by
      exact div_nonneg hBreal hJreal.le
    norm_num
    linarith
  · have hnonempty : S.Nonempty := Set.nonempty_iff_ne_empty.mpr hempty
    let s : Finset ℤ := hfinite.toFinset
    have hsne : s.Nonempty := by
      rcases hnonempty with ⟨t, ht⟩
      exact ⟨t, by simpa [s] using ht⟩
    let lo : ℤ := s.min' hsne
    let hi : ℤ := s.max' hsne
    have hlo_mem : lo ∈ s := by
      exact s.min'_mem hsne
    have hhi_mem : hi ∈ s := by
      exact s.max'_mem hsne
    have hlohi : lo ≤ hi := by
      exact s.min'_le hi hhi_mem
    have hsubset : s ⊆ Finset.Icc lo hi := by
      intro t ht
      simp only [Finset.mem_Icc]
      exact ⟨s.min'_le t ht, s.le_max' t ht⟩
    have hcard_nat : s.card ≤ (Finset.Icc lo hi).card :=
      Finset.card_le_card hsubset
    rw [Int.card_Icc] at hcard_nat
    have hnonneg : 0 ≤ hi + 1 - lo := by omega
    have hcard_int : (s.card : ℤ) ≤ hi + 1 - lo := by
      have hcast : (s.card : ℤ) ≤ ((hi + 1 - lo).toNat : ℤ) := by
        exact_mod_cast hcard_nat
      rwa [Int.toNat_of_nonneg hnonneg] at hcast
    have hncard_eq : S.ncard = s.card := by
      simpa [s] using Set.ncard_eq_toFinset_card S hfinite
    have hcard_real : (S.ncard : ℝ) ≤ ((hi + 1 - lo : ℤ) : ℝ) := by
      rw [hncard_eq]
      exact_mod_cast hcard_int
    have hloS : lo ∈ S := by
      simpa [s] using hlo_mem
    have hhiS : hi ∈ S := by
      simpa [s] using hhi_mem
    have hspan_int : (-J) * (hi - lo) ≤ B := by
      calc
        (-J) * (hi - lo) =
            (C + J * lo) - (C + J * hi) := by ring
        _ ≤ B := by
          linarith [(hbound lo hloS).2, (hbound hi hhiS).1]
    have hstep : (0 : ℝ) < -(J : ℝ) := by
      exact_mod_cast (neg_pos.mpr hJ)
    have hspan_real₀ :
        (-(J : ℝ)) * ((hi - lo : ℤ) : ℝ) ≤ (B : ℝ) := by
      exact_mod_cast hspan_int
    have hspan_real :
        ((hi - lo : ℤ) : ℝ) * (-(J : ℝ)) ≤ (B : ℝ) := by
      simpa [mul_comm] using hspan_real₀
    have hspan_div :
        ((hi - lo : ℤ) : ℝ) ≤ (B : ℝ) / (-(J : ℝ)) :=
      (le_div_iff₀ hstep).2 hspan_real
    push_cast at hcard_real hspan_div
    linarith

/-- Paper label: `lem:off-corridor` (Section 7). -/
theorem lem_off_corridor (Q : ℕ) (hQ : 0 < Q) :
    ∃ Ccorr : ℝ, 0 < Ccorr ∧ ∀ X : ℕ, ∀ line : AffineLine,
      (line.slope Q : ℝ) ∉ Set.Icc (0 : ℝ) 1 →
      {t : ℤ | InAdmissibleCarryRegion Q X
        (line.A + line.H * t) (line.C + line.K * t)}.Finite ∧
      ({t : ℤ | InAdmissibleCarryRegion Q X
        (line.A + line.H * t) (line.C + line.K * t)}.ncard : ℝ) ≤
        1 + Ccorr * X /
          ((line.H : ℝ) * distanceToUnitInterval (line.slope Q)) := by
  refine ⟨5, by norm_num, ?_⟩
  intro X line hslope
  let S : Set ℤ :=
    {t | InAdmissibleCarryRegion Q X
      (line.A + line.H * t) (line.C + line.K * t)}
  change S.Finite ∧
    (S.ncard : ℝ) ≤
      1 + 5 * X /
        ((line.H : ℝ) * distanceToUnitInterval (line.slope Q))
  by_cases hX : X = 0
  · subst X
    have hsub : S.Subsingleton := by
      intro t ht u hu
      change InAdmissibleCarryRegion Q 0
        (line.A + line.H * t) (line.C + line.K * t) at ht
      change InAdmissibleCarryRegion Q 0
        (line.A + line.H * u) (line.C + line.K * u) at hu
      rcases ht with ⟨hxt₀, hxt₁, _, _⟩
      rcases hu with ⟨hxu₀, hxu₁, _, _⟩
      have hxt : line.A + line.H * t = 0 := by omega
      have hxu : line.A + line.H * u = 0 := by omega
      apply mul_left_cancel₀ (ne_of_gt line.H_pos)
      linarith
    have hfinite : S.Finite := hsub.finite
    refine ⟨hfinite, ?_⟩
    have hcard : S.ncard ≤ 1 :=
      (Set.ncard_le_one hfinite).2 fun _ ht _ hu => hsub ht hu
    have hcard_real : (S.ncard : ℝ) ≤ 1 := by exact_mod_cast hcard
    simpa using hcard_real
  · have hXone : 1 ≤ X := Nat.one_le_iff_ne_zero.mpr hX
    have hQint : (0 : ℤ) ≤ (Q : ℤ) := by omega
    let B : ℤ := (Q : ℤ) * (3 * (X : ℤ) + 2)
    have hB : (0 : ℤ) ≤ B := by
      dsimp [B]
      positivity
    have hxwidth : 3 * (X : ℤ) + 2 ≤ 5 * X := by
      exact_mod_cast (show 3 * X + 2 ≤ 5 * X by omega)
    have hBfive : B ≤ 5 * (Q : ℤ) * X := by
      dsimp [B]
      calc
        (Q : ℤ) * (3 * (X : ℤ) + 2) ≤
            (Q : ℤ) * (5 * X) :=
          mul_le_mul_of_nonneg_left hxwidth hQint
        _ = 5 * (Q : ℤ) * X := by ring
    have hQrat : (0 : ℚ) < (Q : ℚ) := by exact_mod_cast hQ
    have hHrat : (0 : ℚ) < (line.H : ℚ) := by
      exact_mod_cast line.H_pos
    have hdenQ : (0 : ℚ) < (Q : ℚ) * line.H :=
      mul_pos hQrat hHrat
    have hQr : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
    have hHr : (line.H : ℝ) ≠ 0 := by
      exact_mod_cast line.H_pos.ne'
    by_cases hneg : (line.slope Q : ℝ) < 0
    · have hnegQ : line.slope Q < 0 := by exact_mod_cast hneg
      have hKQ : (line.K : ℚ) < 0 := by
        rw [AffineLine.slope] at hnegQ
        simpa using (div_lt_iff₀ hdenQ).mp hnegQ
      have hK : line.K < 0 := by exact_mod_cast hKQ
      have hcount := affineIntegerParameterCount
        S line.C line.K B hK hB (by
          intro t ht
          change InAdmissibleCarryRegion Q X
            (line.A + line.H * t) (line.C + line.K * t) at ht
          rcases ht with ⟨_, hxhi, hrlo, hrhi⟩
          have hxplus : line.A + line.H * t + 2 ≤
              3 * (X : ℤ) + 2 := by linarith
          have hprod := mul_le_mul_of_nonneg_left hxplus hQint
          exact ⟨hrlo, hrhi.trans (by simpa [B] using hprod)⟩)
      have hminusK : (0 : ℝ) < -(line.K : ℝ) := by
        exact_mod_cast (neg_pos.mpr hK)
      have hBfive_real : (B : ℝ) ≤
          5 * (Q : ℝ) * X := by exact_mod_cast hBfive
      have hden_id :
          (line.H : ℝ) * (-(line.slope Q : ℝ)) =
            -(line.K : ℝ) / (Q : ℝ) := by
        rw [AffineLine.slope]
        push_cast
        field_simp [hQr, hHr]
      have hratio : (B : ℝ) / (-(line.K : ℝ)) ≤
          5 * X /
            ((line.H : ℝ) * distanceToUnitInterval (line.slope Q)) := by
        rw [distanceToUnitInterval, if_pos hneg, hden_id]
        calc
          (B : ℝ) / (-(line.K : ℝ)) ≤
              (5 * (Q : ℝ) * X) / (-(line.K : ℝ)) :=
            (div_le_div_iff_of_pos_right hminusK).2 hBfive_real
          _ = 5 * X / (-(line.K : ℝ) / (Q : ℝ)) := by
            field_simp [hQr, ne_of_lt hminusK]
      refine ⟨hcount.1, ?_⟩
      nlinarith [hcount.2, hratio]
    · have hnonneg : (0 : ℝ) ≤ (line.slope Q : ℝ) :=
        le_of_not_gt hneg
      have hgt : (1 : ℝ) < line.slope Q := by
        by_contra hnot
        exact hslope ⟨hnonneg, le_of_not_gt hnot⟩
      have hgtQ : (1 : ℚ) < line.slope Q := by exact_mod_cast hgt
      have hKQ : (Q : ℚ) * line.H < line.K := by
        rw [AffineLine.slope] at hgtQ
        exact (one_lt_div hdenQ).mp hgtQ
      have hK : (Q : ℤ) * line.H < line.K := by exact_mod_cast hKQ
      let Ccomp : ℤ := (Q : ℤ) * (line.A + 2) - line.C
      let J : ℤ := (Q : ℤ) * line.H - line.K
      have hJ : J < 0 := by
        dsimp [J]
        omega
      have hcount := affineIntegerParameterCount
        S Ccomp J B hJ hB (by
          intro t ht
          change InAdmissibleCarryRegion Q X
            (line.A + line.H * t) (line.C + line.K * t) at ht
          rcases ht with ⟨_, hxhi, hrlo, hrhi⟩
          have hxplus : line.A + line.H * t + 2 ≤
              3 * (X : ℤ) + 2 := by linarith
          have hprod := mul_le_mul_of_nonneg_left hxplus hQint
          have hid : Ccomp + J * t =
              (Q : ℤ) * (line.A + line.H * t + 2) -
                (line.C + line.K * t) := by
            dsimp [Ccomp, J]
            ring
          rw [hid]
          exact ⟨sub_nonneg.mpr hrhi,
            (sub_le_self _ hrlo).trans (by simpa [B] using hprod)⟩)
      have hminusJ : (0 : ℝ) < -(J : ℝ) := by
        exact_mod_cast (neg_pos.mpr hJ)
      have hBfive_real : (B : ℝ) ≤
          5 * (Q : ℝ) * X := by exact_mod_cast hBfive
      have hden_id :
          (line.H : ℝ) * ((line.slope Q : ℝ) - 1) =
            -(J : ℝ) / (Q : ℝ) := by
        dsimp [J]
        rw [AffineLine.slope]
        push_cast
        field_simp [hQr, hHr]
        ring
      have hratio : (B : ℝ) / (-(J : ℝ)) ≤
          5 * X /
            ((line.H : ℝ) * distanceToUnitInterval (line.slope Q)) := by
        rw [distanceToUnitInterval, if_neg hneg, if_pos hgt, hden_id]
        calc
          (B : ℝ) / (-(J : ℝ)) ≤
              (5 * (Q : ℝ) * X) / (-(J : ℝ)) :=
            (div_le_div_iff_of_pos_right hminusJ).2 hBfive_real
          _ = 5 * X / (-(J : ℝ) / (Q : ℝ)) := by
            field_simp [hQr, ne_of_lt hminusJ]
      refine ⟨hcount.1, ?_⟩
      nlinarith [hcount.2, hratio]

/-- Paper label: `prop:fixed-off-word` (Section 7). -/
theorem prop_fixed_off_word (Q : ℕ) (hQ : 0 < Q) :
    ∃ Coff : ℝ, 0 < Coff ∧ ∀ X : ℕ, ∀ line : AffineLine,
      ∀ word : GapWord, word.Positive →
      classifySlope (line.slope Q) = .exterior →
      (admissibleOriginalParameters Q X line word).Finite ∧
        ((admissibleOriginalParameters Q X line word).ncard : ℝ) ≤
          1 + Coff * X * (2 : ℝ) ^ (-(word.span : ℤ)) := by
  rcases lem_off_corridor Q hQ with ⟨Ccorr, hCcorr, hcorr⟩
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  refine ⟨Ccorr * Q, mul_pos hCcorr hQr, ?_⟩
  intro X line word hword hexterior
  let finish := line.transformWord Q word
  have hinitialOutside := classifySlope_exterior_not_mem (line.slope Q) hexterior
  have hinitialDistance :
      (1 : ℝ) ≤ (Q : ℝ) * (line.H : ℝ) *
        distanceToUnitInterval (line.slope Q : ℝ) :=
    exterior_rational_distance_lower Q hQ line hexterior
  have hamplify :
      (2 : ℝ) ^ word.span * distanceToUnitInterval (line.slope Q : ℝ) ≤
        distanceToUnitInterval (finish.slope Q : ℝ) := by
    rw [AffineLine.transformWord_slope_real Q hQ line word]
    exact distance_amplify_word (line.slope Q : ℝ) word hword hinitialOutside
  have hfinishDistance : 0 < distanceToUnitInterval (finish.slope Q : ℝ) := by
    have hleft :
        0 < (2 : ℝ) ^ word.span *
          distanceToUnitInterval (line.slope Q : ℝ) :=
      mul_pos (by positivity)
        (distanceToUnitInterval_pos_of_not_mem (line.slope Q : ℝ) hinitialOutside)
    exact lt_of_lt_of_le hleft hamplify
  have hfinishOutside :
      (finish.slope Q : ℝ) ∉ Set.Icc (0 : ℝ) 1 :=
    not_mem_unitInterval_of_distance_pos (finish.slope Q : ℝ) hfinishDistance
  let corridor : Set ℤ :=
    {t | InAdmissibleCarryRegion Q X
      (finish.A + finish.H * t) (finish.C + finish.K * t)}
  have hsubset : admissibleOriginalParameters Q X line word ⊆ corridor := by
    intro t ht
    change InAdmissibleCarryRegion Q X
        (line.A + line.H * t) (line.C + line.K * t) ∧
      InAdmissibleCarryRegion Q X
        (finish.A + finish.H * t) (finish.C + finish.K * t) at ht
    exact ht.2
  have hcorridor : corridor.Finite ∧
      (corridor.ncard : ℝ) ≤
        1 + Ccorr * X /
          ((finish.H : ℝ) * distanceToUnitInterval (finish.slope Q)) := by
    simpa [corridor] using hcorr X finish hfinishOutside
  refine ⟨hcorridor.1.subset hsubset, ?_⟩
  have hncardNat := Set.ncard_le_ncard hsubset hcorridor.1
  have hncardReal :
      ((admissibleOriginalParameters Q X line word).ncard : ℝ) ≤
        (corridor.ncard : ℝ) := by exact_mod_cast hncardNat
  calc
    ((admissibleOriginalParameters Q X line word).ncard : ℝ) ≤
        (corridor.ncard : ℝ) := hncardReal
    _ ≤ 1 + Ccorr * X /
          ((finish.H : ℝ) * distanceToUnitInterval (finish.slope Q)) :=
      hcorridor.2
    _ ≤ 1 + (Ccorr * Q) * X * (2 : ℝ) ^ (-(word.span : ℤ)) := by
      have hH : (finish.H : ℝ) = line.H := by
        exact_mod_cast AffineLine.transformWord_H Q line word
      have hlineH : (0 : ℝ) < line.H := by exact_mod_cast line.H_pos
      have hden :
          0 < (finish.H : ℝ) * distanceToUnitInterval (finish.slope Q) :=
        mul_pos (by simpa [hH] using hlineH) hfinishDistance
      have hpow : (0 : ℝ) < (2 : ℝ) ^ word.span := by positivity
      have hdenprod :
          (2 : ℝ) ^ word.span ≤
            (Q : ℝ) * ((finish.H : ℝ) *
              distanceToUnitInterval (finish.slope Q)) := by
        rw [hH]
        calc
          (2 : ℝ) ^ word.span ≤
              (2 : ℝ) ^ word.span *
                ((Q : ℝ) * (line.H : ℝ) *
                  distanceToUnitInterval (line.slope Q : ℝ)) := by
            nlinarith [hinitialDistance]
          _ ≤ (Q : ℝ) * (line.H : ℝ) *
                distanceToUnitInterval (finish.slope Q : ℝ) := by
            have := mul_le_mul_of_nonneg_left hamplify
              (mul_nonneg hQr.le hlineH.le)
            nlinarith
          _ = (Q : ℝ) * ((line.H : ℝ) *
                distanceToUnitInterval (finish.slope Q : ℝ)) := by ring
      have hratio :
          Ccorr * X /
              ((finish.H : ℝ) * distanceToUnitInterval (finish.slope Q)) ≤
            (Ccorr * Q) * X / (2 : ℝ) ^ word.span := by
        rw [div_le_div_iff₀ hden hpow]
        have hnonneg : (0 : ℝ) ≤ Ccorr * X := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hdenprod hnonneg]
      have hzpow :
          (Ccorr * Q) * X / (2 : ℝ) ^ word.span =
            (Ccorr * Q) * X * (2 : ℝ) ^ (-(word.span : ℤ)) := by
        rw [zpow_neg, zpow_natCast]
        ring
      rw [← hzpow]
      linarith

/-- The selected post-exit long prefix of a supplied exterior continuation. -/
def postExitLongPrefix (W : WindowSystem) (gaps : GapWord) : GapWord :=
  gaps.firstPrefixAbove (Nat.floor (W.structural.Gamma * W.L))

/-- Deterministic exterior counting data attached to an actual pair. -/
structure ExteriorSignature where
  record : FirstExitRecord
  word : GapWord
  deriving DecidableEq, Repr

def ValidExteriorSignature (W : WindowSystem) (Z0 Cgap : ℕ)
    (e : WindowThreshold) (signature : ExteriorSignature) : Prop :=
  signature.record.Valid W.m W.L Cgap ∧ signature.word.Positive ∧
    ∃ line : AffineLine, ∃ continuation : GapWord,
      FirstExitRecord.DescribesFirstExit W Z0 e signature.record line continuation ∧
      IsExteriorTrajectory W.rational.eta.den line continuation ∧
      signature.word = postExitLongPrefix W continuation

def exteriorSignatures (W : WindowSystem) (Z0 Cgap : ℕ) :
    Set ExteriorSignature :=
  {signature | ∃ e : WindowThreshold,
    LongExteriorPair W Z0 e ∧ ValidExteriorSignature W Z0 Cgap e signature}

/-- Uniform natural ceiling for a selected post-exit prefix. -/
def exteriorWordBound (W : WindowSystem) (Cgap : ℕ) : ℕ :=
  Nat.floor (W.structural.Gamma * W.L) + W.L + Cgap + 1

/-- Anchors supporting at least one long-exterior threshold.  Thresholds are
integrated only after the spatial parameter count. -/
def exteriorAnchors (W : WindowSystem) (Z0 : ℕ) : Finset ℕ := by
  classical
  exact W.anchors.filter fun k =>
    ∃ T : ℝ, LongExteriorPair W Z0 (k, T)

private def defaultAffineLine : AffineLine where
  A := 0
  C := 0
  H := 1
  K := 0
  H_pos := by norm_num

private def HasPrimitiveOccurrenceLine (W : WindowSystem) (Z0 : ℕ)
    (p : GapWord) : Prop :=
  ∃ line : AffineLine,
    IsOccurrenceLine W Z0 p line ∧ Int.gcd line.H line.K = 1

/-- A deterministic primitive raw parameterization is chosen for each
frequent locked prefix.  Prefixes outside the locked family receive a harmless
default; the exterior-source construction proves that this branch is never
used. -/
private noncomputable def chosenExteriorLine (W : WindowSystem) (Z0 : ℕ)
    (p : GapWord) : AffineLine := by
  classical
  exact if h : HasPrimitiveOccurrenceLine W Z0 p then Classical.choose h
    else defaultAffineLine

private theorem chosenExteriorLine_spec (W : WindowSystem) (Z0 : ℕ)
    (p : GapWord) (h : HasPrimitiveOccurrenceLine W Z0 p) :
    IsOccurrenceLine W Z0 p (chosenExteriorLine W Z0 p) ∧
      Int.gcd (chosenExteriorLine W Z0 p).H
        (chosenExteriorLine W Z0 p).K = 1 := by
  rw [chosenExteriorLine, dif_pos h]
  exact Classical.choose_spec h

/-- A genuine long-exterior source relative to one deterministic occurrence
line chosen for each initial prefix.  The record, continuation, raw integer
parameter, and admissibility certificate all refer to the same anchor.  No
injectivity or fibre-size assertion is stored as input data. -/
structure ExteriorSource (W : WindowSystem) (Z0 : ℕ)
    (lineFor : GapWord → AffineLine) where
  anchor : ℕ
  threshold : ℝ
  offset_le : W.s ≤ anchor
  pair : LongExteriorPair W Z0 (anchor, threshold)
  before : GapWord
  continuation : GapWord
  after : GapWord
  record : FirstExitRecord
  word : GapWord
  parameter : ℤ
  occurrence :
    IsOccurrenceLine W Z0 (initialLongPrefix W anchor)
      (lineFor (initialLongPrefix W anchor))
  suffix_eq :
    actualPostPrefixGaps W anchor = before ++ continuation ++ after
  first_nonexterior : ∀ r < before.length,
    classifySlope
      (((lineFor (initialLongPrefix W anchor)).transformWord
        W.rational.eta.den (before.take r)).slope W.rational.eta.den) ≠
      .exterior
  exit_exterior :
    classifySlope
      (((lineFor (initialLongPrefix W anchor)).transformWord
        W.rational.eta.den before).slope W.rational.eta.den) = .exterior
  continuation_exterior :
    IsExteriorTrajectory W.rational.eta.den
      ((lineFor (initialLongPrefix W anchor)).transformWord
        W.rational.eta.den before) continuation
  record_eq : record = FirstExitRecord.ofFirstExit W.rational.eta.den
    (lineFor (initialLongPrefix W anchor)) before
  word_eq : word = postExitLongPrefix W continuation
  initial_parameter :
    let p := initialLongPrefix W anchor
    let line := lineFor p
    ((W.enumeration.a (anchor - W.s) + p.span : ℕ) : ℤ) =
        line.A + line.H * parameter ∧
      carryInt W.rational (W.enumeration.a (anchor - W.s) + p.span) =
        line.C + line.K * parameter
  admissible : parameter ∈ admissibleOriginalParameters
    W.rational.eta.den W.X
      ((lineFor (initialLongPrefix W anchor)).transformWord
        W.rational.eta.den before) word

namespace ExteriorSource

def baseLine {W : WindowSystem} {Z0 : ℕ} {lineFor : GapWord → AffineLine}
    (source : ExteriorSource W Z0 lineFor) : AffineLine :=
  lineFor (initialLongPrefix W source.anchor)

def canonicalLine {W : WindowSystem} {Z0 : ℕ}
    {lineFor : GapWord → AffineLine} (source : ExteriorSource W Z0 lineFor) :
    GeometricLine := source.baseLine.canonicalGeometricLine

def exitLine {W : WindowSystem} {Z0 : ℕ} {lineFor : GapWord → AffineLine}
    (source : ExteriorSource W Z0 lineFor) : AffineLine :=
  source.baseLine.transformWord W.rational.eta.den source.before

/-- The source code deliberately contains no threshold coordinate.  Its raw
integer parameter is retained exactly as required by the exterior count. -/
def code {W : WindowSystem} {Z0 : ℕ} {lineFor : GapWord → AffineLine}
    (source : ExteriorSource W Z0 lineFor) :
    GapWord × FirstExitRecord × GapWord × ℤ :=
  (initialLongPrefix W source.anchor, source.record, source.word,
    source.parameter)

/-- One source code determines the anchor.  This is proved from the absolute
post-prefix coordinate and strict monotonicity; it is not an assumed field of
`ExteriorSource`. -/
theorem code_injective_on_anchor {W : WindowSystem} {Z0 : ℕ}
    {lineFor : GapWord → AffineLine}
    (left right : ExteriorSource W Z0 lineFor)
    (hcode : left.code = right.code) : left.anchor = right.anchor := by
  simp only [code, Prod.mk.injEq] at hcode
  rcases hcode with ⟨hprefix, _hrecord, _hword, hparameter⟩
  have hline :
      lineFor (initialLongPrefix W left.anchor) =
        lineFor (initialLongPrefix W right.anchor) := congrArg lineFor hprefix
  have hcoordinateInt :
      ((W.enumeration.a (left.anchor - W.s) +
          (initialLongPrefix W left.anchor).span : ℕ) : ℤ) =
        ((W.enumeration.a (right.anchor - W.s) +
          (initialLongPrefix W right.anchor).span : ℕ) : ℤ) := by
    calc
      ((W.enumeration.a (left.anchor - W.s) +
          (initialLongPrefix W left.anchor).span : ℕ) : ℤ) =
          (lineFor (initialLongPrefix W left.anchor)).A +
            (lineFor (initialLongPrefix W left.anchor)).H * left.parameter :=
        left.initial_parameter.1
      _ = (lineFor (initialLongPrefix W right.anchor)).A +
            (lineFor (initialLongPrefix W right.anchor)).H * right.parameter := by
        rw [hline, hparameter]
      _ = ((W.enumeration.a (right.anchor - W.s) +
          (initialLongPrefix W right.anchor).span : ℕ) : ℤ) :=
        right.initial_parameter.1.symm
  have hcoordinate :
      W.enumeration.a (left.anchor - W.s) +
          (initialLongPrefix W left.anchor).span =
        W.enumeration.a (right.anchor - W.s) +
          (initialLongPrefix W right.anchor).span := by
    exact_mod_cast hcoordinateInt
  have hvalues : W.enumeration.a (left.anchor - W.s) =
      W.enumeration.a (right.anchor - W.s) := by
    rw [hprefix] at hcoordinate
    omega
  have hindices : left.anchor - W.s = right.anchor - W.s :=
    W.enumeration.strictMono.injective hvalues
  have hleftOffset := left.offset_le
  have hrightOffset := right.offset_le
  omega

/-- For one fixed prefix line, the first-exit record determines the actual
pre-exit word.  This is the reconstruction fact needed to put every source
with the same `(prefix, record)` into one parameter fibre. -/
theorem before_eq_of_prefix_record {W : WindowSystem} {Z0 : ℕ}
    {lineFor : GapWord → AffineLine}
    (hQ : 0 < W.rational.eta.den)
    (left right : ExteriorSource W Z0 lineFor)
    (hprefix : initialLongPrefix W left.anchor =
      initialLongPrefix W right.anchor)
    (hrecord : left.record = right.record) :
    left.before = right.before := by
  have hline :
      lineFor (initialLongPrefix W left.anchor) =
        lineFor (initialLongPrefix W right.anchor) := congrArg lineFor hprefix
  have hleftPrefix : left.before.IsPrefix
      (actualPostPrefixGaps W left.anchor) :=
    ⟨left.continuation ++ left.after, by
      simpa only [List.append_assoc] using left.suffix_eq.symm⟩
  have hrightPrefix : right.before.IsPrefix
      (actualPostPrefixGaps W right.anchor) :=
    ⟨right.continuation ++ right.after, by
      simpa only [List.append_assoc] using right.suffix_eq.symm⟩
  have hleftWord : IsFirstExitWord W.rational.eta.den
      (lineFor (initialLongPrefix W left.anchor)) left.before := by
    refine ⟨?_, left.first_nonexterior, left.exit_exterior⟩
    intro g hg
    exact actualPostPrefixGaps_positive W left.anchor g
      (hleftPrefix.mem hg)
  have hrightWord : IsFirstExitWord W.rational.eta.den
      (lineFor (initialLongPrefix W right.anchor)) right.before := by
    refine ⟨?_, right.first_nonexterior, right.exit_exterior⟩
    intro g hg
    exact actualPostPrefixGaps_positive W right.anchor g
      (hrightPrefix.mem hg)
  have hrecordWords :
      FirstExitRecord.ofFirstExit W.rational.eta.den
          (lineFor (initialLongPrefix W left.anchor)) left.before =
        FirstExitRecord.ofFirstExit W.rational.eta.den
          (lineFor (initialLongPrefix W right.anchor)) right.before := by
    calc
      _ = left.record := left.record_eq.symm
      _ = right.record := hrecord
      _ = _ := right.record_eq
  rw [← hline] at hrightWord hrecordWords
  exact FirstExitRecord.ofFirstExit_injective_on_firstExit
    W.rational.eta.den hQ
    (lineFor (initialLongPrefix W left.anchor)) left.before right.before
    hleftWord hrightWord hrecordWords

end ExteriorSource

private theorem exteriorHighAnchor_offset_le (W : WindowSystem) (Z0 k : ℕ)
    (hk : k ∈ highAnchors W Z0) : W.s ≤ k := by
  classical
  rw [highAnchors, Finset.mem_filter] at hk
  rcases hk.2 with ⟨T, hT, hlarge⟩
  by_contra hnot
  have hspan : W.rawWindowSpan k = 0 := by
    simp [WindowSystem.rawWindowSpan, hnot]
  have hTnonneg : 0 ≤ T := le_trans (by positivity) hT.1
  have hexcess : W.excess (k, T) = 0 := by
    rw [WindowSystem.excess, hspan]
    simp only [Nat.cast_zero, zero_sub]
    rw [max_eq_right]
    have heps : 0 ≤ W.epsilon * W.L :=
      mul_nonneg W.epsilon_nonneg (by positivity)
    linarith
  rw [hexcess] at hlarge
  have hnonneg : (0 : ℝ) ≤ W.m * Z0 := by positivity
  linarith

private theorem supportGap_anchor_mem_rawWindowGapWord (W : WindowSystem)
    (Z0 k : ℕ) (hk : k ∈ highAnchors W Z0) :
    supportGap W.enumeration k ∈ W.rawWindowGapWord k := by
  have hsk := exteriorHighAnchor_offset_le W Z0 k hk
  rw [rawWindowGapWord_eq_enumerationGapWord W k hsk]
  unfold enumerationGapWord
  rw [List.mem_map]
  refine ⟨W.s, ?_, ?_⟩
  · simp [WindowSystem.m]
  · congr 1
    omega

private theorem enumeration_anchor_succ_le_three_mul_X
    (W : WindowSystem) (Z0 k G : ℕ) (hk : k ∈ highAnchors W Z0)
    (hgap : ∀ g ∈ W.rawWindowGapWord k, g ≤ G) (hGX : G ≤ W.X) :
    W.enumeration.a (k + 1) ≤ 3 * W.X := by
  have hkAnchor : k ∈ W.anchors := by
    classical
    rw [highAnchors, Finset.mem_filter] at hk
    exact hk.1
  have hkUpper : W.enumeration.a k ≤ 2 * W.X := by
    classical
    simpa [WindowSystem.anchors] using (Finset.mem_filter.mp hkAnchor).2.2
  have hlast := hgap (supportGap W.enumeration k)
    (supportGap_anchor_mem_rawWindowGapWord W Z0 k hk)
  have hmono := W.enumeration.strictMono (Nat.lt_succ_self k)
  have hendpoint :
      W.enumeration.a k + supportGap W.enumeration k =
        W.enumeration.a (k + 1) := by
    simp only [supportGap]
    exact Nat.add_sub_of_le hmono.le
  omega

/-- Propagate the raw integer parameter of a primitive occurrence line through
two genuine prefixes of the same anchored suffix.  This is the point where
the exterior count keeps the original parameter rather than replacing it by
a primitive reparameterization. -/
private theorem occurrence_parameter_admissible_actual_prefix
    (W : WindowSystem) (Z0 k Cgap : ℕ)
    (hk : k ∈ highAnchors W Z0) (line : AffineLine)
    (hoccurrence : IsOccurrenceLine W Z0 (initialLongPrefix W k) line)
    (before word : GapWord)
    (hbefore : before.IsPrefix (actualPostPrefixGaps W k))
    (hcombined : (before ++ word).IsPrefix (actualPostPrefixGaps W k))
    (hgap : ∀ g ∈ W.rawWindowGapWord k,
      g ≤ W.L + Cgap + 1)
    (hgapScale : W.L + Cgap + 1 ≤ W.X) :
    ∃ t : ℤ,
      (((W.enumeration.a (k - W.s) +
          (initialLongPrefix W k).span : ℕ) : ℤ) =
          line.A + line.H * t ∧
        carryInt W.rational
            (W.enumeration.a (k - W.s) +
              (initialLongPrefix W k).span) =
          line.C + line.K * t) ∧
      t ∈ admissibleOriginalParameters W.rational.eta.den W.X
        (line.transformWord W.rational.eta.den before) word := by
  let p := initialLongPrefix W k
  let i := k - W.s
  let j := i + p.length
  have hsk := exteriorHighAnchor_offset_le W Z0 k hk
  have hpword : p = enumerationGapWord W.enumeration i p.length :=
    initialPrefix_eq_enumerationGapWord W Z0 k p hk rfl
  have hpspan := enumerationGapWord_span W.enumeration i p.length
  rw [← hpword] at hpspan
  have hstart : W.enumeration.a i + p.span = W.enumeration.a j := by
    have hmono := W.enumeration.strictMono.monotone
      (show i ≤ i + p.length by omega)
    dsimp [j]
    omega
  have hcontains := hoccurrence k hk rfl
  rcases hcontains with ⟨t, hx, hr⟩
  have hxStart : (W.enumeration.a j : ℤ) = line.A + line.H * t := by
    rw [← hstart]
    exact hx
  have hrStart : carryInt W.rational (W.enumeration.a j) =
      line.C + line.K * t := by
    rw [← hstart]
    exact hr
  have hbeforeWord : before = enumerationGapWord W.enumeration j before.length := by
    simpa [i, p, j] using
      prefix_actualPostPrefixGaps_eq_enumerationGapWord W Z0 k hsk hk
        before hbefore
  have hcombinedWord : before ++ word =
      enumerationGapWord W.enumeration j (before ++ word).length := by
    simpa [i, p, j] using
      prefix_actualPostPrefixGaps_eq_enumerationGapWord W Z0 k hsk hk
        (before ++ word) hcombined
  have hbeforeParameter :=
    line.transformWord_parameter_enumerationGapWord
      W.rational.eta.den W.rational rfl W.enumeration j before.length t
        hxStart hrStart
  rw [← hbeforeWord] at hbeforeParameter
  have hcombinedParameter :=
    line.transformWord_parameter_enumerationGapWord
      W.rational.eta.den W.rational rfl W.enumeration j
        (before ++ word).length t hxStart hrStart
  rw [← hcombinedWord] at hcombinedParameter
  have hpLength : p.length ≤ W.m := by
    exact (GapWord.firstPrefixAbove_length_le (W.rawWindowGapWord k) _).trans
      (rawWindowGapWord_length_le W k)
  have hactual : actualPostPrefixGaps W k =
      enumerationGapWord W.enumeration j (W.m - p.length) := by
    simpa [i, p, j] using
      actualPostPrefixGaps_eq_enumerationGapWord W Z0 k hsk hk
  have hbeforeLength : before.length ≤ W.m - p.length := by
    have h := hbefore.length_le
    rw [hactual] at h
    simpa [enumerationGapWord] using h
  have hcombinedLength : (before ++ word).length ≤ W.m - p.length := by
    have h := hcombined.length_le
    rw [hactual] at h
    simpa [enumerationGapWord] using h
  have hbeforeIndex : j + before.length ≤ k + 1 := by
    dsimp [i, j]
    rw [WindowSystem.m] at hpLength hbeforeLength
    omega
  have hcombinedIndex : j + (before ++ word).length ≤ k + 1 := by
    dsimp [i, j]
    rw [WindowSystem.m] at hpLength hcombinedLength
    omega
  have hanchorEnd : W.enumeration.a (k + 1) ≤ 3 * W.X :=
    enumeration_anchor_succ_le_three_mul_X W Z0 k
      (W.L + Cgap + 1) hk hgap hgapScale
  have hbeforeEnd : W.enumeration.a (j + before.length) ≤ 3 * W.X :=
    (W.enumeration.strictMono.monotone hbeforeIndex).trans hanchorEnd
  have hcombinedEnd :
      W.enumeration.a (j + (before ++ word).length) ≤ 3 * W.X :=
    (W.enumeration.strictMono.monotone hcombinedIndex).trans hanchorEnd
  have admissibleAt (n : ℕ)
      (hn : W.enumeration.a n ≤ 3 * W.X) :
      InAdmissibleCarryRegion W.rational.eta.den W.X
        (W.enumeration.a n) (carryInt W.rational (W.enumeration.a n)) := by
    refine ⟨?_, ?_, (prop_carry W.rational).2.1 _,
      (prop_carry W.rational).2.2.1 _⟩
    · have hx : (0 : ℤ) ≤ W.enumeration.a n := by positivity
      have hX : (0 : ℤ) ≤ W.X := by positivity
      omega
    · exact_mod_cast hn
  refine ⟨t, ?_, ?_⟩
  · simpa [p, i] using And.intro hx hr
  · change InAdmissibleCarryRegion W.rational.eta.den W.X
        ((line.transformWord W.rational.eta.den before).A +
          (line.transformWord W.rational.eta.den before).H * t)
        ((line.transformWord W.rational.eta.den before).C +
          (line.transformWord W.rational.eta.den before).K * t) ∧
      InAdmissibleCarryRegion W.rational.eta.den W.X
        (((line.transformWord W.rational.eta.den before).transformWord
          W.rational.eta.den word).A +
          ((line.transformWord W.rational.eta.den before).transformWord
            W.rational.eta.den word).H * t)
        (((line.transformWord W.rational.eta.den before).transformWord
          W.rational.eta.den word).C +
          ((line.transformWord W.rational.eta.den before).transformWord
            W.rational.eta.den word).K * t)
    constructor
    · rw [← hbeforeParameter.1, ← hbeforeParameter.2]
      exact admissibleAt _ hbeforeEnd
    · rw [← AffineLine.transformWord_append,
        ← hcombinedParameter.1, ← hcombinedParameter.2]
      exact admissibleAt _ hcombinedEnd

private theorem continuation_sublist_actualPostPrefix
    (W : WindowSystem) (Z0 : ℕ) (e : WindowThreshold)
    (record : FirstExitRecord) (line : AffineLine)
    (continuation : GapWord)
    (hdescribe : FirstExitRecord.DescribesFirstExit W Z0 e record line continuation) :
    continuation <+ actualPostPrefixGaps W e.1 := by
  rcases hdescribe with
    ⟨base, finish, before, after, _hbase, hsuffix, _hbefore,
      _hcontinuation, _hexterior, _hfirst, _hrecord⟩
  rw [hsuffix]
  exact (List.sublist_append_right before continuation).trans
    (List.sublist_append_left (before ++ continuation) after)

/-- Bind a valid exterior signature back to one genuine anchor, replacing the
raw occurrence line by the deterministic primitive line for its prefix.  The
canonical-line equality transfers the first-exit dynamics, while the actual
support run preserves one original integer parameter. -/
private theorem validExteriorSignature_has_source
    (W : WindowSystem) (Z0 Cgap : ℕ)
    (hQ : 0 < W.rational.eta.den)
    (hcutoff : 1 < frequencyCutoff W)
    (e : WindowThreshold) (he : LongExteriorPair W Z0 e)
    (signature : ExteriorSignature)
    (hvalid : ValidExteriorSignature W Z0 Cgap e signature)
    (hprimitive : HasPrimitiveOccurrenceLine W Z0
      (initialLongPrefix W e.1))
    (hgap : ∀ g ∈ W.rawWindowGapWord e.1,
      g ≤ W.L + Cgap + 1)
    (hgapScale : W.L + Cgap + 1 ≤ W.X) :
    ∃ source : ExteriorSource W Z0 (chosenExteriorLine W Z0),
      source.anchor = e.1 ∧ source.record = signature.record ∧
        source.word = signature.word := by
  rcases hvalid with
    ⟨_hrecordValid, hwordPositive, exitLine, continuation,
      hdescribe, _hexteriorTrajectory, hwordEq⟩
  rcases hdescribe with
    ⟨base, _finish, before, after, hbase, hsuffix, hbeforeTrajectory,
      _hcontinuationTrajectory, hexitExterior, hfirst, hrecordEq⟩
  let p := initialLongPrefix W e.1
  have hchosen := chosenExteriorLine_spec W Z0 p hprimitive
  have hcanonical :
      (chosenExteriorLine W Z0 p).canonicalGeometricLine =
        base.canonicalGeometricLine := by
    apply occurrenceLines_canonical_eq_of_frequent W Z0 p hcutoff he.2.1
    · exact hchosen.1
    · exact hbase
  have hslope : (chosenExteriorLine W Z0 p).slope W.rational.eta.den =
      base.slope W.rational.eta.den := by
    calc
      (chosenExteriorLine W Z0 p).slope W.rational.eta.den =
          (chosenExteriorLine W Z0 p).canonicalGeometricLine.slope
            W.rational.eta.den :=
        (AffineLine.canonicalGeometricLine_slope W.rational.eta.den hQ _).symm
      _ = base.canonicalGeometricLine.slope W.rational.eta.den := by
        rw [hcanonical]
      _ = base.slope W.rational.eta.den :=
        AffineLine.canonicalGeometricLine_slope W.rational.eta.den hQ _
  have hchosenFirst : ∀ r < before.length,
      classifySlope
        (((chosenExteriorLine W Z0 p).transformWord W.rational.eta.den
          (before.take r)).slope W.rational.eta.den) ≠ .exterior := by
    intro r hr
    rcases hfirst r hr with ⟨state, hstate, hbaseNon⟩
    have hstateEq : state =
        base.transformWord W.rational.eta.den (before.take r) :=
      (sharedGapTrajectory_iff_eq_transformWord _ _ _ _).1 hstate
    subst state
    rw [AffineLine.transformWord_slope_eq_of_slope_eq
      W.rational.eta.den hQ (chosenExteriorLine W Z0 p) base
      (before.take r) hslope]
    exact hbaseNon
  have hexitEq : exitLine =
      base.transformWord W.rational.eta.den before :=
    (sharedGapTrajectory_iff_eq_transformWord _ _ _ _).1 hbeforeTrajectory
  have hchosenExit :
      classifySlope
        (((chosenExteriorLine W Z0 p).transformWord W.rational.eta.den
          before).slope W.rational.eta.den) = .exterior := by
    rw [AffineLine.transformWord_slope_eq_of_slope_eq
      W.rational.eta.den hQ (chosenExteriorLine W Z0 p) base before hslope,
      ← hexitEq]
    exact hexitExterior
  have hbeforePrefix : before.IsPrefix (actualPostPrefixGaps W e.1) :=
    ⟨continuation ++ after, by
      simpa only [List.append_assoc] using hsuffix.symm⟩
  have hcontinuationSub : continuation <+ actualPostPrefixGaps W e.1 := by
    rw [hsuffix]
    exact (List.sublist_append_right before continuation).trans
      (List.sublist_append_left (before ++ continuation) after)
  have hcontinuationPositive : continuation.Positive := by
    intro g hg
    exact actualPostPrefixGaps_positive W e.1 g
      (hcontinuationSub.subset hg)
  have hchosenContinuation : IsExteriorTrajectory W.rational.eta.den
      ((chosenExteriorLine W Z0 p).transformWord W.rational.eta.den before)
      continuation :=
    isExteriorTrajectory_of_positive W.rational.eta.den hQ _ _
      hcontinuationPositive hchosenExit
  have hrecordChosen : signature.record =
      FirstExitRecord.ofFirstExit W.rational.eta.den
        (chosenExteriorLine W Z0 p) before := by
    calc
      signature.record = FirstExitRecord.ofFirstExit W.rational.eta.den
          base before := hrecordEq
      _ = FirstExitRecord.ofFirstExit W.rational.eta.den
          (chosenExteriorLine W Z0 p) before :=
        FirstExitRecord.ofFirstExit_eq_of_slope_eq W.rational.eta.den hQ
          base (chosenExteriorLine W Z0 p) before hslope.symm
  have hwordPrefix : signature.word.IsPrefix continuation := by
    rw [hwordEq]
    exact GapWord.firstPrefixAbove_isPrefix _ _
  have hcombinedPrefix : (before ++ signature.word).IsPrefix
      (actualPostPrefixGaps W e.1) := by
    rcases hwordPrefix with ⟨tail, htail⟩
    refine ⟨tail ++ after, ?_⟩
    calc
      (before ++ signature.word) ++ (tail ++ after) =
          before ++ (signature.word ++ tail) ++ after := by
        simp only [List.append_assoc]
      _ = before ++ continuation ++ after := by rw [htail]
      _ = actualPostPrefixGaps W e.1 := hsuffix.symm
  have hkHigh : e.1 ∈ highAnchors W Z0 := by
    classical
    rw [highAnchors, Finset.mem_filter]
    exact ⟨he.1.1.1, e.2, he.1.1.2, he.1.2⟩
  have hparameter := occurrence_parameter_admissible_actual_prefix
    W Z0 e.1 Cgap hkHigh (chosenExteriorLine W Z0 p) hchosen.1
      before signature.word hbeforePrefix hcombinedPrefix hgap hgapScale
  rcases hparameter with ⟨parameter, hinitial, hadmissible⟩
  let source : ExteriorSource W Z0 (chosenExteriorLine W Z0) :=
    { anchor := e.1
      threshold := e.2
      offset_le := exteriorHighAnchor_offset_le W Z0 e.1 hkHigh
      pair := he
      before := before
      continuation := continuation
      after := after
      record := signature.record
      word := signature.word
      parameter := parameter
      occurrence := by simpa only [p] using hchosen.1
      suffix_eq := hsuffix
      first_nonexterior := by simpa only [p] using hchosenFirst
      exit_exterior := by simpa only [p] using hchosenExit
      continuation_exterior := by simpa only [p] using hchosenContinuation
      record_eq := by simpa only [p] using hrecordChosen
      word_eq := hwordEq
      initial_parameter := by simpa only [p] using hinitial
      admissible := by simpa only [p] using hadmissible }
  exact ⟨source, rfl, rfl, rfl⟩

/-- A finite source family is counted by initial prefix, deterministic
first-exit signature, and the surviving original integer parameter.  The
last coordinate is genuinely injective on each fixed prefix/signature fibre. -/
private theorem exteriorAnchors_card_le_of_sources
    (W : WindowSystem) (Z0 Cgap : ℕ)
    (hQ : 0 < W.rational.eta.den) (Coff : ℝ) (_hCoff : 0 < Coff)
    (hfixed : ∀ X : ℕ, ∀ line : AffineLine, ∀ word : GapWord,
      word.Positive →
      classifySlope (line.slope W.rational.eta.den) = .exterior →
      (admissibleOriginalParameters W.rational.eta.den X line word).Finite ∧
        ((admissibleOriginalParameters W.rational.eta.den X line word).ncard : ℝ) ≤
          1 + Coff * X * (2 : ℝ) ^ (-(word.span : ℤ)))
    (hsignaturesFinite : (exteriorSignatures W Z0 Cgap).Finite)
    (sourceFor : {k // k ∈ exteriorAnchors W Z0} →
      ExteriorSource W Z0 (chosenExteriorLine W Z0))
    (signatureFor : {k // k ∈ exteriorAnchors W Z0} → ExteriorSignature)
    (hanchor : ∀ k, (sourceFor k).anchor = k.1)
    (hsignature : ∀ k, signatureFor k ∈ exteriorSignatures W Z0 Cgap)
    (hrecord : ∀ k, (sourceFor k).record = (signatureFor k).record)
    (hword : ∀ k, (sourceFor k).word = (signatureFor k).word)
    (hsmall : ∀ k,
      Coff * W.X * (2 : ℝ) ^ (-((sourceFor k).word.span : ℤ)) ≤ 1) :
    (exteriorAnchors W Z0).card ≤
      (initialPrefixes W Z0).card *
        (exteriorSignatures W Z0 Cgap).ncard * 2 := by
  classical
  let Anchor := {k // k ∈ exteriorAnchors W Z0}
  let signatures : Finset ExteriorSignature :=
    hsignaturesFinite.toFinset
  let codes : Finset (GapWord × ExteriorSignature) :=
    (initialPrefixes W Z0).product signatures
  let fibre : GapWord × ExteriorSignature → Finset Anchor := fun code =>
    Finset.univ.filter fun k =>
      (initialLongPrefix W k.1, signatureFor k) = code
  have highOfAnchor (k : Anchor) : k.1 ∈ highAnchors W Z0 := by
    have hpair := (sourceFor k).pair
    rw [hanchor k] at hpair
    rw [highAnchors, Finset.mem_filter]
    exact ⟨hpair.1.1.1, (sourceFor k).threshold,
      hpair.1.1.2, hpair.1.2⟩
  have hprefixMem (k : Anchor) :
      initialLongPrefix W k.1 ∈ initialPrefixes W Z0 := by
    rw [initialPrefixes, Finset.mem_image]
    exact ⟨k.1, highOfAnchor k, rfl⟩
  have hcodes (k : Anchor) :
      (initialLongPrefix W k.1, signatureFor k) ∈ codes := by
    change (initialLongPrefix W k.1, signatureFor k) ∈
      (initialPrefixes W Z0).product signatures
    exact Finset.mem_product.mpr ⟨hprefixMem k, by
      simpa only [signatures, Set.Finite.mem_toFinset] using hsignature k⟩
  have hcover : (Finset.univ : Finset Anchor) ⊆ codes.biUnion fibre := by
    intro k _hk
    rw [Finset.mem_biUnion]
    refine ⟨(initialLongPrefix W k.1, signatureFor k), hcodes k, ?_⟩
    change k ∈ (Finset.univ : Finset Anchor).filter fun j =>
      (initialLongPrefix W j.1, signatureFor j) =
        (initialLongPrefix W k.1, signatureFor k)
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, rfl⟩
  have hfibreCard : ∀ code ∈ codes, (fibre code).card ≤ 2 := by
    intro code hcode
    by_cases hempty : fibre code = ∅
    · simp [hempty]
    · obtain ⟨baseAnchor, hbaseAnchor⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      let parameters : Finset ℤ :=
        (fibre code).image fun k => (sourceFor k).parameter
      have hparameterInjective : Set.InjOn
          (fun k : Anchor => (sourceFor k).parameter) (fibre code) := by
        intro left hleft right hright hparameter
        have hleftCode := (Finset.mem_filter.mp hleft).2
        have hrightCode := (Finset.mem_filter.mp hright).2
        have hprefixValues : initialLongPrefix W left.1 =
            initialLongPrefix W right.1 := by
          exact congrArg Prod.fst (hleftCode.trans hrightCode.symm)
        have hsignatureValues : signatureFor left = signatureFor right := by
          exact congrArg Prod.snd (hleftCode.trans hrightCode.symm)
        have hsourcePrefix : initialLongPrefix W (sourceFor left).anchor =
            initialLongPrefix W (sourceFor right).anchor := by
          rw [hanchor left, hanchor right]
          exact hprefixValues
        have hsourceRecord : (sourceFor left).record =
            (sourceFor right).record := by
          rw [hrecord left, hrecord right, hsignatureValues]
        have hsourceWord : (sourceFor left).word =
            (sourceFor right).word := by
          rw [hword left, hword right, hsignatureValues]
        have hsourceCode : (sourceFor left).code = (sourceFor right).code := by
          simp only [ExteriorSource.code, Prod.mk.injEq]
          exact ⟨hsourcePrefix, hsourceRecord, hsourceWord, hparameter⟩
        have hanchors :=
          ExteriorSource.code_injective_on_anchor
            (sourceFor left) (sourceFor right) hsourceCode
        apply Subtype.ext
        rw [← hanchor left, ← hanchor right]
        exact hanchors
      have hparametersCard : parameters.card = (fibre code).card := by
        exact Finset.card_image_of_injOn hparameterInjective
      have hbaseCode := (Finset.mem_filter.mp hbaseAnchor).2
      have hparametersSubset : (parameters : Set ℤ) ⊆
          admissibleOriginalParameters W.rational.eta.den W.X
            (sourceFor baseAnchor).exitLine (sourceFor baseAnchor).word := by
        intro t ht
        change t ∈ (fibre code).image
          (fun k => (sourceFor k).parameter) at ht
        rw [Finset.mem_image] at ht
        rcases ht with ⟨anchor, hanchorFibre, rfl⟩
        have hanchorCode := (Finset.mem_filter.mp hanchorFibre).2
        have hprefixValues : initialLongPrefix W anchor.1 =
            initialLongPrefix W baseAnchor.1 := by
          exact congrArg Prod.fst (hanchorCode.trans hbaseCode.symm)
        have hsignatureValues : signatureFor anchor = signatureFor baseAnchor := by
          exact congrArg Prod.snd (hanchorCode.trans hbaseCode.symm)
        have hsourcePrefix : initialLongPrefix W (sourceFor anchor).anchor =
            initialLongPrefix W (sourceFor baseAnchor).anchor := by
          rw [hanchor anchor, hanchor baseAnchor]
          exact hprefixValues
        have hsourceRecord : (sourceFor anchor).record =
            (sourceFor baseAnchor).record := by
          rw [hrecord anchor, hrecord baseAnchor, hsignatureValues]
        have hsourceBefore := ExteriorSource.before_eq_of_prefix_record hQ
          (sourceFor anchor) (sourceFor baseAnchor) hsourcePrefix hsourceRecord
        have hsourceWord : (sourceFor anchor).word =
            (sourceFor baseAnchor).word := by
          rw [hword anchor, hword baseAnchor, hsignatureValues]
        have hbaseLine : (sourceFor anchor).baseLine =
            (sourceFor baseAnchor).baseLine := by
          simpa only [ExteriorSource.baseLine] using
            congrArg (chosenExteriorLine W Z0) hsourcePrefix
        have hexitLine : (sourceFor anchor).exitLine =
            (sourceFor baseAnchor).exitLine := by
          simp only [ExteriorSource.exitLine]
          rw [hbaseLine, hsourceBefore]
        have hadmissible := (sourceFor anchor).admissible
        change (sourceFor anchor).parameter ∈
          admissibleOriginalParameters W.rational.eta.den W.X
            (sourceFor anchor).exitLine (sourceFor anchor).word at hadmissible
        rw [hexitLine, hsourceWord] at hadmissible
        exact hadmissible
      have hbaseWordPositive : (sourceFor baseAnchor).word.Positive := by
        have hmem := hsignature baseAnchor
        rcases hmem with ⟨_e, _he, hvalid⟩
        rw [hword baseAnchor]
        exact hvalid.2.1
      have hfixedBase := hfixed W.X (sourceFor baseAnchor).exitLine
        (sourceFor baseAnchor).word hbaseWordPositive
          (sourceFor baseAnchor).exit_exterior
      have hparameterBound :
          (admissibleOriginalParameters W.rational.eta.den W.X
            (sourceFor baseAnchor).exitLine
              (sourceFor baseAnchor).word).ncard ≤ 2 := by
        have hreal :
            ((admissibleOriginalParameters W.rational.eta.den W.X
              (sourceFor baseAnchor).exitLine
                (sourceFor baseAnchor).word).ncard : ℝ) ≤ 2 :=
          hfixedBase.2.trans (by nlinarith [hsmall baseAnchor])
        exact_mod_cast hreal
      have hparametersLe : parameters.card ≤
          (admissibleOriginalParameters W.rational.eta.den W.X
            (sourceFor baseAnchor).exitLine
              (sourceFor baseAnchor).word).ncard := by
        have hsubsetFinset : parameters ⊆ hfixedBase.1.toFinset := by
          intro t ht
          rw [Set.Finite.mem_toFinset]
          exact hparametersSubset ht
        simpa [Set.ncard_eq_toFinset_card _ hfixedBase.1] using
          Finset.card_le_card hsubsetFinset
      rw [← hparametersCard]
      exact hparametersLe.trans hparameterBound
  have hcardCover : (Finset.univ : Finset Anchor).card ≤
      ∑ code ∈ codes, (fibre code).card :=
    (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hsumBound : (∑ code ∈ codes, (fibre code).card) ≤ codes.card * 2 := by
    calc
      (∑ code ∈ codes, (fibre code).card) ≤ ∑ _code ∈ codes, 2 := by
        exact Finset.sum_le_sum fun code hcode => hfibreCard code hcode
      _ = codes.card * 2 := by simp
  have hanchorCard : (exteriorAnchors W Z0).card =
      (Finset.univ : Finset Anchor).card := by
    simp [Anchor]
  have hcodesCard : codes.card =
      (initialPrefixes W Z0).card *
        (exteriorSignatures W Z0 Cgap).ncard := by
    dsimp [codes]
    rw [Finset.card_product]
    simp only [signatures, Set.ncard_eq_toFinset_card _ hsignaturesFinite]
  calc
    (exteriorAnchors W Z0).card =
        (Finset.univ : Finset Anchor).card := hanchorCard
    _ ≤ ∑ code ∈ codes, (fibre code).card := hcardCover
    _ ≤ codes.card * 2 := hsumBound
    _ = (initialPrefixes W Z0).card *
        (exteriorSignatures W Z0 Cgap).ncard * 2 := by rw [hcodesCard]

/-- Every signature is contained in a denominator-uniform finite record ×
word box. -/
theorem exteriorSignatures_finite_and_ncard_le
    (context : FixedScaleContext) (gap : GapParams context.Q)
    (F : ScaleFamily) (hF : F.MatchesContext context) (Z0 : ℕ) :
    ∀ᶠ L : ℕ in atTop,
      (exteriorSignatures (F.system L) Z0 gap.Cgap).Finite ∧
      ((exteriorSignatures (F.system L) Z0 gap.Cgap).ncard : ℕ) ≤
        (((F.system L).m + 1) * 4 * ((F.system L).m + 1) *
            ((F.system L).L + gap.Cgap + 2)) *
          (∑ r ∈ Finset.Icc 0 (F.system L).m,
            (exteriorWordBound (F.system L) gap.Cgap).choose r) := by
  filter_upwards [eventually_rawWindowGap_le context gap F hF] with L hgap
  let W := F.system L
  let signatures := exteriorSignatures W Z0 gap.Cgap
  let words : Set GapWord :=
    {word | word.Positive ∧
      word.span ≤ exteriorWordBound W gap.Cgap ∧ word.length ≤ W.m}
  have hsignatureMaps : Set.MapsTo
      (fun signature : ExteriorSignature => (signature.record, signature.word))
      signatures (validFirstExitRecords W.m W.L gap.Cgap ×ˢ words) := by
    intro signature hsignature
    rcases hsignature with ⟨e, he, hvalid⟩
    rcases hvalid with
      ⟨hrecord, hwordPositive, line, continuation, hdescribe,
        _hexterior, hword⟩
    have heAnchor : e.1 ∈ W.anchors := he.1.1.1
    have hcontinuationSub : continuation <+ actualPostPrefixGaps W e.1 :=
      continuation_sublist_actualPostPrefix W Z0 e signature.record line
        continuation hdescribe
    have hwordPrefix : signature.word.IsPrefix continuation := by
      rw [hword]
      exact GapWord.firstPrefixAbove_isPrefix _ _
    have hwordSubActual : signature.word <+ actualPostPrefixGaps W e.1 :=
      hwordPrefix.sublist.trans hcontinuationSub
    have hlength : signature.word.length ≤ W.m :=
      hwordSubActual.length_le.trans (actualPostPrefixGaps_length_le W e.1)
    have hwordGap : ∀ g ∈ signature.word, g ≤ W.L + gap.Cgap + 1 := by
      intro g hg
      have hgActual : g ∈ actualPostPrefixGaps W e.1 :=
        hwordSubActual.subset hg
      have hgRaw : g ∈ W.rawWindowGapWord e.1 :=
        List.mem_of_mem_drop hgActual
      simpa [W, F.level_eq] using hgap e.1 heAnchor g hgRaw
    have hspan : signature.word.span ≤ exteriorWordBound W gap.Cgap := by
      rw [hword]
      simpa [postExitLongPrefix, exteriorWordBound, Nat.add_assoc] using
        GapWord.span_firstPrefixAbove_le_add continuation
          (Nat.floor (W.structural.Gamma * W.L))
          (W.L + gap.Cgap + 1) (by
            intro g hg
            have hgActual : g ∈ actualPostPrefixGaps W e.1 :=
              hcontinuationSub.subset hg
            have hgRaw : g ∈ W.rawWindowGapWord e.1 :=
              List.mem_of_mem_drop hgActual
            simpa [W, F.level_eq] using hgap e.1 heAnchor g hgRaw)
    exact ⟨hrecord, hwordPositive, hspan, hlength⟩
  have hrecordFinite :=
    (validFirstExitRecords_finite_and_ncard_le W.m W.L gap.Cgap).1
  have hwordsFinite : words.Finite := by
    apply (positiveGapWords_bounded_finite
      (exteriorWordBound W gap.Cgap) W.m).subset
    intro word hword
    exact hword
  have htargetFinite :
      (validFirstExitRecords W.m W.L gap.Cgap ×ˢ words).Finite :=
    hrecordFinite.prod hwordsFinite
  have hsignatureImageFinite :
      ((fun signature : ExteriorSignature =>
          (signature.record, signature.word)) '' signatures).Finite := by
    apply htargetFinite.subset
    rintro _ ⟨signature, hsignature, rfl⟩
    exact hsignatureMaps hsignature
  have hencodeInjective : Function.Injective
      (fun signature : ExteriorSignature =>
        (signature.record, signature.word)) := by
    intro a b h
    cases a
    cases b
    simp_all
  have hsignaturesFinite : signatures.Finite :=
    Set.Finite.of_finite_image hsignatureImageFinite hencodeInjective.injOn
  have hwordsCard : words.ncard ≤
      ∑ r ∈ Finset.Icc 0 W.m,
        (exteriorWordBound W gap.Cgap).choose r := by
    have hfinset := positiveGapWords_card_le_compositions
      hwordsFinite.toFinset (exteriorWordBound W gap.Cgap) W.m
      (by
        intro word hword g hg
        have hw : word ∈ words := by
          simpa only [Set.Finite.mem_toFinset] using hword
        exact hw.1 g hg)
      (by
        intro word hword
        have hw : word ∈ words := by
          simpa only [Set.Finite.mem_toFinset] using hword
        exact hw.2.1)
      (by
        intro word hword
        have hw : word ∈ words := by
          simpa only [Set.Finite.mem_toFinset] using hword
        exact hw.2.2)
    simpa [Set.ncard_eq_toFinset_card words hwordsFinite] using hfinset
  have hsignatureCard : signatures.ncard ≤
      (validFirstExitRecords W.m W.L gap.Cgap).ncard * words.ncard := by
    calc
      signatures.ncard =
          ((fun signature : ExteriorSignature =>
            (signature.record, signature.word)) '' signatures).ncard := by
        symm
        exact Set.ncard_image_of_injective _ hencodeInjective
      _ ≤ (validFirstExitRecords W.m W.L gap.Cgap ×ˢ words).ncard :=
        Set.ncard_le_ncard (by
          rintro _ ⟨signature, hsignature, rfl⟩
          exact hsignatureMaps hsignature) htargetFinite
      _ = (validFirstExitRecords W.m W.L gap.Cgap).ncard * words.ncard :=
        Set.ncard_prod
  refine ⟨hsignaturesFinite, ?_⟩
  calc
    signatures.ncard ≤
        (validFirstExitRecords W.m W.L gap.Cgap).ncard * words.ncard :=
      hsignatureCard
    _ ≤ (((W.m + 1) * 4 * (W.m + 1) * (W.L + gap.Cgap + 2))) *
          (∑ r ∈ Finset.Icc 0 W.m,
            (exteriorWordBound W gap.Cgap).choose r) := by
      exact Nat.mul_le_mul
        (validFirstExitRecords_finite_and_ncard_le W.m W.L gap.Cgap).2
        hwordsCard

private theorem longExteriorPair_has_signature
    (context : FixedScaleContext) (gap : GapParams context.Q)
    (F : ScaleFamily) (hF : F.MatchesContext context) (Z0 L : ℕ)
    (hcutoff : 4 * context.structural.Gamma / context.entropy.kappa < Z0)
    (hgap : ∀ k : ℕ, k ∈ (F.system L).anchors →
      ∀ g ∈ (F.system L).rawWindowGapWord k,
        g ≤ L + gap.Cgap + 1)
    (e : WindowThreshold) (he : LongExteriorPair (F.system L) Z0 e) :
    ∃ signature : ExteriorSignature,
      signature ∈ exteriorSignatures (F.system L) Z0 gap.Cgap ∧
      ValidExteriorSignature (F.system L) Z0 gap.Cgap e signature ∧
      (F.system L).structural.Gamma * L < signature.word.span ∧
      (signature.word.span : ℝ) ≤
        ((F.system L).structural.Gamma + 1) * L + (gap.Cgap + 1) ∧
      signature.word.length ≤ (F.system L).m := by
  let W := F.system L
  rcases he.2.2.2 with
    ⟨line, continuation, hactual, hexteriorTrajectory, hspanContinuation⟩
  rcases hactual with
    ⟨base, finish, before, after, hbase, hsuffix, hbefore, hfirst,
      hlineExterior, hcontinuation⟩
  let record := FirstExitRecord.ofFirstExit W.rational.eta.den base before
  let word := postExitLongPrefix W continuation
  let signature : ExteriorSignature := ⟨record, word⟩
  have heAnchor : e.1 ∈ W.anchors := he.1.1.1
  have hactualPositive := actualPostPrefixGaps_positive W e.1
  have hbeforePrefix : before.IsPrefix (actualPostPrefixGaps W e.1) := by
    exact ⟨continuation ++ after, by simpa [List.append_assoc] using hsuffix.symm⟩
  have hcontinuationSub : continuation <+ actualPostPrefixGaps W e.1 := by
    rw [hsuffix]
    exact (List.sublist_append_right before continuation).trans
      (List.sublist_append_left (before ++ continuation) after)
  have hbeforePositive : before.Positive := by
    intro g hg
    exact hactualPositive g (hbeforePrefix.mem hg)
  have hcontinuationPositive : continuation.Positive := by
    intro g hg
    exact hactualPositive g (hcontinuationSub.subset hg)
  have hbeforeLength : before.length ≤ W.m :=
    hbeforePrefix.length_le.trans (actualPostPrefixGaps_length_le W e.1)
  have hbeforeGap : ∀ g ∈ before, g ≤ W.L + gap.Cgap + 1 := by
    intro g hg
    simpa [W, F.level_eq] using hgap e.1 heAnchor g
      (List.mem_of_mem_drop (hbeforePrefix.subset hg))
  have hrecordValid : record.Valid W.m W.L gap.Cgap := by
    apply FirstExitRecord.ofFirstExit_valid W.rational.eta.den W.m W.L
      gap.Cgap
    · have hden : W.rational.eta.den = context.Q := by
        change (F.system L).rational.eta.den = context.Q
        rw [F.rational_eq, hF.1]
      simpa [hden] using context.Q_pos
    · exact hbefore
    · exact hlineExterior
    · exact hbeforeLength
    · exact hbeforePositive
    · exact hbeforeGap
  have hdescribe : FirstExitRecord.DescribesFirstExit W Z0 e record line continuation := by
    refine ⟨base, finish, before, after, hbase, hsuffix, hbefore,
      hcontinuation, hlineExterior, ?_, rfl⟩
    intro r hr
    let state := base.transformWord W.rational.eta.den (before.take r)
    have hstate : SharedGapTrajectory W.rational.eta.den base
        (before.take r) state :=
      (sharedGapTrajectory_iff_eq_transformWord _ _ _ _).2 rfl
    exact ⟨state, hstate, hfirst r hr state hstate⟩
  have hsignatureValid : ValidExteriorSignature W Z0 gap.Cgap e signature := by
    refine ⟨hrecordValid, ?_, line, continuation, hdescribe,
      hexteriorTrajectory, rfl⟩
    exact GapWord.firstPrefixAbove_positive continuation _ hcontinuationPositive
  have hmLower : context.entropy.kappa * (L : ℝ) < (W.m : ℝ) := by
    have hs : W.s = Nat.floor (context.entropy.kappa * (L : ℝ)) := by
      change (F.system L).s = _
      rw [F.offset_eq, hF.2.2.1]
    rw [WindowSystem.m, hs]
    simpa only [Nat.cast_add, Nat.cast_one] using
      (Nat.lt_floor_add_one (context.entropy.kappa * (L : ℝ)))
  have hZpos : (0 : ℝ) < Z0 := by
    have hquotPos : 0 <
        4 * context.structural.Gamma / context.entropy.kappa := by
      have hGamma : 0 < context.structural.Gamma :=
        lt_trans (by norm_num) context.structural.Gamma_gt
      exact div_pos (mul_pos (by norm_num) hGamma) context.entropy.kappa_pos
    exact hquotPos.trans hcutoff
  have hcoefficient :
      4 * context.structural.Gamma < context.entropy.kappa * (Z0 : ℝ) := by
    have := (div_lt_iff₀ context.entropy.kappa_pos).mp hcutoff
    simpa [mul_comm] using this
  have hscale :
      4 * context.structural.Gamma * (L : ℝ) < (W.m : ℝ) * Z0 := by
    have hleft :
        4 * context.structural.Gamma * (L : ℝ) ≤
          (context.entropy.kappa * (Z0 : ℝ)) * L := by
      exact mul_le_mul_of_nonneg_right hcoefficient.le (Nat.cast_nonneg L)
    have hright :
        (context.entropy.kappa * (Z0 : ℝ)) * L <
          (W.m : ℝ) * Z0 := by
      have := mul_lt_mul_of_pos_right hmLower hZpos
      nlinarith
    exact hleft.trans_lt hright
  have hlarge : (W.m : ℝ) * Z0 < W.excess e := by
    simpa only [Set.mem_setOf_eq] using he.1.2
  have hcontinuationCross :
      W.structural.Gamma * (L : ℝ) < (continuation.span : ℝ) := by
    have hstruct : W.structural = context.structural := by
      change (F.system L).structural = context.structural
      rw [F.structural_eq, hF.2.1]
    rw [hstruct]
    have hquarter :
        context.structural.Gamma * (L : ℝ) <
          (W.m : ℝ) * Z0 / 4 := by nlinarith
    have hdiv : (W.m : ℝ) * Z0 / 4 < W.excess e / 4 :=
      (div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 4)).2 hlarge
    exact hquarter.trans (hdiv.trans_le hspanContinuation)
  have hfloorCross :
      Nat.floor (W.structural.Gamma * W.L) < continuation.span := by
    have hnonneg : 0 ≤ W.structural.Gamma * (W.L : ℝ) := by
      have hGamma : 0 < W.structural.Gamma :=
        lt_trans (by norm_num) W.structural.Gamma_gt
      positivity
    have hcross : W.structural.Gamma * (W.L : ℝ) <
        (continuation.span : ℝ) := by
      simpa [W, F.level_eq] using hcontinuationCross
    exact_mod_cast (lt_of_le_of_lt (Nat.floor_le hnonneg) hcross)
  have hwordLowerNat :
      Nat.floor (W.structural.Gamma * W.L) < word.span := by
    exact GapWord.lt_span_firstPrefixAbove_of_lt_span _ _ hfloorCross
  have hwordLower : W.structural.Gamma * (L : ℝ) < (word.span : ℝ) := by
    have hlevel : W.L = L := F.level_eq L
    rw [← hlevel]
    have hnext := Nat.lt_floor_add_one (W.structural.Gamma * (W.L : ℝ))
    have hsucc : Nat.floor (W.structural.Gamma * W.L) + 1 ≤ word.span :=
      Nat.succ_le_iff.mpr hwordLowerNat
    exact hnext.trans_le (by exact_mod_cast hsucc)
  have hcontinuationGap : ∀ g ∈ continuation, g ≤ W.L + gap.Cgap + 1 := by
    intro g hg
    simpa [W, F.level_eq] using hgap e.1 heAnchor g
      (List.mem_of_mem_drop (hcontinuationSub.subset hg))
  have hwordUpperNat : word.span ≤
      Nat.floor (W.structural.Gamma * W.L) + (W.L + gap.Cgap + 1) := by
    exact GapWord.span_firstPrefixAbove_le_add continuation _ _ hcontinuationGap
  have hwordUpper : (word.span : ℝ) ≤
      (W.structural.Gamma + 1) * L + (gap.Cgap + 1) := by
    have hGamma : 0 < W.structural.Gamma :=
      lt_trans (by norm_num) W.structural.Gamma_gt
    have hnonneg : 0 ≤ W.structural.Gamma * (W.L : ℝ) := by positivity
    have hfloor := Nat.floor_le hnonneg
    have hcast : (word.span : ℝ) ≤
        (Nat.floor (W.structural.Gamma * W.L) : ℝ) +
          ((W.L : ℝ) + gap.Cgap + 1) := by
      exact_mod_cast hwordUpperNat
    rw [F.level_eq] at hfloor hcast
    nlinarith
  have hwordLength : word.length ≤ W.m := by
    exact (GapWord.firstPrefixAbove_length_le continuation _).trans
      (hcontinuationSub.length_le.trans (actualPostPrefixGaps_length_le W e.1))
  refine ⟨signature, ⟨e, he, hsignatureValid⟩, hsignatureValid,
    ?_, hwordUpper, hwordLength⟩
  simpa [signature, W] using hwordLower

private def exteriorCountSpanCap (context : FixedScaleContext)
    (gap : GapParams context.Q) (L : ℕ) : ℕ :=
  Nat.floor (context.structural.Gamma * (L : ℝ)) + L + gap.Cgap + 1

private def exteriorCountAlpha (context : FixedScaleContext)
    (gap : GapParams context.Q) (L : ℕ) : ℝ :=
  ((Nat.floor (context.entropy.kappa * (L : ℝ)) + 2 : ℕ) : ℝ) /
    ((exteriorCountSpanCap context gap L + 5 : ℕ) : ℝ)

/-- The absolute entropy discrepancy and the degree-six polynomial loss,
both measured as exponents of `X = 2^L`. -/
private def exteriorCountError (context : FixedScaleContext)
    (gap : GapParams context.Q) (L : ℕ) : ℝ :=
  if L = 0 then 0 else
    |(((exteriorCountSpanCap context gap L + 5 : ℕ) : ℝ) / (L : ℝ)) *
          binaryEntropy (exteriorCountAlpha context gap L) -
        exteriorPrefixExponent context.entropy| +
      6 * Real.log (((exteriorCountSpanCap context gap L + 5 : ℕ) : ℝ)) /
        ((L : ℝ) * Real.log 2)

private theorem exteriorCountError_tendsto_zero
    (context : FixedScaleContext) (gap : GapParams context.Q) :
    Tendsto (exteriorCountError context gap) atTop (𝓝 0) := by
  let A : ℝ := context.structural.Gamma + 1
  have hGamma : 0 < context.structural.Gamma :=
    lt_trans (by norm_num) context.structural.Gamma_gt
  have hA : 0 < A := by dsimp [A]; linarith
  have hA0 : A ≠ 0 := ne_of_gt hA
  have hnatTop : Tendsto (fun L : ℕ => (L : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hgammaFloor : Tendsto
      (fun L : ℕ =>
        (Nat.floor (context.structural.Gamma * (L : ℝ)) : ℝ) / (L : ℝ))
      atTop (𝓝 context.structural.Gamma) := by
    simpa using tendsto_natFloor_affine_div context.structural.Gamma 0
      hGamma (le_refl 0)
  have hconstDiv : Tendsto
      (fun L : ℕ => ((gap.Cgap + 6 : ℕ) : ℝ) / (L : ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hnatTop
  have hcap : Tendsto
      (fun L : ℕ =>
        ((exteriorCountSpanCap context gap L + 5 : ℕ) : ℝ) / (L : ℝ))
      atTop (𝓝 A) := by
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
      tendsto_const_nhds
    have hsum : Tendsto
        (fun L : ℕ =>
          (Nat.floor (context.structural.Gamma * (L : ℝ)) : ℝ) /
              (L : ℝ) + 1 + ((gap.Cgap + 6 : ℕ) : ℝ) / (L : ℝ))
        atTop (𝓝 A) := by
      simpa [A] using (hgammaFloor.add hone).add hconstDiv
    apply hsum.congr'
    filter_upwards [eventually_ge_atTop 1] with L hL
    have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
    dsimp [exteriorCountSpanCap, A]
    push_cast
    field_simp [hL0]
    ring
  have hkFloor : Tendsto
      (fun L : ℕ =>
        (Nat.floor (context.entropy.kappa * (L : ℝ)) : ℝ) / (L : ℝ))
      atTop (𝓝 context.entropy.kappa) := by
    simpa using tendsto_natFloor_affine_div context.entropy.kappa 0
      context.entropy.kappa_pos (le_refl 0)
  have htwoDiv : Tendsto (fun L : ℕ => (2 : ℝ) / (L : ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hnatTop
  have hnum : Tendsto
      (fun L : ℕ =>
        ((Nat.floor (context.entropy.kappa * (L : ℝ)) + 2 : ℕ) : ℝ) /
          (L : ℝ))
      atTop (𝓝 context.entropy.kappa) := by
    convert hkFloor.add htwoDiv using 1 <;> simp [Nat.cast_add, add_div]
  have halpha : Tendsto (exteriorCountAlpha context gap) atTop
      (𝓝 (context.entropy.kappa / A)) := by
    have hquot := hnum.div hcap hA0
    apply hquot.congr'
    filter_upwards [eventually_ge_atTop 1] with L hL
    have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
    dsimp [exteriorCountAlpha]
    field_simp
  have hentropy : Tendsto
      (fun L => binaryEntropy (exteriorCountAlpha context gap L))
      atTop (𝓝 (binaryEntropy (context.entropy.kappa / A))) :=
    binaryEntropy_continuous.continuousAt.tendsto.comp halpha
  have hmain : Tendsto
      (fun L : ℕ =>
        ((exteriorCountSpanCap context gap L + 5 : ℕ) : ℝ) / (L : ℝ) *
          binaryEntropy (exteriorCountAlpha context gap L))
      atTop (𝓝 (exteriorPrefixExponent context.entropy)) := by
    have := hcap.mul hentropy
    rw [exteriorPrefixExponent, context.entropy_structural]
    simpa only [A] using this
  have habs : Tendsto
      (fun L : ℕ =>
        |(((exteriorCountSpanCap context gap L + 5 : ℕ) : ℝ) / (L : ℝ)) *
            binaryEntropy (exteriorCountAlpha context gap L) -
          exteriorPrefixExponent context.entropy|)
      atTop (𝓝 0) := by
    have hconst : Tendsto
        (fun _ : ℕ => exteriorPrefixExponent context.entropy)
        atTop (𝓝 (exteriorPrefixExponent context.entropy)) :=
      tendsto_const_nhds
    simpa using (hmain.sub hconst).abs
  have hcapNatTop : Tendsto
      (fun L : ℕ => exteriorCountSpanCap context gap L + 5) atTop atTop := by
    exact Filter.tendsto_atTop_mono
      (fun L => by dsimp [exteriorCountSpanCap]; omega)
      (tendsto_id : Tendsto (fun L : ℕ => L) atTop atTop)
  have hcapRealTop : Tendsto
      (fun L : ℕ => ((exteriorCountSpanCap context gap L + 5 : ℕ) : ℝ))
      atTop atTop := hnatTop.comp hcapNatTop
  have hlogOverCap : Tendsto
      (fun L : ℕ =>
        Real.log (((exteriorCountSpanCap context gap L + 5 : ℕ) : ℝ)) /
          (((exteriorCountSpanCap context gap L + 5 : ℕ) : ℝ)))
      atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hcapRealTop
  have hlogOverL : Tendsto
      (fun L : ℕ =>
        Real.log (((exteriorCountSpanCap context gap L + 5 : ℕ) : ℝ)) /
          (L : ℝ))
      atTop (𝓝 0) := by
    have hprod := hlogOverCap.mul hcap
    have hprod' : Tendsto
        (fun L : ℕ =>
          Real.log (((exteriorCountSpanCap context gap L + 5 : ℕ) : ℝ)) /
              (((exteriorCountSpanCap context gap L + 5 : ℕ) : ℝ)) *
            (((exteriorCountSpanCap context gap L + 5 : ℕ) : ℝ) / (L : ℝ)))
        atTop (𝓝 0) := by simpa using hprod
    apply hprod'.congr'
    filter_upwards [eventually_ge_atTop 1] with L hL
    have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
    have hcapPos : (0 : ℝ) <
        ((exteriorCountSpanCap context gap L + 5 : ℕ) : ℝ) := by positivity
    field_simp [hL0, ne_of_gt hcapPos]
  have hpoly : Tendsto
      (fun L : ℕ =>
        6 * Real.log (((exteriorCountSpanCap context gap L + 5 : ℕ) : ℝ)) /
          ((L : ℝ) * Real.log 2))
      atTop (𝓝 0) := by
    have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
    have hsimple : Tendsto
        (fun L : ℕ =>
          (6 * (Real.log
            (((exteriorCountSpanCap context gap L + 5 : ℕ) : ℝ)) /
              (L : ℝ))) / Real.log 2)
        atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul hlogOverL).div_const (Real.log 2)
    apply hsimple.congr'
    filter_upwards [eventually_ge_atTop 1] with L hL
    have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
    field_simp [hL0, hlog2]
  have hsum : Tendsto
      (fun L : ℕ =>
        |(((exteriorCountSpanCap context gap L + 5 : ℕ) : ℝ) / (L : ℝ)) *
            binaryEntropy (exteriorCountAlpha context gap L) -
          exteriorPrefixExponent context.entropy| +
        6 * Real.log (((exteriorCountSpanCap context gap L + 5 : ℕ) : ℝ)) /
          ((L : ℝ) * Real.log 2))
      atTop (𝓝 0) := by simpa using habs.add hpoly
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop 1] with L hL
  simp only [exteriorCountError, Nat.ne_of_gt hL, if_false]

/-- Paper label: `lem:seconddeep` (Section 7).  The fixed additive word
constant and a denominator-level cutoff are chosen before the support.  For
each larger cutoff the subexponential counting error is shared by every
compatible family. -/
theorem lem_seconddeep (context : FixedScaleContext)
    (gap : GapParams context.Q) :
    ∃ CQ : ℝ, 0 < CQ ∧ ∃ Zmin : ℕ, ∀ Z0 : ℕ, Zmin ≤ Z0 →
      ∃ error : ℕ → ℝ, Tendsto error atTop (𝓝 0) ∧
      ∀ F : ScaleFamily, F.MatchesContext context →
        ∀ᶠ L : ℕ in atTop,
            (exteriorSignatures (F.system L) Z0 gap.Cgap).Finite ∧
            ((exteriorSignatures (F.system L) Z0 gap.Cgap).ncard : ℝ) ≤
            Real.rpow (F.system L).X
              (exteriorPrefixExponent (F.system L).entropy + error L) ∧
          ∀ e : WindowThreshold,
            LongExteriorPair (F.system L) Z0 e →
            ∃ signature : ExteriorSignature,
                signature ∈ exteriorSignatures (F.system L) Z0 gap.Cgap ∧
              (F.system L).structural.Gamma * L < signature.word.span ∧
              (signature.word.span : ℝ) ≤
                ((F.system L).structural.Gamma + 1) * L + CQ ∧
              signature.word.length ≤ (F.system L).m := by
  classical
  let CQ : ℝ := gap.Cgap + 1
  let Zmin := Nat.ceil
    (4 * context.structural.Gamma / context.entropy.kappa) + 1
  refine ⟨CQ, by dsimp [CQ]; positivity, Zmin, ?_⟩
  intro Z0 hZ0
  refine ⟨exteriorCountError context gap,
    exteriorCountError_tendsto_zero context gap, ?_⟩
  intro F hF
  have hcutoff :
      4 * context.structural.Gamma / context.entropy.kappa < (Z0 : ℝ) := by
    have hceil :
        4 * context.structural.Gamma / context.entropy.kappa ≤
          (Nat.ceil (4 * context.structural.Gamma /
            context.entropy.kappa) : ℝ) :=
      Nat.le_ceil _
    have hZcast :
        Nat.ceil (4 * context.structural.Gamma / context.entropy.kappa) + 1 ≤
          Z0 := by simpa [Zmin] using hZ0
    exact hceil.trans_lt (by exact_mod_cast hZcast)
  filter_upwards [exteriorSignatures_finite_and_ncard_le context gap F hF Z0,
    eventually_rawWindowGap_le context gap F hF,
    eventually_ge_atTop 1] with L hsignatureCount hgap hL
  let W := F.system L
  let H := exteriorCountSpanCap context gap L
  let B := H + 5
  have hstruct : W.structural = context.structural := by
    change (F.system L).structural = context.structural
    rw [F.structural_eq, hF.2.1]
  have hentropy : W.entropy = context.entropy := by
    change (F.system L).entropy = context.entropy
    rw [F.entropy_eq, hF.2.2.1]
  have hlevel : W.L = L := F.level_eq L
  have hm : W.m =
      Nat.floor (context.entropy.kappa * (L : ℝ)) + 1 := by
    change (F.system L).s + 1 = _
    rw [F.offset_eq, hF.2.2.1]
  have hnumEq : W.m + 1 =
      Nat.floor (context.entropy.kappa * (L : ℝ)) + 2 := by omega
  have hwordBound : exteriorWordBound W gap.Cgap = H := by
    simp only [exteriorWordBound, H, exteriorCountSpanCap, hstruct, hlevel]
  have hGamma : 0 < context.structural.Gamma :=
    lt_trans (by norm_num) context.structural.Gamma_gt
  have hkappaA :
      2 * context.entropy.kappa ≤ context.structural.Gamma + 1 := by
    have hh := context.entropy.kappa_exterior_half
    rw [context.entropy_structural] at hh
    have hA : 0 < context.structural.Gamma + 1 := by linarith
    have := (div_le_iff₀ hA).mp hh
    nlinarith
  have hkFloor :
      (Nat.floor (context.entropy.kappa * (L : ℝ)) : ℝ) ≤
        context.entropy.kappa * L := by
    exact Nat.floor_le
      (mul_nonneg context.entropy.kappa_pos.le (Nat.cast_nonneg L))
  have hGammaFloor :
      context.structural.Gamma * (L : ℝ) - 1 <
        (Nat.floor (context.structural.Gamma * (L : ℝ)) : ℝ) := by
    have := Nat.lt_floor_add_one (context.structural.Gamma * (L : ℝ))
    linarith
  have htwice : 2 * ((W.m + 1 : ℕ) : ℝ) ≤ (B : ℝ) := by
    rw [hm]
    dsimp [B, H, exteriorCountSpanCap]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hkappaA (Nat.cast_nonneg L)]
  have hB : 2 ≤ B := by dsimp [B]; omega
  have halphaPos : 0 < exteriorCountAlpha context gap L := by
    dsimp [exteriorCountAlpha, B, H]
    positivity
  have halphaHalf : exteriorCountAlpha context gap L ≤ 1 / 2 := by
    have hBpos : (0 : ℝ) < B := by positivity
    change
      (((Nat.floor (context.entropy.kappa * (L : ℝ)) + 2 : ℕ) : ℝ) /
          (B : ℝ)) ≤ 1 / 2
    rw [← hnumEq]
    apply (div_le_iff₀ hBpos).2
    nlinarith
  have hr : ((W.m + 1 : ℕ) : ℝ) ≤
      exteriorCountAlpha context gap L * (B : ℝ) := by
    change ((W.m + 1 : ℕ) : ℝ) ≤
      ((((Nat.floor (context.entropy.kappa * (L : ℝ)) + 2 : ℕ) : ℝ) /
        (B : ℝ)) * (B : ℝ))
    rw [← hnumEq]
    have hB0 : (B : ℝ) ≠ 0 := by positivity
    field_simp [hB0]
    norm_num
  have hcomposition := lem_composition_entropy B (W.m + 1)
    (exteriorCountAlpha context gap L) hB halphaPos halphaHalf hr
  have hsumMono :
      (∑ r ∈ Finset.Icc 0 W.m,
          (exteriorWordBound W gap.Cgap).choose r) ≤
        ∑ r ∈ Finset.Icc 0 W.m, (B - 1).choose r := by
    apply Finset.sum_le_sum
    intro r hrmem
    apply Nat.choose_le_choose
    rw [hwordBound]
    dsimp [B]
    omega
  have hsumReal :
      ((∑ r ∈ Finset.Icc 0 W.m,
          (exteriorWordBound W gap.Cgap).choose r : ℕ) : ℝ) ≤
        (B : ℝ) ^ 2 * Real.rpow 2
          ((B : ℝ) * binaryEntropy (exteriorCountAlpha context gap L)) := by
    calc
      ((∑ r ∈ Finset.Icc 0 W.m,
          (exteriorWordBound W gap.Cgap).choose r : ℕ) : ℝ) ≤
          ((∑ r ∈ Finset.Icc 0 W.m, (B - 1).choose r : ℕ) : ℝ) := by
        exact_mod_cast hsumMono
      _ = ((∑ q ∈ Finset.Icc 1 (W.m + 1),
          (B - 1).choose (q - 1) : ℕ) : ℝ) := by
        rw [sum_choose_Icc_zero_eq_shift]
      _ ≤ (B : ℝ) ^ 2 * Real.rpow 2
          ((B : ℝ) * binaryEntropy (exteriorCountAlpha context gap L)) := by
        simpa only [Nat.add_sub_cancel] using hcomposition
  have hpolyNat :
      (W.m + 1) * 4 * (W.m + 1) * (W.L + gap.Cgap + 2) ≤
        B ^ 4 := by
    have hmBReal : ((W.m + 1 : ℕ) : ℝ) ≤ (B : ℝ) := by
      nlinarith [htwice]
    have hmB : W.m + 1 ≤ B := by exact_mod_cast hmBReal
    have hLB : W.L + gap.Cgap + 2 ≤ B := by
      rw [hlevel]
      dsimp [B, H, exteriorCountSpanCap]
      omega
    have hfourB : 4 ≤ B := by dsimp [B]; omega
    nlinarith [Nat.mul_le_mul hmB hmB,
      Nat.mul_le_mul hfourB hLB]
  have hcardReal :
      ((exteriorSignatures W Z0 gap.Cgap).ncard : ℝ) ≤
        (B : ℝ) ^ 6 * Real.rpow 2
          ((B : ℝ) * binaryEntropy (exteriorCountAlpha context gap L)) := by
    have hcount := hsignatureCount.2
    change (exteriorSignatures W Z0 gap.Cgap).ncard ≤ _ at hcount
    have hcountReal : ((exteriorSignatures W Z0 gap.Cgap).ncard : ℝ) ≤
        (((W.m + 1) * 4 * (W.m + 1) *
          (W.L + gap.Cgap + 2) : ℕ) : ℝ) *
          ((∑ r ∈ Finset.Icc 0 W.m,
            (exteriorWordBound W gap.Cgap).choose r : ℕ) : ℝ) := by
      exact_mod_cast hcount
    calc
      ((exteriorSignatures W Z0 gap.Cgap).ncard : ℝ) ≤ _ := hcountReal
      _ ≤ ((B : ℝ) ^ 4) *
          ((B : ℝ) ^ 2 * Real.rpow 2
            ((B : ℝ) * binaryEntropy (exteriorCountAlpha context gap L))) := by
        exact mul_le_mul (by exact_mod_cast hpolyNat) hsumReal
          (by positivity) (by positivity)
      _ = (B : ℝ) ^ 6 * Real.rpow 2
          ((B : ℝ) * binaryEntropy (exteriorCountAlpha context gap L)) := by ring
  have hcardTarget :
      ((exteriorSignatures W Z0 gap.Cgap).ncard : ℝ) ≤
        Real.rpow W.X
          (exteriorPrefixExponent W.entropy + exteriorCountError context gap L) := by
    apply hcardReal.trans
    have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
    have hL0 : (L : ℝ) ≠ 0 := ne_of_gt hLpos
    have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog2 : Real.log 2 ≠ 0 := ne_of_gt hlog2pos
    have hBreal : (0 : ℝ) < B := by positivity
    have hbase : (0 : ℝ) < (W.X : ℝ) := by simp [WindowSystem.X, dyadicScale]
    have hrpowTwo : Real.rpow 2
        ((B : ℝ) * binaryEntropy (exteriorCountAlpha context gap L)) =
        Real.exp (Real.log 2 *
          ((B : ℝ) * binaryEntropy (exteriorCountAlpha context gap L))) :=
      Real.rpow_def_of_pos (x := 2) (by norm_num) _
    have hrpowBase : Real.rpow (W.X : ℝ)
        (exteriorPrefixExponent W.entropy + exteriorCountError context gap L) =
        Real.exp (Real.log (W.X : ℝ) *
          (exteriorPrefixExponent W.entropy +
            exteriorCountError context gap L)) :=
      Real.rpow_def_of_pos (x := (W.X : ℝ)) hbase _
    rw [hrpowTwo, hrpowBase]
    have hpolyExp : (B : ℝ) ^ 6 =
        Real.exp (6 * Real.log (B : ℝ)) := by
      calc
        (B : ℝ) ^ 6 = Real.exp (Real.log ((B : ℝ) ^ 6)) :=
          (Real.exp_log (pow_pos hBreal 6)).symm
        _ = Real.exp (6 * Real.log (B : ℝ)) := by
          rw [Real.log_pow]
          norm_num
    rw [hpolyExp, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hXcast : (W.X : ℝ) = (2 : ℝ) ^ L := by
      simp [WindowSystem.X, dyadicScale, hlevel]
    rw [hXcast, Real.log_pow, hentropy]
    have herror : exteriorCountError context gap L =
        |((B : ℝ) / (L : ℝ)) *
            binaryEntropy (exteriorCountAlpha context gap L) -
          exteriorPrefixExponent context.entropy| +
          6 * Real.log (B : ℝ) / ((L : ℝ) * Real.log 2) := by
      simpa [B, H] using
        (show exteriorCountError context gap L =
          |(((exteriorCountSpanCap context gap L + 5 : ℕ) : ℝ) / (L : ℝ)) *
              binaryEntropy (exteriorCountAlpha context gap L) -
            exteriorPrefixExponent context.entropy| +
            6 * Real.log
              (((exteriorCountSpanCap context gap L + 5 : ℕ) : ℝ)) /
              ((L : ℝ) * Real.log 2) by
            simp only [exteriorCountError, Nat.ne_of_gt hL, if_false])
    rw [herror]
    have hmainLe :
        ((B : ℝ) / (L : ℝ)) *
            binaryEntropy (exteriorCountAlpha context gap L) ≤
          exteriorPrefixExponent context.entropy +
            |((B : ℝ) / (L : ℝ)) *
              binaryEntropy (exteriorCountAlpha context gap L) -
              exteriorPrefixExponent context.entropy| := by
      linarith [le_abs_self
        (((B : ℝ) / (L : ℝ)) *
          binaryEntropy (exteriorCountAlpha context gap L) -
          exteriorPrefixExponent context.entropy)]
    have hscalePos : 0 < (L : ℝ) * Real.log 2 := mul_pos hLpos hlog2pos
    have hscaled := mul_le_mul_of_nonneg_left hmainLe hscalePos.le
    have hpolyCancel :
        ((L : ℝ) * Real.log 2) *
            (6 * Real.log (B : ℝ) / ((L : ℝ) * Real.log 2)) =
          6 * Real.log (B : ℝ) := by field_simp [hL0, hlog2]
    have hentropyScale :
        Real.log 2 * ((B : ℝ) *
            binaryEntropy (exteriorCountAlpha context gap L)) =
          ((L : ℝ) * Real.log 2) *
            (((B : ℝ) / (L : ℝ)) *
              binaryEntropy (exteriorCountAlpha context gap L)) := by
      field_simp [hL0]
    calc
      6 * Real.log (B : ℝ) +
          Real.log 2 * ((B : ℝ) *
            binaryEntropy (exteriorCountAlpha context gap L)) =
          ((L : ℝ) * Real.log 2) *
              (((B : ℝ) / (L : ℝ)) *
                binaryEntropy (exteriorCountAlpha context gap L)) +
            ((L : ℝ) * Real.log 2) *
              (6 * Real.log (B : ℝ) / ((L : ℝ) * Real.log 2)) := by
        rw [hentropyScale, hpolyCancel]
        ring
      _ ≤ ((L : ℝ) * Real.log 2) *
              (exteriorPrefixExponent context.entropy +
                |((B : ℝ) / (L : ℝ)) *
                    binaryEntropy (exteriorCountAlpha context gap L) -
                  exteriorPrefixExponent context.entropy|) +
            ((L : ℝ) * Real.log 2) *
              (6 * Real.log (B : ℝ) / ((L : ℝ) * Real.log 2)) :=
        add_le_add hscaled le_rfl
      _ = ((L : ℝ) * Real.log 2) *
          (exteriorPrefixExponent context.entropy +
            (|((B : ℝ) / (L : ℝ)) *
                binaryEntropy (exteriorCountAlpha context gap L) -
              exteriorPrefixExponent context.entropy| +
              6 * Real.log (B : ℝ) / ((L : ℝ) * Real.log 2))) := by ring
  refine ⟨hsignatureCount.1, ?_, ?_⟩
  · simpa [W] using hcardTarget
  · intro e he
    obtain ⟨signature, hmem, _hvalid, hlower, hupper, hlength⟩ :=
      longExteriorPair_has_signature context gap F hF Z0 L hcutoff hgap e he
    exact ⟨signature, hmem, by simpa [W] using hlower,
      by simpa [W, CQ] using hupper, by simpa [W] using hlength⟩

theorem exteriorPairs_subset_pairSet (W : WindowSystem) (Z0 : ℕ) :
    exteriorPairs W Z0 ⊆ W.pairSet := by
  intro e he
  exact he.1.1

theorem exteriorPairs_subset_exteriorRectangle (W : WindowSystem) (Z0 : ℕ) :
    exteriorPairs W Z0 ⊆
      Set.prod (exteriorAnchors W Z0 : Set ℕ) W.thresholds := by
  classical
  intro e he
  refine ⟨?_, he.1.1.2⟩
  rw [Finset.mem_coe, exteriorAnchors, Finset.mem_filter]
  exact ⟨he.1.1.1, e.2, he⟩

private theorem windowThresholdMeasure_exteriorRectangle
    (W : WindowSystem) (Z0 : ℕ) :
    windowThresholdMeasure
        (Set.prod (exteriorAnchors W Z0 : Set ℕ) W.thresholds) =
      ((exteriorAnchors W Z0).card : ℝ≥0∞) *
        ENNReal.ofReal (thresholdLength W) := by
  rw [windowThresholdMeasure]
  have hprod :
      (Measure.count.prod volume)
          (Set.prod (exteriorAnchors W Z0 : Set ℕ) W.thresholds) =
        Measure.count (exteriorAnchors W Z0 : Set ℕ) * volume W.thresholds :=
    MeasureTheory.Measure.prod_prod _ _
  rw [hprod]
  simp only [Measure.count_apply_finset, WindowSystem.thresholds,
    thresholdInterval, Real.volume_Icc, thresholdLength]
  congr 2
  ring

/-- Certified real mass of the long-exterior parent family. -/
def exteriorPairsMass (W : WindowSystem) (Z0 : ℕ) : ℝ :=
  finiteWindowMass W (exteriorPairs W Z0)
    (exteriorPairs_subset_pairSet W Z0)

private theorem exteriorPairsMass_le (W : WindowSystem) (Z0 : ℕ) (M : ℝ)
    (hM : 0 ≤ M)
    (hbound : ∀ e ∈ exteriorPairs W Z0, W.excess e ≤ M) :
    exteriorPairsMass W Z0 ≤
      M * (exteriorAnchors W Z0).card * thresholdLength W := by
  have hmass : mass (exteriorPairs W Z0) W.excess ≤
      ENNReal.ofReal M * windowThresholdMeasure
        (Set.prod (exteriorAnchors W Z0 : Set ℕ) W.thresholds) := by
    unfold mass
    calc
      (∫⁻ e in exteriorPairs W Z0, ENNReal.ofReal (W.excess e)
          ∂windowThresholdMeasure) ≤
          ∫⁻ _e in exteriorPairs W Z0, ENNReal.ofReal M
            ∂windowThresholdMeasure := by
        apply setLIntegral_mono measurable_const
        intro e he
        exact ENNReal.ofReal_le_ofReal (hbound e he)
      _ ≤ ∫⁻ _e in
          Set.prod (exteriorAnchors W Z0 : Set ℕ) W.thresholds,
          ENNReal.ofReal M ∂windowThresholdMeasure :=
        lintegral_mono_set (exteriorPairs_subset_exteriorRectangle W Z0)
      _ = ENNReal.ofReal M * windowThresholdMeasure
          (Set.prod (exteriorAnchors W Z0 : Set ℕ) W.thresholds) :=
        setLIntegral_const _ _
  have hleftTop : mass (exteriorPairs W Z0) W.excess ≠ ⊤ :=
    (finiteMassOfSubset W (exteriorPairs W Z0)
      (exteriorPairs_subset_pairSet W Z0)).ne_top
  have hlength : 0 ≤ thresholdLength W :=
    mul_nonneg W.structural.cI_pos.le (Nat.cast_nonneg _)
  have hrightTop :
      ENNReal.ofReal M * windowThresholdMeasure
          (Set.prod (exteriorAnchors W Z0 : Set ℕ) W.thresholds) ≠ ⊤ := by
    rw [windowThresholdMeasure_exteriorRectangle]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top)
  have hto := (ENNReal.toReal_le_toReal hleftTop hrightTop).2 hmass
  change (mass (exteriorPairs W Z0) W.excess).toReal ≤ _
  rw [windowThresholdMeasure_exteriorRectangle] at hto
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hM,
    ENNReal.toReal_natCast, ENNReal.toReal_ofReal hlength, mul_assoc] using hto

private theorem eventually_exterior_parameter_term_le_one
    (Gamma Coff : ℝ) (hGamma : 1 < Gamma) (hCoff : 0 < Coff) :
    ∀ᶠ L : ℕ in atTop, ∀ n : ℕ, Gamma * (L : ℝ) < n →
      Coff * dyadicScale L * (2 : ℝ) ^ (-(n : ℤ)) ≤ 1 := by
  let d : ℝ := Gamma - 1
  let b : ℝ := Real.log 2 * d
  have hd : 0 < d := by dsimp [d]; linarith
  have hb : 0 < b := mul_pos (Real.log_pos (by norm_num)) hd
  have hnatTop : Tendsto (fun L : ℕ => (L : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hexpTop : Tendsto (fun L : ℕ => Real.exp (b * (L : ℝ)))
      atTop atTop :=
    Real.tendsto_exp_atTop.comp
      (Filter.Tendsto.const_mul_atTop hb hnatTop)
  have hdecay : Tendsto
      (fun L : ℕ => Coff / Real.exp (b * (L : ℝ))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hexpTop
  have hevent : ∀ᶠ L : ℕ in atTop,
      Coff / Real.exp (b * (L : ℝ)) ≤ 1 :=
    ((tendsto_order.1 hdecay).2 1 (by norm_num)).mono fun _ h => h.le
  filter_upwards [hevent] with L hL
  intro n hn
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnPower : Real.exp (Real.log 2 * (Gamma * (L : ℝ))) ≤
      (2 : ℝ) ^ n := by
    rw [← Real.rpow_natCast,
      Real.rpow_def_of_pos (x := (2 : ℝ)) (by norm_num)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hn.le hlog2.le)
  have hdenom :
      Real.exp (b * (L : ℝ)) * (2 : ℝ) ^ L =
        Real.exp (Real.log 2 * (Gamma * (L : ℝ))) := by
    rw [← Real.rpow_natCast,
      Real.rpow_def_of_pos (x := (2 : ℝ)) (by norm_num),
      ← Real.exp_add]
    congr 1
    dsimp [b, d]
    ring
  have hdenomLe : Real.exp (b * (L : ℝ)) * (2 : ℝ) ^ L ≤
      (2 : ℝ) ^ n := by rw [hdenom]; exact hnPower
  have hpowL : (0 : ℝ) < (2 : ℝ) ^ L := by positivity
  have hfraction :
      Coff * (2 : ℝ) ^ L / (2 : ℝ) ^ n ≤
        Coff / Real.exp (b * (L : ℝ)) := by
    calc
      Coff * (2 : ℝ) ^ L / (2 : ℝ) ^ n ≤
          Coff * (2 : ℝ) ^ L /
            (Real.exp (b * (L : ℝ)) * (2 : ℝ) ^ L) :=
        div_le_div_of_nonneg_left (by positivity)
          (mul_pos (Real.exp_pos _) hpowL) hdenomLe
      _ = Coff / Real.exp (b * (L : ℝ)) := by
        field_simp [ne_of_gt hpowL, ne_of_gt (Real.exp_pos _)]
  calc
    Coff * dyadicScale L * (2 : ℝ) ^ (-(n : ℤ)) =
        Coff * (2 : ℝ) ^ L / (2 : ℝ) ^ n := by
      rw [zpow_neg, zpow_natCast]
      simp only [dyadicScale, Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv]
    _ ≤ Coff / Real.exp (b * (L : ℝ)) := hfraction
    _ ≤ 1 := hL

private theorem eventually_exteriorAnchors_card_le
    (context : FixedScaleContext) (gap : GapParams context.Q) :
    ∃ Zmin : ℕ, ∀ Z0 : ℕ, Zmin ≤ Z0 →
      ∃ initialError exteriorError : ℕ → ℝ,
        Tendsto initialError atTop (𝓝 0) ∧
        Tendsto exteriorError atTop (𝓝 0) ∧
        ∀ F : ScaleFamily, F.MatchesContext context →
          ∀ᶠ L : ℕ in atTop,
            ((exteriorAnchors (F.system L) Z0).card : ℝ) ≤
              Real.rpow (F.system L).X
                  (initialPrefixExponent (F.system L).entropy + initialError L) *
                Real.rpow (F.system L).X
                  (exteriorPrefixExponent (F.system L).entropy + exteriorError L) * 2 := by
  classical
  obtain ⟨Cline, Clock, hClock, hlocking⟩ :=
    lem_ap_locking context.Q context.Q_pos
  obtain ⟨Coff, hCoff, hfixed⟩ :=
    prop_fixed_off_word context.Q context.Q_pos
  obtain ⟨CQfirst, hCQfirst, hfirstExists⟩ := lem_firstdeep_exists context
  obtain ⟨CQexterior, hCQexterior, Zsecond, hsecond⟩ :=
    lem_seconddeep context gap
  let Zfirst := Nat.ceil
    (2 * context.structural.Caff / context.entropy.kappa)
  let Zexit := Nat.ceil
    (4 * context.structural.Gamma / context.entropy.kappa) + 1
  let Zmin := max Zsecond (max Zfirst Zexit)
  refine ⟨Zmin, ?_⟩
  intro Z0 hZ0
  have hZfirst : Zfirst ≤ Z0 :=
    (le_max_left Zfirst Zexit).trans
      ((le_max_right Zsecond (max Zfirst Zexit)).trans hZ0)
  have hZsecond : Zsecond ≤ Z0 :=
    (le_max_left Zsecond (max Zfirst Zexit)).trans hZ0
  have hZexit : Zexit ≤ Z0 :=
    (le_max_right Zfirst Zexit).trans
      ((le_max_right Zsecond (max Zfirst Zexit)).trans hZ0)
  have hcutoff :
      4 * context.structural.Gamma / context.entropy.kappa < (Z0 : ℝ) := by
    have hceil : 4 * context.structural.Gamma / context.entropy.kappa ≤
        (Nat.ceil (4 * context.structural.Gamma /
          context.entropy.kappa) : ℝ) := Nat.le_ceil _
    have hsucc : Nat.ceil
        (4 * context.structural.Gamma / context.entropy.kappa) + 1 ≤ Z0 := by
      simpa only [Zexit] using hZexit
    exact hceil.trans_lt (by exact_mod_cast hsucc)
  obtain ⟨initialError, hinitialError, hinitialCount⟩ :=
    lem_firstdeep_count context Z0 (by simpa only [Zfirst] using hZfirst)
  obtain ⟨exteriorError, hexteriorError, hexteriorCount⟩ :=
    hsecond Z0 hZsecond
  refine ⟨initialError, exteriorError, hinitialError, hexteriorError, ?_⟩
  intro F hF
  have hfirstEvent := hfirstExists Z0
    (by simpa only [Zfirst] using hZfirst) F hF
  have hinitialEvent := hinitialCount F hF
  have hexteriorEvent := hexteriorCount F hF
  have hgapEvent := eventually_rawWindowGap_le context gap F hF
  have hGamma : 1 < context.structural.Gamma := context.structural.Gamma_gt
  have hparameterEvent := eventually_exterior_parameter_term_le_one
    context.structural.Gamma Coff hGamma hCoff
  let lineSlack : ℝ := context.structural.Caff - 2
  have hlineSlack : 0 < lineSlack := by
    dsimp [lineSlack]
    linarith [context.structural.Caff_gt]
  have hnatTop : Tendsto (fun L : ℕ => (L : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlineTop : Tendsto (fun L : ℕ => lineSlack * (L : ℝ))
      atTop atTop := Filter.Tendsto.const_mul_atTop hlineSlack hnatTop
  have hlineEvent : ∀ᶠ L : ℕ in atTop,
      (Cline : ℝ) < lineSlack * (L : ℝ) :=
    hlineTop.eventually_gt_atTop Cline
  obtain ⟨Lpow, hpow⟩ := eventually_quadratic_lt_two_pow (gap.Cgap + 2)
  have hgapScaleEvent : ∀ᶠ L : ℕ in atTop,
      L + gap.Cgap + 1 ≤ dyadicScale L := by
    filter_upwards [eventually_ge_atTop (max Lpow 1)] with L hL
    have hLpow : Lpow ≤ L := (le_max_left Lpow 1).trans hL
    have hLone : 1 ≤ L := (le_max_right Lpow 1).trans hL
    have hlinear : L + gap.Cgap + 1 ≤ (gap.Cgap + 2) * L ^ 2 := by
      have hc : gap.Cgap + 1 ≤ (gap.Cgap + 1) * L :=
        by simpa using Nat.mul_le_mul_left (gap.Cgap + 1) hLone
      have hbase : L + gap.Cgap + 1 ≤ (gap.Cgap + 2) * L := by
        calc
          L + gap.Cgap + 1 = L + (gap.Cgap + 1) := by omega
          _ ≤ L + (gap.Cgap + 1) * L := Nat.add_le_add_left hc L
          _ = (gap.Cgap + 2) * L := by ring
      have hsq : L ≤ L ^ 2 := by
        calc
          L = L * 1 := by simp
          _ ≤ L * L := Nat.mul_le_mul_left L hLone
          _ = L ^ 2 := by ring
      exact hbase.trans (Nat.mul_le_mul_left (gap.Cgap + 2) hsq)
    exact hlinear.trans (hpow L hLpow).le
  filter_upwards [hfirstEvent, hinitialEvent, hexteriorEvent, hgapEvent,
    hparameterEvent, hlineEvent, hgapScaleEvent, eventually_ge_atTop 1]
      with L hfirstL hinitialL hexteriorL hgapL hparameterL hlineL
        hgapScale hL
  let W := F.system L
  have hden : W.rational.eta.den = context.Q := by
    change (F.system L).rational.eta.den = context.Q
    rw [F.rational_eq, hF.1]
  have hQW : 0 < W.rational.eta.den := by simpa [hden] using context.Q_pos
  have hstruct : W.structural = context.structural := by
    change (F.system L).structural = context.structural
    rw [F.structural_eq, hF.2.1]
  have hentropy : W.entropy = context.entropy := by
    change (F.system L).entropy = context.entropy
    rw [F.entropy_eq, hF.2.2.1]
  have hlevel : W.L = L := F.level_eq L
  have hfrequency : 1 < frequencyCutoff W := by
    unfold frequencyCutoff
    have hX : (1 : ℝ) < W.X := by
      rw [WindowSystem.X, hlevel, dyadicScale]
      exact_mod_cast (one_lt_pow₀ (by norm_num : 1 < (2 : ℕ))
        (Nat.ne_of_gt hL))
    apply Real.one_lt_rpow hX
    rw [hstruct]
    linarith [context.structural.rho_pos]
  let Anchor := {k // k ∈ exteriorAnchors W Z0}
  have pairExists (k : Anchor) :
      ∃ T : ℝ, LongExteriorPair W Z0 (k.1, T) := by
    have hk := k.2
    change k.1 ∈ W.anchors.filter fun j =>
      ∃ T : ℝ, LongExteriorPair W Z0 (j, T) at hk
    rw [Finset.mem_filter] at hk
    exact hk.2
  let thresholdFor : Anchor → ℝ := fun k => Classical.choose (pairExists k)
  have thresholdSpec (k : Anchor) :
      LongExteriorPair W Z0 (k.1, thresholdFor k) :=
    Classical.choose_spec (pairExists k)
  have signatureExists (k : Anchor) :
      ∃ signature : ExteriorSignature,
        signature ∈ exteriorSignatures W Z0 gap.Cgap ∧
        ValidExteriorSignature W Z0 gap.Cgap (k.1, thresholdFor k) signature ∧
        W.structural.Gamma * L < signature.word.span ∧
        (signature.word.span : ℝ) ≤
          (W.structural.Gamma + 1) * L + (gap.Cgap + 1) ∧
        signature.word.length ≤ W.m := by
    simpa only [W] using longExteriorPair_has_signature context gap F hF Z0 L
      hcutoff hgapL (k.1, thresholdFor k) (thresholdSpec k)
  let signatureFor : Anchor → ExteriorSignature := fun k =>
    Classical.choose (signatureExists k)
  have signatureSpec (k : Anchor) :
      signatureFor k ∈ exteriorSignatures W Z0 gap.Cgap ∧
      ValidExteriorSignature W Z0 gap.Cgap (k.1, thresholdFor k)
        (signatureFor k) ∧
      W.structural.Gamma * L < (signatureFor k).word.span ∧
      ((signatureFor k).word.span : ℝ) ≤
        (W.structural.Gamma + 1) * L + (gap.Cgap + 1) ∧
      (signatureFor k).word.length ≤ W.m :=
    Classical.choose_spec (signatureExists k)
  have highOfAnchor (k : Anchor) : k.1 ∈ highAnchors W Z0 := by
    have hpair := thresholdSpec k
    rw [highAnchors, Finset.mem_filter]
    exact ⟨hpair.1.1.1, thresholdFor k, hpair.1.1.2, hpair.1.2⟩
  have primitiveAt (k : Anchor) :
      HasPrimitiveOccurrenceLine W Z0 (initialLongPrefix W k.1) := by
    let p := initialLongPrefix W k.1
    have hpMem : p ∈ initialPrefixes W Z0 := by
      rw [initialPrefixes, Finset.mem_image]
      exact ⟨k.1, highOfAnchor k, rfl⟩
    have hpLower := hfirstL (k.1, thresholdFor k) (thresholdSpec k).1
    dsimp only at hpLower
    have hpLong : 2 * W.L + Cline < p.span := by
      have hpReal : context.structural.Caff * (L : ℝ) < (p.span : ℝ) := by
        have hpReal' := hpLower.1
        change W.structural.Caff * (W.L : ℝ) < (p.span : ℝ) at hpReal'
        rw [hstruct, hlevel] at hpReal'
        exact hpReal'
      have htarget : ((2 * W.L + Cline : ℕ) : ℝ) < (p.span : ℝ) := by
        rw [hlevel]
        push_cast
        dsimp [lineSlack] at hlineL
        nlinarith
      exact_mod_cast htarget
    rcases hlocking W hden Z0 p hpMem hpLong (thresholdSpec k).2.1 with
      ⟨line, hoccurrence, hprimitive, _hheight⟩
    exact ⟨line, hoccurrence, hprimitive⟩
  have sourceExists (k : Anchor) :
      ∃ source : ExteriorSource W Z0 (chosenExteriorLine W Z0),
        source.anchor = k.1 ∧ source.record = (signatureFor k).record ∧
          source.word = (signatureFor k).word := by
    apply validExteriorSignature_has_source W Z0 gap.Cgap hQW hfrequency
      (k.1, thresholdFor k) (thresholdSpec k) (signatureFor k)
      (signatureSpec k).2.1 (primitiveAt k)
    · intro g hg
      simpa only [hlevel] using hgapL k.1 (thresholdSpec k).1.1.1 g hg
    · simpa [WindowSystem.X, hlevel] using hgapScale
  let sourceFor : Anchor → ExteriorSource W Z0 (chosenExteriorLine W Z0) :=
    fun k => Classical.choose (sourceExists k)
  have sourceSpec (k : Anchor) :
      (sourceFor k).anchor = k.1 ∧
      (sourceFor k).record = (signatureFor k).record ∧
      (sourceFor k).word = (signatureFor k).word :=
    Classical.choose_spec (sourceExists k)
  have hsourceSmall (k : Anchor) :
      Coff * W.X * (2 : ℝ) ^ (-((sourceFor k).word.span : ℤ)) ≤ 1 := by
    have hlower : context.structural.Gamma * (L : ℝ) <
        (sourceFor k).word.span := by
      rw [(sourceSpec k).2.2]
      simpa [hstruct] using (signatureSpec k).2.2.1
    have h := hparameterL (sourceFor k).word.span hlower
    simpa [WindowSystem.X, hlevel] using h
  have hanchorNat := exteriorAnchors_card_le_of_sources W Z0 gap.Cgap
    hQW Coff hCoff (by simpa [hden] using hfixed) hexteriorL.1
    sourceFor signatureFor
    (fun k => (sourceSpec k).1)
    (fun k => (signatureSpec k).1)
    (fun k => (sourceSpec k).2.1)
    (fun k => (sourceSpec k).2.2) hsourceSmall
  have hanchorReal : ((exteriorAnchors W Z0).card : ℝ) ≤
      ((initialPrefixes W Z0).card : ℝ) *
        ((exteriorSignatures W Z0 gap.Cgap).ncard : ℝ) * 2 := by
    exact_mod_cast hanchorNat
  have hinitialW : ((initialPrefixes W Z0).card : ℝ) ≤
      Real.rpow W.X
        (initialPrefixExponent W.entropy + initialError L) := by
    simpa only [W] using hinitialL
  have hexteriorW : ((exteriorSignatures W Z0 gap.Cgap).ncard : ℝ) ≤
      Real.rpow W.X
        (exteriorPrefixExponent W.entropy + exteriorError L) := by
    simpa only [W] using hexteriorL.2.1
  have hinitialNonneg : 0 ≤ Real.rpow W.X
      (initialPrefixExponent W.entropy + initialError L) :=
    Real.rpow_nonneg (by positivity) _
  calc
    ((exteriorAnchors W Z0).card : ℝ) ≤
        ((initialPrefixes W Z0).card : ℝ) *
          ((exteriorSignatures W Z0 gap.Cgap).ncard : ℝ) * 2 := hanchorReal
    _ ≤ Real.rpow W.X
          (initialPrefixExponent W.entropy + initialError L) *
        ((exteriorSignatures W Z0 gap.Cgap).ncard : ℝ) * 2 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hinitialW (by positivity)) (by norm_num)
    _ ≤ Real.rpow W.X
          (initialPrefixExponent W.entropy + initialError L) *
        Real.rpow W.X
          (exteriorPrefixExponent W.entropy + exteriorError L) * 2 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hexteriorW hinitialNonneg) (by norm_num)

/-- Paper label: `thm:off-mass` (Section 7).  The exterior estimate starts
after one denominator-level cutoff, as required by `lem_seconddeep`. -/
theorem thm_off_mass (context : FixedScaleContext) :
    ∃ Zmin : ℕ, ∀ Z0 : ℕ, Zmin ≤ Z0 →
      ∀ F : ScaleFamily, F.MatchesContext context →
      (fun L =>
        exteriorPairsMass (F.system L) Z0) =o[atTop]
        (fun L =>
          ((F.system L).m : ℝ) * (F.system L).X *
            thresholdLength (F.system L)) := by
  classical
  obtain ⟨gap⟩ := gapParams_exists context.Q context.Q_pos
  obtain ⟨Zmin, hanchors⟩ := eventually_exteriorAnchors_card_le context gap
  refine ⟨Zmin, ?_⟩
  intro Z0 hZ0 F hF
  obtain ⟨initialError, exteriorError, hinitialError, hexteriorError,
      hanchorCount⟩ := hanchors Z0 hZ0
  have hanchorEvent := hanchorCount F hF
  have hgapEvent := eventually_rawWindowGap_le context gap F hF
  let Δ : ℝ := initialPrefixExponent context.entropy
  let δext : ℝ := exteriorPrefixExponent context.entropy
  let margin : ℝ := 1 - 2 * context.structural.rho - (Δ + δext)
  let d : ℝ := margin / 2
  have htotal : Δ + δext < 1 - 2 * context.structural.rho := by
    dsimp [Δ, δext, initialPrefixExponent, exteriorPrefixExponent]
    simpa only [context.entropy_structural] using context.entropy.total_margin
  have hmargin : 0 < margin := by dsimp [margin]; linarith
  have hd : 0 < d := by dsimp [d]; linarith
  have herrorZero : Tendsto (fun L => initialError L + exteriorError L)
      atTop (𝓝 0) := by simpa using hinitialError.add hexteriorError
  have herrorSmall : ∀ᶠ L : ℕ in atTop,
      initialError L + exteriorError L ≤ d :=
    ((tendsto_order.1 herrorZero).2 d hd).mono fun _ h => h.le
  have hnatTop : Tendsto (fun L : ℕ => (L : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  let b : ℝ := Real.log 2 * d
  have hb : 0 < b := mul_pos (Real.log_pos (by norm_num)) hd
  have hpolyExp :
      Tendsto (fun L : ℕ => (L : ℝ) / Real.exp (b * (L : ℝ)))
        atTop (𝓝 0) := by
    have hlittle :=
      (isLittleO_pow_exp_pos_mul_atTop 1 hb).comp_tendsto hnatTop
    simpa only [Function.comp_apply, pow_one] using
      hlittle.tendsto_div_nhds_zero
  have hexpTop : Tendsto (fun L : ℕ => Real.exp (b * (L : ℝ)))
      atTop atTop := by
    exact Real.tendsto_exp_atTop.comp
      (Filter.Tendsto.const_mul_atTop hb hnatTop)
  have hconstExp : Tendsto
      (fun L : ℕ => ((gap.Cgap : ℝ) + 1) /
        Real.exp (b * (L : ℝ))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hexpTop
  have hbaseDecay : Tendsto
      (fun L : ℕ => ((L : ℝ) + gap.Cgap + 1) /
        Real.exp (b * (L : ℝ))) atTop (𝓝 0) := by
    simpa only [add_div, zero_add, add_assoc] using hpolyExp.add hconstExp
  have hdecayExp : Tendsto
      (fun L : ℕ => 2 * (((L : ℝ) + gap.Cgap + 1) /
        Real.exp (b * (L : ℝ)))) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hbaseDecay
  have hrpowExp : ∀ L : ℕ,
      Real.rpow (dyadicScale L) d = Real.exp (b * (L : ℝ)) := by
    intro L
    have hdyadic : (0 : ℝ) < dyadicScale L := by
      rw [dyadicScale]
      positivity
    rw [Real.rpow_eq_pow, Real.rpow_def_of_pos
      (x := (dyadicScale L : ℝ)) (y := d) hdyadic]
    simp only [dyadicScale, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    dsimp [b]
    congr 1
    ring
  have hdecay : Tendsto
      (fun L : ℕ => 2 * ((L : ℝ) + gap.Cgap + 1) /
        Real.rpow (dyadicScale L) d) atTop (𝓝 0) := by
    apply hdecayExp.congr'
    filter_upwards with L
    rw [hrpowExp]
    simp only [div_eq_mul_inv, mul_assoc]
  apply IsLittleO.of_bound
  intro c hc
  have hdecayC : ∀ᶠ L : ℕ in atTop,
      2 * ((L : ℝ) + gap.Cgap + 1) /
          Real.rpow (dyadicScale L) d ≤ c :=
    ((tendsto_order.1 hdecay).2 c hc).mono fun _ h => h.le
  filter_upwards [hanchorEvent, hgapEvent, herrorSmall, hdecayC,
    eventually_ge_atTop 1]
      with L hanchor hgap herrorL hdecayL hL
  let W := F.system L
  let G : ℕ := L + gap.Cgap + 1
  have hWstruct : W.structural = context.structural :=
    (F.structural_eq L).trans hF.2.1
  have hWentropy : W.entropy = context.entropy :=
    (F.entropy_eq L).trans hF.2.2.1
  have hlevel : W.L = L := F.level_eq L
  have hX : W.X = dyadicScale L := by rw [WindowSystem.X, hlevel]
  have hXpos : 0 < (W.X : ℝ) := by
    rw [hX, dyadicScale]
    positivity
  have hXone : (1 : ℝ) ≤ W.X := by
    rw [hX, dyadicScale]
    exact_mod_cast (Left.one_le_pow_of_le (by norm_num : (1 : ℕ) ≤ 2) L)
  have hmnonneg : (0 : ℝ) ≤ W.m := by positivity
  have hGnonneg : (0 : ℝ) ≤ G := by positivity
  have hlengthNonneg : 0 ≤ thresholdLength W := by
    unfold thresholdLength
    exact mul_nonneg W.structural.cI_pos.le (Nat.cast_nonneg _)
  have hexcessBound : ∀ e ∈ exteriorPairs W Z0,
      W.excess e ≤ (W.m : ℝ) * G := by
    intro e he
    have hexcess := W.excess_le_rawWindowSpan e he.1.1
    have hsum : (W.rawWindowGapWord e.1).sum ≤
        (W.rawWindowGapWord e.1).length * G := by
      simpa [nsmul_eq_mul] using
        List.sum_le_card_nsmul (W.rawWindowGapWord e.1) G
          (hgap e.1 he.1.1.1)
    have hlen : (W.rawWindowGapWord e.1).length ≤ W.m :=
      rawWindowGapWord_length_le W e.1
    have hspan : W.rawWindowSpan e.1 ≤ W.m * G := by
      have hspanEq : (W.rawWindowGapWord e.1).span =
          W.rawWindowSpan e.1 := by
        unfold WindowSystem.rawWindowGapWord WindowSystem.rawWindowSpan
        split <;> rfl
      rw [← hspanEq]
      exact hsum.trans (Nat.mul_le_mul_right G hlen)
    exact hexcess.trans (by exact_mod_cast hspan)
  have hmass := exteriorPairsMass_le W Z0 ((W.m : ℝ) * G)
    (mul_nonneg hmnonneg hGnonneg) hexcessBound
  have hanchorW : ((exteriorAnchors W Z0).card : ℝ) ≤
      Real.rpow W.X (Δ + initialError L) *
        Real.rpow W.X (δext + exteriorError L) * 2 := by
    simpa only [W, hWentropy, Δ, δext] using hanchor
  have hexponent :
      Δ + initialError L + (δext + exteriorError L) ≤ 1 - d := by
    dsimp [d, margin] at herrorL ⊢
    nlinarith [context.structural.rho_pos]
  have hrpowExponent : Real.rpow W.X
      (Δ + initialError L + (δext + exteriorError L)) ≤
      Real.rpow W.X (1 - d) :=
    Real.rpow_le_rpow_of_exponent_le hXone hexponent
  have hanchorFinal : ((exteriorAnchors W Z0).card : ℝ) ≤
      2 * (W.X / Real.rpow W.X d) := by
    calc
      ((exteriorAnchors W Z0).card : ℝ) ≤
          Real.rpow W.X (Δ + initialError L) *
            Real.rpow W.X (δext + exteriorError L) * 2 := hanchorW
      _ = 2 * (Real.rpow W.X (Δ + initialError L) *
          Real.rpow W.X (δext + exteriorError L)) := by ring
      _ = 2 * Real.rpow W.X
          (Δ + initialError L + (δext + exteriorError L)) := by
        congr 1
        exact (Real.rpow_add hXpos _ _).symm
      _ ≤ 2 * Real.rpow W.X (1 - d) := by gcongr
      _ = 2 * (W.X / Real.rpow W.X d) := by
        simp only [Real.rpow_eq_pow]
        rw [Real.rpow_sub hXpos 1 d, Real.rpow_one]
  have hdecayW : 2 * (G : ℝ) / Real.rpow W.X d ≤ c := by
    rw [hX]
    simpa only [G, Nat.cast_add, Nat.cast_one] using hdecayL
  have hmassFinal : exteriorPairsMass W Z0 ≤
      c * ((W.m : ℝ) * W.X * thresholdLength W) := by
    calc
      exteriorPairsMass W Z0 ≤
          ((W.m : ℝ) * G) * (exteriorAnchors W Z0).card *
            thresholdLength W := hmass
      _ ≤ ((W.m : ℝ) * G) *
          (2 * (W.X / Real.rpow W.X d)) * thresholdLength W := by
        gcongr
      _ = ((W.m : ℝ) * W.X * thresholdLength W) *
          (2 * (G : ℝ) / Real.rpow W.X d) := by ring
      _ ≤ ((W.m : ℝ) * W.X * thresholdLength W) * c := by
        gcongr
      _ = c * ((W.m : ℝ) * W.X * thresholdLength W) := by ring
  have hmassNonneg : 0 ≤ exteriorPairsMass W Z0 := by
    unfold exteriorPairsMass finiteWindowMass FiniteMass.toReal
    exact ENNReal.toReal_nonneg
  simpa only [Real.norm_eq_abs, abs_of_nonneg hmassNonneg,
    abs_of_nonneg (mul_nonneg (mul_nonneg hmnonneg hXpos.le)
      hlengthNonneg), W] using hmassFinal

end Erdos260

/-! Source module: Erdos260/Uniformity.lean -/

/-!
# Uniformity and the constant hierarchy

This module corresponds to Appendix D of the manuscript.
-/

noncomputable section

open Filter Set Topology

namespace Erdos260

def normalizationScale (W : WindowSystem) : ℝ :=
  W.m * W.X * thresholdLength W

def boundaryLossRatio (W : WindowSystem) : ℝ :=
  ((W.s + 1 : ℕ) : ℝ) * (W.L : ℝ) ^ 2 / (W.m * W.X)

def rareMassRatio (W : WindowSystem) (Z0 : ℕ) : ℝ :=
  rareLargePairsMass W Z0 / normalizationScale W

def exteriorMassRatio (W : WindowSystem) (Z0 : ℕ) : ℝ :=
  exteriorPairsMass W Z0 / normalizationScale W

def interiorMassRatio (W : WindowSystem) (Z0 : ℕ) : ℝ :=
  interiorPairsMass W Z0 / normalizationScale W

/-- Paper label: `prop:uniform-errors` (Appendix D).  One cutoff and one
nonnegative interior coefficient function are selected from the
denominator-level context before the rational numerator/support family.  The
rare, exterior, and interior conclusions are asserted uniformly for every
cutoff beyond that common threshold; their eventual scales may still depend
on the compatible family and cutoff. -/
theorem prop_uniform_errors (context : FixedScaleContext) :
    ∃ Zmin : ℕ, ∃ interiorBound : ℕ → ℝ,
      (∀ Z0, 0 ≤ interiorBound Z0) ∧
      Tendsto interiorBound atTop (𝓝 0) ∧
      ∀ F : ScaleFamily, F.MatchesContext context →
        Tendsto (fun L => boundaryLossRatio (F.system L)) atTop (𝓝 0) ∧
        (∀ Z0, Zmin ≤ Z0 →
          (fun L => rareLargePairsMass (F.system L) Z0) =o[atTop]
            (fun L => normalizationScale (F.system L))) ∧
        (∀ Z0, Zmin ≤ Z0 →
          (fun L => exteriorPairsMass (F.system L) Z0) =o[atTop]
            (fun L => normalizationScale (F.system L))) ∧
        ∀ Z0, Zmin ≤ Z0 → ∀ᶠ L : ℕ in atTop,
          interiorMassRatio (F.system L) Z0 ≤ interiorBound Z0 := by
  obtain ⟨Zstrict, ηQ, hηQ_nonneg, hηQ_zero, hstrict⟩ :=
    thm_strict_mass context
  obtain ⟨Zoff, hoff⟩ := thm_off_mass context
  let Zrare := Nat.ceil
    (2 * context.structural.Caff / context.entropy.kappa)
  let Zmin := max Zstrict (max Zrare Zoff)
  refine ⟨Zmin, ηQ, hηQ_nonneg, hηQ_zero, ?_⟩
  intro F hF
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hlim :=
      tendsto_pow_const_div_const_pow_of_one_lt 2
        (by norm_num : (1 : ℝ) < 2)
    convert hlim using 1
    funext L
    simp only [boundaryLossRatio, WindowSystem.m, WindowSystem.X,
      dyadicScale, F.level_eq, Nat.cast_add, Nat.cast_one, Nat.cast_pow,
      Nat.cast_ofNat]
    have hm : (0 : ℝ) < (F.system L).s + 1 := by positivity
    field_simp
  · intro Z0 hZ0
    have hrare : Zrare ≤ Z0 :=
      le_trans
        (le_trans (le_max_left Zrare Zoff)
          (le_max_right Zstrict (max Zrare Zoff))) hZ0
    simpa [normalizationScale] using
      (prop_low_firstdeep context Z0 hrare F hF)
  · intro Z0 hZ0
    have hZoff : Zoff ≤ Z0 :=
      le_trans
        (le_trans (le_max_right Zrare Zoff)
          (le_max_right Zstrict (max Zrare Zoff))) hZ0
    simpa [normalizationScale] using
      (hoff Z0 hZoff F hF)
  · intro Z0 hZ0
    have hZstrict : Zstrict ≤ Z0 :=
      le_trans (le_max_left Zstrict (max Zrare Zoff)) hZ0
    filter_upwards [hstrict Z0 hZstrict F hF, eventually_ge_atTop 1] with L hL hLpos
    obtain ⟨_refinement, hmass⟩ := hL
    have hnormalization : 0 < normalizationScale (F.system L) := by
      rw [normalizationScale, thresholdLength, F.level_eq]
      have hm : (0 : ℝ) < (F.system L).m := by
        exact_mod_cast Nat.succ_pos (F.system L).s
      have hX : (0 : ℝ) < (F.system L).X := by
        exact_mod_cast pow_pos (by decide : 0 < (2 : ℕ)) (F.system L).L
      have hcI : 0 < (F.system L).structural.cI :=
        (F.system L).structural.cI_pos
      have hLreal : (0 : ℝ) < L := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hLpos)
      positivity
    rw [interiorMassRatio, div_le_iff₀ hnormalization]
    simpa [normalizationScale, mul_assoc] using hmass

end Erdos260

/-! Source module: Erdos260/SequenceBridge.lean -/

/-!
# Sequence/support bridges for the Erdős 260 endpoint

This module contains the analytic reindexing facts used after the positive
dyadic-density theorem.  It is independent of the carry/window argument.
-/

noncomputable section

open Filter Set
open scoped BigOperators

namespace Erdos260

/-- The positive-integer sequence summand, placed below `Completion` so the
support reindexing lemmas do not introduce an import cycle. -/
def natSequenceTerm (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  (a n : ℝ) / (2 : ℝ) ^ a n

theorem summable_nat_weight :
    Summable (fun n : ℕ => (n : ℝ) / (2 : ℝ) ^ n) := by
  apply summable_of_ratio_norm_eventually_le (r := (3 : ℝ) / 4) (by norm_num)
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hterm : 0 ≤ (n : ℝ) / (2 : ℝ) ^ n := by positivity
  have htermSucc :
      0 ≤ ((n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1) := by positivity
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg htermSucc, abs_of_nonneg hterm]
  rw [pow_succ]
  field_simp
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  push_cast
  nlinarith

theorem summable_weightedSupportTerm (S : Set ℕ) :
    Summable (weightedSupportTerm S) := by
  apply summable_nat_weight.of_norm_bounded
  intro n
  have hbase : 0 ≤ (n : ℝ) / (2 : ℝ) ^ n := by positivity
  by_cases hn : n ∈ S
  · simp [weightedSupportTerm, hn]
  · simp [weightedSupportTerm, hn, hbase]

theorem natSequenceTerm_eq_weightedSupport_comp (a : ℕ → ℕ)
    (n : ℕ) :
    natSequenceTerm a n = weightedSupportTerm (Set.range a) (a n) := by
  simp [natSequenceTerm, weightedSupportTerm]

theorem hasSum_range_weightedSupport (a : ℕ → ℕ) (ha : StrictMono a) :
    HasSum (weightedSupportTerm (Set.range a))
      (∑' n : ℕ, natSequenceTerm a n) := by
  let f := weightedSupportTerm (Set.range a)
  have hzero : ∀ x ∉ Set.range a, f x = 0 := by
    intro x hx
    unfold f weightedSupportTerm
    rw [if_neg hx]
  have hcomp :
      (fun n => natSequenceTerm a n) = f ∘ a := by
    funext n
    exact natSequenceTerm_eq_weightedSupport_comp a n
  have hsummableF : Summable f := summable_weightedSupportTerm (Set.range a)
  have hsummableComp : Summable (f ∘ a) :=
    (ha.injective.summable_iff hzero).2 hsummableF
  have hsum : HasSum (f ∘ a) (∑' n : ℕ, natSequenceTerm a n) := by
    have hs : Summable (fun n => natSequenceTerm a n) := by
      rw [hcomp]
      exact hsummableComp
    exact hs.hasSum.congr_fun fun n => (congrFun hcomp n).symm
  exact (ha.injective.hasSum_iff hzero).1 hsum

theorem range_infinite_of_strictMono (a : ℕ → ℕ) (ha : StrictMono a) :
    (Set.range a).Infinite := by
  exact Set.infinite_range_of_injective ha.injective

/-- Superlinear growth forces the range to occupy less than any prescribed
positive proportion of every sufficiently large dyadic block. -/
theorem eventually_dyadicBlockCount_lt_of_growth (a : ℕ → ℕ)
    (hgrowth : Tendsto (fun n => (a n : ℝ) / (n + 1)) atTop atTop)
    (c : ℝ) (hc : 0 < c) :
    ∀ᶠ L : ℕ in atTop,
      (dyadicBlockCount (Set.range a) (dyadicScale L) : ℝ) <
        c * dyadicScale L := by
  classical
  let M : ℝ := 8 / c
  obtain ⟨N, hN⟩ :=
    eventually_atTop.1 (hgrowth.eventually_gt_atTop M)
  have hscale :
      Tendsto (fun L : ℕ => ((dyadicScale L : ℕ) : ℝ)) atTop atTop := by
    simpa [dyadicScale] using
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  filter_upwards
      [hscale.eventually_gt_atTop (2 * (N + 1) / c)] with L hL
  let X := dyadicScale L
  let K := N + Nat.ceil (c * X / 4)
  have hsubset :
      ((Finset.Ioc X (2 * X)).filter fun x => x ∈ Set.range a) ⊆
        (Finset.range K).image a := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hx
    rcases hx.2 with ⟨n, rfl⟩
    have hnK : n < K := by
      by_contra hnot
      have hKn : K ≤ n := le_of_not_gt hnot
      have hNn : N ≤ n := le_trans (Nat.le_add_right N _) hKn
      have hceiln : Nat.ceil (c * X / 4) ≤ n := by
        dsimp [K] at hKn
        omega
      have hratio := hN n hNn
      have hnreal : c * X / 4 ≤ (n : ℝ) := by
        exact (Nat.le_ceil (c * X / 4)).trans (by exact_mod_cast hceiln)
      have hn1pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hmul : M * ((n : ℝ) + 1) < (a n : ℝ) :=
        (lt_div_iff₀ hn1pos).mp (by simpa [Nat.cast_add, Nat.cast_one] using hratio)
      have h2X : (2 : ℝ) * X < a n := by
        dsimp [M] at hmul
        have hXnonneg : (0 : ℝ) ≤ X := by positivity
        field_simp [hc.ne'] at hmul ⊢
        nlinarith
      have hupper : (a n : ℝ) ≤ 2 * X := by exact_mod_cast hx.1.2
      linarith
    simp only [Finset.mem_image, Finset.mem_range]
    exact ⟨n, hnK, rfl⟩
  have hcardNat : dyadicBlockCount (Set.range a) X ≤ K := by
    calc
      dyadicBlockCount (Set.range a) X ≤
          ((Finset.range K).image a).card := Finset.card_le_card hsubset
      _ ≤ (Finset.range K).card := Finset.card_image_le
      _ = K := Finset.card_range K
  have hcardReal :
      (dyadicBlockCount (Set.range a) X : ℝ) ≤ K := by
    exact_mod_cast hcardNat
  have hceil :
      (Nat.ceil (c * X / 4) : ℝ) < c * X / 4 + 1 := by
    exact Nat.ceil_lt_add_one (by positivity)
  have hlarge : (N : ℝ) + 1 < c * X / 2 := by
    dsimp [X] at hL ⊢
    have hcross := (div_lt_iff₀ hc).mp hL
    nlinarith
  dsimp [K] at hcardReal
  push_cast at hcardReal
  dsimp [X] at hcardReal hceil hlarge ⊢
  nlinarith

end Erdos260

/-! Source module: Erdos260/Completion.lean -/

/-!
# Exact partition, integrated upper bound, and the main theorem

This module corresponds to Section 8 and contains the paper's public theorem
and sequence corollary.
-/

noncomputable section

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal

namespace Erdos260

/-- The four parent families form a literal disjoint partition. -/
def ParentPartition (W : WindowSystem) (Z0 : ℕ) : Prop :=
  W.boundedPairs Z0 ∪ rareLargePairs W Z0 ∪
      interiorPairs W Z0 ∪ exteriorPairs W Z0 = W.pairSet ∧
    W.boundedPairs Z0 ∩ rareLargePairs W Z0 = ∅ ∧
    W.boundedPairs Z0 ∩ interiorPairs W Z0 = ∅ ∧
    W.boundedPairs Z0 ∩ exteriorPairs W Z0 = ∅ ∧
    rareLargePairs W Z0 ∩ interiorPairs W Z0 = ∅ ∧
    rareLargePairs W Z0 ∩ exteriorPairs W Z0 = ∅ ∧
    interiorPairs W Z0 ∩ exteriorPairs W Z0 = ∅

/-- Scale-local form of the continuation dichotomy.  Lemma `lem_dichotomy`
supplies this predicate only after the cutoff and scale are sufficiently
large; it is therefore an explicit input to the exact partition theorem. -/
def ExactContinuationDichotomy (W : WindowSystem) (Z0 : ℕ) : Prop :=
  ∀ e : WindowThreshold, e ∈ W.largePairs Z0 →
    IsFrequentPrefix W Z0 (initialLongPrefix W e.1) →
      (LongInteriorPair W Z0 e ∨ LongExteriorPair W Z0 e) ∧
      ¬ (LongInteriorPair W Z0 e ∧ LongExteriorPair W Z0 e)

local instance : Countable AffineLine := by
  let code : AffineLine → ℤ × ℤ × ℤ × ℤ := fun line =>
    (line.A, line.C, line.H, line.K)
  exact (show Function.Injective code from by
    intro line₁ line₂ h
    cases line₁
    cases line₂
    simp only [code, Prod.mk.injEq] at h
    simp_all).countable

private theorem measurableSet_exists_le_countable {α β : Type*}
    [Countable α] [MeasurableSpace β] (f : β → ℝ) (hf : Measurable f)
    (P : α → Prop) (c : α → ℝ) :
    MeasurableSet {x | ∃ a, P a ∧ f x ≤ c a} := by
  classical
  rw [show {x | ∃ a, P a ∧ f x ≤ c a} =
      ⋃ a, if P a then {x | f x ≤ c a} else ∅ by
    ext x
    simp]
  exact MeasurableSet.iUnion fun a => by
    by_cases ha : P a
    · simpa [ha] using measurableSet_le hf measurable_const
    · simp [ha]

private theorem measurableSet_windowThreshold_of_sections
    (E : Set WindowThreshold)
    (hsection : ∀ k : ℕ, MeasurableSet {T : ℝ | (k, T) ∈ E}) :
    MeasurableSet E := by
  rw [show E = ⋃ k : ℕ, Set.prod {k} {T : ℝ | (k, T) ∈ E} by
    ext e
    rcases e with ⟨k, T⟩
    rw [Set.mem_iUnion]
    change (k, T) ∈ E ↔
      ∃ i : ℕ, (k, T) ∈ Set.prod {i} {u : ℝ | (i, u) ∈ E}
    constructor
    · intro h
      exact ⟨k, ⟨by simp, h⟩⟩
    · rintro ⟨i, hi⟩
      have hik : k = i := hi.1
      subst i
      exact hi.2]
  exact MeasurableSet.iUnion fun k =>
    (MeasurableSet.singleton k).prod (hsection k)

theorem measurableSet_boundedPairs (W : WindowSystem) (Z0 : ℕ) :
    MeasurableSet (W.boundedPairs Z0) := by
  exact W.measurableSet_pairSet.inter
    (measurableSet_le W.measurable_excess
      (measurable_const : Measurable
        (fun _ : WindowThreshold => (W.m : ℝ) * Z0)))

theorem measurableSet_largePairs (W : WindowSystem) (Z0 : ℕ) :
    MeasurableSet (W.largePairs Z0) := by
  exact W.measurableSet_pairSet.inter
    (measurableSet_lt
      (measurable_const : Measurable
        (fun _ : WindowThreshold => (W.m : ℝ) * Z0))
      W.measurable_excess)

private theorem measurableSet_longInteriorPair_section
    (W : WindowSystem) (Z0 k : ℕ) :
    MeasurableSet {T : ℝ | LongInteriorPair W Z0 (k, T)} := by
  classical
  have hlargeSection :
      MeasurableSet {T : ℝ | (k, T) ∈ W.largePairs Z0} :=
    (measurableSet_largePairs W Z0).preimage measurable_prodMk_left
  let P : AffineLine × GapWord → Prop := fun lg =>
    IsActualInitialContinuation W Z0 (k, 0) lg.1 lg.2 ∧
      IsInteriorTrajectory W.rational.eta.den lg.1 lg.2
  have hexists : MeasurableSet
      {T : ℝ | ∃ lg : AffineLine × GapWord,
        P lg ∧ W.excess (k, T) / 8 ≤ (lg.2.span : ℝ)} := by
    apply measurableSet_exists_le_countable
    exact W.measurable_excess.comp measurable_prodMk_left |>.div_const 8
  by_cases hfreq : IsFrequentPrefix W Z0 (initialLongPrefix W k)
  · have heq : {T : ℝ | LongInteriorPair W Z0 (k, T)} =
        {T | (k, T) ∈ W.largePairs Z0 ∧
          ∃ lg : AffineLine × GapWord,
            P lg ∧ W.excess (k, T) / 8 ≤ (lg.2.span : ℝ)} := by
      ext T
      change
        ((k, T) ∈ W.largePairs Z0 ∧
          IsFrequentPrefix W Z0 (initialLongPrefix W k) ∧
          ∃ line gaps,
            IsActualInitialContinuation W Z0 (k, T) line gaps ∧
            IsInteriorTrajectory W.rational.eta.den line gaps ∧
            W.excess (k, T) / 8 ≤ (gaps.span : ℝ)) ↔ _
      have hactual : ∀ line gaps,
          IsActualInitialContinuation W Z0 (k, T) line gaps ↔
            IsActualInitialContinuation W Z0 (k, 0) line gaps := by
        intro line gaps
        rfl
      simp only [hfreq, true_and, hactual, P]
      constructor <;> aesop
    rw [heq]
    exact hlargeSection.inter hexists
  · have heq : {T : ℝ | LongInteriorPair W Z0 (k, T)} = ∅ := by
      ext T
      constructor
      · intro h
        exact (hfreq h.2.1).elim
      · intro h
        exact h.elim
    rw [heq]
    exact MeasurableSet.empty

private theorem measurableSet_longExteriorPair_section
    (W : WindowSystem) (Z0 k : ℕ) :
    MeasurableSet {T : ℝ | LongExteriorPair W Z0 (k, T)} := by
  classical
  have hlargeSection :
      MeasurableSet {T : ℝ | (k, T) ∈ W.largePairs Z0} :=
    (measurableSet_largePairs W Z0).preimage measurable_prodMk_left
  have hinteriorSection :
      MeasurableSet {T : ℝ | LongInteriorPair W Z0 (k, T)} :=
    measurableSet_longInteriorPair_section W Z0 k
  let P : AffineLine × GapWord → Prop := fun lg =>
    IsActualFirstExteriorContinuation W Z0 (k, 0) lg.1 lg.2 ∧
      IsExteriorTrajectory W.rational.eta.den lg.1 lg.2
  have hexists : MeasurableSet
      {T : ℝ | ∃ lg : AffineLine × GapWord,
        P lg ∧ W.excess (k, T) / 4 ≤ (lg.2.span : ℝ)} := by
    apply measurableSet_exists_le_countable
    exact W.measurable_excess.comp measurable_prodMk_left |>.div_const 4
  by_cases hfreq : IsFrequentPrefix W Z0 (initialLongPrefix W k)
  · have heq : {T : ℝ | LongExteriorPair W Z0 (k, T)} =
        {T | (k, T) ∈ W.largePairs Z0 ∧
          ¬ LongInteriorPair W Z0 (k, T) ∧
          ∃ lg : AffineLine × GapWord,
            P lg ∧ W.excess (k, T) / 4 ≤ (lg.2.span : ℝ)} := by
      ext T
      change
        ((k, T) ∈ W.largePairs Z0 ∧
          IsFrequentPrefix W Z0 (initialLongPrefix W k) ∧
          ¬ LongInteriorPair W Z0 (k, T) ∧
          ∃ line gaps,
            IsActualFirstExteriorContinuation W Z0 (k, T) line gaps ∧
            IsExteriorTrajectory W.rational.eta.den line gaps ∧
            W.excess (k, T) / 4 ≤ (gaps.span : ℝ)) ↔ _
      have hactual : ∀ line gaps,
          IsActualFirstExteriorContinuation W Z0 (k, T) line gaps ↔
            IsActualFirstExteriorContinuation W Z0 (k, 0) line gaps := by
        intro line gaps
        rfl
      simp only [hfreq, true_and, hactual, P]
      constructor <;> aesop
    rw [heq]
    convert (hlargeSection.inter hinteriorSection.compl).inter hexists using 1
    ext T
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff]
    aesop
  · have heq : {T : ℝ | LongExteriorPair W Z0 (k, T)} = ∅ := by
      ext T
      constructor
      · intro h
        exact (hfreq h.2.1).elim
      · intro h
        exact h.elim
    rw [heq]
    exact MeasurableSet.empty

theorem measurableSet_rareLargePairs (W : WindowSystem) (Z0 : ℕ) :
    MeasurableSet (rareLargePairs W Z0) := by
  apply measurableSet_windowThreshold_of_sections
  intro k
  have hlargeSection :
      MeasurableSet {T : ℝ | (k, T) ∈ W.largePairs Z0} :=
    (measurableSet_largePairs W Z0).preimage measurable_prodMk_left
  by_cases hrare : IsRarePrefix W Z0 (initialLongPrefix W k)
  · simpa [rareLargePairs, hrare] using hlargeSection
  · have heq : {T : ℝ | (k, T) ∈ rareLargePairs W Z0} = ∅ := by
      ext T
      simp [rareLargePairs, hrare]
    rw [heq]
    exact MeasurableSet.empty

theorem measurableSet_interiorPairs (W : WindowSystem) (Z0 : ℕ) :
    MeasurableSet (interiorPairs W Z0) := by
  apply measurableSet_windowThreshold_of_sections
  intro k
  exact measurableSet_longInteriorPair_section W Z0 k

theorem measurableSet_exteriorPairs (W : WindowSystem) (Z0 : ℕ) :
    MeasurableSet (exteriorPairs W Z0) := by
  apply measurableSet_windowThreshold_of_sections
  intro k
  exact measurableSet_longExteriorPair_section W Z0 k

theorem refinedInteriorMass_eq_mass {W : WindowSystem} {Z0 : ℕ}
    (refinement : InteriorRefinement W Z0) :
    refinedInteriorMass refinement = mass (interiorPairs W Z0) W.excess := by
  unfold refinedInteriorMass mass
  apply setLIntegral_congr_fun (measurableSet_interiorPairs W Z0)
  intro e he
  apply congrArg ENNReal.ofReal
  have hsum := refinement.sums_to_excess e he
  calc
    (∑ b ∈ (refinement.blocks e.1).toFinset,
        interiorComponentWeight (W.excess e) (refinement.blocks e.1) b) =
        ∑ b ∈ refinement.labels e, refinement.weight e b := by
          rw [refinement.labels_eq e he]
          apply Finset.sum_congr rfl
          intro b hb
          symm
          apply refinement.weight_eq e he b
          simpa [refinement.labels_eq e he] using hb
    _ = W.excess e := hsum

private theorem parentPartition_of_exactContinuationDichotomy
    (W : WindowSystem) (Z0 : ℕ)
    (hdichotomy : ExactContinuationDichotomy W Z0) :
    ParentPartition W Z0 := by
  unfold ParentPartition
  have hunion :
      W.boundedPairs Z0 ∪ rareLargePairs W Z0 ∪
          interiorPairs W Z0 ∪ exteriorPairs W Z0 = W.pairSet := by
    apply Set.Subset.antisymm
    · intro e he
      rcases he with (((hbounded | hrare) | hinterior) | hexterior)
      · exact hbounded.1
      · exact hrare.1.1
      · exact hinterior.1.1
      · exact hexterior.1.1
    · intro e he
      by_cases hbounded : W.excess e ≤ (W.m : ℝ) * Z0
      · exact Or.inl (Or.inl (Or.inl ⟨he, hbounded⟩))
      · have hlarge : e ∈ W.largePairs Z0 :=
          ⟨he, lt_of_not_ge hbounded⟩
        by_cases hfrequent :
            IsFrequentPrefix W Z0 (initialLongPrefix W e.1)
        · rcases (hdichotomy e hlarge hfrequent).1 with
            hinterior | hexterior
          · exact Or.inl (Or.inr hinterior)
          · exact Or.inr hexterior
        · have hrarePrefix :
              IsRarePrefix W Z0 (initialLongPrefix W e.1) := by
            unfold IsRarePrefix
            change ¬ frequencyCutoff W ≤
              prefixMultiplicity W Z0 (initialLongPrefix W e.1) at hfrequent
            exact lt_of_not_ge hfrequent
          exact Or.inl (Or.inl (Or.inr ⟨hlarge, hrarePrefix⟩))
  refine ⟨hunion, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Set.eq_empty_iff_forall_notMem.mpr
    intro e he
    have hbounded := he.1.2
    have hlarge := he.2.1.2
    change W.excess e ≤ (W.m : ℝ) * Z0 at hbounded
    change (W.m : ℝ) * Z0 < W.excess e at hlarge
    exact (not_lt_of_ge hbounded) hlarge
  · apply Set.eq_empty_iff_forall_notMem.mpr
    intro e he
    have hbounded := he.1.2
    have hlarge := he.2.1.2
    change W.excess e ≤ (W.m : ℝ) * Z0 at hbounded
    change (W.m : ℝ) * Z0 < W.excess e at hlarge
    exact (not_lt_of_ge hbounded) hlarge
  · apply Set.eq_empty_iff_forall_notMem.mpr
    intro e he
    have hbounded := he.1.2
    have hlarge := he.2.1.2
    change W.excess e ≤ (W.m : ℝ) * Z0 at hbounded
    change (W.m : ℝ) * Z0 < W.excess e at hlarge
    exact (not_lt_of_ge hbounded) hlarge
  · apply Set.eq_empty_iff_forall_notMem.mpr
    intro e he
    have hrare := he.1.2
    have hfrequent := he.2.2.1
    change (prefixMultiplicity W Z0 (initialLongPrefix W e.1) : ℝ) <
      frequencyCutoff W at hrare
    unfold IsFrequentPrefix at hfrequent
    exact (not_lt_of_ge hfrequent) hrare
  · apply Set.eq_empty_iff_forall_notMem.mpr
    intro e he
    have hrare := he.1.2
    have hfrequent := he.2.2.1
    change (prefixMultiplicity W Z0 (initialLongPrefix W e.1) : ℝ) <
      frequencyCutoff W at hrare
    unfold IsFrequentPrefix at hfrequent
    exact (not_lt_of_ge hfrequent) hrare
  · apply Set.eq_empty_iff_forall_notMem.mpr
    intro e he
    exact he.2.2.2.1 he.1

private theorem mass_union_of_disjoint {E F : Set WindowThreshold}
    {weight : WindowThreshold → ℝ} (hF : MeasurableSet F)
    (hdisjoint : Disjoint E F) :
    mass (E ∪ F) weight = mass E weight + mass F weight := by
  unfold mass
  exact lintegral_union hF hdisjoint

/-- Paper label: `prop:exact-source-decomp` (Section 8). -/
theorem prop_exact_source_decomp (W : WindowSystem) (Z0 : ℕ)
    (hdichotomy : ExactContinuationDichotomy W Z0)
    (refinement : InteriorRefinement W Z0) :
    ParentPartition W Z0 ∧ MeasurableSet W.pairSet ∧
    MeasurableSet (W.boundedPairs Z0) ∧
    MeasurableSet (rareLargePairs W Z0) ∧
    MeasurableSet (interiorPairs W Z0) ∧
    MeasurableSet (exteriorPairs W Z0) ∧
    FiniteMass W.pairSet W.excess ∧
    mass W.pairSet W.excess =
      mass (W.boundedPairs Z0) W.excess +
      mass (rareLargePairs W Z0) W.excess +
      refinedInteriorMass refinement +
      mass (exteriorPairs W Z0) W.excess ∧
    refinedInteriorMass refinement = mass (interiorPairs W Z0) W.excess := by
  have hpartition :=
    parentPartition_of_exactContinuationDichotomy W Z0 hdichotomy
  have hpair := W.measurableSet_pairSet
  have hbounded := measurableSet_boundedPairs W Z0
  have hrare := measurableSet_rareLargePairs W Z0
  have hinterior := measurableSet_interiorPairs W Z0
  have hexterior := measurableSet_exteriorPairs W Z0
  have hrefined := refinedInteriorMass_eq_mass refinement
  have hAB : Disjoint (W.boundedPairs Z0) (rareLargePairs W Z0) :=
    Set.disjoint_iff_inter_eq_empty.mpr hpartition.2.1
  have hAC : Disjoint (W.boundedPairs Z0) (interiorPairs W Z0) :=
    Set.disjoint_iff_inter_eq_empty.mpr hpartition.2.2.1
  have hAD : Disjoint (W.boundedPairs Z0) (exteriorPairs W Z0) :=
    Set.disjoint_iff_inter_eq_empty.mpr hpartition.2.2.2.1
  have hBC : Disjoint (rareLargePairs W Z0) (interiorPairs W Z0) :=
    Set.disjoint_iff_inter_eq_empty.mpr hpartition.2.2.2.2.1
  have hBD : Disjoint (rareLargePairs W Z0) (exteriorPairs W Z0) :=
    Set.disjoint_iff_inter_eq_empty.mpr hpartition.2.2.2.2.2.1
  have hCD : Disjoint (interiorPairs W Z0) (exteriorPairs W Z0) :=
    Set.disjoint_iff_inter_eq_empty.mpr hpartition.2.2.2.2.2.2
  have hAB_C :
      Disjoint (W.boundedPairs Z0 ∪ rareLargePairs W Z0)
        (interiorPairs W Z0) := by
    apply Set.disjoint_left.2
    intro e heAB heC
    rcases heAB with heA | heB
    · exact Set.disjoint_left.1 hAC heA heC
    · exact Set.disjoint_left.1 hBC heB heC
  have hABC_D :
      Disjoint
        (W.boundedPairs Z0 ∪ rareLargePairs W Z0 ∪ interiorPairs W Z0)
        (exteriorPairs W Z0) := by
    apply Set.disjoint_left.2
    intro e heABC heD
    rcases heABC with (heA | heB) | heC
    · exact Set.disjoint_left.1 hAD heA heD
    · exact Set.disjoint_left.1 hBD heB heD
    · exact Set.disjoint_left.1 hCD heC heD
  have hmass :
      mass W.pairSet W.excess =
        mass (W.boundedPairs Z0) W.excess +
        mass (rareLargePairs W Z0) W.excess +
        refinedInteriorMass refinement +
        mass (exteriorPairs W Z0) W.excess := by
    calc
      mass W.pairSet W.excess =
          mass
            (W.boundedPairs Z0 ∪ rareLargePairs W Z0 ∪
              interiorPairs W Z0 ∪ exteriorPairs W Z0)
            W.excess := congrArg (fun E => mass E W.excess) hpartition.1.symm
      _ = mass
              (W.boundedPairs Z0 ∪ rareLargePairs W Z0 ∪
                interiorPairs W Z0) W.excess +
            mass (exteriorPairs W Z0) W.excess :=
        mass_union_of_disjoint hexterior hABC_D
      _ = (mass (W.boundedPairs Z0 ∪ rareLargePairs W Z0) W.excess +
              mass (interiorPairs W Z0) W.excess) +
            mass (exteriorPairs W Z0) W.excess := by
        rw [mass_union_of_disjoint hinterior hAB_C]
      _ = ((mass (W.boundedPairs Z0) W.excess +
              mass (rareLargePairs W Z0) W.excess) +
              mass (interiorPairs W Z0) W.excess) +
            mass (exteriorPairs W Z0) W.excess := by
        rw [mass_union_of_disjoint hrare hAB]
      _ = mass (W.boundedPairs Z0) W.excess +
            mass (rareLargePairs W Z0) W.excess +
            refinedInteriorMass refinement +
            mass (exteriorPairs W Z0) W.excess := by
        rw [hrefined]
  exact ⟨hpartition, hpair, hbounded, hrare, hinterior, hexterior,
    totalFiniteMass W, hmass, hrefined⟩

private theorem finiteWindowMass_nonneg (W : WindowSystem)
    (E : Set WindowThreshold) (hE : E ⊆ W.pairSet) :
    0 ≤ finiteWindowMass W E hE := by
  change 0 ≤ (finiteMassOfSubset W E hE).toReal
  exact FiniteMass.toReal_nonneg _

private theorem ofReal_finiteWindowMass (W : WindowSystem)
    (E : Set WindowThreshold) (hE : E ⊆ W.pairSet) :
    ENNReal.ofReal (finiteWindowMass W E hE) = mass E W.excess := by
  change ENNReal.ofReal (finiteMassOfSubset W E hE).toReal = mass E W.excess
  exact FiniteMass.ofReal_toReal _

/-- Safe real-valued form of the exact parent decomposition.  Every real
conversion is backed by `finiteMassOfSubset`; in particular no infinite
`ENNReal` mass is ever silently mapped to zero. -/
theorem integratedExcess_exact_decomposition (W : WindowSystem) (Z0 : ℕ)
    (hdichotomy : ExactContinuationDichotomy W Z0)
    (refinement : InteriorRefinement W Z0) :
    integratedExcess W =
      boundedPairsMass W Z0 + rareLargePairsMass W Z0 +
      interiorPairsMass W Z0 + exteriorPairsMass W Z0 := by
  obtain ⟨_, _, _, _, _, _, _, hmass, hrefined⟩ :=
    prop_exact_source_decomp W Z0 hdichotomy refinement
  rw [hrefined] at hmass
  have htotal : 0 ≤ integratedExcess W := by
    change 0 ≤ (totalFiniteMass W).toReal
    exact FiniteMass.toReal_nonneg _
  have hbounded : 0 ≤ boundedPairsMass W Z0 := by
    exact finiteWindowMass_nonneg W (W.boundedPairs Z0)
      (boundedPairs_subset_pairSet W Z0)
  have hrare : 0 ≤ rareLargePairsMass W Z0 := by
    exact finiteWindowMass_nonneg W (rareLargePairs W Z0)
      (rareLargePairs_subset_pairSet W Z0)
  have hinterior : 0 ≤ interiorPairsMass W Z0 := by
    exact finiteWindowMass_nonneg W (interiorPairs W Z0)
      (interiorPairs_subset_pairSet W Z0)
  have hexterior : 0 ≤ exteriorPairsMass W Z0 := by
    exact finiteWindowMass_nonneg W (exteriorPairs W Z0)
      (exteriorPairs_subset_pairSet W Z0)
  have hsum : 0 ≤
      boundedPairsMass W Z0 + rareLargePairsMass W Z0 +
      interiorPairsMass W Z0 + exteriorPairsMass W Z0 := by
    positivity
  have hbounded_ofReal :
      ENNReal.ofReal (boundedPairsMass W Z0) =
        mass (W.boundedPairs Z0) W.excess := by
    unfold boundedPairsMass
    exact ofReal_finiteWindowMass W (W.boundedPairs Z0)
      (boundedPairs_subset_pairSet W Z0)
  have hrare_ofReal :
      ENNReal.ofReal (rareLargePairsMass W Z0) =
        mass (rareLargePairs W Z0) W.excess := by
    unfold rareLargePairsMass
    exact ofReal_finiteWindowMass W (rareLargePairs W Z0)
      (rareLargePairs_subset_pairSet W Z0)
  have hinterior_ofReal :
      ENNReal.ofReal (interiorPairsMass W Z0) =
        mass (interiorPairs W Z0) W.excess := by
    unfold interiorPairsMass
    exact ofReal_finiteWindowMass W (interiorPairs W Z0)
      (interiorPairs_subset_pairSet W Z0)
  have hexterior_ofReal :
      ENNReal.ofReal (exteriorPairsMass W Z0) =
        mass (exteriorPairs W Z0) W.excess := by
    unfold exteriorPairsMass
    exact ofReal_finiteWindowMass W (exteriorPairs W Z0)
      (exteriorPairs_subset_pairSet W Z0)
  apply (ENNReal.ofReal_eq_ofReal_iff htotal hsum).mp
  calc
    ENNReal.ofReal (integratedExcess W) =
        mass W.pairSet W.excess := ofReal_integratedExcess W
    _ = mass (W.boundedPairs Z0) W.excess +
          mass (rareLargePairs W Z0) W.excess +
          mass (interiorPairs W Z0) W.excess +
          mass (exteriorPairs W Z0) W.excess := hmass
    _ = ENNReal.ofReal
          (boundedPairsMass W Z0 + rareLargePairsMass W Z0 +
            interiorPairsMass W Z0 + exteriorPairsMass W Z0) := by
      rw [ENNReal.ofReal_add (add_nonneg (add_nonneg hbounded hrare) hinterior)
          hexterior,
        ENNReal.ofReal_add (add_nonneg hbounded hrare) hinterior,
        ENNReal.ofReal_add hbounded hrare,
        hbounded_ofReal, hrare_ofReal, hinterior_ofReal, hexterior_ofReal]

/-- Paper label: `prop:upper` (Section 8).  The cutoff and vanishing error are
selected from the denominator-level context before the numerator/support
family and before the pointwise density deficit. -/
theorem prop_upper (context : FixedScaleContext) :
    ∀ θ : ℝ, 0 < θ →
      ∃ Z0 : ℕ, ∃ error : ℕ → ℝ,
        Tendsto error atTop (𝓝 0) ∧
        ∀ F : ScaleFamily, F.MatchesContext context →
          ∀ᶠ L : ℕ in atTop, ∀ cstar : ℝ,
            cstar ∈ Set.Icc (0 : ℝ) 1 →
            (dyadicBlockCount (F.system L).rational.S
                (F.system L).X : ℝ) ≤ cstar * (F.system L).X →
            integratedExcess (F.system L) ≤
              ((Z0 : ℝ) * cstar + θ + error L) *
                normalizationScale (F.system L) := by
  intro θ hθ
  obtain ⟨gap⟩ := gapParams_exists context.Q context.Q_pos
  obtain ⟨Zdichotomy, hdichotomy⟩ := lem_dichotomy context gap
  obtain ⟨Zuniform, interiorBound, hinterior_nonneg, hinterior_zero,
      huniform⟩ := prop_uniform_errors context
  obtain ⟨Zstrict, ηQ, hηQ_nonneg, hηQ_zero, hstrict⟩ :=
    thm_strict_mass context
  have hinterior_small : ∀ᶠ Z : ℕ in atTop, interiorBound Z < θ / 3 :=
    (tendsto_order.1 hinterior_zero).2 _ (by linarith)
  obtain ⟨Zsmall, hZsmall⟩ := eventually_atTop.1 hinterior_small
  let Z0 := max Zsmall (max Zdichotomy (max Zuniform Zstrict))
  have hZsmall_le : Zsmall ≤ Z0 := le_max_left _ _
  have hZdichotomy : Zdichotomy ≤ Z0 := by
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hZuniform : Zuniform ≤ Z0 := by
    exact le_trans
      (le_trans (le_max_left _ _) (le_max_right Zdichotomy _))
      (le_max_right Zsmall _)
  have hZstrict : Zstrict ≤ Z0 := by
    exact le_trans
      (le_trans (le_max_right _ _) (le_max_right Zdichotomy _))
      (le_max_right Zsmall _)
  have hbound_small : interiorBound Z0 < θ / 3 :=
    hZsmall Z0 hZsmall_le
  refine ⟨Z0, (fun _ : ℕ => (0 : ℝ)), tendsto_const_nhds, ?_⟩
  intro F hF
  obtain ⟨_hboundary, hrare_all, hexterior_all, hinterior_all⟩ :=
    huniform F hF
  have hrare_zero :
      Tendsto (fun L => rareMassRatio (F.system L) Z0) atTop (𝓝 0) := by
    simpa [rareMassRatio] using
      (hrare_all Z0 hZuniform).tendsto_div_nhds_zero
  have hexterior_zero :
      Tendsto (fun L => exteriorMassRatio (F.system L) Z0) atTop (𝓝 0) := by
    simpa [exteriorMassRatio] using
      (hexterior_all Z0 hZuniform).tendsto_div_nhds_zero
  have hrare_small : ∀ᶠ L : ℕ in atTop,
      rareMassRatio (F.system L) Z0 < θ / 3 :=
    (tendsto_order.1 hrare_zero).2 _ (by linarith)
  have hexterior_small : ∀ᶠ L : ℕ in atTop,
      exteriorMassRatio (F.system L) Z0 < θ / 3 :=
    (tendsto_order.1 hexterior_zero).2 _ (by linarith)
  filter_upwards [hdichotomy Z0 hZdichotomy F hF,
      hstrict Z0 hZstrict F hF,
      hinterior_all Z0 hZuniform,
      hrare_small, hexterior_small, eventually_ge_atTop 1] with
      L hLdichotomy hLstrict hLinterior hLrare hLexterior hLpos
  intro cstar hcstar hsparse
  obtain ⟨refinement, _hrefinement_bound⟩ := hLstrict
  have hnormalization : 0 < normalizationScale (F.system L) := by
    rw [normalizationScale, thresholdLength, F.level_eq]
    have hm : (0 : ℝ) < (F.system L).m := by
      exact_mod_cast Nat.succ_pos (F.system L).s
    have hX : (0 : ℝ) < (F.system L).X := by
      exact_mod_cast pow_pos (by decide : 0 < (2 : ℕ)) (F.system L).L
    have hcI : 0 < (F.system L).structural.cI :=
      (F.system L).structural.cI_pos
    have hLreal : (0 : ℝ) < L := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hLpos)
    positivity
  have hrare_mass : rareLargePairsMass (F.system L) Z0 ≤
      (θ / 3) * normalizationScale (F.system L) := by
    have h := mul_lt_mul_of_pos_right hLrare hnormalization
    simpa [rareMassRatio, hnormalization.ne'] using h.le
  have hexterior_mass : exteriorPairsMass (F.system L) Z0 ≤
      (θ / 3) * normalizationScale (F.system L) := by
    have h := mul_lt_mul_of_pos_right hLexterior hnormalization
    simpa [exteriorMassRatio, hnormalization.ne'] using h.le
  have hinterior_ratio : interiorMassRatio (F.system L) Z0 < θ / 3 :=
    lt_of_le_of_lt hLinterior hbound_small
  have hinterior_mass : interiorPairsMass (F.system L) Z0 ≤
      (θ / 3) * normalizationScale (F.system L) := by
    have h := mul_lt_mul_of_pos_right hinterior_ratio hnormalization
    simpa [interiorMassRatio, hnormalization.ne'] using h.le
  have hmoderate : boundedPairsMass (F.system L) Z0 ≤
      ((Z0 : ℝ) * cstar) * normalizationScale (F.system L) := by
    simpa [normalizationScale, mul_assoc] using
      prop_moderate (F.system L) Z0 cstar hcstar.1 hsparse
  have hexact : ExactContinuationDichotomy (F.system L) Z0 :=
    hLdichotomy
  rw [integratedExcess_exact_decomposition (F.system L) Z0 hexact refinement]
  calc
    boundedPairsMass (F.system L) Z0 +
          rareLargePairsMass (F.system L) Z0 +
          interiorPairsMass (F.system L) Z0 +
          exteriorPairsMass (F.system L) Z0 ≤
        ((Z0 : ℝ) * cstar) * normalizationScale (F.system L) +
          (θ / 3) * normalizationScale (F.system L) +
          (θ / 3) * normalizationScale (F.system L) +
          (θ / 3) * normalizationScale (F.system L) := by
      gcongr
    _ = ((Z0 : ℝ) * cstar + θ + (fun _ : ℕ => (0 : ℝ)) L) *
          normalizationScale (F.system L) := by ring

/-- Paper label: `thm:main-density` (Introduction / Section 8). -/
theorem thm_main_density :
    ∀ Q : ℕ, 0 < Q →
      ∃ cDensity : ℝ, 0 < cDensity ∧
        ∀ S : Set ℕ, ∀ η : ℚ, η.den = Q → S.Infinite →
          HasSum (weightedSupportTerm S) (η : ℝ) →
          ∀ᶠ L : ℕ in atTop,
            cDensity * dyadicScale L ≤
              (dyadicBlockCount S (dyadicScale L) : ℝ) := by
  intro Q hQ
  obtain ⟨p, entropy, hstructural⟩ := exists_structural_entropy_params
  obtain ⟨ε, cLower, deltaLower, hε, hcLower, hdeltaLower,
      L0, hpressure⟩ := prop_pressure Q hQ p entropy hstructural
  let context : FixedScaleContext :=
    { Q := Q
      Q_pos := hQ
      structural := p
      entropy := entropy
      entropy_structural := hstructural
      epsilon := ε
      epsilon_pos := hε }
  let θ : ℝ := cLower / 4
  have hθ : 0 < θ := by
    dsimp [θ]
    positivity
  obtain ⟨Z0, error, herror, hupper⟩ := prop_upper context θ hθ
  let cDensity : ℝ :=
    min (1 / 2 : ℝ)
      (min (deltaLower / 2) (cLower / (8 * ((Z0 : ℝ) + 1))))
  have hcDensity : 0 < cDensity := by
    dsimp [cDensity]
    apply lt_min
    · norm_num
    · apply lt_min
      · linarith
      · positivity
  have hcDensity_one : cDensity ≤ 1 := by
    calc
      cDensity ≤ 1 / 2 := min_le_left _ _
      _ ≤ 1 := by norm_num
  have hcDensity_delta : cDensity ≤ deltaLower := by
    calc
      cDensity ≤ deltaLower / 2 :=
        le_trans (min_le_right _ _) (min_le_left _ _)
      _ ≤ deltaLower := by linarith
  have hcutoff : (Z0 : ℝ) * cDensity < cLower / 4 := by
    have hbound : cDensity ≤ cLower / (8 * ((Z0 : ℝ) + 1)) :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    have hZnonneg : (0 : ℝ) ≤ Z0 := by positivity
    have hdenpos : 0 < 8 * ((Z0 : ℝ) + 1) := by positivity
    have hmul : (Z0 : ℝ) * cDensity ≤
        (Z0 : ℝ) * (cLower / (8 * ((Z0 : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_left hbound hZnonneg
    have hratio :
        (Z0 : ℝ) * (cLower / (8 * ((Z0 : ℝ) + 1))) <
          cLower / 8 := by
      calc
        (Z0 : ℝ) * (cLower / (8 * ((Z0 : ℝ) + 1))) =
            ((Z0 : ℝ) * cLower) / (8 * ((Z0 : ℝ) + 1)) := by ring
        _ < cLower / 8 := by
          rw [div_lt_div_iff₀ hdenpos (by norm_num : (0 : ℝ) < 8)]
          nlinarith
    exact lt_of_le_of_lt hmul (lt_trans hratio (by linarith))
  refine ⟨cDensity, hcDensity, ?_⟩
  intro S η hη hSinfinite hsum
  let rational : RationalSupport :=
    RationalSupport.normalize S η hSinfinite hsum
  let enumeration : SupportEnumeration rational.S :=
    supportEnumerationOfInfinite rational.S rational.infinite rational.positive
  let system : ℕ → WindowSystem := fun L =>
    { rational := rational
      enumeration := enumeration
      structural := p
      entropy := entropy
      entropy_structural := hstructural
      L := L
      s := Nat.floor (entropy.kappa * (L : ℝ))
      epsilon := ε
      epsilon_nonneg := hε.le }
  let F : ScaleFamily :=
    { rational := rational
      enumeration := enumeration
      structural := p
      entropy := entropy
      entropy_structural := hstructural
      epsilon := ε
      epsilon_nonneg := hε.le
      system := system
      level_eq := by intro L; rfl
      rational_eq := by intro L; rfl
      enumeration_eq := by intro L n; rfl
      structural_eq := by intro L; rfl
      entropy_eq := by intro L; rfl
      epsilon_eq := by intro L; rfl
      offset_eq := by intro L; rfl }
  have hmatches : F.MatchesContext context := by
    refine ⟨?_, rfl, rfl, rfl⟩
    simpa [F, rational, RationalSupport.normalize] using hη
  have herrorSmall : ∀ᶠ L : ℕ in atTop, error L < cLower / 4 :=
    (tendsto_order.1 herror).2 _ (by linarith)
  filter_upwards [hupper F hmatches, herrorSmall,
      eventually_ge_atTop L0, eventually_ge_atTop 1] with
      L hupperL herrorL hL0 hLpos
  by_contra hnot
  have hdeficit :
      (dyadicBlockCount S (dyadicScale L) : ℝ) <
        cDensity * dyadicScale L := lt_of_not_ge hnot
  have hsparse :
      (dyadicBlockCount (F.system L).rational.S (F.system L).X : ℝ) ≤
        cDensity * (F.system L).X := by
    have hlt :
        (dyadicBlockCount (F.system L).rational.S (F.system L).X : ℝ) <
          cDensity * (F.system L).X := by
      change
        (dyadicBlockCount (positiveSupport S) (dyadicScale L) : ℝ) <
          cDensity * dyadicScale L
      simpa only [dyadicBlockCount_positiveSupport] using hdeficit
    exact hlt.le
  have hlower := hpressure (F.system L) cDensity
    (by simpa [F, system, rational, RationalSupport.normalize] using hη)
    (by rfl) (by rfl) (by rfl) (by rfl) hL0 hcDensity
    hcDensity_delta hsparse
  have hupperBound := hupperL cDensity
    ⟨hcDensity.le, hcDensity_one⟩ hsparse
  have hnormalization : 0 < normalizationScale (F.system L) := by
    rw [normalizationScale, thresholdLength, F.level_eq]
    have hm : (0 : ℝ) < (F.system L).m := by
      exact_mod_cast Nat.succ_pos (F.system L).s
    have hX : (0 : ℝ) < (F.system L).X := by
      exact_mod_cast pow_pos (by decide : 0 < (2 : ℕ)) (F.system L).L
    have hcI : 0 < (F.system L).structural.cI :=
      (F.system L).structural.cI_pos
    have hLreal : (0 : ℝ) < L := by exact_mod_cast hLpos
    positivity
  have hlower' : cLower * normalizationScale (F.system L) ≤
      integratedExcess (F.system L) := by
    simpa [normalizationScale, mul_assoc] using hlower
  have hcoefficient :
      (Z0 : ℝ) * cDensity + θ + error L < cLower := by
    dsimp [θ]
    linarith
  have hstrictUpper : integratedExcess (F.system L) <
      cLower * normalizationScale (F.system L) :=
    lt_of_le_of_lt hupperBound
      (mul_lt_mul_of_pos_right hcoefficient hnormalization)
  exact (not_lt_of_ge hlower') hstrictUpper

/-- Paper label: `cor:erdos260` (Introduction). -/
theorem cor_erdos260 (a : ℕ → ℕ) (ha : StrictMono a)
    (_hpositive : ∀ n, 0 < a n)
    (hgrowth : Tendsto (fun n => (a n : ℝ) / (n + 1)) atTop atTop) :
    Irrational (∑' n : ℕ, natSequenceTerm a n) := by
  by_contra hnot
  obtain ⟨η, hη⟩ := exists_rat_of_not_irrational hnot
  have hsum :
      HasSum (weightedSupportTerm (Set.range a)) (η : ℝ) := by
    rw [← hη]
    exact hasSum_range_weightedSupport a ha
  obtain ⟨cDensity, hcDensity, hmain⟩ :=
    thm_main_density η.den (Rat.den_pos η)
  have hlower := hmain (Set.range a) η rfl
    (range_infinite_of_strictMono a ha) hsum
  have hupper :=
    eventually_dyadicBlockCount_lt_of_growth a hgrowth cDensity hcDensity
  obtain ⟨L₁, hL₁⟩ := eventually_atTop.1 hlower
  obtain ⟨L₂, hL₂⟩ := eventually_atTop.1 hupper
  let L := max L₁ L₂
  exact (not_lt_of_ge (hL₁ L (le_max_left _ _)))
    (hL₂ L (le_max_right _ _))

end Erdos260

/-! Source module: Erdos260/DeepMind.lean -/

/-!
# DeepMind Formal Conjectures compatible endpoint

The theorem `erdos_260` has exactly the right-hand-side type used by
`FormalConjectures/ErdosProblems/260.lean`: integer-valued sequence, the
original division by `n`, a supplied `HasSum`, and an `Irrational` conclusion.
This project intentionally does not depend on the Formal Conjectures package.
-/

noncomputable section

open Filter Set
open scoped BigOperators

namespace Erdos260

/-- Integer-exponent summand appearing in the DeepMind statement. -/
def integerSequenceTerm (a : ℕ → ℤ) (n : ℕ) : ℝ :=
  (a n : ℝ) / (2 : ℝ) ^ a n

/-- Positive natural tail after deleting a finite integer-valued prefix. -/
def positiveTail (a : ℕ → ℤ) (N n : ℕ) : ℕ :=
  Int.toNat (a (n + N))

theorem eventually_positive_of_tendsto_ratio (a : ℕ → ℤ)
    (hgrowth : Tendsto (fun n => (a n : ℝ) / n) atTop atTop) :
    ∀ᶠ n : ℕ in atTop, 0 < a n := by
  filter_upwards [hgrowth.eventually_gt_atTop 0, eventually_gt_atTop 0] with n hratio hn
  have hn_real : (0 : ℝ) < n := by exact_mod_cast hn
  rcases (div_pos_iff.mp hratio) with hsame | hsame
  · exact_mod_cast hsame.1
  · exact (not_lt_of_ge hn_real.le hsame.2).elim

theorem positiveTail_strictMono (a : ℕ → ℤ) (N : ℕ)
    (ha : StrictMono a) (hpos : ∀ n ≥ N, 0 < a n) :
    StrictMono (positiveTail a N) := by
  intro n m hnm
  simp only [positiveTail]
  rw [Int.toNat_lt_toNat (hpos (m + N) (by omega))]
  exact ha (by omega)

theorem positiveTail_positive (a : ℕ → ℤ) (N : ℕ)
    (hpos : ∀ n ≥ N, 0 < a n) :
    ∀ n, 0 < positiveTail a N n := by
  intro n
  rw [positiveTail, Int.lt_toNat]
  exact hpos (n + N) (by omega)

theorem positiveTail_growth (a : ℕ → ℤ) (N : ℕ)
    (hgrowth : Tendsto (fun n => (a n : ℝ) / n) atTop atTop)
    (hpos : ∀ n ≥ N, 0 < a n) :
    Tendsto (fun n => (positiveTail a N n : ℝ) / (n + 1)) atTop atTop := by
  have hshift :
      Tendsto (fun n : ℕ => (a (n + N) : ℝ) / (n + N)) atTop atTop := by
    simpa [Function.comp_def] using hgrowth.comp (tendsto_add_atTop_nat N)
  have hfactor :
      Tendsto (fun n : ℕ => ((n + N : ℕ) : ℝ) / (n + 1)) atTop (nhds 1) := by
    simpa [Nat.cast_add, add_comm, add_left_comm, add_assoc] using
      (tendsto_add_mul_div_add_mul_atTop_nhds (N : ℝ) 1 1 (d := 1) one_ne_zero)
  apply (hshift.atTop_mul_pos zero_lt_one hfactor).congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnN_pos : (0 : ℝ) < ((n + N : ℕ) : ℝ) := by positivity
  have htail_cast : (positiveTail a N n : ℝ) = (a (n + N) : ℝ) := by
    have htail_int : (positiveTail a N n : ℤ) = a (n + N) := by
      exact Int.toNat_of_nonneg (hpos (n + N) (by omega)).le
    exact_mod_cast htail_int
  rw [htail_cast]
  field_simp
  simp only [Nat.cast_add]

theorem finite_integer_prefix_is_rational (a : ℕ → ℤ) (N : ℕ) :
    ∃ q : ℚ, (q : ℝ) = ∑ n ∈ Finset.range N, integerSequenceTerm a n := by
  refine ⟨∑ n ∈ Finset.range N, (a n : ℚ) / (2 : ℚ) ^ a n, ?_⟩
  simp only [Rat.cast_sum, Rat.cast_div, Rat.cast_intCast, Rat.cast_ofNat, Rat.cast_zpow,
    integerSequenceTerm]

theorem irrational_add_rational_iff (x : ℝ) (q : ℚ) :
    Irrational (x + q) ↔ Irrational x := by
  exact irrational_add_ratCast_iff

/-- Exact RHS of DeepMind Formal Conjectures' Erdős Problem 260 statement. -/
def deepmindStatement : Prop :=
  ∀ a : ℕ → ℤ, ∀ s : ℝ,
    StrictMono a →
    Tendsto (fun n => (a n : ℝ) / n) atTop atTop →
    HasSum (fun n => (a n : ℝ) / 2 ^ a n) s →
    Irrational s

/-- DeepMind-compatible public endpoint. -/
theorem erdos_260 :
    ∀ a : ℕ → ℤ, ∀ s : ℝ,
      StrictMono a →
      Tendsto (fun n => (a n : ℝ) / n) atTop atTop →
      HasSum (fun n => (a n : ℝ) / 2 ^ a n) s →
      Irrational s := by
  intro a s ha hgrowth hsum
  obtain ⟨N, hpos⟩ :=
    (eventually_atTop.1 (eventually_positive_of_tendsto_ratio a hgrowth))
  let b := positiveTail a N
  have hbmono : StrictMono b := positiveTail_strictMono a N ha hpos
  have hbpos : ∀ n, 0 < b n := positiveTail_positive a N hpos
  have hbgrowth :
      Tendsto (fun n => (b n : ℝ) / (n + 1)) atTop atTop :=
    positiveTail_growth a N hgrowth hpos
  have hirrTail : Irrational (∑' n : ℕ, natSequenceTerm b n) :=
    cor_erdos260 b hbmono hbpos hbgrowth
  have hsum' : HasSum (integerSequenceTerm a) s := hsum
  let prefixSum : ℝ := ∑ n ∈ Finset.range N, integerSequenceTerm a n
  have htailRaw :
      HasSum (fun n => integerSequenceTerm a (n + N)) (s - prefixSum) := by
    simpa [prefixSum] using (hasSum_nat_add_iff' N).2 hsum'
  have hterm (n : ℕ) :
      natSequenceTerm b n = integerSequenceTerm a (n + N) := by
    have han : 0 < a (n + N) := hpos (n + N) (by omega)
    have hnat : (b n : ℤ) = a (n + N) := by
      simpa [b, positiveTail] using Int.toNat_of_nonneg han.le
    have hnum : (b n : ℝ) = (a (n + N) : ℝ) := by
      exact_mod_cast hnat
    have hpow : (2 : ℝ) ^ b n = (2 : ℝ) ^ a (n + N) := by
      rw [← hnat, zpow_natCast]
    simp only [natSequenceTerm, integerSequenceTerm, hnum, hpow]
  have htailNat :
      HasSum (fun n => natSequenceTerm b n) (s - prefixSum) :=
    htailRaw.congr_fun hterm
  obtain ⟨q, hq⟩ := finite_integer_prefix_is_rational a N
  have hs_decomp : s = (∑' n : ℕ, natSequenceTerm b n) + (q : ℝ) := by
    rw [htailNat.tsum_eq, hq]
    exact (sub_add_cancel s prefixSum).symm
  rw [hs_decomp]
  exact (irrational_add_rational_iff _ q).2 hirrTail

end Erdos260

namespace Submissions.Erdos260IrrationalBinarySum.Full

theorem proof :
    ∀ a : ℕ → ℤ, ∀ s : ℝ,
      StrictMono a →
      Filter.Tendsto (fun n => (a n : ℝ) / n) Filter.atTop Filter.atTop →
      HasSum (fun n => (a n : ℝ) / 2 ^ a n) s →
      Irrational s :=
  Erdos260.erdos_260

end Submissions.Erdos260IrrationalBinarySum.Full
