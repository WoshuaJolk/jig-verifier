import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Combinatorics.Additive.Energy
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Int.Basic

/-!
Integer sum-product with the conjectured epsilon exponent on the restricted
class whose elements each have at most two distinct prime factors in absolute
value. The primes may vary with each element. Zero and signs are included.
The complete proof derives support extraction, valuation energy and the actual
normalized graph cap. This does not settle unrestricted integer sum-product.
-/

namespace Submissions.Erdos52OmegaTwo.Finite

/- Audited component: CommonPrimeQuery.lean; input SHA256 46b84cee9e7675cc673298a80eac2a09376d22d34f0ad0b04ee8534763e70de4. -/

/-!
# Finite common-prime query charge for rational pair graphs

This standalone source assembles the ten locally checked components listed in
common-prime-query-assembly-provenance.json. The component documentation below
records the scope and audit history of each original drafting step. The theorem
`proof` at the end constructs all normalization, labels and affine certificates;
its only structural assumption is the cap on the actual projected cofactor
product fibers. It allows negative rational endpoints, zero sums, empty graphs,
and asymmetric selected ordered graphs, but excludes zero endpoints.

This finite charge is not a proof of the unrestricted sum-product conjecture.
-/

namespace CommonPrimeCore

/- Begin assembled component: QueryArithmeticDraft.lean. -/
/- Arithmetic steps of the recursive query-label proof.
This draft does not construct the labels or prove the full sum-product conjecture. -/
namespace QueryArithmetic

def Good (p : ℕ) (L R : ℚ → Finset ℤ) (lam x z : ℚ) : Prop :=
  ∀ a ∈ L x, ∀ b ∈ R z, padicValRat p lam ≠ a - b

variable {p : ℕ}

theorem add_ne_zero_of_val_ne {a b : ℚ}
    (h : padicValRat p a ≠ padicValRat p b) : a + b ≠ 0 := by
  intro hab
  have ha : a = -b := eq_neg_of_add_eq_zero_left hab
  exact h (by rw [ha, padicValRat.neg])

variable [Fact p.Prime]

theorem query_alternatives {L R : ℚ → Finset ℤ}
    {lam x z y α β : ℚ} (hlam : lam ≠ 0) (hx : x ≠ α) (hz : z ≠ β)
    (he : padicValRat p (x - α) ∈ L x)
    (hf : padicValRat p (z - β) ∈ R z)
    (hgood : Good p L R lam x z) (hsum : x + lam * z = y) :
    y - α - lam * β ≠ 0 ∧
      ((padicValRat p (x - α) = padicValRat p (y - α - lam * β) ∧
        padicValRat p (x - α) < padicValRat p lam + padicValRat p (z - β)) ∨
       (padicValRat p lam + padicValRat p (z - β) =
          padicValRat p (y - α - lam * β) ∧
        padicValRat p lam + padicValRat p (z - β) < padicValRat p (x - α))) := by
  have hx0 : x - α ≠ 0 := sub_ne_zero.mpr hx
  have hz0 : z - β ≠ 0 := sub_ne_zero.mpr hz
  have hneq : padicValRat p (x - α) ≠
      padicValRat p lam + padicValRat p (z - β) := by
    intro h
    have hbad := hgood _ he _ hf
    apply hbad
    omega
  have hmul := padicValRat.mul (p := p) hlam hz0
  have heq : y - α - lam * β = (x - α) + lam * (z - β) := by
    rw [← hsum]
    ring
  have hnonzero : y - α - lam * β ≠ 0 := by
    rw [heq]
    apply add_ne_zero_of_val_ne
    rwa [hmul]
  refine ⟨hnonzero, ?_⟩
  have hval : padicValRat p (y - α - lam * β) =
      min (padicValRat p (x - α))
        (padicValRat p lam + padicValRat p (z - β)) := by
    rw [heq]
    rw [padicValRat.add_eq_min (by rwa [← heq]) hx0 (mul_ne_zero hlam hz0)
      (by rwa [hmul]), hmul]
  rcases lt_or_gt_of_ne hneq with h | h
  · exact Or.inl ⟨by rw [hval, min_eq_left (le_of_lt h)], h⟩
  · exact Or.inr ⟨by rw [hval, min_eq_right (le_of_lt h)], h⟩

theorem affine_difference_valuation {lam x x' z z' y : ℚ}
    (hlam : lam ≠ 0) (hxx : x ≠ x')
    (hs : x + lam * z = y) (hs' : x' + lam * z' = y) :
    z ≠ z' ∧ padicValRat p (x - x') =
      padicValRat p lam + padicValRat p (z - z') := by
  have hzz : z ≠ z' := by
    intro hz
    apply hxx
    rw [hz] at hs
    exact add_right_cancel (hs.trans hs'.symm)
  have hd : x - x' = -(lam * (z - z')) := by
    have hh := hs.trans hs'.symm
    linarith
  refine ⟨hzz, ?_⟩
  rw [hd, padicValRat.neg, padicValRat.mul hlam (sub_ne_zero.mpr hzz)]

theorem full_separation_excludes_two {L R : ℚ → Finset ℤ}
    {lam x x' z z' y : ℚ} (hlam : lam ≠ 0) (hxx : x ≠ x')
    (hs : x + lam * z = y) (hs' : x' + lam * z' = y)
    (hl : padicValRat p (x - x') ∈ L x)
    (hl' : padicValRat p (x - x') ∈ L x')
    (hr : padicValRat p (z - z') ∈ R z ∨
      padicValRat p (z - z') ∈ R z') :
    ¬(Good p L R lam x z ∧ Good p L R lam x' z') := by
  intro hgood
  have hv := (affine_difference_valuation (p := p) hlam hxx hs hs').2
  rcases hr with hr | hr
  · have hbad := hgood.1 _ hl _ hr
    apply hbad
    omega
  · have hbad := hgood.2 _ hl' _ hr
    apply hbad
    omega

omit [Fact p.Prime] in
theorem shared_left_answer_excludes_column {L R : ℚ → Finset ℤ}
    {lam x z : ℚ} {t : ℤ} (hl : t ∈ L x)
    (hr : t - padicValRat p lam ∈ R z) : ¬Good p L R lam x z := by
  intro hgood
  have hbad := hgood _ hl _ hr
  apply hbad
  omega

theorem orbit_valuation {q : ℚ} (hq : q ≠ 0) (i : ℤ) :
    padicValRat p ((p : ℚ) ^ i * q) = i + padicValRat p q := by
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [padicValRat.mul (zpow_ne_zero i hp0) hq, padicValRat.zpow,
    padicValRat.self (Fact.out : p.Prime).one_lt, mul_one]

theorem orbit_sum_recovers_lower_level {q r : ℚ} {i j : ℤ}
    (hq : q ≠ 0) (hr : r ≠ 0)
    (hvq : padicValRat p q = 0) (hvr : padicValRat p r = 0) (hij : i < j) :
    (p : ℚ) ^ i * q + (p : ℚ) ^ j * r ≠ 0 ∧
    padicValRat p ((p : ℚ) ^ i * q + (p : ℚ) ^ j * r) = i := by
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hv1 : padicValRat p ((p : ℚ) ^ i * q) = i := by
    rw [orbit_valuation hq, hvq, add_zero]
  have hv2 : padicValRat p ((p : ℚ) ^ j * r) = j := by
    rw [orbit_valuation hr, hvr, add_zero]
  have hn : (p : ℚ) ^ i * q + (p : ℚ) ^ j * r ≠ 0 :=
    add_ne_zero_of_val_ne (by rw [hv1, hv2]; exact ne_of_lt hij)
  refine ⟨hn, ?_⟩
  rw [padicValRat.add_eq_of_lt hn (mul_ne_zero (zpow_ne_zero i hp0) hq)
    (mul_ne_zero (zpow_ne_zero j hp0) hr) (by rw [hv1, hv2]; exact hij), hv1]

theorem product_and_gap_recover_levels {q r : ℚ} {i j k l : ℤ}
    (hq : q ≠ 0) (hr : r ≠ 0)
    (heq : ((p : ℚ) ^ i * q) * ((p : ℚ) ^ j * r) =
      ((p : ℚ) ^ k * q) * ((p : ℚ) ^ l * r))
    (hgap : i - j = k - l) : i = k ∧ j = l := by
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hv := congrArg (padicValRat p) heq
  rw [padicValRat.mul (mul_ne_zero (zpow_ne_zero i hp0) hq)
      (mul_ne_zero (zpow_ne_zero j hp0) hr),
    padicValRat.mul (mul_ne_zero (zpow_ne_zero k hp0) hq)
      (mul_ne_zero (zpow_ne_zero l hp0) hr),
    orbit_valuation hq, orbit_valuation hr, orbit_valuation hq, orbit_valuation hr] at hv
  constructor <;> omega

theorem smaller_gap_difference {q q' r r' : ℚ} {g g' : ℤ}
    (hr : r ≠ 0) (hr' : r' ≠ 0)
    (hvr : padicValRat p r = 0) (hvr' : padicValRat p r' = 0)
    (hgg : g < g')
    (hs : q + (p : ℚ) ^ g * r = q' + (p : ℚ) ^ g' * r') :
    q ≠ q' ∧ padicValRat p (q - q') = g := by
  have hnvr : padicValRat p (-r) = 0 := by rw [padicValRat.neg, hvr]
  have h := orbit_sum_recovers_lower_level (neg_ne_zero.mpr hr) hr' hnvr hvr' hgg
  have hd : q - q' = (p : ℚ) ^ g * (-r) + (p : ℚ) ^ g' * r' := by
    linarith
  refine ⟨sub_ne_zero.mp (by rw [hd]; exact h.1), ?_⟩
  rw [hd]
  exact h.2


end QueryArithmetic

namespace LaminarMajority

/- A smallest majority member of a finite laminar family lies inside every
other majority member. This constructs a pivot from laminarity and cardinalities;
no hypothesis prescribes the pivot or asserts its desired membership property. -/
theorem exists_majority_pivot {α : Type*} [DecidableEq α]
    {U : Finset α} {F : Finset (Finset α)}
    (hsub : ∀ B ∈ F, B ⊆ U) (hU : U ∈ F) (hne : U.Nonempty)
    (hlam : ∀ B ∈ F, ∀ D ∈ F,
      (B ∩ D).Nonempty → B ⊆ D ∨ D ⊆ B) :
    ∃ x ∈ U, ∀ B ∈ F, U.card < 2 * B.card → x ∈ B := by
  classical
  let M : Finset (Finset α) := F.filter (fun B => U.card < 2 * B.card)
  have hUM : U ∈ M := by
    apply Finset.mem_filter.mpr
    refine ⟨hU, ?_⟩
    have hpos : 0 < U.card := Finset.card_pos.mpr hne
    omega
  obtain ⟨C, hCM, hmin⟩ :=
    Finset.exists_min_image M (fun B : Finset α => B.card) ⟨U, hUM⟩
  have hCF : C ∈ F := (Finset.mem_filter.mp hCM).1
  have hCmajor : U.card < 2 * C.card := (Finset.mem_filter.mp hCM).2
  have hCpos : 0 < C.card := by omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hCpos
  refine ⟨x, hsub C hCF hx, ?_⟩
  intro D hDF hDmajor
  have hDM : D ∈ M := Finset.mem_filter.mpr ⟨hDF, hDmajor⟩
  have hmincard : C.card ≤ D.card := hmin D hDM
  have hinter : (C ∩ D).Nonempty := by
    apply Finset.card_pos.mp
    have hunion : (C ∪ D).card ≤ U.card :=
      Finset.card_le_card (Finset.union_subset (hsub C hCF) (hsub D hDF))
    have hidentity := Finset.card_union_add_card_inter C D
    omega
  rcases hlam C hCF D hDF hinter with hCD | hDC
  · exact hCD hx
  · have hEq : D = C := Finset.eq_of_subset_of_card_le hDC hmincard
    rw [hEq]
    exact hx


end LaminarMajority

namespace QueryBalls

def Close (p : ℕ) (t : ℤ) (x y : ℚ) : Prop :=
  x = y ∨ t < padicValRat p (x - y)

theorem close_symm {p : ℕ} {t : ℤ} {x y : ℚ}
    (h : Close p t x y) : Close p t y x := by
  rcases h with h | h
  · exact Or.inl h.symm
  · right
    have heq : y - x = -(x - y) := by ring
    rwa [heq, padicValRat.neg]

theorem close_mono {p : ℕ} {t s : ℤ} {x y : ℚ}
    (hts : t ≤ s) (h : Close p s x y) : Close p t x y := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (hts.trans_lt h)

theorem close_trans {p : ℕ} [Fact p.Prime] {t : ℤ} {x y z : ℚ}
    (hxy : Close p t x y) (hyz : Close p t y z) : Close p t x z := by
  rcases hxy with rfl | hxy
  · exact hyz
  rcases hyz with rfl | hyz
  · exact Or.inr hxy
  by_cases hxz : x = z
  · exact Or.inl hxz
  right
  have heq : (x - y) + (y - z) = x - z := by ring
  have hn : (x - y) + (y - z) ≠ 0 := by rw [heq]; exact sub_ne_zero.mpr hxz
  have hv := padicValRat.min_le_padicValRat_add (p := p) hn
  rw [heq] at hv
  exact (lt_min hxy hyz).trans_le hv

noncomputable def ball (p : ℕ) (U : Finset ℚ) (x : ℚ) (t : ℤ) : Finset ℚ := by
  classical
  exact U.filter (Close p t x)

@[simp] theorem mem_ball {p : ℕ} {U : Finset ℚ} {x y : ℚ} {t : ℤ} :
    y ∈ ball p U x t ↔ y ∈ U ∧ Close p t x y := by
  classical
  simp only [ball, Finset.mem_filter]

theorem ball_subset (p : ℕ) (U : Finset ℚ) (x : ℚ) (t : ℤ) :
    ball p U x t ⊆ U := by
  intro y hy
  exact (mem_ball.mp hy).1

theorem ball_nested_of_le {p : ℕ} [Fact p.Prime] {U : Finset ℚ}
    {x y : ℚ} {t s : ℤ} (hts : t ≤ s)
    (hi : (ball p U x t ∩ ball p U y s).Nonempty) :
    ball p U y s ⊆ ball p U x t := by
  obtain ⟨w, hw⟩ := hi
  obtain ⟨hwx, hwy⟩ := Finset.mem_inter.mp hw
  have hxy : Close p t x y := close_trans (mem_ball.mp hwx).2
    (close_symm (close_mono hts (mem_ball.mp hwy).2))
  intro z hz
  exact mem_ball.mpr ⟨(mem_ball.mp hz).1,
    close_trans hxy (close_mono hts (mem_ball.mp hz).2)⟩

theorem ball_laminar {p : ℕ} [Fact p.Prime] {U : Finset ℚ}
    {x y : ℚ} {t s : ℤ}
    (hi : (ball p U x t ∩ ball p U y s).Nonempty) :
    ball p U x t ⊆ ball p U y s ∨ ball p U y s ⊆ ball p U x t := by
  rcases le_total t s with h | h
  · exact Or.inr (ball_nested_of_le h hi)
  · exact Or.inl (ball_nested_of_le h (by simpa only [Finset.inter_comm] using hi))

/-- A finite list of valuation thresholds suffices; it need not be a complete spectrum. -/
theorem exists_ball_majority_pivot {p : ℕ} [Fact p.Prime]
    (U : Finset ℚ) (T : Finset ℤ) (hne : U.Nonempty) :
    ∃ x ∈ U, ∀ z ∈ U, ∀ t ∈ T,
      U.card < 2 * (ball p U z t).card → x ∈ ball p U z t := by
  classical
  let F := insert U ((U ×ˢ T).image (fun z => ball p U z.1 z.2))
  have hsub : ∀ B ∈ F, B ⊆ U := by
    intro B hB
    rcases Finset.mem_insert.mp hB with rfl | hB
    · exact Finset.Subset.refl _
    · obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hB
      exact ball_subset p U z.1 z.2
  have hlam : ∀ B ∈ F, ∀ D ∈ F, (B ∩ D).Nonempty → B ⊆ D ∨ D ⊆ B := by
    intro B hB D hD hi
    rcases Finset.mem_insert.mp hB with rfl | hB
    · exact Or.inr (hsub D hD)
    rcases Finset.mem_insert.mp hD with rfl | hD
    · exact Or.inl (hsub B (Finset.mem_insert_of_mem hB))
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hD
    exact ball_laminar hi
  obtain ⟨x, hx, hpivot⟩ := LaminarMajority.exists_majority_pivot hsub
    (Finset.mem_insert_self _ _) hne hlam
  refine ⟨x, hx, ?_⟩
  intro z hz t ht hmajor
  apply hpivot _ ?_ hmajor
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨(z,t),
    Finset.mem_product.mpr ⟨hz,ht⟩, rfl⟩)


end QueryBalls
/- End assembled component: QueryArithmeticDraft.lean. -/

/- Begin assembled component: QueryFiberDraft.lean. -/
/-!
# Finite cardinality core of the query-label affine recursion

This draft formalizes the combinatorial recursion in equations (14)--(16) of
`p29/cofactor-tree-route.md`, inspected at SHA256
`57bcd5209e43819faca2feb5396f5e47bb79698d87b44d03aaa543cc67b8f41b`.

The input is a finite relation E whose two coordinate projections are injective,
as holds for any subset of an affine fiber x + lambda * y = t with lambda != 0.
A QueryCertificate records actual restrictions of that relation:
* empty or singleton-coordinate terminals;
* localization into a proper coordinate subset, with no rank increase;
* a disjoint row/column cover, decreasing the corresponding rank in each branch;
* harmless enlargement of rank budgets.

The result is the binomial cardinality bound. No constructor assumes that bound
or a bound on the cardinality of a nonterminal relation. Constructing such a
certificate from the p-adic labels and the subsequent sum/product argument are
not formalized here. The final lemmas supply the ceiling-logarithm arithmetic
for nonempty small children and specialize the bound to rational affine fibers.

Source audit: the relevant Finset image/cardinality, filter, union/disjointness,
and Nat.choose declarations were read in the pinned local Mathlib sources.
The added Nat.clog adjunction/monotonicity and rational cancellation declarations
were also read. All three imports and the Choose.Basic dependency already have
cached oleans. No supplied code, Lean build, cache command, API, or GUI operation was
executed by the drafting subtask. The root task owns compilation and preflight.
-/

namespace QueryFiberCore

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

/-- Restrict a fixed finite relation to a coordinate rectangle. -/
def rectangle (E : Finset (α × β)) (X : Finset α) (Y : Finset β) :
    Finset (α × β) :=
  E.filter (fun z => z.1 ∈ X ∧ z.2 ∈ Y)

@[simp]
theorem mem_rectangle {E : Finset (α × β)} {X : Finset α} {Y : Finset β}
    {z : α × β} :
    z ∈ rectangle E X Y ↔ z ∈ E ∧ z.1 ∈ X ∧ z.2 ∈ Y := by
  simp only [rectangle, Finset.mem_filter]

theorem rectangle_mono {E : Finset (α × β)} {X U : Finset α} {Y V : Finset β}
    (hU : U ⊆ X) (hV : V ⊆ Y) :
    rectangle E U V ⊆ rectangle E X Y := by
  intro z hz
  obtain ⟨hzE, hzU, hzV⟩ := mem_rectangle.mp hz
  exact mem_rectangle.mpr ⟨hzE, hU hzU, hV hzV⟩

theorem rectangle_eq_left {E : Finset (α × β)} {X U : Finset α} {Y : Finset β}
    (hU : U ⊆ X)
    (hcover : ∀ z ∈ rectangle E X Y, z.1 ∈ U) :
    rectangle E X Y = rectangle E U Y := by
  apply Finset.Subset.antisymm
  · intro z hz
    obtain ⟨hzE, _, hzY⟩ := mem_rectangle.mp hz
    exact mem_rectangle.mpr ⟨hzE, hcover z hz, hzY⟩
  · exact rectangle_mono hU (fun _ hz => hz)

theorem rectangle_eq_right {E : Finset (α × β)} {X : Finset α} {Y V : Finset β}
    (hV : V ⊆ Y)
    (hcover : ∀ z ∈ rectangle E X Y, z.2 ∈ V) :
    rectangle E X Y = rectangle E X V := by
  apply Finset.Subset.antisymm
  · intro z hz
    obtain ⟨hzE, hzX, _⟩ := mem_rectangle.mp hz
    exact mem_rectangle.mpr ⟨hzE, hzX, hcover z hz⟩
  · exact rectangle_mono (fun _ hz => hz) hV

/-- A genuine disjoint row/column split has additive relation cardinality. -/
theorem rectangle_card_split {E : Finset (α × β)} {X U : Finset α}
    {Y V : Finset β} (hU : U ⊆ X) (hV : V ⊆ Y)
    (hcover : ∀ z ∈ rectangle E X Y, z.1 ∈ U ∨ z.2 ∈ V)
    (hsep : ∀ z ∈ rectangle E X Y, ¬ (z.1 ∈ U ∧ z.2 ∈ V)) :
    (rectangle E X Y).card =
      (rectangle E U Y).card + (rectangle E X V).card := by
  have heq : rectangle E X Y = rectangle E U Y ∪ rectangle E X V := by
    apply Finset.Subset.antisymm
    · intro z hz
      obtain ⟨hzE, hzX, hzY⟩ := mem_rectangle.mp hz
      rcases hcover z hz with hzU | hzV
      · exact Finset.mem_union.mpr (Or.inl (mem_rectangle.mpr ⟨hzE, hzU, hzY⟩))
      · exact Finset.mem_union.mpr (Or.inr (mem_rectangle.mpr ⟨hzE, hzX, hzV⟩))
    · intro z hz
      rcases Finset.mem_union.mp hz with hzU | hzV
      · exact rectangle_mono hU (fun _ h => h) hzU
      · exact rectangle_mono (fun _ h => h) hV hzV
  have hdisjoint : Disjoint (rectangle E U Y) (rectangle E X V) := by
    apply Finset.disjoint_left.mpr
    intro z hzU hzV
    have hz : z ∈ rectangle E X Y := rectangle_mono hU (fun _ h => h) hzU
    exact hsep z hz ⟨(mem_rectangle.mp hzU).2.1, (mem_rectangle.mp hzV).2.2⟩
  rw [heq, Finset.card_union_of_disjoint hdisjoint]

/-- The rank budget used by the two-coordinate recursion. -/
def capacity (a b : ℕ) : ℕ := (a + b).choose a

theorem one_le_capacity (a b : ℕ) : 1 ≤ capacity a b := by
  exact Nat.succ_le_iff.mpr (Nat.choose_pos (Nat.le_add_right a b))

theorem capacity_mono_left {a a' b : ℕ} (h : a ≤ a') :
    capacity a b ≤ capacity a' b := by
  calc
    capacity a b = (a + b).choose b := Nat.choose_symm_add
    _ ≤ (a' + b).choose b := Nat.choose_le_choose b (Nat.add_le_add_right h b)
    _ = capacity a' b := Nat.choose_symm_add.symm

theorem capacity_mono_right {a b b' : ℕ} (h : b ≤ b') :
    capacity a b ≤ capacity a b' := by
  exact Nat.choose_le_choose a (Nat.add_le_add_left h a)

theorem capacity_step (a b : ℕ) :
    capacity a (b + 1) + capacity (a + 1) b = capacity (a + 1) (b + 1) := by
  simpa only [capacity, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm,
    Nat.add_comm] using (Nat.choose_succ_succ (a + b + 1) a).symm

/-- First-coordinate injectivity bounds a restricted relation by its left domain. -/
theorem rectangle_card_le_left {E : Finset (α × β)} (X : Finset α) (Y : Finset β)
    (hfst : Set.InjOn (fun z : α × β => z.1) (E : Set (α × β))) :
    (rectangle E X Y).card ≤ X.card := by
  have hinj : Set.InjOn (fun z : α × β => z.1)
      (rectangle E X Y : Set (α × β)) := by
    intro z hz w hw heq
    exact hfst (mem_rectangle.mp hz).1 (mem_rectangle.mp hw).1 heq
  calc
    (rectangle E X Y).card =
        ((rectangle E X Y).image (fun z => z.1)).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ X.card := by
      apply Finset.card_le_card
      intro x hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      exact (mem_rectangle.mp hz).2.1

/-- Second-coordinate injectivity bounds a restricted relation by its right domain. -/
theorem rectangle_card_le_right {E : Finset (α × β)} (X : Finset α) (Y : Finset β)
    (hsnd : Set.InjOn (fun z : α × β => z.2) (E : Set (α × β))) :
    (rectangle E X Y).card ≤ Y.card := by
  have hinj : Set.InjOn (fun z : α × β => z.2)
      (rectangle E X Y : Set (α × β)) := by
    intro z hz w hw heq
    exact hsnd (mem_rectangle.mp hz).1 (mem_rectangle.mp hw).1 heq
  calc
    (rectangle E X Y).card =
        ((rectangle E X Y).image (fun z => z.2)).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ Y.card := by
      apply Finset.card_le_card
      intro y hy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
      exact (mem_rectangle.mp hz).2.2

/--
A finite decoding certificate. The strict cardinality fields record genuine
unary/full-separation descent and genuine query-child restrictions. Finiteness is
also enforced by this inductive type. Rank weakening merely pads a valid budget.
-/
inductive QueryCertificate (E : Finset (α × β)) :
    Finset α → Finset β → ℕ → ℕ → Prop
  | empty {X : Finset α} {Y : Finset β} {a b : ℕ}
      (hempty : rectangle E X Y = ∅) : QueryCertificate E X Y a b
  | left_leaf {X : Finset α} {Y : Finset β} {a b : ℕ}
      (hX : X.card ≤ 1) : QueryCertificate E X Y a b
  | right_leaf {X : Finset α} {Y : Finset β} {a b : ℕ}
      (hY : Y.card ≤ 1) : QueryCertificate E X Y a b
  | unary_left {X U : Finset α} {Y : Finset β} {a a' b : ℕ}
      (hU : U ⊆ X) (hsmall : U.card < X.card)
      (hcover : ∀ z ∈ rectangle E X Y, z.1 ∈ U)
      (ha : a' ≤ a) (child : QueryCertificate E U Y a' b) :
      QueryCertificate E X Y a b
  | unary_right {X : Finset α} {Y V : Finset β} {a b b' : ℕ}
      (hV : V ⊆ Y) (hsmall : V.card < Y.card)
      (hcover : ∀ z ∈ rectangle E X Y, z.2 ∈ V)
      (hb : b' ≤ b) (child : QueryCertificate E X V a b') :
      QueryCertificate E X Y a b
  | split {X U : Finset α} {Y V : Finset β} {a b : ℕ}
      (hU : U ⊆ X) (hsmallU : U.card < X.card)
      (hV : V ⊆ Y) (hsmallV : V.card < Y.card)
      (hcover : ∀ z ∈ rectangle E X Y, z.1 ∈ U ∨ z.2 ∈ V)
      (hsep : ∀ z ∈ rectangle E X Y, ¬ (z.1 ∈ U ∧ z.2 ∈ V))
      (row : QueryCertificate E U Y a (b + 1))
      (column : QueryCertificate E X V (a + 1) b) :
      QueryCertificate E X Y (a + 1) (b + 1)
  | weaken {X : Finset α} {Y : Finset β} {a b a' b' : ℕ}
      (ha : a ≤ a') (hb : b ≤ b')
      (child : QueryCertificate E X Y a b) : QueryCertificate E X Y a' b'

theorem QueryCertificate.card_le_capacity {E : Finset (α × β)}
    {X : Finset α} {Y : Finset β} {a b : ℕ}
    (cert : QueryCertificate E X Y a b)
    (hfst : Set.InjOn (fun z : α × β => z.1) (E : Set (α × β)))
    (hsnd : Set.InjOn (fun z : α × β => z.2) (E : Set (α × β))) :
    (rectangle E X Y).card ≤ capacity a b := by
  induction cert with
  | empty hempty =>
    simp only [hempty, Finset.card_empty, Nat.zero_le]
  | left_leaf hX =>
    exact (rectangle_card_le_left _ _ hfst).trans (hX.trans (one_le_capacity _ _))
  | right_leaf hY =>
    exact (rectangle_card_le_right _ _ hsnd).trans (hY.trans (one_le_capacity _ _))
  | unary_left hU _hsmall hcover ha _child ih =>
    rw [rectangle_eq_left hU hcover]
    exact ih.trans (capacity_mono_left ha)
  | unary_right hV _hsmall hcover hb _child ih =>
    rw [rectangle_eq_right hV hcover]
    exact ih.trans (capacity_mono_right hb)
  | split hU _hsmallU hV _hsmallV hcover hsep _row _column ihrow ihcolumn =>
    rw [rectangle_card_split hU hV hcover hsep]
    exact (Nat.add_le_add ihrow ihcolumn).trans (le_of_eq (capacity_step _ _))
  | weaken ha hb _child ih =>
    exact ih.trans ((capacity_mono_left ha).trans (capacity_mono_right hb))

/-- The exact binomial bound proved by the finite query-decoding core. -/
theorem card_le_choose_of_query_certificate {E : Finset (α × β)}
    {X : Finset α} {Y : Finset β} {a b : ℕ}
    (cert : QueryCertificate E X Y a b)
    (hfst : Set.InjOn (fun z : α × β => z.1) (E : Set (α × β)))
    (hsnd : Set.InjOn (fun z : α × β => z.2) (E : Set (α × β))) :
    (rectangle E X Y).card ≤ (a + b).choose a := by
  exact cert.card_le_capacity hfst hsnd

/-- A concrete terminal certificate; no nonemptiness premise is needed. -/
theorem singleton_left_certificate (E : Finset (α × β)) (x : α) (Y : Finset β)
    (a b : ℕ) : QueryCertificate E {x} Y a b := by
  exact QueryCertificate.left_leaf (by simp)

omit [DecidableEq α] in
/-- Coordinate restriction never increases the ceiling-logarithm rank. -/
theorem clog_card_mono (H : ℕ) {U X : Finset α} (hU : U ⊆ X) :
    Nat.clog H U.card ≤ Nat.clog H X.card :=
  Nat.clog_mono_right H (Finset.card_le_card hU)

/-- A positive child at most a factor `H` of its parent loses at least one rank.
The positivity premise is essential: `u = 0`, `n = 1` would fail. -/
theorem clog_rank_drop_of_mul_le {H u n : ℕ}
    (hH : 1 < H) (hu : 0 < u) (hsmall : H * u ≤ n) :
    Nat.clog H u + 1 ≤ Nat.clog H n := by
  have hHu : H ≤ H * u := by
    simpa only [Nat.mul_one] using
      Nat.mul_le_mul_left H (Nat.succ_le_iff.mpr hu)
  have hn : 1 < n := hH.trans_le (hHu.trans hsmall)
  cases hlog : Nat.clog H n with
  | zero =>
    have hpos := Nat.clog_pos hH hn
    rw [hlog] at hpos
    exact False.elim (Nat.lt_irrefl 0 hpos)
  | succ r =>
    have hp : n ≤ H * H ^ r := by
      simpa only [hlog, Nat.pow_succ, Nat.mul_comm] using Nat.le_pow_clog hH n
    have huPow : u ≤ H ^ r :=
      Nat.le_of_mul_le_mul_left (hsmall.trans hp) (Nat.zero_lt_of_lt hH)
    exact Nat.add_le_add_right (Nat.clog_le_of_le_pow huPow) 1

omit [DecidableEq α] in
/-- The strict threshold used for the nonempty query children. -/
theorem clog_card_rank_drop {H : ℕ} {U X : Finset α}
    (hH : 1 < H) (hU : U.Nonempty) (hsmall : H * U.card < X.card) :
    Nat.clog H U.card + 1 ≤ Nat.clog H X.card :=
  clog_rank_drop_of_mul_le hH hU.card_pos hsmall.le

/-- Rational affine fibers automatically have injective coordinate projections.
The decoding certificate is still an explicit, substantive hypothesis. -/
theorem affine_card_le_choose_of_query_certificate
    {E : Finset (ℚ × ℚ)} {X Y : Finset ℚ} {a b : ℕ} {lam t : ℚ}
    (hlam : lam ≠ 0) (hfiber : ∀ z ∈ E, z.1 + lam * z.2 = t)
    (cert : QueryCertificate E X Y a b) :
    (rectangle E X Y).card ≤ (a + b).choose a := by
  apply card_le_choose_of_query_certificate cert
  · intro z hz w hw heq
    change z.1 = w.1 at heq
    have h := (hfiber z hz).trans (hfiber w hw).symm
    rw [heq] at h
    exact Prod.ext heq (mul_left_cancel₀ hlam (add_left_cancel h))
  · intro z hz w hw heq
    change z.2 = w.2 at heq
    have h := (hfiber z hz).trans (hfiber w hw).symm
    rw [heq] at h
    exact Prod.ext (add_right_cancel h) heq


end QueryFiberCore
/- End assembled component: QueryFiberDraft.lean. -/

/- Begin assembled component: QueryCenterDraft.lean. -/
/- The perturbed center used by the finite query construction.
This file does not construct recursive labels or prove a sum-product bound. -/
namespace QueryCenter

/-- A positive integer strictly above every nonzero pair-difference valuation.
The statement also allows an empty or singleton set. -/
theorem exists_positive_pair_bound (p : ℕ) (U : Finset ℚ) :
    ∃ L : ℤ, 0 < L ∧
      ∀ x ∈ U, ∀ y ∈ U, x ≠ y → padicValRat p (x - y) < L := by
  classical
  let D : Finset (ℚ × ℚ) := (U ×ˢ U).filter (fun z => z.1 ≠ z.2)
  let V : Finset ℤ := insert 0 (D.image (fun z => padicValRat p (z.1 - z.2)))
  have hzero : (0 : ℤ) ∈ V := Finset.mem_insert_self _ _
  obtain ⟨m, _, hmax⟩ :=
    Finset.exists_max_image V (fun z : ℤ => z) ⟨0, hzero⟩
  refine ⟨m + 1, ?_, ?_⟩
  · have hnonneg : 0 ≤ m := hmax 0 hzero
    omega
  · intro x hx y hy hxy
    have hD : (x, y) ∈ D :=
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hxy⟩
    have hV : padicValRat p (x - y) ∈ V :=
      Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨(x, y), hD, rfl⟩)
    have hle : padicValRat p (x - y) ≤ m := hmax _ hV
    omega

/-- Perturb any chosen member of a finite set of nonzero p-units.
Membership of x0 supplies nonemptiness. Neither positivity of the rationals nor
a second member of U is assumed. All queried differences are explicitly nonzero. -/
theorem exists_perturbed_center {p : ℕ} [Fact p.Prime]
    (U : Finset ℚ) (x0 : ℚ) (hx0 : x0 ∈ U)
    (hunit : ∀ x ∈ U, x ≠ 0 ∧ padicValRat p x = 0) :
    ∃ L : ℤ, 0 < L ∧
      (∀ x ∈ U, ∀ y ∈ U, x ≠ y → padicValRat p (x - y) < L) ∧
      ∃ alpha : ℚ, alpha = x0 + (p : ℚ) ^ L ∧
        alpha ≠ 0 ∧ padicValRat p alpha = 0 ∧ alpha ∉ U ∧
        x0 - alpha ≠ 0 ∧ padicValRat p (x0 - alpha) = L ∧
        (∀ x ∈ U, x ≠ x0 →
          x - alpha ≠ 0 ∧
          padicValRat p (x - alpha) = padicValRat p (x - x0) ∧
          padicValRat p (x - x0) < L) := by
  obtain ⟨L, hL, hbound⟩ := exists_positive_pair_bound p U
  have hx0ne : x0 ≠ 0 := (hunit x0 hx0).1
  have hx0val : padicValRat p x0 = 0 := (hunit x0 hx0).2
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hpow : (p : ℚ) ^ L ≠ 0 := zpow_ne_zero L hp0
  have hpowval : padicValRat p ((p : ℚ) ^ L) = L := by
    rw [padicValRat.zpow, padicValRat.self (Fact.out : p.Prime).one_lt, mul_one]
  let alpha : ℚ := x0 + (p : ℚ) ^ L
  have halpha_ne : alpha ≠ 0 := by
    apply QueryArithmetic.add_ne_zero_of_val_ne (p := p)
    rw [hx0val, hpowval]
    exact ne_of_lt hL
  have halpha_val : padicValRat p alpha = 0 := by
    change padicValRat p (x0 + (p : ℚ) ^ L) = 0
    rw [padicValRat.add_eq_of_lt halpha_ne hx0ne hpow
      (by rw [hx0val, hpowval]; exact hL), hx0val]
  have hpivotdiff : x0 - alpha = -((p : ℚ) ^ L) := by
    dsimp only [alpha]
    ring
  have hpivot_ne : x0 - alpha ≠ 0 := by
    rw [hpivotdiff]
    exact neg_ne_zero.mpr hpow
  have hpivot_val : padicValRat p (x0 - alpha) = L := by
    rw [hpivotdiff, padicValRat.neg, hpowval]
  have hother : ∀ x ∈ U, x ≠ x0 →
      x - alpha ≠ 0 ∧
      padicValRat p (x - alpha) = padicValRat p (x - x0) ∧
      padicValRat p (x - x0) < L := by
    intro x hx hxx0
    have hdiff_ne : x - x0 ≠ 0 := sub_ne_zero.mpr hxx0
    have hsmall : padicValRat p (x - x0) < L := hbound x hx x0 hx0 hxx0
    have heq : x - alpha = (x - x0) + -((p : ℚ) ^ L) := by
      dsimp only [alpha]
      ring
    have hnegval : padicValRat p (-((p : ℚ) ^ L)) = L := by
      rw [padicValRat.neg, hpowval]
    have hquery_ne : x - alpha ≠ 0 := by
      rw [heq]
      apply QueryArithmetic.add_ne_zero_of_val_ne (p := p)
      rw [hnegval]
      exact ne_of_lt hsmall
    have hquery_val : padicValRat p (x - alpha) = padicValRat p (x - x0) := by
      rw [heq]
      exact padicValRat.add_eq_of_lt (by rwa [← heq]) hdiff_ne
        (neg_ne_zero.mpr hpow) (by rw [hnegval]; exact hsmall)
    exact ⟨hquery_ne, hquery_val, hsmall⟩
  have halpha_out : alpha ∉ U := by
    intro halpha_mem
    by_cases heq : alpha = x0
    · exact hpivot_ne (sub_eq_zero.mpr heq.symm)
    · exact (hother alpha halpha_mem heq).1 (sub_self alpha)
  exact ⟨L, hL, hbound, alpha, rfl, halpha_ne, halpha_val, halpha_out,
    hpivot_ne, hpivot_val, hother⟩


end QueryCenter
/- End assembled component: QueryCenterDraft.lean. -/

/- Begin assembled component: QueryLabelDraft.lean. -/
/-!
# Recursive labels from actual query rounds

This draft formalizes the label-assignment part of the query construction in
`cofactor-tree-route.md`, read at SHA256
`783f4ba9105bb1fe39ecce79b3bff9df360ff0fce65a52aabc90886a18f29b89`.
The imported local drafts were read at SHA256
`d69703cc5dec36cd3e18490104767a675e38855b4216cfd8b3b184b4035385b0`
and `967e49066da29fe8abb054a3a9afa5284e33fc845d876de68a2cbec487a9703a`.
The root task supplies their local oleans.

A QueryRound exposes actual valuation answers, their raw fibers, and routed
recursive cells. A large raw sphere may be split into several cells; equal-answer
points in distinct cells have their common answer as their difference valuation.
Every routed cell has at most half the parent's cardinality. No label-coverage,
label-cardinality, affine-fiber, or sum-product conclusion is a round field.

LabelTree records recursive rounds and the exact union of the own answer, the
shared answers of large raw fibers, and the descendant labels. The shared-answer
count is proved from disjoint fibers rather than assumed. Geometric existence of
QueryRound and construction of the affine QueryCertificate are separate tasks.

Audit: all new source below and the used local Finset fiber-cardinality, sum,
union/insert cardinality, Nat.clog, and unequal-valuation addition declarations
were read. The extra Mathlib import has a cached olean. No Lean/build/cache,
network/API, or GUI operation was run by this drafting subtask.
-/

namespace QueryLabelsCore

open scoped BigOperators
open QueryFiberCore

def answer (p : ℕ) (center x : ℚ) : ℤ := padicValRat p (x - center)

def rawFiber (p : ℕ) (U : Finset ℚ) (center : ℚ) (e : ℤ) : Finset ℚ :=
  U.filter (fun x => answer p center x = e)

@[simp] theorem mem_rawFiber {p : ℕ} {U : Finset ℚ} {center x : ℚ} {e : ℤ} :
    x ∈ rawFiber p U center e ↔ x ∈ U ∧ answer p center x = e := by
  simp only [rawFiber, Finset.mem_filter]

def sharedAnswers (p H : ℕ) (U : Finset ℚ) (center : ℚ) : Finset ℤ :=
  (U.image (answer p center)).filter
    (fun e => U.card ≤ H * (rawFiber p U center e).card)

/-- At most `H` nonempty fibers can each carry at least a fraction `1/H`.
The integer formulation also handles `H = 0` and `H = 1`. -/
theorem sharedAnswers_card_le (p H : ℕ) {U : Finset ℚ} (center : ℚ)
    (hU : U.Nonempty) : (sharedAnswers p H U center).card ≤ H := by
  have hsum : (∑ e ∈ sharedAnswers p H U center,
      (rawFiber p U center e).card) ≤ U.card := by
    simp only [rawFiber]
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have hmul : (sharedAnswers p H U center).card * U.card ≤ H * U.card := by
    calc
      (sharedAnswers p H U center).card * U.card =
          ∑ _e ∈ sharedAnswers p H U center, U.card := by simp
      _ ≤ ∑ e ∈ sharedAnswers p H U center,
          H * (rawFiber p U center e).card := by
        apply Finset.sum_le_sum
        intro e he
        exact (Finset.mem_filter.mp he).2
      _ = H * ∑ e ∈ sharedAnswers p H U center,
          (rawFiber p U center e).card := (Finset.mul_sum _ _ _).symm
      _ ≤ H * U.card := Nat.mul_le_mul_left H hsum
  exact Nat.le_of_mul_le_mul_right hmul hU.card_pos

/-- One complete query round, including any full-separation split of a large
raw sphere. The routing map is a genuine finite partition on `U`. -/
structure QueryRound (p : ℕ) (U : Finset ℚ) where
  center : ℚ
  center_out : center ∉ U
  cell : ℚ → Finset ℚ
  self_mem : ∀ x ∈ U, x ∈ cell x
  cell_subset : ∀ x ∈ U, cell x ⊆ U
  cell_eq_of_mem : ∀ x ∈ U, ∀ y ∈ cell x, cell y = cell x
  half : ∀ x ∈ U, 2 * (cell x).card ≤ U.card
  answer_eq : ∀ x ∈ U, ∀ y ∈ cell x, answer p center y = answer p center x
  full_separation : ∀ x ∈ U, ∀ y ∈ U, cell x ≠ cell y →
    answer p center x = answer p center y →
    padicValRat p (x - y) = answer p center x
  small_raw_cell : ∀ x ∈ U,
    2 * (rawFiber p U center (answer p center x)).card ≤ U.card →
    cell x = rawFiber p U center (answer p center x)

theorem QueryRound.cell_nonempty {p : ℕ} {U : Finset ℚ}
    (D : QueryRound p U) {x : ℚ} (hx : x ∈ U) : (D.cell x).Nonempty :=
  ⟨x, D.self_mem x hx⟩

theorem QueryRound.cell_card_lt {p : ℕ} {U : Finset ℚ}
    (D : QueryRound p U) {x : ℚ} (hx : x ∈ U) : (D.cell x).card < U.card := by
  have hp := (D.cell_nonempty hx).card_pos
  have hh := D.half x hx
  omega

theorem QueryRound.cell_subset_raw {p : ℕ} {U : Finset ℚ}
    (D : QueryRound p U) {x : ℚ} (hx : x ∈ U) :
    D.cell x ⊆ rawFiber p U D.center (answer p D.center x) := by
  intro y hy
  exact mem_rawFiber.mpr ⟨D.cell_subset x hx hy, D.answer_eq x hx y hy⟩

theorem QueryRound.center_ne {p : ℕ} {U : Finset ℚ}
    (D : QueryRound p U) {x : ℚ} (hx : x ∈ U) : x ≠ D.center := by
  intro h
  exact D.center_out (h ▸ hx)

/-- Unequal actual query answers separate at one of those answers. -/
theorem distance_eq_one_answer {p : ℕ} [Fact p.Prime] {center x y : ℚ}
    (hx : x ≠ center) (hy : y ≠ center)
    (hne : answer p center x ≠ answer p center y) :
    padicValRat p (x - y) = answer p center x ∨
      padicValRat p (x - y) = answer p center y := by
  have hxy : x ≠ y := by
    intro h
    exact hne (congrArg (answer p center) h)
  have heq : (x - center) + -(y - center) = x - y := by ring
  have hval := padicValRat.add_eq_min (p := p) (q := x - center) (r := -(y - center))
    (by rw [heq]; exact sub_ne_zero.mpr hxy)
    (sub_ne_zero.mpr hx) (neg_ne_zero.mpr (sub_ne_zero.mpr hy))
    (by simpa only [answer, padicValRat.neg] using hne)
  rw [heq, padicValRat.neg] at hval
  change padicValRat p (x - y) = min (answer p center x) (answer p center y) at hval
  rcases le_total (answer p center x) (answer p center y) with h | h
  · exact Or.inl (hval.trans (min_eq_left h))
  · exact Or.inr (hval.trans (min_eq_right h))

/-- An exact recursive assignment. Singleton and empty sets receive no labels. -/
inductive LabelTree (p H : ℕ) : Finset ℚ → (ℚ → Finset ℤ) → Prop
  | leaf {U : Finset ℚ} {L : ℚ → Finset ℤ}
      (hcard : U.card ≤ 1) (hlabels : ∀ x ∈ U, L x = ∅) : LabelTree p H U L
  | query {U : Finset ℚ} {L : ℚ → Finset ℤ}
      (hcard : 1 < U.card) (D : QueryRound p U)
      (childLabels : Finset ℚ → ℚ → Finset ℤ)
      (children : ∀ x ∈ U, LabelTree p H (D.cell x) (childLabels (D.cell x)))
      (hlabels : ∀ x ∈ U, L x =
        insert (answer p D.center x) (sharedAnswers p H U D.center) ∪
          childLabels (D.cell x) x) : LabelTree p H U L

/-- The own answers and full-separation labels give union coverage at the
first distinct routed cells; common-cell points use the recursive assignment. -/
theorem LabelTree.union_coverage {p H : ℕ} [Fact p.Prime]
    {U : Finset ℚ} {L : ℚ → Finset ℤ} (T : LabelTree p H U L) :
    ∀ x ∈ U, ∀ y ∈ U, x ≠ y →
      padicValRat p (x - y) ∈ L x ∨ padicValRat p (x - y) ∈ L y := by
  induction T with
  | leaf hcard _hlabels =>
    intro x hx y hy hxy
    have hEq : x = y := (Finset.card_le_one.mp hcard) x hx y hy
    exact False.elim (hxy hEq)
  | @query U L _hcard D childLabels _children hlabels ih =>
    intro x hx y hy hxy
    have hownx : answer p D.center x ∈ L x := by
      rw [hlabels x hx]
      exact Finset.mem_union_left _ (Finset.mem_insert_self _ _)
    have howny : answer p D.center y ∈ L y := by
      rw [hlabels y hy]
      exact Finset.mem_union_left _ (Finset.mem_insert_self _ _)
    by_cases hc : D.cell x = D.cell y
    · have hycell : y ∈ D.cell x := by
        rw [hc]
        exact D.self_mem y hy
      rcases ih x hx x (D.self_mem x hx) y hycell hxy with hl | hr
      · left
        rw [hlabels x hx]
        exact Finset.mem_union_right _ hl
      · right
        rw [hlabels y hy]
        apply Finset.mem_union_right
        simpa only [hc] using hr
    · by_cases he : answer p D.center x = answer p D.center y
      · left
        simpa only [D.full_separation x hx y hy hc he] using hownx
      · rcases distance_eq_one_answer (D.center_ne hx) (D.center_ne hy) he with hv | hv
        · left
          simpa only [hv] using hownx
        · right
          simpa only [hv] using howny

/-- Each halving round contributes at most `H+1` labels. No depth or final
label-cardinality estimate is a constructor hypothesis. -/
theorem LabelTree.card_le {p H : ℕ} {U : Finset ℚ} {L : ℚ → Finset ℤ}
    (T : LabelTree p H U L) :
    ∀ x ∈ U, (L x).card ≤ (H + 1) * Nat.clog 2 U.card := by
  induction T with
  | leaf _hcard hlabels =>
    intro x hx
    rw [hlabels x hx, Finset.card_empty]
    exact Nat.zero_le _
  | @query U L _hcard D childLabels _children hlabels ih =>
    intro x hx
    have hshared := sharedAnswers_card_le p H D.center ⟨x, hx⟩
    have hi := ih x hx x (D.self_mem x hx)
    have hdrop : Nat.clog 2 (D.cell x).card + 1 ≤ Nat.clog 2 U.card :=
      clog_rank_drop_of_mul_le (by decide) (D.cell_nonempty hx).card_pos (D.half x hx)
    have hlocal : (insert (answer p D.center x)
        (sharedAnswers p H U D.center)).card ≤ H + 1 :=
      (Finset.card_insert_le _ _).trans (Nat.add_le_add_right hshared 1)
    calc
      (L x).card ≤ H + 1 + (H + 1) * Nat.clog 2 (D.cell x).card := by
        rw [hlabels x hx]
        exact (Finset.card_union_le _ _).trans (Nat.add_le_add hlocal hi)
      _ = (H + 1) * (Nat.clog 2 (D.cell x).card + 1) := by
        rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      _ ≤ (H + 1) * Nat.clog 2 U.card := Nat.mul_le_mul_left (H + 1) hdrop

/-- The paper's safe `H+2` budget follows from the sharper round count. -/
theorem LabelTree.card_le_paper {p H : ℕ} {U : Finset ℚ} {L : ℚ → Finset ℤ}
    (T : LabelTree p H U L) {x : ℚ} (hx : x ∈ U) :
    (L x).card ≤ (H + 2) * Nat.clog 2 U.card :=
  (T.card_le x hx).trans (Nat.mul_le_mul_right _ (by omega))

/-- Actual local rounds on nontrivial subsets suffice to construct the whole
recursive label assignment. Strict cell-cardinality descent supplies termination.
No recursive label tree is assumed in the input. -/
theorem exists_labelTree_of_rounds (p H : ℕ) (U₀ : Finset ℚ)
    (hround : ∀ U ⊆ U₀, 1 < U.card → Nonempty (QueryRound p U)) :
    ∃ L, LabelTree p H U₀ L := by
  classical
  have haux : ∀ n : ℕ, ∀ U : Finset ℚ, U ⊆ U₀ → U.card = n →
      ∃ L, LabelTree p H U L := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro U hU hn
      by_cases hcard : U.card ≤ 1
      · exact ⟨fun _ => ∅, LabelTree.leaf hcard (by intro x hx; rfl)⟩
      · have hnontrivial : 1 < U.card := Nat.lt_of_not_ge hcard
        let D : QueryRound p U := Classical.choice (hround U hU hnontrivial)
        have hchild : ∀ C : Finset ℚ, C ⊆ U → C.card < U.card →
            ∃ L, LabelTree p H C L := by
          intro C hCU hlt
          exact ih C.card (by simpa only [hn] using hlt) C (hCU.trans hU) rfl
        let childLabels : Finset ℚ → ℚ → Finset ℤ := fun C =>
          if hC : C ⊆ U ∧ C.card < U.card then
            Classical.choose (hchild C hC.1 hC.2)
          else fun _ => ∅
        have children : ∀ x ∈ U,
            LabelTree p H (D.cell x) (childLabels (D.cell x)) := by
          intro x hx
          have hC : D.cell x ⊆ U ∧ (D.cell x).card < U.card :=
            ⟨D.cell_subset x hx, D.cell_card_lt hx⟩
          simpa only [childLabels, dif_pos hC] using
            Classical.choose_spec (hchild (D.cell x) hC.1 hC.2)
        let L : ℚ → Finset ℤ := fun x =>
          insert (answer p D.center x) (sharedAnswers p H U D.center) ∪
            childLabels (D.cell x) x
        exact ⟨L, LabelTree.query hnontrivial D childLabels children
          (by intro x hx; rfl)⟩
  exact haux U₀.card U₀ (Finset.Subset.refl _) rfl

/-- Geometric round existence yields both advertised label conclusions.
The hypotheses concern only finite query partitions of subsets of `U`. -/
theorem exists_bounded_cover_of_rounds (p H : ℕ) [Fact p.Prime] (U : Finset ℚ)
    (hround : ∀ V ⊆ U, 1 < V.card → Nonempty (QueryRound p V)) :
    ∃ L : ℚ → Finset ℤ, LabelTree p H U L ∧
      (∀ x ∈ U, (L x).card ≤ (H + 1) * Nat.clog 2 U.card) ∧
      (∀ x ∈ U, ∀ y ∈ U, x ≠ y →
        padicValRat p (x - y) ∈ L x ∨ padicValRat p (x - y) ∈ L y) := by
  obtain ⟨L, hL⟩ := exists_labelTree_of_rounds p H U hround
  exact ⟨L, hL, hL.card_le, hL.union_coverage⟩


end QueryLabelsCore
/- End assembled component: QueryLabelDraft.lean. -/

/- Begin assembled component: QueryGeometryDraft.lean. -/
/- Actual residue cells used by one recursive query round. -/
namespace QueryGeometry

open QueryBalls

abbrev answer (p : ℕ) (alpha x : ℚ) : ℤ := padicValRat p (x - alpha)

noncomputable def raw (p : ℕ) (U : Finset ℚ) (alpha : ℚ) (e : ℤ) : Finset ℚ :=
  U.filter (fun x => answer p alpha x = e)

@[simp] theorem mem_raw {p : ℕ} {U : Finset ℚ} {alpha x : ℚ} {e : ℤ} :
    x ∈ raw p U alpha e ↔ x ∈ U ∧ answer p alpha x = e := by
  simp only [raw, Finset.mem_filter]

theorem raw_subset (p : ℕ) (U : Finset ℚ) (alpha : ℚ) (e : ℤ) :
    raw p U alpha e ⊆ U := by
  intro x hx
  exact (mem_raw.mp hx).1

theorem close_preserves_answer {p : ℕ} [Fact p.Prime]
    {alpha x y : ℚ} (hx : x ≠ alpha)
    (hclose : Close p (answer p alpha x) x y) :
    y ≠ alpha ∧ answer p alpha y = answer p alpha x := by
  by_cases hxy : x = y
  · subst y
    exact ⟨hx, rfl⟩
  have hvxy : answer p alpha x < padicValRat p (x - y) := hclose.resolve_left hxy
  have heq : (x - alpha) + -(x - y) = y - alpha := by ring
  have hn : (x - alpha) + -(x - y) ≠ 0 := by
    apply QueryArithmetic.add_ne_zero_of_val_ne (p := p)
    rw [padicValRat.neg]
    exact ne_of_lt hvxy
  have hv := padicValRat.add_eq_of_lt (p := p) hn (sub_ne_zero.mpr hx)
    (neg_ne_zero.mpr (sub_ne_zero.mpr hxy))
    (by rwa [padicValRat.neg])
  rw [heq] at hn hv
  exact ⟨sub_ne_zero.mp hn, hv⟩

theorem ball_subset_raw {p : ℕ} [Fact p.Prime] {U : Finset ℚ}
    {alpha x : ℚ} (hout : alpha ∉ U) (hx : x ∈ U) :
    ball p U x (answer p alpha x) ⊆ raw p U alpha (answer p alpha x) := by
  intro y hy
  have hxne : x ≠ alpha := fun h => hout (h ▸ hx)
  exact mem_raw.mpr ⟨(mem_ball.mp hy).1,
    (close_preserves_answer hxne (mem_ball.mp hy).2).2⟩

noncomputable def cell (p : ℕ) (U : Finset ℚ) (alpha x : ℚ) : Finset ℚ :=
  if 2 * (raw p U alpha (answer p alpha x)).card ≤ U.card
  then raw p U alpha (answer p alpha x)
  else ball p U x (answer p alpha x)

theorem cell_self {p : ℕ} {U : Finset ℚ} {alpha x : ℚ} (hx : x ∈ U) :
    x ∈ cell p U alpha x := by
  classical
  unfold cell
  split_ifs
  · exact mem_raw.mpr ⟨hx, rfl⟩
  · exact mem_ball.mpr ⟨hx, Or.inl rfl⟩

theorem cell_subset (p : ℕ) (U : Finset ℚ) (alpha x : ℚ) : cell p U alpha x ⊆ U := by
  classical
  unfold cell
  split_ifs
  · exact raw_subset p U alpha _
  · exact ball_subset p U x _

theorem cell_subset_raw {p : ℕ} [Fact p.Prime] {U : Finset ℚ} {alpha x : ℚ}
    (hout : alpha ∉ U) (hx : x ∈ U) :
    cell p U alpha x ⊆ raw p U alpha (answer p alpha x) := by
  classical
  unfold cell
  split_ifs
  · exact Finset.Subset.refl _
  · exact ball_subset_raw hout hx

theorem cell_answer {p : ℕ} [Fact p.Prime] {U : Finset ℚ} {alpha x y : ℚ}
    (hout : alpha ∉ U) (hx : x ∈ U) (hy : y ∈ cell p U alpha x) :
    answer p alpha y = answer p alpha x :=
  (mem_raw.mp (cell_subset_raw hout hx hy)).2

theorem cell_eq_of_mem {p : ℕ} [Fact p.Prime] {U : Finset ℚ} {alpha x y : ℚ}
    (hout : alpha ∉ U) (hx : x ∈ U) (hy : y ∈ cell p U alpha x) :
    cell p U alpha y = cell p U alpha x := by
  classical
  have hyU := cell_subset p U alpha x hy
  have he := cell_answer hout hx hy
  unfold cell
  rw [he]
  split_ifs with h
  · rfl
  · have hyball : y ∈ ball p U x (answer p alpha x) := by
      simpa only [cell, if_neg h] using hy
    have hyself : y ∈ ball p U y (answer p alpha x) :=
      mem_ball.mpr ⟨hyU, Or.inl rfl⟩
    have hi : (ball p U x (answer p alpha x) ∩
        ball p U y (answer p alpha x)).Nonempty :=
      ⟨y, Finset.mem_inter.mpr ⟨hyball, hyself⟩⟩
    exact Finset.Subset.antisymm (ball_nested_of_le (le_refl _) hi)
      (ball_nested_of_le (le_refl _) (by simpa only [Finset.inter_comm] using hi))

theorem same_answer_separation {p : ℕ} [Fact p.Prime] {U : Finset ℚ}
    {alpha x y : ℚ} (hout : alpha ∉ U) (hx : x ∈ U) (hy : y ∈ U)
    (he : answer p alpha x = answer p alpha y)
    (hcell : cell p U alpha x ≠ cell p U alpha y) :
    padicValRat p (x - y) = answer p alpha x := by
  classical
  have hxy : x ≠ y := by
    intro h
    exact hcell (congrArg (cell p U alpha) h)
  have hynot : y ∉ cell p U alpha x := by
    intro h
    exact hcell (cell_eq_of_mem hout hx h).symm
  have hnotclose : ¬Close p (answer p alpha x) x y := by
    intro hclose
    apply hynot
    unfold cell
    split_ifs
    · exact mem_raw.mpr ⟨hy, he.symm⟩
    · exact mem_ball.mpr ⟨hy, hclose⟩
  have hupper : padicValRat p (x - y) ≤ answer p alpha x := by
    exact le_of_not_gt (fun h => hnotclose (Or.inr h))
  have hd : (x - alpha) + -(y - alpha) = x - y := by ring
  have hn : (x - alpha) + -(y - alpha) ≠ 0 := by
    rw [hd]
    exact sub_ne_zero.mpr hxy
  have hmin := padicValRat.min_le_padicValRat_add (p := p) hn
  rw [hd, padicValRat.neg] at hmin
  change min (answer p alpha x) (answer p alpha y) ≤ padicValRat p (x - y) at hmin
  rw [← he, min_self] at hmin
  exact le_antisymm hupper hmin

theorem exists_halving_center {p : ℕ} [Fact p.Prime]
    (U : Finset ℚ) (hU : 1 < U.card)
    (hunit : ∀ x ∈ U, x ≠ 0 ∧ padicValRat p x = 0) :
    ∃ alpha : ℚ, alpha ∉ U ∧ alpha ≠ 0 ∧ padicValRat p alpha = 0 ∧
      ∀ x ∈ U, 2 * (ball p U x (answer p alpha x)).card ≤ U.card := by
  classical
  let T : Finset ℤ := ((U ×ˢ U).filter (fun z => z.1 ≠ z.2)).image
    (fun z => padicValRat p (z.1 - z.2))
  have hne : U.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x0, hx0, hpivot⟩ := exists_ball_majority_pivot (p := p) U T hne
  obtain ⟨L, hL, hbound, alpha, halpha, ha0, hav, haout, hx0a, hx0v, hother⟩ :=
    QueryCenter.exists_perturbed_center U x0 hx0 hunit
  refine ⟨alpha, haout, ha0, hav, ?_⟩
  intro x hx
  by_cases hxx0 : x = x0
  · subst x
    have hsubset : ball p U x0 (answer p alpha x0) ⊆ ({x0} : Finset ℚ) := by
      intro y hy
      obtain ⟨hyU, hclose⟩ := mem_ball.mp hy
      by_cases hx0y : x0 = y
      · exact Finset.mem_singleton.mpr hx0y.symm
      have hv := hclose.resolve_left hx0y
      change padicValRat p (x0 - alpha) < padicValRat p (x0 - y) at hv
      rw [hx0v] at hv
      have hbelow := hbound x0 hx0 y hyU hx0y
      omega
    have hc : (ball p U x0 (answer p alpha x0)).card ≤ 1 := by
      simpa only [Finset.card_singleton] using Finset.card_le_card hsubset
    omega
  · have hans : answer p alpha x = padicValRat p (x - x0) := (hother x hx hxx0).2.1
    have hT : answer p alpha x ∈ T := by
      rw [hans]
      exact Finset.mem_image.mpr ⟨(x, x0),
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hx0⟩, hxx0⟩, rfl⟩
    have hnot : x0 ∉ ball p U x (answer p alpha x) := by
      intro hmem
      have hv := (mem_ball.mp hmem).2.resolve_left hxx0
      rw [hans] at hv
      exact lt_irrefl _ hv
    exact le_of_not_gt (fun hmajor => hnot (hpivot x hx _ hT hmajor))

theorem cell_half {p : ℕ} {U : Finset ℚ} {alpha : ℚ}
    (hball : ∀ x ∈ U, 2 * (ball p U x (answer p alpha x)).card ≤ U.card)
    {x : ℚ} (hx : x ∈ U) : 2 * (cell p U alpha x).card ≤ U.card := by
  classical
  unfold cell
  split_ifs with h
  · exact h
  · exact hball x hx

open QueryLabelsCore (QueryRound LabelTree)

/-- The finite-ball pivot supplies every field of a real query round. -/
theorem exists_queryRound {p : ℕ} [Fact p.Prime]
    (U : Finset ℚ) (hU : 1 < U.card)
    (hunit : ∀ x ∈ U, x ≠ 0 ∧ padicValRat p x = 0) :
    Nonempty (QueryRound p U) := by
  classical
  obtain ⟨alpha, hout, _hzero, _hval, hball⟩ := exists_halving_center U hU hunit
  exact ⟨{
    center := alpha
    center_out := hout
    cell := cell p U alpha
    self_mem := fun _ hx => cell_self hx
    cell_subset := fun x _ => cell_subset p U alpha x
    cell_eq_of_mem := fun _ hx _ hy => cell_eq_of_mem hout hx hy
    half := fun _ hx => cell_half hball hx
    answer_eq := fun _ hx _ hy => cell_answer hout hx hy
    full_separation := fun _ hx _ hy hc he => same_answer_separation hout hx hy he hc
    small_raw_cell := by
      intro x _hx hs
      change cell p U alpha x = raw p U alpha (answer p alpha x)
      unfold cell
      exact if_pos hs
  }⟩

/-- Every finite rational p-unit set has the actual recursive labels and their
logarithmic budget; local round existence is now proved, not a hypothesis. -/
theorem exists_bounded_cover {p : ℕ} [Fact p.Prime]
    (H : ℕ) (U : Finset ℚ)
    (hunit : ∀ x ∈ U, x ≠ 0 ∧ padicValRat p x = 0) :
    ∃ L : ℚ → Finset ℤ, LabelTree p H U L ∧
      (∀ x ∈ U, (L x).card ≤ (H + 1) * Nat.clog 2 U.card) ∧
      (∀ x ∈ U, ∀ y ∈ U, x ≠ y →
        padicValRat p (x - y) ∈ L x ∨ padicValRat p (x - y) ∈ L y) := by
  apply QueryLabelsCore.exists_bounded_cover_of_rounds p H U
  intro V hVU hV
  exact exists_queryRound V hV (fun x hx => hunit x (hVU hx))


end QueryGeometry
/- End assembled component: QueryGeometryDraft.lean. -/

/- Begin assembled component: QueryAffineDraft.lean. -/
/-!
# Affine decoding certificates from recursive query labels

The local imports and the complete query-label/affine recursion in
`cofactor-tree-route.md` were reread before drafting. This file constructs the
certificate; it does not assume its existence or its cardinality conclusion.
The input label trees retain their actual query rounds and exact label unions.
Only the current rectangle must satisfy Good, so descendants inherit goodness
from the inclusion of child labels in their parent labels.
The LabelTree source was compiled by the root at SHA256
`5c33b457cb01625940c45f122f6bcc91a535f35b3dc15f4dd4a7586318cf87cc`.
The geometric round construction and its center dependency were read completely
at SHA256 `1ca5e9383334c4cd5a29902fa91b5124f40e11307ae8a688bfb68c477d0e1c95`
and `17097c426df1cc9f36acf9cda207385302848225d7afe5acd994624833931b1e`.

No Lean/build/cache, API/network, or GUI action was performed by this subtask.
The root task owns compilation. This is the finite common-prime affine core,
not the unrestricted integer sum-product conjecture.
-/

namespace QueryAffineCore

open QueryLabelsCore
open QueryFiberCore
open QueryArithmetic

variable {p H : ℕ}

theorem own_mem {X : Finset ℚ} {L : ℚ → Finset ℤ}
    (D : QueryRound p X) (C : Finset ℚ → ℚ → Finset ℤ)
    (hL : ∀ x ∈ X, L x = insert (answer p D.center x)
      (sharedAnswers p H X D.center) ∪ C (D.cell x) x)
    {x : ℚ} (hx : x ∈ X) : answer p D.center x ∈ L x := by
  rw [hL x hx]
  exact Finset.mem_union_left _ (Finset.mem_insert_self _ _)

theorem shared_mem {X : Finset ℚ} {L : ℚ → Finset ℤ}
    (D : QueryRound p X) (C : Finset ℚ → ℚ → Finset ℤ)
    (hL : ∀ x ∈ X, L x = insert (answer p D.center x)
      (sharedAnswers p H X D.center) ∪ C (D.cell x) x)
    {x : ℚ} (hx : x ∈ X) {e : ℤ} (he : e ∈ sharedAnswers p H X D.center) :
    e ∈ L x := by
  rw [hL x hx]
  exact Finset.mem_union_left _ (Finset.mem_insert_of_mem he)

theorem child_labels_subset {X : Finset ℚ} {L : ℚ → Finset ℤ}
    (D : QueryRound p X) (C : Finset ℚ → ℚ → Finset ℤ)
    (hL : ∀ x ∈ X, L x = insert (answer p D.center x)
      (sharedAnswers p H X D.center) ∪ C (D.cell x) x)
    {x y : ℚ} (hx : x ∈ X) (hy : y ∈ D.cell x) : C (D.cell x) y ⊆ L y := by
  intro e he
  rw [hL y (D.cell_subset x hx hy), D.cell_eq_of_mem x hx y hy]
  exact Finset.mem_union_right _ he

variable [Fact p.Prime]

/-- In a good affine fiber, one fixed left query answer uses one routed cell.
Distinct cells at that answer would fully separate both left endpoints. -/
theorem fixed_answer_left_cell
    {X Y : Finset ℚ} {L R : ℚ → Finset ℤ} {lam t : ℚ}
    (D : QueryRound p X) (hlam : lam ≠ 0)
    (hown : ∀ x ∈ X, answer p D.center x ∈ L x)
    (hcover : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' →
      padicValRat p (y - y') ∈ R y ∨ padicValRat p (y - y') ∈ R y')
    {x x' y y' : ℚ} (hx : x ∈ X) (hx' : x' ∈ X)
    (hy : y ∈ Y) (hy' : y' ∈ Y)
    (hs : x + lam * y = t) (hs' : x' + lam * y' = t)
    (hg : Good p L R lam x y) (hg' : Good p L R lam x' y')
    (he : answer p D.center x = answer p D.center x') :
    D.cell x = D.cell x' := by
  by_contra hc
  have hxx : x ≠ x' := fun h => hc (congrArg D.cell h)
  have hd := D.full_separation x hx x' hx' hc he
  have hl : padicValRat p (x - x') ∈ L x := by
    simpa only [hd] using hown x hx
  have hl' : padicValRat p (x - x') ∈ L x' := by
    simpa only [hd, he] using hown x' hx'
  have hyy := (affine_difference_valuation (p := p) hlam hxx hs hs').1
  exact (full_separation_excludes_two (p := p) hlam hxx hs hs'
    hl hl' (hcover y hy y' hy' hyy)) ⟨hg, hg'⟩

/-- The symmetric localization keeps the original multiplier, avoiding an
inverse or any positivity restriction on the rational slope. -/
theorem fixed_answer_right_cell
    {X Y : Finset ℚ} {L R : ℚ → Finset ℤ} {lam t : ℚ}
    (D : QueryRound p Y) (hlam : lam ≠ 0)
    (hown : ∀ y ∈ Y, answer p D.center y ∈ R y)
    (hcover : ∀ x ∈ X, ∀ x' ∈ X, x ≠ x' →
      padicValRat p (x - x') ∈ L x ∨ padicValRat p (x - x') ∈ L x')
    {x x' y y' : ℚ} (hx : x ∈ X) (hx' : x' ∈ X)
    (hy : y ∈ Y) (hy' : y' ∈ Y)
    (hs : x + lam * y = t) (hs' : x' + lam * y' = t)
    (hg : Good p L R lam x y) (hg' : Good p L R lam x' y')
    (he : answer p D.center y = answer p D.center y') :
    D.cell y = D.cell y' := by
  by_contra hc
  have hyy : y ≠ y' := fun h => hc (congrArg D.cell h)
  have hxx : x ≠ x' := by
    intro h
    have hh := hs.trans hs'.symm
    rw [h] at hh
    exact hyy (mul_left_cancel₀ hlam (add_left_cancel hh))
  have hd := D.full_separation y hy y' hy' hc he
  have hr : padicValRat p (y - y') ∈ R y := by
    simpa only [hd] using hown y hy
  have hr' : padicValRat p (y - y') ∈ R y' := by
    simpa only [hd, he] using hown y' hy'
  have hv := (affine_difference_valuation (p := p) hlam hxx hs hs').2
  rcases hcover x hx x' hx' hxx with hl | hl
  · apply hg _ hl _ hr
    omega
  · apply hg' _ hl _ hr'
    omega

/-- The actual decoding certificate follows from two recursive label trees.
The induction measure is the sum of current coordinate cardinalities. -/
theorem certificate_of_labelTrees
    {E : Finset (ℚ × ℚ)} {X Y : Finset ℚ} {L R : ℚ → Finset ℤ}
    {lam t : ℚ} (hH : 2 ≤ H) (hlam : lam ≠ 0)
    (hsum : ∀ z ∈ E, z.1 + lam * z.2 = t)
    (TX : LabelTree p H X L) (TY : LabelTree p H Y R)
    (hgood : ∀ z ∈ rectangle E X Y, Good p L R lam z.1 z.2) :
    QueryCertificate E X Y (Nat.clog H X.card) (Nat.clog H Y.card) := by
  classical
  have hH' : 1 < H := by omega
  have aux : ∀ n : ℕ, ∀ X Y : Finset ℚ, ∀ L R : ℚ → Finset ℤ,
      X.card + Y.card = n → LabelTree p H X L → LabelTree p H Y R →
      (∀ z ∈ rectangle E X Y, Good p L R lam z.1 z.2) →
      QueryCertificate E X Y (Nat.clog H X.card) (Nat.clog H Y.card) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro X Y L R hn TX TY hgood
      have hcoverX := TX.union_coverage
      have hcoverY := TY.union_coverage
      have TXoriginal := TX
      have TYoriginal := TY
      cases TX with
      | leaf hX _ => exact QueryCertificate.left_leaf hX
      | query hX DX CX TXchildren hLX =>
        cases TY with
        | leaf hY _ => exact QueryCertificate.right_leaf hY
        | query hY DY CY TYchildren hRY =>
          have hownX : ∀ x ∈ X, answer p DX.center x ∈ L x :=
            fun x hx => own_mem DX CX hLX hx
          have hownY : ∀ y ∈ Y, answer p DY.center y ∈ R y :=
            fun y hy => own_mem DY CY hRY hy
          have recurse_left : ∀ x ∈ X,
              QueryCertificate E (DX.cell x) Y
                (Nat.clog H (DX.cell x).card) (Nat.clog H Y.card) := by
            intro x hx
            have hlt := DX.cell_card_lt hx
            apply ih ((DX.cell x).card + Y.card) (by omega)
              (DX.cell x) Y (CX (DX.cell x)) R rfl (TXchildren x hx) TYoriginal
            intro z hz
            have hzparent := rectangle_mono (DX.cell_subset x hx)
              (fun _ h => h) hz
            intro a ha b hb
            exact hgood z hzparent a
              (child_labels_subset DX CX hLX hx (mem_rectangle.mp hz).2.1 ha) b hb
          have recurse_right : ∀ y ∈ Y,
              QueryCertificate E X (DY.cell y)
                (Nat.clog H X.card) (Nat.clog H (DY.cell y).card) := by
            intro y hy
            have hlt := DY.cell_card_lt hy
            apply ih (X.card + (DY.cell y).card) (by omega)
              X (DY.cell y) L (CY (DY.cell y)) rfl TXoriginal (TYchildren y hy)
            intro z hz
            have hzparent := rectangle_mono (fun _ h => h)
              (DY.cell_subset y hy) hz
            intro a ha b hb
            exact hgood z hzparent a ha b
              (child_labels_subset DY CY hRY hy (mem_rectangle.mp hz).2.2 hb)
          let g : ℤ := padicValRat p lam
          let v : ℤ := padicValRat p (t - DX.center - lam * DY.center)
          have alternatives : ∀ z ∈ rectangle E X Y,
              answer p DX.center z.1 = v ∨ answer p DY.center z.2 = v - g := by
            intro z hz
            obtain ⟨hzE, hzX, hzY⟩ := mem_rectangle.mp hz
            have ha := (query_alternatives (p := p) hlam
              (DX.center_ne hzX) (DY.center_ne hzY)
              (hownX z.1 hzX) (hownY z.2 hzY) (hgood z hz) (hsum z hzE)).2
            change (answer p DX.center z.1 = v ∧
                answer p DX.center z.1 < g + answer p DY.center z.2) ∨
              (g + answer p DY.center z.2 = v ∧
                g + answer p DY.center z.2 < answer p DX.center z.1) at ha
            rcases ha with ha | ha
            · exact Or.inl ha.1
            · right
              omega
          have row_localizes : ∀ a ∈ rectangle E X Y, answer p DX.center a.1 = v →
              ∀ z ∈ rectangle E X Y, answer p DX.center z.1 = v →
                z.1 ∈ DX.cell a.1 := by
            intro a ha harow z hz hzrow
            obtain ⟨haE, haX, haY⟩ := mem_rectangle.mp ha
            obtain ⟨hzE, hzX, hzY⟩ := mem_rectangle.mp hz
            have hc := fixed_answer_left_cell DX hlam hownX hcoverY
              haX hzX haY hzY (hsum a haE) (hsum z hzE)
              (hgood a ha) (hgood z hz) (harow.trans hzrow.symm)
            rw [hc]
            exact DX.self_mem z.1 hzX
          have column_localizes : ∀ b ∈ rectangle E X Y, answer p DY.center b.2 = v - g →
              ∀ z ∈ rectangle E X Y, answer p DY.center z.2 = v - g →
                z.2 ∈ DY.cell b.2 := by
            intro b hb hbcol z hz hzcol
            obtain ⟨hbE, hbX, hbY⟩ := mem_rectangle.mp hb
            obtain ⟨hzE, hzX, hzY⟩ := mem_rectangle.mp hz
            have hc := fixed_answer_right_cell DY hlam hownY hcoverX
              hbX hzX hbY hzY (hsum b hbE) (hsum z hzE)
              (hgood b hb) (hgood z hz) (hbcol.trans hzcol.symm)
            rw [hc]
            exact DY.self_mem z.2 hzY
          by_cases hrow : ∃ a ∈ rectangle E X Y, answer p DX.center a.1 = v
          · obtain ⟨a, ha, harow⟩ := hrow
            obtain ⟨haE, haX, haY⟩ := mem_rectangle.mp ha
            by_cases hcol : ∃ b ∈ rectangle E X Y, answer p DY.center b.2 = v - g
            · obtain ⟨b, hb, hbcol⟩ := hcol
              obtain ⟨hbE, hbX, hbY⟩ := mem_rectangle.mp hb
              have hrawX : H * (rawFiber p X DX.center v).card < X.card := by
                by_contra hlarge
                have hv : v ∈ sharedAnswers p H X DX.center := by
                  apply Finset.mem_filter.mpr
                  exact ⟨Finset.mem_image.mpr ⟨a.1, haX, harow⟩, by omega⟩
                have hlabel := shared_mem DX CX hLX hbX hv
                apply hgood b hb v hlabel (answer p DY.center b.2) (hownY b.2 hbY)
                change g = v - answer p DY.center b.2
                omega
              have hrawY : H * (rawFiber p Y DY.center (v - g)).card < Y.card := by
                by_contra hlarge
                have hv : v - g ∈ sharedAnswers p H Y DY.center := by
                  apply Finset.mem_filter.mpr
                  exact ⟨Finset.mem_image.mpr ⟨b.2, hbY, hbcol⟩, by omega⟩
                have hlabel := shared_mem DY CY hRY haY hv
                apply hgood a ha (answer p DX.center a.1) (hownX a.1 haX) (v - g) hlabel
                change g = answer p DX.center a.1 - (v - g)
                omega
              have hcellX : (DX.cell a.1).card ≤ (rawFiber p X DX.center v).card := by
                apply Finset.card_le_card
                simpa only [harow] using DX.cell_subset_raw haX
              have hcellY : (DY.cell b.2).card ≤ (rawFiber p Y DY.center (v - g)).card := by
                apply Finset.card_le_card
                simpa only [hbcol] using DY.cell_subset_raw hbY
              have hdropX := clog_card_rank_drop hH' (DX.cell_nonempty haX)
                ((Nat.mul_le_mul_left H hcellX).trans_lt hrawX)
              have hdropY := clog_card_rank_drop hH' (DY.cell_nonempty hbY)
                ((Nat.mul_le_mul_left H hcellY).trans_lt hrawY)
              have hposX := Nat.clog_pos hH' hX
              have hposY := Nat.clog_pos hH' hY
              obtain ⟨arank, harank⟩ : ∃ a, Nat.clog H X.card = a + 1 :=
                ⟨Nat.clog H X.card - 1, by omega⟩
              obtain ⟨brank, hbrank⟩ : ∃ b, Nat.clog H Y.card = b + 1 :=
                ⟨Nat.clog H Y.card - 1, by omega⟩
              have row_cert : QueryCertificate E (DX.cell a.1) Y arank (brank + 1) :=
                QueryCertificate.weaken
                  (a := Nat.clog H (DX.cell a.1).card) (b := Nat.clog H Y.card)
                  (by omega) (by omega) (recurse_left a.1 haX)
              have column_cert : QueryCertificate E X (DY.cell b.2) (arank + 1) brank :=
                QueryCertificate.weaken
                  (a := Nat.clog H X.card) (b := Nat.clog H (DY.cell b.2).card)
                  (by omega) (by omega) (recurse_right b.2 hbY)
              have hcover : ∀ z ∈ rectangle E X Y,
                  z.1 ∈ DX.cell a.1 ∨ z.2 ∈ DY.cell b.2 := by
                intro z hz
                rcases alternatives z hz with hr | hc
                · exact Or.inl (row_localizes a ha harow z hz hr)
                · exact Or.inr (column_localizes b hb hbcol z hz hc)
              have hsep : ∀ z ∈ rectangle E X Y,
                  ¬(z.1 ∈ DX.cell a.1 ∧ z.2 ∈ DY.cell b.2) := by
                intro z hz hboth
                obtain ⟨_, hzX, hzY⟩ := mem_rectangle.mp hz
                have he := DX.answer_eq a.1 haX z.1 hboth.1
                have hf := DY.answer_eq b.2 hbY z.2 hboth.2
                apply hgood z hz (answer p DX.center z.1) (hownX z.1 hzX)
                  (answer p DY.center z.2) (hownY z.2 hzY)
                change g = answer p DX.center z.1 - answer p DY.center z.2
                omega
              rw [harank, hbrank]
              exact QueryCertificate.split (DX.cell_subset a.1 haX) (DX.cell_card_lt haX)
                (DY.cell_subset b.2 hbY) (DY.cell_card_lt hbY) hcover hsep row_cert column_cert
            · have hcover : ∀ z ∈ rectangle E X Y, z.1 ∈ DX.cell a.1 := by
                intro z hz
                rcases alternatives z hz with hr | hc
                · exact row_localizes a ha harow z hz hr
                · exact False.elim (hcol ⟨z, hz, hc⟩)
              exact QueryCertificate.unary_left (DX.cell_subset a.1 haX)
                (DX.cell_card_lt haX) hcover (clog_card_mono H (DX.cell_subset a.1 haX))
                (recurse_left a.1 haX)
          · by_cases hcol : ∃ b ∈ rectangle E X Y, answer p DY.center b.2 = v - g
            · obtain ⟨b, hb, hbcol⟩ := hcol
              have hbY := (mem_rectangle.mp hb).2.2
              have hcover : ∀ z ∈ rectangle E X Y, z.2 ∈ DY.cell b.2 := by
                intro z hz
                rcases alternatives z hz with hr | hc
                · exact False.elim (hrow ⟨z, hz, hr⟩)
                · exact column_localizes b hb hbcol z hz hc
              exact QueryCertificate.unary_right (DY.cell_subset b.2 hbY)
                (DY.cell_card_lt hbY) hcover (clog_card_mono H (DY.cell_subset b.2 hbY))
                (recurse_right b.2 hbY)
            · apply QueryCertificate.empty
              apply Finset.Subset.antisymm
              · intro z hz
                rcases alternatives z hz with hr | hc
                · exact False.elim (hrow ⟨z, hz, hr⟩)
                · exact False.elim (hcol ⟨z, hz, hc⟩)
              · exact Finset.empty_subset _
  exact aux (X.card + Y.card) X Y L R rfl TX TY hgood

/-- The binomial affine bound now has no certificate hypothesis. -/
theorem affine_card_le_of_labelTrees
    {E : Finset (ℚ × ℚ)} {X Y : Finset ℚ} {L R : ℚ → Finset ℤ}
    {lam t : ℚ} (hH : 2 ≤ H) (hlam : lam ≠ 0)
    (hsum : ∀ z ∈ E, z.1 + lam * z.2 = t)
    (TX : LabelTree p H X L) (TY : LabelTree p H Y R)
    (hgood : ∀ z ∈ rectangle E X Y, Good p L R lam z.1 z.2) :
    (rectangle E X Y).card ≤
      (Nat.clog H X.card + Nat.clog H Y.card).choose (Nat.clog H X.card) :=
  affine_card_le_choose_of_query_certificate hlam hsum
    (certificate_of_labelTrees hH hlam hsum TX TY hgood)

/-- One assignment works simultaneously for every nonzero rational slope,
target, and selected affine relation inside the finite p-unit set. All those
quantifiers occur after the existential choice of labels. -/
theorem exists_universal_affine_labels (H : ℕ) (hH : 2 ≤ H) (Q : Finset ℚ)
    (hunit : ∀ q ∈ Q, q ≠ 0 ∧ padicValRat p q = 0) :
    ∃ L : ℚ → Finset ℤ, LabelTree p H Q L ∧
      (∀ q ∈ Q, (L q).card ≤ (H + 1) * Nat.clog 2 Q.card) ∧
      (∀ q ∈ Q, ∀ r ∈ Q, q ≠ r →
        padicValRat p (q - r) ∈ L q ∨ padicValRat p (q - r) ∈ L r) ∧
      (∀ lam : ℚ, lam ≠ 0 → ∀ t : ℚ, ∀ E : Finset (ℚ × ℚ),
        E ⊆ Q ×ˢ Q →
        (∀ z ∈ E, z.1 + lam * z.2 = t) →
        (∀ z ∈ E, Good p L L lam z.1 z.2) →
        E.card ≤ (2 * Nat.clog H Q.card).choose (Nat.clog H Q.card)) := by
  obtain ⟨L, hT, hbudget, hcover⟩ := QueryGeometry.exists_bounded_cover (p := p) H Q hunit
  refine ⟨L, hT, hbudget, hcover, ?_⟩
  intro lam hlam t E hEQ hsum hgood
  have hrect : rectangle E Q Q = E := by
    apply Finset.Subset.antisymm
    · intro z hz
      exact (mem_rectangle.mp hz).1
    · intro z hz
      have hcoords := Finset.mem_product.mp (hEQ hz)
      exact mem_rectangle.mpr ⟨hz, hcoords.1, hcoords.2⟩
  have hgoodrect : ∀ z ∈ rectangle E Q Q, Good p L L lam z.1 z.2 :=
    fun z hz => hgood z (mem_rectangle.mp hz).1
  have hbound := affine_card_le_of_labelTrees hH hlam hsum hT hT hgoodrect
  simpa only [hrect, Nat.two_mul] using hbound


end QueryAffineCore
/- End assembled component: QueryAffineDraft.lean. -/

/- Begin assembled component: QueryOrbitDraft.lean. -/
/- Finite sum-gap and bad-product counts for the actual prime-power orbit.
The affine fixed-gap bound is assembled separately. -/
namespace QueryOrbit

abbrev GapTriple := ℤ × (ℚ × ℚ)
abbrev OrbitPoint := ℤ × ℚ
abbrev OrbitPair := OrbitPoint × OrbitPoint

def value (p : ℕ) (x : OrbitPoint) : ℚ := (p : ℚ) ^ x.1 * x.2
def cofactors (z : OrbitPair) : ℚ × ℚ := (z.1.2, z.2.2)
def gap (z : OrbitPair) : ℤ := z.2.1 - z.1.1

/-- At one normalized sum, each smaller gap must occur in the label list of
a representative with maximum gap. This counts actual rational solutions. -/
theorem normalized_gap_card_le {p : ℕ} [Fact p.Prime]
    {F : Finset GapTriple} {L : ℚ → Finset ℤ} {B : ℕ} {y : ℚ}
    (hunit : ∀ z ∈ F, z.2.2 ≠ 0 ∧ padicValRat p z.2.2 = 0)
    (hsum : ∀ z ∈ F, z.2.1 + (p : ℚ) ^ z.1 * z.2.2 = y)
    (havoid : ∀ z ∈ F, z.1 ∉ L z.2.1)
    (hcover : ∀ z ∈ F, ∀ w ∈ F, z.2.1 ≠ w.2.1 →
      padicValRat p (z.2.1 - w.2.1) ∈ L z.2.1 ∨
      padicValRat p (z.2.1 - w.2.1) ∈ L w.2.1)
    (hbudget : ∀ z ∈ F, (L z.2.1).card ≤ B) :
    (F.image Prod.fst).card ≤ B + 1 := by
  classical
  by_cases hF : F.Nonempty
  · obtain ⟨w, hw, hmax⟩ := Finset.exists_max_image F Prod.fst hF
    have hsub : F.image Prod.fst ⊆ insert w.1 (L w.2.1) := by
      intro g hg
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hg
      by_cases he : z.1 = w.1
      · exact Finset.mem_insert.mpr (Or.inl he)
      have hlt : z.1 < w.1 := lt_of_le_of_ne (hmax z hz) he
      have hd := QueryArithmetic.smaller_gap_difference
        (hunit z hz).1 (hunit w hw).1 (hunit z hz).2 (hunit w hw).2 hlt
        ((hsum z hz).trans (hsum w hw).symm)
      rcases hcover z hz w hw hd.1 with hl | hr
      · exact False.elim (havoid z hz (by simpa only [hd.2] using hl))
      · exact Finset.mem_insert_of_mem (by simpa only [hd.2] using hr)
    exact (Finset.card_le_card hsub).trans
      ((Finset.card_insert_le _ _).trans (Nat.add_le_add_right (hbudget w hw) 1))
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hF, Finset.image_empty,
      Finset.card_empty, Nat.zero_le]

/-- Combine the proved gap count with a bound for each fixed-gap affine fiber. -/
theorem normalized_fiber_card_le {p : ℕ} [Fact p.Prime]
    {F : Finset GapTriple} {L : ℚ → Finset ℤ} {B C : ℕ} {y : ℚ}
    (hunit : ∀ z ∈ F, z.2.2 ≠ 0 ∧ padicValRat p z.2.2 = 0)
    (hsum : ∀ z ∈ F, z.2.1 + (p : ℚ) ^ z.1 * z.2.2 = y)
    (havoid : ∀ z ∈ F, z.1 ∉ L z.2.1)
    (hcover : ∀ z ∈ F, ∀ w ∈ F, z.2.1 ≠ w.2.1 →
      padicValRat p (z.2.1 - w.2.1) ∈ L z.2.1 ∨
      padicValRat p (z.2.1 - w.2.1) ∈ L w.2.1)
    (hbudget : ∀ z ∈ F, (L z.2.1).card ≤ B)
    (haffine : ∀ g ∈ F.image Prod.fst, (F.filter (fun z => z.1 = g)).card ≤ C) :
    F.card ≤ (B + 1) * C := by
  calc
    F.card ≤ C * (F.image Prod.fst).card :=
      Finset.card_le_mul_card_image F C haffine
    _ ≤ C * (B + 1) := Nat.mul_le_mul_left C
      (normalized_gap_card_le hunit hsum havoid hcover hbudget)
    _ = (B + 1) * C := Nat.mul_comm _ _

/-- A product and directed gap recover both levels once the cofactors are fixed. -/
theorem pair_eq_of_product_gap {p : ℕ} [Fact p.Prime]
    {z w : OrbitPair} (hz : z.1.2 ≠ 0 ∧ z.2.2 ≠ 0)
    (hc : cofactors z = cofactors w)
    (hp : value p z.1 * value p z.2 = value p w.1 * value p w.2)
    (hg : gap z = gap w) : z = w := by
  have hq : z.1.2 = w.1.2 := congrArg (fun c : ℚ × ℚ => c.1) hc
  have hr : z.2.2 = w.2.2 := congrArg (fun c : ℚ × ℚ => c.2) hc
  have hlevels : z.1.1 = w.1.1 ∧ z.2.1 = w.2.1 := by
    apply QueryArithmetic.product_and_gap_recover_levels (p := p) hz.1 hz.2
    · simpa only [value, ← hq, ← hr] using hp
    · change z.2.1 - z.1.1 = w.2.1 - w.1.1 at hg
      omega
  exact Prod.ext (Prod.ext hlevels.1 hq) (Prod.ext hlevels.2 hr)

/-- Each cofactor pair has at most one level pair per bad gap. The bad-gap set
is the actual difference image of the two augmented endpoint label lists. -/
theorem fixed_cofactor_bad_card_le {p : ℕ} [Fact p.Prime]
    {F : Finset OrbitPair} {q r t : ℚ} {L : ℚ → Finset ℤ} {B : ℕ}
    (hnz : q ≠ 0 ∧ r ≠ 0)
    (hcof : ∀ z ∈ F, cofactors z = (q, r))
    (hprod : ∀ z ∈ F, value p z.1 * value p z.2 = t)
    (hbad : ∀ z ∈ F, ∃ a ∈ insert 0 (L q), ∃ b ∈ insert 0 (L r), gap z = a - b)
    (hBq : (L q).card ≤ B) (hBr : (L r).card ≤ B) :
    F.card ≤ (B + 1) ^ 2 := by
  classical
  have hinj : Set.InjOn gap (F : Set OrbitPair) := by
    intro z hz w hw hg
    have hc := hcof z hz
    have hq : z.1.2 = q := congrArg (fun c : ℚ × ℚ => c.1) hc
    have hr : z.2.2 = r := congrArg (fun c : ℚ × ℚ => c.2) hc
    exact pair_eq_of_product_gap (p := p) (by simpa only [hq, hr] using hnz)
      (hc.trans (hcof w hw).symm) ((hprod z hz).trans (hprod w hw).symm) hg
  let D : Finset ℤ := ((insert 0 (L q)) ×ˢ (insert 0 (L r))).image
    (fun a => a.1 - a.2)
  have hsub : F.image gap ⊆ D := by
    intro g hg
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hg
    obtain ⟨a, ha, b, hb, heq⟩ := hbad z hz
    exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, heq.symm⟩
  calc
    F.card = (F.image gap).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ D.card := Finset.card_le_card hsub
    _ ≤ (insert 0 (L q)).card * (insert 0 (L r)).card := by
      simpa only [Finset.card_product] using Finset.card_image_le
        (s := (insert 0 (L q)) ×ˢ (insert 0 (L r))) (f := fun a => a.1 - a.2)
    _ ≤ (B + 1) * (B + 1) := Nat.mul_le_mul
      ((Finset.card_insert_le _ _).trans (Nat.add_le_add_right hBq 1))
      ((Finset.card_insert_le _ _).trans (Nat.add_le_add_right hBr 1))
    _ = (B + 1) ^ 2 := (pow_two _).symm

/-- Only projected cofactor pairs actually used by this product fiber are counted. -/
theorem bad_product_fiber_card_le {p : ℕ} [Fact p.Prime]
    {F : Finset OrbitPair} {L : ℚ → Finset ℤ} {B M : ℕ} {t : ℚ}
    (hnz : ∀ z ∈ F, z.1.2 ≠ 0 ∧ z.2.2 ≠ 0)
    (hprod : ∀ z ∈ F, value p z.1 * value p z.2 = t)
    (hbad : ∀ z ∈ F, ∃ a ∈ insert 0 (L z.1.2),
      ∃ b ∈ insert 0 (L z.2.2), gap z = a - b)
    (hbudget : ∀ z ∈ F, (L z.1.2).card ≤ B ∧ (L z.2.2).card ≤ B)
    (hprojection : (F.image cofactors).card ≤ M) :
    F.card ≤ M * (B + 1) ^ 2 := by
  classical
  have hfiber : ∀ c ∈ F.image cofactors,
      (F.filter (fun z => cofactors z = c)).card ≤ (B + 1) ^ 2 := by
    intro c hc
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hc
    apply fixed_cofactor_bad_card_le (p := p) (hnz w hw)
    · intro z hz
      exact (Finset.mem_filter.mp hz).2
    · intro z hz
      exact hprod z (Finset.mem_filter.mp hz).1
    · intro z hz
      obtain ⟨hzF, hzw⟩ := Finset.mem_filter.mp hz
      have hq : z.1.2 = w.1.2 := congrArg (fun c : ℚ × ℚ => c.1) hzw
      have hr : z.2.2 = w.2.2 := congrArg (fun c : ℚ × ℚ => c.2) hzw
      simpa only [hq, hr] using hbad z hzF
    · exact (hbudget w hw).1
    · exact (hbudget w hw).2
  calc
    F.card ≤ (B + 1) ^ 2 * (F.image cofactors).card :=
      Finset.card_le_mul_card_image F _ hfiber
    _ ≤ (B + 1) ^ 2 * M := Nat.mul_le_mul_left _ hprojection
    _ = M * (B + 1) ^ 2 := Nat.mul_comm _ _

/-- Equal products of p-unit orbits have equal cofactor products: valuation
first recovers the total exponent, then nonzero cancellation removes it. -/
theorem cofactor_product_of_equal_product {p : ℕ} [Fact p.Prime]
    {z w : OrbitPair}
    (hz : (z.1.2 ≠ 0 ∧ padicValRat p z.1.2 = 0) ∧
      (z.2.2 ≠ 0 ∧ padicValRat p z.2.2 = 0))
    (hw : (w.1.2 ≠ 0 ∧ padicValRat p w.1.2 = 0) ∧
      (w.2.2 ≠ 0 ∧ padicValRat p w.2.2 = 0))
    (hprod : value p z.1 * value p z.2 = value p w.1 * value p w.2) :
    z.1.2 * z.2.2 = w.1.2 * w.2.2 := by
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have he : z.1.1 + z.2.1 = w.1.1 + w.2.1 := by
    have hv := congrArg (padicValRat p) hprod
    simp only [value, padicValRat.mul (mul_ne_zero (zpow_ne_zero _ hp0) hz.1.1)
      (mul_ne_zero (zpow_ne_zero _ hp0) hz.2.1),
      padicValRat.mul (mul_ne_zero (zpow_ne_zero _ hp0) hw.1.1)
      (mul_ne_zero (zpow_ne_zero _ hp0) hw.2.1),
      QueryArithmetic.orbit_valuation hz.1.1, QueryArithmetic.orbit_valuation hz.2.1,
      QueryArithmetic.orbit_valuation hw.1.1, QueryArithmetic.orbit_valuation hw.2.1,
      hz.1.2, hz.2.2, hw.1.2, hw.2.2, add_zero] at hv
    exact hv
  have hform : ∀ a : OrbitPair, value p a.1 * value p a.2 =
      (p : ℚ) ^ (a.1.1 + a.2.1) * (a.1.2 * a.2.2) := by
    intro a
    rw [zpow_add₀ hp0]
    simp only [value]
    ring
  rw [hform, hform, he] at hprod
  exact mul_left_cancel₀ (zpow_ne_zero _ hp0) hprod

/-- A global bound on the projected cofactor-product fibers supplies the
projection bound needed at every actual product, including selected subgraphs. -/
theorem product_fiber_projection_card_le {p : ℕ} [Fact p.Prime]
    {E F : Finset OrbitPair} {M : ℕ} {t : ℚ}
    (hFE : F ⊆ E)
    (hunit : ∀ z ∈ F, (z.1.2 ≠ 0 ∧ padicValRat p z.1.2 = 0) ∧
      (z.2.2 ≠ 0 ∧ padicValRat p z.2.2 = 0))
    (hprod : ∀ z ∈ F, value p z.1 * value p z.2 = t)
    (hcap : ∀ u : ℚ, ((E.image cofactors).filter (fun c => c.1 * c.2 = u)).card ≤ M) :
    (F.image cofactors).card ≤ M := by
  classical
  by_cases hF : F.Nonempty
  · obtain ⟨w, hw⟩ := hF
    apply (Finset.card_le_card (s := F.image cofactors)
      (t := (E.image cofactors).filter (fun c => c.1 * c.2 = w.1.2 * w.2.2)) ?_).trans
      (hcap _)
    intro c hc
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hc
    exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem cofactors (hFE hz),
      cofactor_product_of_equal_product (p := p) (hunit z hz) (hunit w hw)
        ((hprod z hz).trans (hprod w hw).symm)⟩
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hF, Finset.image_empty,
      Finset.card_empty, Nat.zero_le]


end QueryOrbit
/- End assembled component: QueryOrbitDraft.lean. -/

/- Begin assembled component: QueryOrbitSumDraft.lean. -/
/- Actual good fixed-sum fibers in a prime-power orbit.
The only remaining analytic/combinatorial input here is the explicit universal
fixed-gap affine cap. No hypothesis bounds the cardinality of the orbit fiber F. -/
namespace QueryOrbitSum

open QueryOrbit

def Good (L : ℚ → Finset ℤ) (z : OrbitPair) : Prop :=
  ∀ a ∈ insert 0 (L z.1.2), ∀ b ∈ insert 0 (L z.2.2), gap z ≠ a - b

/-- A universal normalized fixed-gap cap, to be supplied by the affine theorem.
Its goodness uses the original lists; the orbit predicate augments them by zero. -/
def AffineCap (p : ℕ) (Q : Finset ℚ) (L : ℚ → Finset ℤ) (C : ℕ) : Prop :=
  ∀ (g : ℤ) (y : ℚ) (E : Finset (ℚ × ℚ)),
    (∀ c ∈ E, c.1 ∈ Q ∧ c.2 ∈ Q) →
    (∀ c ∈ E, c.1 + (p : ℚ) ^ g * c.2 = y) →
    (∀ c ∈ E, ∀ a ∈ L c.1, ∀ b ∈ L c.2, g ≠ a - b) →
    E.card ≤ C

theorem good_gap_ne_zero {L : ℚ → Finset ℤ} {z : OrbitPair}
    (hz : Good L z) : gap z ≠ 0 := by
  intro hzero
  exact hz 0 (Finset.mem_insert_self _ _) 0 (Finset.mem_insert_self _ _)
    (by simpa only [sub_self] using hzero)

theorem good_swap {L : ℚ → Finset ℤ} {z : OrbitPair}
    (hz : Good L z) : Good L (Prod.swap z) := by
  intro a ha b hb hbad
  have h := hz b hb a ha
  apply h
  change z.1.1 - z.2.1 = a - b at hbad
  change z.2.1 - z.1.1 = b - a
  omega

def encode (z : OrbitPair) : GapTriple := (gap z, cofactors z)

/-- An unequal-level sum is nonzero and recovers its lower level, including
negative levels and either sign of each rational cofactor. -/
theorem positive_sum_recovers_left {p : ℕ} [Fact p.Prime]
    {z : OrbitPair} {t : ℚ}
    (hq : z.1.2 ≠ 0 ∧ padicValRat p z.1.2 = 0)
    (hr : z.2.2 ≠ 0 ∧ padicValRat p z.2.2 = 0)
    (hg : 0 < gap z) (hs : value p z.1 + value p z.2 = t) :
    t ≠ 0 ∧ padicValRat p t = z.1.1 := by
  have hij : z.1.1 < z.2.1 := by
    change 0 < z.2.1 - z.1.1 at hg
    omega
  have h := QueryArithmetic.orbit_sum_recovers_lower_level hq.1 hr.1 hq.2 hr.2 hij
  change (p : ℚ) ^ z.1.1 * z.1.2 + (p : ℚ) ^ z.2.1 * z.2.2 = t at hs
  simpa only [hs] using h

theorem normalized_sum {p : ℕ} [Fact p.Prime] {z : OrbitPair} {t : ℚ}
    (hs : value p z.1 + value p z.2 = t)
    (hlevel : padicValRat p t = z.1.1) :
    z.1.2 + (p : ℚ) ^ gap z * z.2.2 = t / (p : ℚ) ^ padicValRat p t := by
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  apply (eq_div_iff (zpow_ne_zero (padicValRat p t) hp0)).mpr
  rw [hlevel]
  have hexp : z.1.1 + gap z = z.2.1 := by
    dsimp only [gap]
    omega
  calc
    (z.1.2 + (p : ℚ) ^ gap z * z.2.2) * (p : ℚ) ^ z.1.1 =
        (p : ℚ) ^ z.1.1 * z.1.2 +
          ((p : ℚ) ^ z.1.1 * (p : ℚ) ^ gap z) * z.2.2 := by ring
    _ = (p : ℚ) ^ z.1.1 * z.1.2 + (p : ℚ) ^ z.2.1 * z.2.2 := by
      rw [← zpow_add₀ hp0, hexp]
    _ = t := hs

/-- A fixed-sum fiber with positive directed gap has at most (B+1)C pairs. -/
theorem positive_good_sum_fiber_card_le {p : ℕ} [Fact p.Prime]
    {F : Finset OrbitPair} {Q : Finset ℚ} {L : ℚ → Finset ℤ}
    {B C : ℕ} {t : ℚ}
    (hunit : ∀ q ∈ Q, q ≠ 0 ∧ padicValRat p q = 0)
    (hcof : ∀ z ∈ F, z.1.2 ∈ Q ∧ z.2.2 ∈ Q)
    (hsum : ∀ z ∈ F, value p z.1 + value p z.2 = t)
    (hgood : ∀ z ∈ F, Good L z)
    (hpositive : ∀ z ∈ F, 0 < gap z)
    (hbudget : ∀ q ∈ Q, (L q).card ≤ B)
    (hcover : ∀ q ∈ Q, ∀ r ∈ Q, q ≠ r →
      padicValRat p (q - r) ∈ L q ∨ padicValRat p (q - r) ∈ L r)
    (haffine : AffineCap p Q L C) : F.card ≤ (B + 1) * C := by
  classical
  have hlevel : ∀ z ∈ F, padicValRat p t = z.1.1 := by
    intro z hz
    exact (positive_sum_recovers_left
      (hunit _ (hcof z hz).1) (hunit _ (hcof z hz).2)
      (hpositive z hz) (hsum z hz)).2
  have hinj : Set.InjOn encode (F : Set OrbitPair) := by
    intro z hz w hw he
    have hg : gap z = gap w := congrArg (fun v : GapTriple => v.1) he
    have hq : z.1.2 = w.1.2 := congrArg (fun v : GapTriple => v.2.1) he
    have hr : z.2.2 = w.2.2 := congrArg (fun v : GapTriple => v.2.2) he
    have hi : z.1.1 = w.1.1 := (hlevel z hz).symm.trans (hlevel w hw)
    have hj : z.2.1 = w.2.1 := by
      change z.2.1 - z.1.1 = w.2.1 - w.1.1 at hg
      omega
    exact Prod.ext (Prod.ext hi hq) (Prod.ext hj hr)
  let N : Finset GapTriple := F.image encode
  have hNcof : ∀ z ∈ N, z.2.1 ∈ Q ∧ z.2.2 ∈ Q := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    exact hcof w hw
  have hNsum : ∀ z ∈ N,
      z.2.1 + (p : ℚ) ^ z.1 * z.2.2 = t / (p : ℚ) ^ padicValRat p t := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    exact normalized_sum (hsum w hw) (hlevel w hw)
  have hNgood : ∀ z ∈ N, ∀ a ∈ insert 0 (L z.2.1),
      ∀ b ∈ insert 0 (L z.2.2), z.1 ≠ a - b := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    exact hgood w hw
  have hNavoid : ∀ z ∈ N, z.1 ∉ L z.2.1 := by
    intro z hz hm
    exact hNgood z hz z.1 (Finset.mem_insert_of_mem hm) 0
      (Finset.mem_insert_self _ _) (sub_zero _).symm
  have hNfixed : ∀ g ∈ N.image Prod.fst,
      (N.filter (fun z => z.1 = g)).card ≤ C := by
    intro g _hg
    let G : Finset GapTriple := N.filter (fun z => z.1 = g)
    let E : Finset (ℚ × ℚ) := G.image Prod.snd
    have hsnd : Set.InjOn Prod.snd (G : Set GapTriple) := by
      intro z hz w hw he
      have hzg : z.1 = g := (Finset.mem_filter.mp hz).2
      have hwg : w.1 = g := (Finset.mem_filter.mp hw).2
      exact Prod.ext (hzg.trans hwg.symm) he
    have hE : E.card ≤ C := by
      apply haffine g (t / (p : ℚ) ^ padicValRat p t) E
      · intro c hc
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hc
        exact hNcof z (Finset.mem_filter.mp hz).1
      · intro c hc
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hc
        obtain ⟨hzN, hzg⟩ := Finset.mem_filter.mp hz
        simpa only [hzg] using hNsum z hzN
      · intro c hc a ha b hb
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hc
        obtain ⟨hzN, hzg⟩ := Finset.mem_filter.mp hz
        simpa only [hzg] using hNgood z hzN a (Finset.mem_insert_of_mem ha)
          b (Finset.mem_insert_of_mem hb)
    calc
      (N.filter (fun z => z.1 = g)).card = E.card :=
        (Finset.card_image_of_injOn hsnd).symm
      _ ≤ C := hE
  have hNbound : N.card ≤ (B + 1) * C := by
    apply QueryOrbit.normalized_fiber_card_le (p := p) (F := N) (L := L)
      (B := B) (C := C) (y := t / (p : ℚ) ^ padicValRat p t)
    · intro z hz
      exact hunit _ (hNcof z hz).2
    · exact hNsum
    · exact hNavoid
    · intro z hz w hw hne
      exact hcover _ (hNcof z hz).1 _ (hNcof w hw).1 hne
    · intro z hz
      exact hbudget _ (hNcof z hz).1
    · exact hNfixed
  calc
    F.card = N.card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (B + 1) * C := hNbound

/-- The actual ordered good fiber bound. Zero directed gap is excluded by the
two augmented zero labels; negative gaps are counted after swapping endpoints. -/
theorem good_sum_fiber_card_le {p : ℕ} [Fact p.Prime]
    {F : Finset OrbitPair} {Q : Finset ℚ} {L : ℚ → Finset ℤ}
    {B C : ℕ} {t : ℚ}
    (hunit : ∀ q ∈ Q, q ≠ 0 ∧ padicValRat p q = 0)
    (hcof : ∀ z ∈ F, z.1.2 ∈ Q ∧ z.2.2 ∈ Q)
    (hsum : ∀ z ∈ F, value p z.1 + value p z.2 = t)
    (hgood : ∀ z ∈ F, Good L z)
    (hbudget : ∀ q ∈ Q, (L q).card ≤ B)
    (hcover : ∀ q ∈ Q, ∀ r ∈ Q, q ≠ r →
      padicValRat p (q - r) ∈ L q ∨ padicValRat p (q - r) ∈ L r)
    (haffine : AffineCap p Q L C) : F.card ≤ 2 * (B + 1) * C := by
  classical
  let P : Finset OrbitPair := F.filter (fun z => 0 < gap z)
  let N : Finset OrbitPair := F.filter (fun z => ¬0 < gap z)
  have hP : P.card ≤ (B + 1) * C := by
    apply positive_good_sum_fiber_card_le (p := p) (Q := Q) (L := L) (t := t) hunit
    · intro z hz
      exact hcof z (Finset.mem_filter.mp hz).1
    · intro z hz
      exact hsum z (Finset.mem_filter.mp hz).1
    · intro z hz
      exact hgood z (Finset.mem_filter.mp hz).1
    · intro z hz
      exact (Finset.mem_filter.mp hz).2
    · exact hbudget
    · exact hcover
    · exact haffine
  have hswapped : (N.image Prod.swap).card ≤ (B + 1) * C := by
    apply positive_good_sum_fiber_card_le (p := p) (Q := Q) (L := L) (t := t) hunit
    · intro z hz
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
      exact ⟨(hcof w (Finset.mem_filter.mp hw).1).2,
        (hcof w (Finset.mem_filter.mp hw).1).1⟩
    · intro z hz
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
      change value p w.2 + value p w.1 = t
      exact (add_comm _ _).trans (hsum w (Finset.mem_filter.mp hw).1)
    · intro z hz
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
      exact good_swap (hgood w (Finset.mem_filter.mp hw).1)
    · intro z hz
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨hwF, hnonpos⟩ := Finset.mem_filter.mp hw
      have hne := good_gap_ne_zero (hgood w hwF)
      change ¬0 < w.2.1 - w.1.1 at hnonpos
      change w.2.1 - w.1.1 ≠ 0 at hne
      change 0 < w.1.1 - w.2.1
      omega
    · exact hbudget
    · exact hcover
    · exact haffine
  have hN : N.card ≤ (B + 1) * C := by
    calc
      N.card = (N.image Prod.swap).card :=
        (Finset.card_image_of_injective N Prod.swap_injective).symm
      _ ≤ (B + 1) * C := hswapped
  have hparts : P.card + N.card = F.card :=
    Finset.card_filter_add_card_filter_not (s := F) (fun z => 0 < gap z)
  calc
    F.card = P.card + N.card := hparts.symm
    _ ≤ (B + 1) * C + (B + 1) * C := Nat.add_le_add hP hN
    _ = 2 * (B + 1) * C := by ring


end QueryOrbitSum
/- End assembled component: QueryOrbitSumDraft.lean. -/

/- Begin assembled component: QueryTransferDraft.lean. -/
/-!
# Canonical transfer of rational pair graphs to prime-power orbits

The imported orbit source was read at SHA256
`1a134e93323dadce8aa8b020e282bd821ed621edc9632f782174bcc013d131e0`.
The local rational valuation division/zpow declarations, nonzero division and
inverse cancellation, and Finset image/cardinality declarations were inspected.

Recovery and injectivity hold even at zero. The explicit nonzero hypotheses are
needed only to make the normalized cofactors nonzero p-units. The graph image
preserves every selected ordered pair and the actual sum/product image sets;
it does not assume distinct orbit representations or use the full Cartesian
square in place of the selected graph.

No Lean/build/cache, API/network, or GUI operation was run by this subtask.
The root task owns compilation and final graph-charge assembly.
-/

namespace QueryTransfer

open QueryOrbit

def unitPart (p : ℕ) (x : ℚ) : ℚ := x / (p : ℚ) ^ padicValRat p x

def canonical (p : ℕ) (x : ℚ) : OrbitPoint := (padicValRat p x, unitPart p x)

def canonicalPair (p : ℕ) (z : ℚ × ℚ) : OrbitPair :=
  (canonical p z.1, canonical p z.2)

def liftGraph (p : ℕ) (R : Finset (ℚ × ℚ)) : Finset OrbitPair :=
  R.image (canonicalPair p)

variable {p : ℕ} [Fact p.Prime]

/-- Normalization recovers the original rational, without a nonzero premise. -/
@[simp] theorem value_canonical (x : ℚ) : value p (canonical p x) = x := by
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  change (p : ℚ) ^ padicValRat p x * (x / (p : ℚ) ^ padicValRat p x) = x
  rw [div_eq_mul_inv, mul_left_comm, mul_inv_cancel₀ (zpow_ne_zero _ hp0), mul_one]

/-- The normalized cofactor of a nonzero rational is a nonzero p-unit. -/
theorem unitPart_unit {x : ℚ} (hx : x ≠ 0) :
    unitPart p x ≠ 0 ∧ padicValRat p (unitPart p x) = 0 := by
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hpow : (p : ℚ) ^ padicValRat p x ≠ 0 := zpow_ne_zero _ hp0
  refine ⟨div_ne_zero hx hpow, ?_⟩
  rw [unitPart, padicValRat.div hx hpow, padicValRat.zpow,
    padicValRat.self (Fact.out : p.Prime).one_lt, mul_one, sub_self]

theorem canonical_injective : Function.Injective (canonical p) := by
  intro x y h
  have hv := congrArg (value p) h
  simpa only [value_canonical] using hv

theorem canonicalPair_injective : Function.Injective (canonicalPair p) := by
  intro z w h
  apply Prod.ext
  · apply canonical_injective (p := p)
    exact congrArg (fun a : OrbitPair => a.1) h
  · apply canonical_injective (p := p)
    exact congrArg (fun a : OrbitPair => a.2) h

/-- No selected ordered pair is lost under the canonical map. -/
@[simp] theorem liftGraph_card (R : Finset (ℚ × ℚ)) :
    (liftGraph p R).card = R.card :=
  Finset.card_image_of_injective R (canonicalPair_injective (p := p))

/-- Every lifted endpoint is a valid nonzero p-unit cofactor when every
original endpoint is nonzero. This condition is local to the selected graph. -/
theorem liftGraph_unit {R : Finset (ℚ × ℚ)}
    (hnz : ∀ z ∈ R, z.1 ≠ 0 ∧ z.2 ≠ 0) :
    ∀ z ∈ liftGraph p R,
      (z.1.2 ≠ 0 ∧ padicValRat p z.1.2 = 0) ∧
      (z.2.2 ≠ 0 ∧ padicValRat p z.2.2 = 0) := by
  intro z hz
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
  exact ⟨unitPart_unit (hnz w hw).1, unitPart_unit (hnz w hw).2⟩

/-- Equality of the sum image sets, including signs and zero sums. -/
theorem liftGraph_sum_image (R : Finset (ℚ × ℚ)) :
    (liftGraph p R).image (fun z => value p z.1 + value p z.2) =
      R.image (fun z => z.1 + z.2) := by
  simp only [liftGraph, Finset.image_image, Function.comp_def, canonicalPair, value_canonical]

/-- Equality of the product image sets. No energy or representation-count
assumption is needed for this change of coordinates. -/
theorem liftGraph_product_image (R : Finset (ℚ × ℚ)) :
    (liftGraph p R).image (fun z => value p z.1 * value p z.2) =
      R.image (fun z => z.1 * z.2) := by
  simp only [liftGraph, Finset.image_image, Function.comp_def, canonicalPair, value_canonical]

omit [Fact p.Prime] in
/-- The projected pairs are exactly the normalized endpoint pairs actually
used by the input graph, with repeated projections deduplicated by Finset.image. -/
theorem liftGraph_cofactors_image (R : Finset (ℚ × ℚ)) :
    (liftGraph p R).image cofactors =
      R.image (fun z => (unitPart p z.1, unitPart p z.2)) := by
  simp only [liftGraph, Finset.image_image, Function.comp_def, cofactors,
    canonicalPair, canonical]

omit [Fact p.Prime] in
/-- Consequently a cap on the actual normalized cofactor-product fibers
transfers exactly to the orbit graph, without counting exponent slots. -/
theorem liftGraph_projection_cap {R : Finset (ℚ × ℚ)} {M : ℕ}
    (hcap : ∀ t : ℚ,
      ((R.image (fun z => (unitPart p z.1, unitPart p z.2))).filter
        (fun c => c.1 * c.2 = t)).card ≤ M) :
    ∀ t : ℚ, (((liftGraph p R).image cofactors).filter
      (fun c => c.1 * c.2 = t)).card ≤ M := by
  intro t
  rw [liftGraph_cofactors_image]
  exact hcap t


end QueryTransfer
/- End assembled component: QueryTransferDraft.lean. -/

/- Begin assembled component: QueryChargeDraft.lean. -/
/- The finite common-prime mixed charge. All labels and the affine cap are
constructed from the actual finite p-unit set; only its projected product cap
is a structural hypothesis. This is not the unrestricted sum-product conjecture. -/
namespace QueryCharge

open QueryOrbit
open QueryOrbitSum

def sumValue (p : ℕ) (z : OrbitPair) : ℚ := value p z.1 + value p z.2
def productValue (p : ℕ) (z : OrbitPair) : ℚ := value p z.1 * value p z.2

/-- An arbitrary selected ordered orbit graph is charged to its actual sum and
product images. The cofactor cap counts distinct projected pairs in this graph. -/
theorem orbit_graph_charge {p : ℕ} [Fact p.Prime]
    (H : ℕ) (hH : 2 ≤ H) (Q : Finset ℚ) (E : Finset OrbitPair) (M : ℕ)
    (hunit : ∀ q ∈ Q, q ≠ 0 ∧ padicValRat p q = 0)
    (hcof : ∀ z ∈ E, z.1.2 ∈ Q ∧ z.2.2 ∈ Q)
    (hcap : ∀ u : ℚ, ((E.image cofactors).filter (fun c => c.1 * c.2 = u)).card ≤ M) :
    E.card ≤
      2 * ((H + 1) * Nat.clog 2 Q.card + 1) *
        (2 * Nat.clog H Q.card).choose (Nat.clog H Q.card) *
        (E.image (sumValue p)).card +
      M * ((H + 1) * Nat.clog 2 Q.card + 1) ^ 2 *
        (E.image (productValue p)).card := by
  classical
  let B := (H + 1) * Nat.clog 2 Q.card
  let C := (2 * Nat.clog H Q.card).choose (Nat.clog H Q.card)
  change E.card ≤ 2 * (B + 1) * C * (E.image (sumValue p)).card +
    M * (B + 1) ^ 2 * (E.image (productValue p)).card
  obtain ⟨L, _hT, hbudget, hcover, hlinear⟩ :=
    QueryAffineCore.exists_universal_affine_labels (p := p) H hH Q hunit
  have haffine : AffineCap p Q L C := by
    intro g y F hFcof hFsum hFgood
    have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
    apply hlinear ((p : ℚ) ^ g) (zpow_ne_zero g hp0) y F
    · intro z hz
      exact Finset.mem_product.mpr (hFcof z hz)
    · exact hFsum
    · intro z hz a ha b hb
      have hv : padicValRat p ((p : ℚ) ^ g) = g := by
        rw [padicValRat.zpow, padicValRat.self (Fact.out : p.Prime).one_lt, mul_one]
      simpa only [hv] using hFgood z hz a ha b hb
  let G := E.filter (Good L)
  let D := E.filter (fun z => ¬Good L z)
  have hG : G.card ≤ 2 * (B + 1) * C * (E.image (sumValue p)).card := by
    apply Finset.card_le_mul_card_image_of_maps_to (f := sumValue p)
      (s := G) (t := E.image (sumValue p))
      (fun z hz => Finset.mem_image_of_mem _ (Finset.mem_filter.mp hz).1)
    intro t _ht
    apply good_sum_fiber_card_le (p := p) (Q := Q) (L := L) (t := t) hunit
    · intro z hz
      exact hcof z (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1
    · intro z hz
      exact (Finset.mem_filter.mp hz).2
    · intro z hz
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).2
    · exact hbudget
    · exact hcover
    · exact haffine
  have hD : D.card ≤ M * (B + 1) ^ 2 * (E.image (productValue p)).card := by
    apply Finset.card_le_mul_card_image_of_maps_to (f := productValue p)
      (s := D) (t := E.image (productValue p))
      (fun z hz => Finset.mem_image_of_mem _ (Finset.mem_filter.mp hz).1)
    intro t _ht
    let F := D.filter (fun z => productValue p z = t)
    have hFE : F ⊆ E := by
      intro z hz
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1
    have hFunit : ∀ z ∈ F, (z.1.2 ≠ 0 ∧ padicValRat p z.1.2 = 0) ∧
        (z.2.2 ≠ 0 ∧ padicValRat p z.2.2 = 0) := by
      intro z hz
      exact ⟨hunit _ (hcof z (hFE hz)).1, hunit _ (hcof z (hFE hz)).2⟩
    have hFprod : ∀ z ∈ F, value p z.1 * value p z.2 = t := by
      intro z hz
      exact (Finset.mem_filter.mp hz).2
    apply bad_product_fiber_card_le (p := p) (F := F) (L := L) (t := t)
    · intro z hz
      exact ⟨(hFunit z hz).1.1, (hFunit z hz).2.1⟩
    · exact hFprod
    · intro z hz
      have hnot := (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).2
      by_contra h
      apply hnot
      intro a ha b hb heq
      exact h ⟨a, ha, b, hb, heq⟩
    · intro z hz
      exact ⟨hbudget _ (hcof z (hFE hz)).1, hbudget _ (hcof z (hFE hz)).2⟩
    · exact product_fiber_projection_card_le (p := p) hFE hFunit hFprod hcap
  have hparts : G.card + D.card = E.card :=
    Finset.card_filter_add_card_filter_not (s := E) (Good L)
  rw [← hparts]
  exact Nat.add_le_add hG hD

/-- The active canonical cofactors of the selected rational pair graph. -/
def cofactorSet (p : ℕ) (R : Finset (ℚ × ℚ)) : Finset ℚ :=
  R.image (fun z => QueryTransfer.unitPart p z.1) ∪
    R.image (fun z => QueryTransfer.unitPart p z.2)

/-- The finite mixed charge for an arbitrary graph of nonzero rational pairs.
Its only structural parameter is the cap on actual normalized cofactor-product
fibers. Signs, zero sums, arbitrary integer levels and asymmetric graphs remain
allowed. The normalization and all query labels are constructed in the proof. -/
theorem rational_graph_charge {p : ℕ} [Fact p.Prime]
    (H : ℕ) (hH : 2 ≤ H) (R : Finset (ℚ × ℚ)) (M : ℕ)
    (hnz : ∀ z ∈ R, z.1 ≠ 0 ∧ z.2 ≠ 0)
    (hcap : ∀ u : ℚ,
      ((R.image (fun z => (QueryTransfer.unitPart p z.1, QueryTransfer.unitPart p z.2))).filter
        (fun c => c.1 * c.2 = u)).card ≤ M) :
    R.card ≤
      2 * ((H + 1) * Nat.clog 2 (cofactorSet p R).card + 1) *
        (2 * Nat.clog H (cofactorSet p R).card).choose (Nat.clog H (cofactorSet p R).card) *
        (R.image (fun z => z.1 + z.2)).card +
      M * ((H + 1) * Nat.clog 2 (cofactorSet p R).card + 1) ^ 2 *
        (R.image (fun z => z.1 * z.2)).card := by
  classical
  let Q := cofactorSet p R
  have hunit : ∀ q ∈ Q, q ≠ 0 ∧ padicValRat p q = 0 := by
    intro q hq
    rcases Finset.mem_union.mp hq with hleft | hright
    · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hleft
      exact QueryTransfer.unitPart_unit (p := p) (hnz z hz).1
    · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hright
      exact QueryTransfer.unitPart_unit (p := p) (hnz z hz).2
  have hcof : ∀ z ∈ QueryTransfer.liftGraph p R, z.1.2 ∈ Q ∧ z.2.2 ∈ Q := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    exact ⟨Finset.mem_union_left _ (Finset.mem_image_of_mem _ hw),
      Finset.mem_union_right _ (Finset.mem_image_of_mem _ hw)⟩
  have hbound := orbit_graph_charge (p := p) H hH Q (QueryTransfer.liftGraph p R) M
    hunit hcof (QueryTransfer.liftGraph_projection_cap hcap)
  have hs : (QueryTransfer.liftGraph p R).image (sumValue p) =
      R.image (fun z => z.1 + z.2) := QueryTransfer.liftGraph_sum_image R
  have hp : (QueryTransfer.liftGraph p R).image (productValue p) =
      R.image (fun z => z.1 * z.2) := QueryTransfer.liftGraph_product_image R
  rw [hs, hp, QueryTransfer.liftGraph_card] at hbound
  exact hbound


end QueryCharge
/- End assembled component: QueryChargeDraft.lean. -/

/-- Remove the complete prime-power factor of a rational number. -/
def unitPart (p : ℕ) (x : ℚ) : ℚ := x / (p : ℚ) ^ padicValRat p x

/-- All normalized cofactors that occur at an endpoint of the selected graph. -/
def cofactorSet (p : ℕ) (R : Finset (ℚ × ℚ)) : Finset ℚ :=
  R.image (fun z => unitPart p z.1) ∪
    R.image (fun z => unitPart p z.2)

/-- Every finite graph of nonzero rational pairs satisfies the explicit mixed
charge for each prime and each integer H at least two. The cap counts distinct
normalized ordered cofactor pairs actually present in R, not exponent slots or
the full square of the active cofactor set. -/
theorem proof (p : ℕ) (hp : p.Prime) (H : ℕ) (hH : 2 ≤ H)
    (R : Finset (ℚ × ℚ)) (M : ℕ)
    (hnz : ∀ z ∈ R, z.1 ≠ 0 ∧ z.2 ≠ 0)
    (hcap : ∀ u : ℚ,
      ((R.image (fun z => (unitPart p z.1, unitPart p z.2))).filter
        (fun c => c.1 * c.2 = u)).card ≤ M) :
    R.card ≤
      2 * ((H + 1) * Nat.clog 2 (cofactorSet p R).card + 1) *
        (2 * Nat.clog H (cofactorSet p R).card).choose (Nat.clog H (cofactorSet p R).card) *
        (R.image (fun z => z.1 + z.2)).card +
      M * ((H + 1) * Nat.clog 2 (cofactorSet p R).card + 1) ^ 2 *
        (R.image (fun z => z.1 * z.2)).card := by
  letI : Fact p.Prime := ⟨hp⟩
  exact QueryCharge.rational_graph_charge (p := p) H hH R M hnz hcap

end CommonPrimeCore

/- Audited component: QueryOptimizationNatDraft.lean; input SHA256 82e06039590e59140425cc2530a60c6816f4c6787066030576882b5732e2ff9a. -/

/- The natural-number coefficient bound only; no analytic or graph hypothesis. -/
namespace QueryOptimizationNat

theorem coefficient_bound (m : ℕ) :
    let n := Nat.clog 2 m
    let k := Nat.sqrt n + 1
    let H := 2 ^ k
    let r := Nat.clog H m
    let B := (H + 1) * n
    2 ≤ H ∧
      2 * (B + 1) * (2 * r).choose r ≤ 2 ^ (6 * k) ∧
      (B + 1) ^ 2 ≤ 2 ^ (6 * k) := by
  let n := Nat.clog 2 m
  let k := Nat.sqrt n + 1
  let H := 2 ^ k
  let r := Nat.clog H m
  let B := (H + 1) * n
  change 2 ≤ H ∧
    2 * (B + 1) * (2 * r).choose r ≤ 2 ^ (6 * k) ∧
    (B + 1) ^ 2 ≤ 2 ^ (6 * k)
  have hk : 1 ≤ k := by omega
  have hn : n ≤ k ^ 2 := by
    simpa only [k, Nat.succ_eq_add_one] using (Nat.lt_succ_sqrt' n).le
  have hH : 2 ≤ H := by
    simpa only [H, pow_one] using
      (Nat.pow_le_pow_right (by decide : 0 < 2) hk)
  have hH1 : 1 ≤ H := (by decide : 1 ≤ 2).trans hH
  have hr : r ≤ k := Nat.clog_le_of_le_pow (calc
    m ≤ 2 ^ n := Nat.le_pow_clog (by decide) m
    _ ≤ 2 ^ (k ^ 2) := Nat.pow_le_pow_right (by decide) hn
    _ = H ^ k := by simp only [H, pow_two, pow_mul])
  have hC : (2 * r).choose r ≤ 2 ^ (2 * k) :=
    (Nat.choose_le_two_pow _ _).trans
      (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left 2 hr))
  have hB : B + 1 ≤ 2 ^ (3 * k) := calc
    B + 1 ≤ (H + 1) * k ^ 2 + 1 :=
      Nat.add_le_add_right (Nat.mul_le_mul_left (H + 1) hn) 1
    _ = H * k ^ 2 + (k ^ 2 + 1) := by simp [Nat.add_mul, Nat.add_assoc]
    _ ≤ H * k ^ 2 + H * (k ^ 2 + 1) :=
      Nat.add_le_add_left (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right (k ^ 2 + 1) hH1) _
    _ = H * (2 * k ^ 2 + 1) := by simp [two_mul, Nat.mul_add, Nat.add_assoc]
    _ ≤ H * 2 ^ (2 * k) :=
      Nat.mul_le_mul_left H (Nat.two_mul_sq_add_one_le_two_pow_two_mul k)
    _ = 2 ^ (3 * k) := by
      change 2 ^ k * 2 ^ (2 * k) = _
      rw [← pow_add]
      congr 1
      omega
  refine ⟨hH, ?_, ?_⟩
  · calc
      2 * (B + 1) * (2 * r).choose r ≤ 2 * 2 ^ (3 * k) * 2 ^ (2 * k) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 2 hB) hC
      _ = 2 ^ (5 * k + 1) := by
        rw [← pow_succ', ← pow_add]
        congr 1
        omega
      _ ≤ 2 ^ (6 * k) := Nat.pow_le_pow_right (by decide) (by omega)
  · calc
      (B + 1) ^ 2 ≤ (2 ^ (3 * k)) ^ 2 := Nat.pow_le_pow_left hB 2
      _ = 2 ^ (6 * k) := by
        rw [← pow_mul]
        congr 1
        omega

end QueryOptimizationNat


/- Audited component: QueryOptimizationRealDraft.lean; input SHA256 c0dc112956737a94a9e6a1b8e516c6c783ac9c1cc93e8ffdb57e7b05df1c1bf2. -/

namespace QueryOptimizationReal

theorem clog_mul_log_le (m : ℕ) (hm : 1 ≤ m) :
    (Nat.clog 2 m : ℝ) * Real.log 2 ≤ Real.log (2 * (m : ℝ)) := by
  rcases eq_or_lt_of_le hm with h | h
  · subst m
    simpa using (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  · have hn : 0 < Nat.clog 2 m := Nat.clog_pos (by decide) h
    have hp : (2 : ℝ) ^ (Nat.clog 2 m).pred < (m : ℝ) := by
      exact_mod_cast Nat.pow_pred_clog_lt_self (by decide : 1 < (2 : ℕ)) h
    have hl := Real.log_lt_log (pow_pos (by norm_num : (0 : ℝ) < 2) _) hp
    rw [Real.log_pow] at hl
    have hc : ((Nat.clog 2 m).pred : ℝ) + 1 = (Nat.clog 2 m : ℝ) := by
      exact_mod_cast Nat.succ_pred_eq_of_pos hn
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hmpos.ne']
    rw [← hc, add_mul, one_mul]
    linarith

theorem power_envelope (m : ℕ) (hm : 1 ≤ m) :
    (2 : ℝ) ^ (6 * (Nat.sqrt (Nat.clog 2 m) + 1)) ≤
      64 * Real.exp (6 * Real.sqrt (Real.log (2 * (m : ℝ)))) := by
  let n := Nat.clog 2 m
  let s := Nat.sqrt n
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hs : (s : ℝ) ^ 2 ≤ (n : ℝ) := by exact_mod_cast Nat.sqrt_le' n
  have hlpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlone : Real.log 2 ≤ 1 := by
    calc
      Real.log 2 ≤ (2 : ℝ) - 1 := Real.log_le_sub_one_of_pos (by norm_num)
      _ = 1 := by norm_num
  have hlog : (n : ℝ) * Real.log 2 ≤ Real.log (2 * (m : ℝ)) :=
    clog_mul_log_le m hm
  have hsq : ((s : ℝ) * Real.log 2) ^ 2 ≤ Real.log (2 * (m : ℝ)) := by
    calc
      ((s : ℝ) * Real.log 2) ^ 2 = (s : ℝ) ^ 2 * (Real.log 2) ^ 2 := by ring
      _ ≤ (n : ℝ) * (Real.log 2) ^ 2 := mul_le_mul_of_nonneg_right hs (sq_nonneg _)
      _ ≤ (n : ℝ) * Real.log 2 := by gcongr; nlinarith
      _ ≤ Real.log (2 * (m : ℝ)) := hlog
  have hslog := Real.le_sqrt_of_sq_le hsq
  have hexp :
      (6 * (s + 1) : ℕ) * Real.log 2 ≤
        6 * Real.sqrt (Real.log (2 * (m : ℝ))) + 6 * Real.log 2 := by
    push_cast
    nlinarith
  calc
    (2 : ℝ) ^ (6 * (Nat.sqrt (Nat.clog 2 m) + 1)) =
        Real.exp ((6 * (s + 1) : ℕ) * Real.log 2) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ ≤ Real.exp (6 * Real.sqrt (Real.log (2 * (m : ℝ))) + 6 * Real.log 2) :=
      Real.exp_le_exp.mpr hexp
    _ = 64 * Real.exp (6 * Real.sqrt (Real.log (2 * (m : ℝ)))) := by
      rw [Real.exp_add]
      have hsix : Real.exp (6 * Real.log 2) = 64 := by
        calc
          Real.exp (6 * Real.log 2) = Real.exp (Real.log 2) ^ 6 :=
            Real.exp_nat_mul (Real.log 2) 6
          _ = 64 := by rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]; norm_num
      rw [hsix]
      ring

end QueryOptimizationReal


/- Audited component: QueryOptimizationEpsilonDraft.lean; input SHA256 36892b5a276304ece6a92eed4a71203d2bbcf4f1e421591465565631bf8ddfff. -/

/- A real-variable epsilon envelope; no sum-product or graph hypothesis. -/
namespace QueryOptimizationEpsilon

theorem sqrt_le_linear (L : ℝ) (hL : 0 ≤ L) (ε : ℝ) (hε : 0 < ε) :
    6 * Real.sqrt L ≤ ε * L + 9 / ε := by
  apply (mul_le_mul_iff_left₀ hε).mp
  have hsq := sq_nonneg (ε * Real.sqrt L - 3)
  rw [sub_sq, mul_pow, Real.sq_sqrt hL] at hsq
  have hcancel : 9 / ε * ε = (9 : ℝ) := div_mul_cancel₀ _ hε.ne'
  nlinarith

theorem envelope_le_power (m : ℕ) (hm : 1 ≤ m) (ε : ℝ) (hε : 0 < ε) :
    64 * Real.exp (6 * Real.sqrt (Real.log (2 * (m : ℝ)))) ≤
      64 * Real.exp (9 / ε) * (2 * (m : ℝ)) ^ ε := by
  have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hbase : 0 < 2 * (m : ℝ) := by linarith
  have hlog : 0 ≤ Real.log (2 * (m : ℝ)) := Real.log_nonneg (by linarith)
  have hexp := Real.exp_le_exp.mpr
    (sqrt_le_linear (Real.log (2 * (m : ℝ))) hlog ε hε)
  calc
    64 * Real.exp (6 * Real.sqrt (Real.log (2 * (m : ℝ)))) ≤
        64 * Real.exp (ε * Real.log (2 * (m : ℝ)) + 9 / ε) :=
      mul_le_mul_of_nonneg_left hexp (by norm_num)
    _ = 64 * Real.exp (9 / ε) * (2 * (m : ℝ)) ^ ε := by
      rw [Real.rpow_def_of_pos hbase, Real.exp_add]
      simp only [mul_comm, mul_left_comm, mul_assoc]

end QueryOptimizationEpsilon


/- Audited component: QueryOptimizedChargeDraft.lean; input SHA256 516bbed3f05652c39f11a28cdc61596cb937e745b24727e1d72232a20d8685cc. -/

namespace QueryOptimizedCharge

open CommonPrimeCore

noncomputable def envelope (m : ℕ) : ℝ :=
  64 * Real.exp (6 * Real.sqrt (Real.log (2 * (m : ℝ))))

theorem rational_graph_charge (p : ℕ) (hp : p.Prime)
    (R : Finset (ℚ × ℚ)) (M : ℕ)
    (hnz : ∀ z ∈ R, z.1 ≠ 0 ∧ z.2 ≠ 0)
    (hcap : ∀ u : ℚ,
      ((R.image (fun z => (unitPart p z.1, unitPart p z.2))).filter
        (fun c => c.1 * c.2 = u)).card ≤ M) :
    (R.card : ℝ) ≤ envelope (cofactorSet p R).card *
      ((R.image (fun z => z.1 + z.2)).card +
        (M : ℝ) * (R.image (fun z => z.1 * z.2)).card) := by
  classical
  by_cases hR : R = ∅
  · subst R
    simp
  have hm : 1 ≤ (cofactorSet p R).card := by
    obtain ⟨z, hz⟩ := Finset.nonempty_iff_ne_empty.mpr hR
    apply Finset.card_pos.mpr
    refine ⟨unitPart p z.1, ?_⟩
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
  let m := (cofactorSet p R).card
  let k := Nat.sqrt (Nat.clog 2 m) + 1
  let H := 2 ^ k
  let B := (H + 1) * Nat.clog 2 m
  let C := (2 * Nat.clog H m).choose (Nat.clog H m)
  have hcoef := QueryOptimizationNat.coefficient_bound m
  change 2 ≤ H ∧ 2 * (B + 1) * C ≤ 2 ^ (6 * k) ∧
    (B + 1) ^ 2 ≤ 2 ^ (6 * k) at hcoef
  have hpower : (2 : ℝ) ^ (6 * k) ≤ envelope m :=
    QueryOptimizationReal.power_envelope m hm
  have hsum : ((2 * (B + 1) * C : ℕ) : ℝ) ≤ envelope m := by
    have h : ((2 * (B + 1) * C : ℕ) : ℝ) ≤ (2 : ℝ) ^ (6 * k) := by
      exact_mod_cast hcoef.2.1
    exact h.trans hpower
  have hprod : (((B + 1) ^ 2 : ℕ) : ℝ) ≤ envelope m := by
    have h : (((B + 1) ^ 2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (6 * k) := by
      exact_mod_cast hcoef.2.2
    exact h.trans hpower
  have hfinite := CommonPrimeCore.proof p hp H hcoef.1 R M hnz hcap
  change R.card ≤ 2 * (B + 1) * C * (R.image (fun z => z.1 + z.2)).card +
    M * (B + 1) ^ 2 * (R.image (fun z => z.1 * z.2)).card at hfinite
  have hreal : (R.card : ℝ) ≤
      ((2 * (B + 1) * C : ℕ) : ℝ) * (R.image (fun z => z.1 + z.2)).card +
      (M : ℝ) * (((B + 1) ^ 2 : ℕ) : ℝ) * (R.image (fun z => z.1 * z.2)).card := by
    exact_mod_cast hfinite
  calc
    (R.card : ℝ) ≤ _ := hreal
    _ ≤ envelope m * (R.image (fun z => z.1 + z.2)).card +
        (M : ℝ) * envelope m * (R.image (fun z => z.1 * z.2)).card := by
      gcongr
    _ = _ := by ring

theorem rational_graph_charge_epsilon (p : ℕ) (hp : p.Prime)
    (R : Finset (ℚ × ℚ)) (M : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hnz : ∀ z ∈ R, z.1 ≠ 0 ∧ z.2 ≠ 0)
    (hcap : ∀ u : ℚ,
      ((R.image (fun z => (unitPart p z.1, unitPart p z.2))).filter
        (fun c => c.1 * c.2 = u)).card ≤ M) :
    (R.card : ℝ) ≤
      64 * Real.exp (9 / ε) * (2 * ((cofactorSet p R).card : ℝ)) ^ ε *
        ((R.image (fun z => z.1 + z.2)).card +
          (M : ℝ) * (R.image (fun z => z.1 * z.2)).card) := by
  classical
  by_cases hR : R = ∅
  · subst R
    simp
  have hm : 1 ≤ (cofactorSet p R).card := by
    obtain ⟨z, hz⟩ := Finset.nonempty_iff_ne_empty.mpr hR
    apply Finset.card_pos.mpr
    refine ⟨unitPart p z.1, ?_⟩
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
  have henv := QueryOptimizationEpsilon.envelope_le_power (cofactorSet p R).card hm ε hε
  exact (rational_graph_charge p hp R M hnz hcap).trans
    (mul_le_mul_of_nonneg_right henv (by positivity))

end QueryOptimizedCharge


/- Audited component: DisjointSupportDraft.lean; input SHA256 5869a41f542e5c0bcb2b21e9a27e9594f2fbfb391051d26d0fa9b32c4daf5428. -/

/-!
For an ordered factorization with disjoint endpoint prime supports, the first
support determines both endpoints. Hence a selected fixed-product fiber injects
into the powerset of the product's support. The bounds count ordered pairs,
exclude zero endpoints explicitly, and allow empty fibers and product one.
-/

namespace DisjointSupport

open Finset

/-- Equal products and equal first supports determine two coprime ordered
factorizations. Divisibility recovers the entire prime powers, not just support. -/
theorem pair_eq_of_product_eq_of_primeFactors_eq {a b c d : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hab : Disjoint a.primeFactors b.primeFactors)
    (hcd : Disjoint c.primeFactors d.primeFactors)
    (hprod : a * b = c * d) (hsupport : a.primeFactors = c.primeFactors) :
    (a, b) = (c, d) := by
  have had : Nat.Coprime a d := (Nat.disjoint_primeFactors ha hd).mp (by
    rw [hsupport]
    exact hcd)
  have hcb : Nat.Coprime c b := (Nat.disjoint_primeFactors hc hb).mp (by
    rw [← hsupport]
    exact hab)
  have hac : a ∣ c := had.dvd_mul_right.mp ⟨b, hprod.symm⟩
  have hca : c ∣ a := hcb.dvd_mul_right.mp ⟨d, hprod⟩
  have heq : a = c := Nat.dvd_antisymm hac hca
  subst c
  exact Prod.ext rfl (mul_left_cancel₀ ha hprod)

/-- The first endpoint support injects any selected disjoint-support product
fiber into the whole powerset of the fixed product's prime factors. -/
theorem card_le_two_pow_product_support (R : Finset (ℕ × ℕ)) (n : ℕ)
    (hpos : ∀ z ∈ R, z.1 ≠ 0 ∧ z.2 ≠ 0)
    (hprod : ∀ z ∈ R, z.1 * z.2 = n)
    (hdisjoint : ∀ z ∈ R, Disjoint z.1.primeFactors z.2.primeFactors) :
    R.card ≤ 2 ^ n.primeFactors.card := by
  have hinj : Set.InjOn (fun z : ℕ × ℕ => z.1.primeFactors) R := by
    rintro ⟨a, b⟩ hx ⟨c, d⟩ hy heq
    exact pair_eq_of_product_eq_of_primeFactors_eq
      (hpos _ hx).1 (hpos _ hx).2 (hpos _ hy).1 (hpos _ hy).2
      (hdisjoint _ hx) (hdisjoint _ hy)
      ((hprod _ hx).trans (hprod _ hy).symm) heq
  have hsub : R.image (fun z => z.1.primeFactors) ⊆ n.primeFactors.powerset := by
    intro S hS
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hS
    apply mem_powerset.mpr
    rw [← hprod z hz, Nat.primeFactors_mul (hpos z hz).1 (hpos z hz).2]
    exact subset_union_left
  calc
    R.card = (R.image (fun z => z.1.primeFactors)).card :=
      (card_image_of_injOn hinj).symm
    _ ≤ n.primeFactors.powerset.card := card_le_card hsub
    _ = 2 ^ n.primeFactors.card := card_powerset _

/-- Uniform ordered product-fiber bound from the two endpoint support bounds.
No bound on the sizes or exponents of the primes is assumed. -/
theorem card_le_two_pow_support_bounds (R : Finset (ℕ × ℕ)) (n k l : ℕ)
    (hpos : ∀ z ∈ R, z.1 ≠ 0 ∧ z.2 ≠ 0)
    (hprod : ∀ z ∈ R, z.1 * z.2 = n)
    (hdisjoint : ∀ z ∈ R, Disjoint z.1.primeFactors z.2.primeFactors)
    (hcard : ∀ z ∈ R, z.1.primeFactors.card ≤ k ∧ z.2.primeFactors.card ≤ l) :
    R.card ≤ 2 ^ (k + l) := by
  by_cases hR : R.Nonempty
  · obtain ⟨z, hz⟩ := hR
    have hn : n.primeFactors.card ≤ k + l := by
      rw [← hprod z hz, Nat.primeFactors_mul (hpos z hz).1 (hpos z hz).2]
      exact (card_union_le _ _).trans (Nat.add_le_add (hcard z hz).1 (hcard z hz).2)
    exact (card_le_two_pow_product_support R n hpos hprod hdisjoint).trans
      (Nat.pow_le_pow_right (by decide) hn)
  · rw [not_nonempty_iff_eq_empty.mp hR]
    exact Nat.zero_le _

/-- The support-at-most-two case needed for a disjoint-support selected graph. -/
theorem card_le_sixteen (R : Finset (ℕ × ℕ)) (n : ℕ)
    (hpos : ∀ z ∈ R, z.1 ≠ 0 ∧ z.2 ≠ 0)
    (hprod : ∀ z ∈ R, z.1 * z.2 = n)
    (hdisjoint : ∀ z ∈ R, Disjoint z.1.primeFactors z.2.primeFactors)
    (hcard : ∀ z ∈ R, z.1.primeFactors.card ≤ 2 ∧ z.2.primeFactors.card ≤ 2) :
    R.card ≤ 16 := by
  exact card_le_two_pow_support_bounds R n 2 2 hpos hprod hdisjoint hcard


end DisjointSupport

/- Audited component: SupportIncidenceDraft.lean; input SHA256 8e2a82c0c37dfeb579c590d2573f1f5a715b82e16f7b41015a6ecd7c1245509c. -/

/-!
A finite incidence bound for ordered pairs with intersecting supports.
Each vertex has at most k labels, and each label belongs to at most L vertices.
The partners intersecting one vertex are covered by the union of its label
fibers. Empty sets and empty supports require no separate nonemptiness premise.
-/

namespace SupportIncidence

open Finset
open scoped BigOperators

/-- The complement of the disjoint-support ordered graph has at most k L |A|
edges. The hypotheses concern actual finite supports and actual label fibers. -/
theorem card_sq_le_disjoint_card_add {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (s : α → Finset β) (k L : ℕ)
    (hsize : ∀ a ∈ A, (s a).card ≤ k)
    (hincidence : ∀ b, (A.filter fun a => b ∈ s a).card ≤ L) :
    A.card ^ 2 ≤
      ((A ×ˢ A).filter fun z => Disjoint (s z.1) (s z.2)).card + k * L * A.card := by
  classical
  let partners (a : α) := A.filter fun b => ¬Disjoint (s a) (s b)
  have hpartners (a : α) (ha : a ∈ A) : (partners a).card ≤ k * L := by
    have hcover : partners a ⊆ (s a).biUnion (fun b => A.filter fun x => b ∈ s x) := by
      intro x hx
      obtain ⟨hxA, hinter⟩ := mem_filter.mp hx
      obtain ⟨b, hba, hbx⟩ := not_disjoint_iff.mp hinter
      exact mem_biUnion.mpr ⟨b, hba, mem_filter.mpr ⟨hxA, hbx⟩⟩
    calc
      (partners a).card ≤ ((s a).biUnion (fun b => A.filter fun x => b ∈ s x)).card :=
        card_le_card hcover
      _ ≤ ∑ b ∈ s a, (A.filter fun x => b ∈ s x).card := card_biUnion_le
      _ ≤ ∑ _b ∈ s a, L := sum_le_sum fun b _ => hincidence b
      _ = (s a).card * L := by simp
      _ ≤ k * L := Nat.mul_le_mul_right L (hsize a ha)
  let bad := (A ×ˢ A).filter fun z => ¬Disjoint (s z.1) (s z.2)
  have hcover : bad ⊆ A.biUnion (fun a => (partners a).image fun b => (a, b)) := by
    rintro ⟨a, b⟩ hz
    obtain ⟨hab, hinter⟩ := mem_filter.mp hz
    obtain ⟨ha, hb⟩ := mem_product.mp hab
    exact mem_biUnion.mpr ⟨a, ha, mem_image.mpr
      ⟨b, mem_filter.mpr ⟨hb, hinter⟩, rfl⟩⟩
  have hbad : bad.card ≤ k * L * A.card := by
    calc
      bad.card ≤ (A.biUnion fun a => (partners a).image fun b => (a, b)).card :=
        card_le_card hcover
      _ ≤ ∑ a ∈ A, ((partners a).image fun b => (a, b)).card := card_biUnion_le
      _ ≤ ∑ a ∈ A, (partners a).card := sum_le_sum fun _ _ => card_image_le
      _ ≤ ∑ _a ∈ A, k * L := sum_le_sum fun a ha => hpartners a ha
      _ = k * L * A.card := by simp [Nat.mul_comm]
  have hpartition := card_filter_add_card_filter_not (s := A ×ˢ A)
    (fun z => Disjoint (s z.1) (s z.2))
  change ((A ×ˢ A).filter fun z => Disjoint (s z.1) (s z.2)).card + bad.card =
    (A ×ˢ A).card at hpartition
  rw [card_product] at hpartition
  calc
    A.card ^ 2 = ((A ×ˢ A).filter fun z => Disjoint (s z.1) (s z.2)).card + bad.card := by
      simpa only [pow_two] using hpartition.symm
    _ ≤ ((A ×ˢ A).filter fun z => Disjoint (s z.1) (s z.2)).card + k * L * A.card :=
      Nat.add_le_add_left hbad _


end SupportIncidence

/- Audited component: SupportProductDraft.lean; input SHA256 e5ce838fb03dc97a383e681f5ddd3bae2d2b2b79a0c147f3f30a437451cb3f81. -/

/-!
Combine actual support incidence with the disjoint-support product-fiber bound.
The disjoint graph is counted over its own product image, contained in A * A.
Empty sets are allowed; all natural endpoints are explicitly nonzero.
-/

namespace SupportProduct

open Finset
open scoped BigOperators Pointwise

/-- Small prime-factor incidences force a large full product set, quantitatively.
Only actual supports and their incidences occur in the hypotheses. -/
theorem card_sq_le_product_card_add (A : Finset ℕ) (k L : ℕ)
    (hpos : ∀ a ∈ A, a ≠ 0)
    (hsize : ∀ a ∈ A, a.primeFactors.card ≤ k)
    (hincidence : ∀ p, (A.filter fun a => p ∈ a.primeFactors).card ≤ L) :
    A.card ^ 2 ≤ 2 ^ (2 * k) * (A * A).card + k * L * A.card := by
  let D := (A ×ˢ A).filter fun z => Disjoint z.1.primeFactors z.2.primeFactors
  have hD {z : ℕ × ℕ} (hz : z ∈ D) :
      z.1 ∈ A ∧ z.2 ∈ A ∧ Disjoint z.1.primeFactors z.2.primeFactors := by
    simpa only [D, mem_filter, mem_product, and_assoc] using hz
  have hfiber (n : ℕ) : (D.filter fun z => z.1 * z.2 = n).card ≤ 2 ^ (k + k) := by
    apply DisjointSupport.card_le_two_pow_support_bounds
      (D.filter fun z => z.1 * z.2 = n) n k k
    · intro z hz
      have hzA := hD (mem_filter.mp hz).1
      exact ⟨hpos _ hzA.1, hpos _ hzA.2.1⟩
    · intro z hz
      exact (mem_filter.mp hz).2
    · intro z hz
      exact (hD (mem_filter.mp hz).1).2.2
    · intro z hz
      have hzA := hD (mem_filter.mp hz).1
      exact ⟨hsize _ hzA.1, hsize _ hzA.2.1⟩
  have himage : D.image (fun z => z.1 * z.2) ⊆ A * A := by
    intro n hn
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hn
    exact mul_mem_mul (hD hz).1 (hD hz).2.1
  have hcount : D.card ≤ 2 ^ (k + k) * (A * A).card := by
    calc
      D.card = ∑ n ∈ D.image (fun z => z.1 * z.2),
          (D.filter fun z => z.1 * z.2 = n).card :=
        card_eq_sum_card_image (fun z => z.1 * z.2) D
      _ ≤ ∑ _n ∈ D.image (fun z => z.1 * z.2), 2 ^ (k + k) :=
        sum_le_sum fun n _ => hfiber n
      _ = 2 ^ (k + k) * (D.image (fun z => z.1 * z.2)).card := by simp [Nat.mul_comm]
      _ ≤ 2 ^ (k + k) * (A * A).card := Nat.mul_le_mul_left _ (card_le_card himage)
  have hinc := SupportIncidence.card_sq_le_disjoint_card_add
    A Nat.primeFactors k L hsize hincidence
  change A.card ^ 2 ≤ D.card + k * L * A.card at hinc
  simpa only [two_mul] using hinc.trans (Nat.add_le_add_right hcount (k * L * A.card))

/-- The case where each natural has at most two distinct prime factors. -/
theorem card_sq_le_sixteen_product_card_add (A : Finset ℕ) (L : ℕ)
    (hpos : ∀ a ∈ A, a ≠ 0)
    (hsize : ∀ a ∈ A, a.primeFactors.card ≤ 2)
    (hincidence : ∀ p, (A.filter fun a => p ∈ a.primeFactors).card ≤ L) :
    A.card ^ 2 ≤ 16 * (A * A).card + 2 * L * A.card := by
  exact card_sq_le_product_card_add A 2 L hpos hsize hincidence

/-- If no prime occurs on more than a quarter of the vertices, the full product
set has at least one thirty-second of the ordered-pair mass. -/
theorem card_sq_le_thirty_two_product_card (A : Finset ℕ) (L : ℕ)
    (hpos : ∀ a ∈ A, a ≠ 0)
    (hsize : ∀ a ∈ A, a.primeFactors.card ≤ 2)
    (hincidence : ∀ p, (A.filter fun a => p ∈ a.primeFactors).card ≤ L)
    (hlight : 4 * L ≤ A.card) :
    A.card ^ 2 ≤ 32 * (A * A).card := by
  have hbase := card_sq_le_sixteen_product_card_add A L hpos hsize hincidence
  have hsmall : 4 * (L * A.card) ≤ A.card ^ 2 := by
    simpa only [Nat.mul_assoc, pow_two] using Nat.mul_le_mul_right A.card hlight
  simp only [Nat.mul_assoc] at hbase
  omega


end SupportProduct

/- Audited component: NaturalUnitPartDraft.lean; input SHA256 73bfc2ff7063ccf15b582af802ec62c72626880eae35758bce6affa844286e74. -/

/-!
The rational p-unit normalization of a natural is its natural complementary
prime-power part, `n / p ^ n.factorization p` (Mathlib's `ordCompl[p] n`).
The equality and support identity include zero and one. Positivity is imposed
only in the final support-cardinality consequence, where p-divisibility must
actually remove a prime from the support.

This component gives no energy or unrestricted sum-product conclusion.
-/

namespace NaturalUnitPart

/-- The canonical rational cofactor equals the cast of the natural complementary part.
Zero normalizes to zero and one to one; no positive-natural premise is needed. -/
theorem unitPart_natCast_eq {p : ℕ} (hp : p.Prime) (n : ℕ) :
    CommonPrimeCore.QueryTransfer.unitPart p (n : ℚ) = ((n / p ^ n.factorization p : ℕ) : ℚ) := by
  unfold CommonPrimeCore.QueryTransfer.unitPart
  rw [Nat.cast_div_charZero (Nat.ordProj_dvd n p), Nat.cast_pow,
    padicValRat.of_nat, ← Nat.factorization_def n hp, zpow_natCast]

/-- Removing all powers of p erases exactly p from the finite prime support.
This support identity holds for all natural n and p, including zero and one. -/
theorem primeFactors_naturalPart (n p : ℕ) :
    (n / p ^ n.factorization p).primeFactors = n.primeFactors.erase p := by
  simpa only [Nat.support_factorization, Finsupp.support_erase] using
    congrArg (fun f : ℕ →₀ ℕ => f.support) (Nat.factorization_ordCompl n p)

/-- A positive multiple of p with at most two distinct prime factors has a
normalized natural cofactor with at most one distinct prime factor. -/
theorem naturalPart_support_card_le_one {p n : ℕ}
    (hp : p.Prime) (hn : 0 < n) (hdiv : p ∣ n) (hcard : n.primeFactors.card ≤ 2) :
    (n / p ^ n.factorization p).primeFactors.card ≤ 1 := by
  rw [primeFactors_naturalPart]
  have hmem : p ∈ n.primeFactors := hp.mem_primeFactors hdiv (Nat.ne_of_gt hn)
  have hdrop := Finset.card_erase_add_one hmem
  omega


end NaturalUnitPart

/- Audited component: OmegaTwoExtractionDraft.lean; input SHA256 2dd12d148628b56772e7ff8c88d04d9a9606ba0f164e16ead1ba893604514ab6. -/

/-!
A finite heavy/light extraction from actual prime-support incidences.
The first threshold is one quarter of the whole set. Inside a common-prime
fiber, removing that prime leaves supports of size at most one; a second
threshold of one half either gives two fixed prime supports or a dense actual
ordered graph with disjoint complementary supports.

This component proves extraction only. It does not assume an energy estimate,
a product-fiber estimate beyond the imported proved theorem, or a sum-product
conclusion for the extracted common-prime graph.
-/

namespace OmegaTwoExtraction

open Finset
open scoped Pointwise

/-- Positive naturals with at most two distinct prime factors either already
have a quadratic product set, or admit a quantitatively large common-prime
subset with a fixed-two-prime or disjoint-complementary-support alternative.
The graph in the second alternative is the displayed full filtered square.
Empty sets and the natural number one are included. -/
theorem extraction (A : Finset ℕ)
    (hpos : ∀ a ∈ A, 0 < a)
    (hsize : ∀ a ∈ A, a.primeFactors.card ≤ 2) :
    A.card ^ 2 ≤ 32 * (A * A).card ∨
      ∃ (p : ℕ) (B : Finset ℕ), p.Prime ∧ B ⊆ A ∧
        (∀ b ∈ B, p ∣ b) ∧ A.card ≤ 4 * B.card ∧
        ((∃ (q : ℕ) (G : Finset ℕ), q.Prime ∧ G ⊆ B ∧
            B.card ≤ 2 * G.card ∧
            ∀ a ∈ G, a.primeFactors ⊆ ({p, q} : Finset ℕ)) ∨
          (B.card ^ 2 ≤ 2 * ((B ×ˢ B).filter fun z =>
              Disjoint (z.1 / p ^ z.1.factorization p).primeFactors
                (z.2 / p ^ z.2.factorization p).primeFactors).card ∧
            ∀ b ∈ B, (b / p ^ b.factorization p).primeFactors.card ≤ 1)) := by
  classical
  by_cases hlight : ∀ p, (A.filter fun a => p ∈ a.primeFactors).card ≤ A.card / 4
  · left
    apply SupportProduct.card_sq_le_thirty_two_product_card
      A (A.card / 4) (fun a ha => Nat.ne_of_gt (hpos a ha)) hsize hlight
    omega
  · right
    obtain ⟨p, hpheavy⟩ := not_forall.mp hlight
    let B := A.filter fun a => p ∈ a.primeFactors
    have hBsub : B ⊆ A := filter_subset _ _
    have hBpos : 0 < B.card := by dsimp [B]; omega
    obtain ⟨b, hb⟩ := card_pos.mp hBpos
    have hp : p.Prime := Nat.prime_of_mem_primeFactors (mem_filter.mp hb).2
    have hBdiv : ∀ b ∈ B, p ∣ b := by
      intro b hb
      exact Nat.dvd_of_mem_primeFactors (mem_filter.mp hb).2
    have hBlarge : A.card ≤ 4 * B.card := by dsimp [B]; omega
    refine ⟨p, B, hp, hBsub, hBdiv, hBlarge, ?_⟩
    let s (n : ℕ) := (n / p ^ n.factorization p).primeFactors
    have hscard : ∀ n ∈ B, (s n).card ≤ 1 := by
      intro n hn
      exact NaturalUnitPart.naturalPart_support_card_le_one
        hp (hpos n (hBsub hn)) (hBdiv n hn) (hsize n (hBsub hn))
    by_cases hsmall : ∀ q, (B.filter fun n => q ∈ s n).card ≤ B.card / 2
    · right
      refine ⟨?_, hscard⟩
      have hinc := SupportIncidence.card_sq_le_disjoint_card_add
        B s 1 (B.card / 2) hscard hsmall
      have hhalf : 2 * ((B.card / 2) * B.card) ≤ B.card ^ 2 := by
        simpa only [Nat.mul_assoc, pow_two] using
          Nat.mul_le_mul_right B.card (show 2 * (B.card / 2) ≤ B.card by omega)
      simp only [one_mul] at hinc
      change B.card ^ 2 ≤ 2 * ((B ×ˢ B).filter fun z => Disjoint (s z.1) (s z.2)).card
      omega
    · left
      obtain ⟨q, hqheavy⟩ := not_forall.mp hsmall
      let G := B.filter fun n => q ∈ s n
      have hGsub : G ⊆ B := filter_subset _ _
      have hGpos : 0 < G.card := by dsimp [G]; omega
      obtain ⟨n, hn⟩ := card_pos.mp hGpos
      have hq : q.Prime := Nat.prime_of_mem_primeFactors (mem_filter.mp hn).2
      have hGlarge : B.card ≤ 2 * G.card := by dsimp [G]; omega
      refine ⟨q, G, hq, hGsub, hGlarge, ?_⟩
      intro n hn r hr
      by_cases hrp : r = p
      · simp [hrp]
      · have hrs : r ∈ s n := by
          dsimp [s]
          rw [NaturalUnitPart.primeFactors_naturalPart]
          exact mem_erase.mpr ⟨hrp, hr⟩
        have hrq : r = q := (card_le_one.mp (hscard n (hGsub hn)))
          r hrs q (mem_filter.mp hn).2
        simp [hrq]


end OmegaTwoExtraction

/- Audited component: ValuationEnergyDraft.lean; input SHA256 646f595fd245ac96f4e3ad8ee6a4965a71445e42fc4c33085ae222204155e32a. -/

/-!
Finite Cauchy inequalities for the two kinds of tied positions in an additive-energy
quadruple. This component proves no valuation decomposition or sum-product theorem.
All counts are ordered, and empty sets and zero elements are allowed.

The proof uses finite fiber counting and the natural-number Cauchy inequality from
the pinned Mathlib sources, followed by an explicit coordinate permutation.
-/

namespace ValuationEnergy

open Finset
open scoped BigOperators

section Matching

variable {α β γ : Type*} [DecidableEq γ]

/-- The number of ordered pairs whose labels under two maps coincide. -/
def matchingCount (s : Finset α) (t : Finset β) (f : α → γ) (g : β → γ) : ℕ :=
  ((s ×ˢ t).filter fun z => f z.1 = g z.2).card

/-- Count matching labels over any finite set containing the first map's image. -/
theorem matchingCount_eq_sum (s : Finset α) (t : Finset β) (f : α → γ) (g : β → γ)
    (V : Finset γ) (hf : ∀ x ∈ s, f x ∈ V) :
    matchingCount s t f g =
      ∑ c ∈ V, (s.filter fun x => f x = c).card * (t.filter fun y => g y = c).card := by
  unfold matchingCount
  have hmap : Set.MapsTo (fun z : α × β => f z.1)
      (((s ×ˢ t).filter fun z => f z.1 = g z.2) : Set (α × β)) V := by
    intro z hz
    exact hf z.1 (mem_product.mp (mem_filter.mp hz).1).1
  rw [card_eq_sum_card_fiberwise hmap]
  apply sum_congr rfl
  intro c _
  rw [← card_product]
  apply congrArg Finset.card
  ext z
  simp only [mem_filter, mem_product]
  constructor
  · rintro ⟨⟨⟨hzs, hzt⟩, heq⟩, hfc⟩
    exact ⟨⟨hzs, hfc⟩, hzt, heq.symm.trans hfc⟩
  · rintro ⟨⟨hzs, hfc⟩, hzt, hgc⟩
    exact ⟨⟨⟨hzs, hzt⟩, hfc.trans hgc.symm⟩, hfc⟩

/-- Finite Cauchy for the overlap of two label-fiber profiles. -/
theorem matchingCount_sq_le (s : Finset α) (t : Finset β) (f : α → γ) (g : β → γ) :
    matchingCount s t f g ^ 2 ≤ matchingCount s s f f * matchingCount t t g g := by
  let V := s.image f ∪ t.image g
  have hs : ∀ x ∈ s, f x ∈ V := by
    intro x hx
    exact mem_union_left _ (mem_image_of_mem f hx)
  have ht : ∀ y ∈ t, g y ∈ V := by
    intro y hy
    exact mem_union_right _ (mem_image_of_mem g hy)
  rw [matchingCount_eq_sum s t f g V hs,
    matchingCount_eq_sum s s f f V hs, matchingCount_eq_sum t t g g V ht]
  simpa only [pow_two] using sum_mul_sq_le_sq_mul_sq (R := ℕ) V
    (fun c => (s.filter fun x => f x = c).card)
    (fun c => (t.filter fun y => g y = c).card)

end Matching

section Additive

variable {α : Type*} [DecidableEq α] [AddCommGroup α]

/-- The same-side count `D(U,A)`: ordered quadruples with both `U` entries on
one side of the equation, `u₁ + u₂ = a₁ + a₂`. -/
def sameSideCount (U A : Finset α) : ℕ :=
  matchingCount (U ×ˢ U) (A ×ˢ A) (fun z => z.1 + z.2) (fun z => z.1 + z.2)

theorem sameSideCount_eq_card_filter (U A : Finset α) :
    sameSideCount U A =
      (((U ×ˢ U) ×ˢ (A ×ˢ A)).filter
        fun z => z.1.1 + z.1.2 = z.2.1 + z.2.2).card := rfl

theorem sameSideCount_self (U : Finset α) :
    sameSideCount U U = Finset.addEnergy U U :=
  (Finset.addEnergy_eq_card_filter U U).symm

/-- Same-side tied positions obey Cauchy with the two self-energies. -/
theorem sameSideCount_sq_le (U A : Finset α) :
    sameSideCount U A ^ 2 ≤ Finset.addEnergy U U * Finset.addEnergy A A := by
  rw [← sameSideCount_self U, ← sameSideCount_self A]
  exact matchingCount_sq_le (U ×ˢ U) (A ×ˢ A)
    (fun z => z.1 + z.2) (fun z => z.1 + z.2)

/-- Matching ordered difference fibers count the usual mixed additive energy.
The bijection swaps the two entries from the second set. -/
theorem difference_matchingCount_eq_addEnergy (U A : Finset α) :
    matchingCount (U ×ˢ U) (A ×ˢ A) (fun z => z.1 - z.2) (fun z => z.1 - z.2) =
      Finset.addEnergy U A := by
  unfold matchingCount Finset.addEnergy
  apply card_equiv (Equiv.prodCongr (Equiv.refl _) (Equiv.prodComm _ _))
  rintro ⟨⟨u₁, u₂⟩, a₁, a₂⟩
  simp only [mem_filter, mem_product]
  change (((u₁ ∈ U ∧ u₂ ∈ U) ∧ a₁ ∈ A ∧ a₂ ∈ A) ∧ u₁ - u₂ = a₁ - a₂) ↔
    (((u₁ ∈ U ∧ u₂ ∈ U) ∧ a₂ ∈ A ∧ a₁ ∈ A) ∧ u₁ + a₂ = u₂ + a₁)
  constructor
  · rintro ⟨⟨hu, ha₁, ha₂⟩, heq⟩
    refine ⟨⟨hu, ha₂, ha₁⟩, ?_⟩
    simpa only [add_comm a₁ u₂] using (sub_eq_sub_iff_add_eq_add.mp heq)
  · rintro ⟨⟨hu, ha₂, ha₁⟩, heq⟩
    refine ⟨⟨hu, ha₁, ha₂⟩, sub_eq_sub_iff_add_eq_add.mpr ?_⟩
    simpa only [add_comm u₂ a₁] using heq

/-- Mixed additive energy obeys Cauchy with the two self-energies. -/
theorem addEnergy_sq_le (U A : Finset α) :
    Finset.addEnergy U A ^ 2 ≤ Finset.addEnergy U U * Finset.addEnergy A A := by
  have h := matchingCount_sq_le (U ×ˢ U) (A ×ˢ A)
    (fun z => z.1 - z.2) (fun z => z.1 - z.2)
  simpa only [difference_matchingCount_eq_addEnergy] using h

end Additive


end ValuationEnergy

/- Audited component: ValuationMinimumDraft.lean; input SHA256 05b25c55565cebbc08642e107bca28f12c2a54296a23838e59c0fd6f6845a48a. -/

/-!
In a nonzero rational additive-energy quadruple, the minimum p-adic valuation
occurs in at least two positions. The six cases retain the minimum inequalities
so that they may later be used in a finite valuation-level partition.

No sign condition or nonvanishing condition on the common sum is imposed.
This component does not itself count quadruples or prove an energy bound.
-/

namespace ValuationMinimum

variable {p : ℕ}

/-- Different valuations rule out cancellation, including Mathlib's value at zero. -/
theorem add_ne_zero_of_valuation_ne {a b : ℚ}
    (hv : padicValRat p a ≠ padicValRat p b) : a + b ≠ 0 := by
  intro hab
  have ha : a = -b := eq_neg_of_add_eq_zero_left hab
  apply hv
  rw [ha, padicValRat.neg]

variable [Fact p.Prime]

/-- The first position cannot have strictly smaller valuation than all other
positions in an additive equality. Only the first two entries need be nonzero. -/
theorem not_unique_minimum_first {a b c d : ℚ} (ha : a ≠ 0) (hb : b ≠ 0)
    (heq : a + b = c + d) :
    ¬(padicValRat p a < padicValRat p b ∧
      padicValRat p a < padicValRat p c ∧ padicValRat p a < padicValRat p d) := by
  rintro ⟨hab, hac, had⟩
  have hab0 : a + b ≠ 0 := add_ne_zero_of_valuation_ne (ne_of_lt hab)
  have hleft : padicValRat p (a + b) = padicValRat p a :=
    padicValRat.add_eq_of_lt hab0 ha hb hab
  have hcd0 : c + d ≠ 0 := by rwa [← heq]
  have hright := padicValRat.min_le_padicValRat_add (p := p) hcd0
  rw [← heq, hleft] at hright
  exact (lt_min hac had).not_ge hright

/-- Explicit six equal-minimum position pairs for a nonzero rational
additive-energy quadruple. Repeated entries and a zero common sum are allowed. -/
theorem six_minimum_cases {a b c d : ℚ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (heq : a + b = c + d) :
    (padicValRat p a = padicValRat p b ∧
      padicValRat p a ≤ padicValRat p c ∧ padicValRat p a ≤ padicValRat p d) ∨
    (padicValRat p a = padicValRat p c ∧
      padicValRat p a ≤ padicValRat p b ∧ padicValRat p a ≤ padicValRat p d) ∨
    (padicValRat p a = padicValRat p d ∧
      padicValRat p a ≤ padicValRat p b ∧ padicValRat p a ≤ padicValRat p c) ∨
    (padicValRat p b = padicValRat p c ∧
      padicValRat p b ≤ padicValRat p a ∧ padicValRat p b ≤ padicValRat p d) ∨
    (padicValRat p b = padicValRat p d ∧
      padicValRat p b ≤ padicValRat p a ∧ padicValRat p b ≤ padicValRat p c) ∨
    (padicValRat p c = padicValRat p d ∧
      padicValRat p c ≤ padicValRat p a ∧ padicValRat p c ≤ padicValRat p b) := by
  have h₁ := not_unique_minimum_first (p := p) ha hb heq
  have h₂ := not_unique_minimum_first (p := p) hb ha
    (show b + a = c + d by simpa only [add_comm b a] using heq)
  have h₃ := not_unique_minimum_first (p := p) hc hd heq.symm
  have h₄ := not_unique_minimum_first (p := p) hd hc
    (show d + c = a + b by simpa only [add_comm d c] using heq.symm)
  omega


end ValuationMinimum

/- Audited component: ValuationPartitionDraft.lean; input SHA256 d30d8b47ad90dfdbbd2e6416cf2cdaf1df10f961b63af5e57baf0e432484657c. -/

/-!
An explicit six-case cover of additive-energy quadruples by a tied valuation
level. Two coordinate permutations have same-side count; four have mixed
additive energy. The cover may overlap, so only finite union upper bounds are
used. No energy estimate or partition certificate is an assumption.
-/

namespace ValuationEnergy

open Finset
open scoped BigOperators

/-- A nonzero rational set's additive energy is bounded by its six tied-level
counts. Signs, repeated entries, zero common sums, and the empty set are allowed. -/
theorem addEnergy_le_sum_valuation_levels {p : ℕ} [Fact p.Prime]
    (A : Finset ℚ) (hA : ∀ a ∈ A, a ≠ 0) :
    Finset.addEnergy A A ≤
      ∑ i ∈ A.image (padicValRat p),
        (2 * sameSideCount (A.filter fun a => padicValRat p a = i) A +
          4 * Finset.addEnergy (A.filter fun a => padicValRat p a = i) A) := by
  classical
  let U (i : ℤ) := A.filter fun a => padicValRat p a = i
  let D (i : ℤ) := (((U i ×ˢ U i) ×ˢ (A ×ˢ A)).filter
    fun z => z.1.1 + z.1.2 = z.2.1 + z.2.2)
  let E (i : ℤ) := (((U i ×ˢ U i) ×ˢ (A ×ˢ A)).filter
    fun z => z.1.1 + z.2.1 = z.1.2 + z.2.2)
  let swapSides (z : (ℚ × ℚ) × (ℚ × ℚ)) := (z.2, z.1)
  let ac (z : (ℚ × ℚ) × (ℚ × ℚ)) := ((z.1.1, z.2.1), (z.1.2, z.2.2))
  let ad (z : (ℚ × ℚ) × (ℚ × ℚ)) := ((z.1.1, z.2.1), (z.2.2, z.1.2))
  let bc (z : (ℚ × ℚ) × (ℚ × ℚ)) := ((z.2.1, z.1.1), (z.1.2, z.2.2))
  let bd (z : (ℚ × ℚ) × (ℚ × ℚ)) := ((z.2.1, z.1.1), (z.2.2, z.1.2))
  let pieces (i : ℤ) := D i ∪ ((D i).image swapSides ∪
    ((E i).image ac ∪ ((E i).image ad ∪ ((E i).image bc ∪ (E i).image bd))))
  let S := (((A ×ˢ A) ×ˢ (A ×ˢ A)).filter
    fun z => z.1.1 + z.1.2 = z.2.1 + z.2.2)
  have memD {i : ℤ} {a b c d : ℚ} (ha : a ∈ A) (hb : b ∈ A)
      (hc : c ∈ A) (hd : d ∈ A) (hia : padicValRat p a = i)
      (hib : padicValRat p b = i) (heq : a + b = c + d) :
      ((a, b), (c, d)) ∈ D i := by
    simp only [D, U, mem_filter, mem_product]
    exact ⟨⟨⟨⟨ha, hia⟩, ⟨hb, hib⟩⟩, ⟨hc, hd⟩⟩, heq⟩
  have memE {i : ℤ} {a b c d : ℚ} (ha : a ∈ A) (hb : b ∈ A)
      (hc : c ∈ A) (hd : d ∈ A) (hia : padicValRat p a = i)
      (hib : padicValRat p b = i) (heq : a + c = b + d) :
      ((a, b), (c, d)) ∈ E i := by
    simp only [E, U, mem_filter, mem_product]
    exact ⟨⟨⟨⟨ha, hia⟩, ⟨hb, hib⟩⟩, ⟨hc, hd⟩⟩, heq⟩
  have hcover : S ⊆ (A.image (padicValRat p)).biUnion pieces := by
    rintro ⟨⟨a, b⟩, c, d⟩ hz
    rcases (show ((a ∈ A ∧ b ∈ A) ∧ c ∈ A ∧ d ∈ A) ∧
        a + b = c + d from by simpa only [S, mem_filter, mem_product] using hz) with
      ⟨⟨⟨ha, hb⟩, hc, hd⟩, heq⟩
    have hcases := ValuationMinimum.six_minimum_cases
      (p := p) (hA a ha) (hA b hb) (hA c hc) (hA d hd) heq
    rcases hcases with hab | hac | had | hbc | hbd | hcd
    · refine mem_biUnion.mpr ⟨padicValRat p a, mem_image_of_mem _ ha, ?_⟩
      simp only [pieces, mem_union]
      exact Or.inl (memD ha hb hc hd rfl hab.1.symm heq)
    · refine mem_biUnion.mpr ⟨padicValRat p a, mem_image_of_mem _ ha, ?_⟩
      simp only [pieces, mem_union]
      apply Or.inr ∘ Or.inr ∘ Or.inl
      exact mem_image.mpr ⟨((a, c), (b, d)), memE ha hc hb hd rfl hac.1.symm heq, rfl⟩
    · refine mem_biUnion.mpr ⟨padicValRat p a, mem_image_of_mem _ ha, ?_⟩
      simp only [pieces, mem_union]
      apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
      refine mem_image.mpr ⟨((a, d), (b, c)), memE ha hd hb hc rfl had.1.symm ?_, rfl⟩
      simpa only [add_comm c d] using heq
    · refine mem_biUnion.mpr ⟨padicValRat p b, mem_image_of_mem _ hb, ?_⟩
      simp only [pieces, mem_union]
      apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
      refine mem_image.mpr ⟨((b, c), (a, d)), memE hb hc ha hd rfl hbc.1.symm ?_, rfl⟩
      simpa only [add_comm a b] using heq
    · refine mem_biUnion.mpr ⟨padicValRat p b, mem_image_of_mem _ hb, ?_⟩
      simp only [pieces, mem_union]
      apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr
      refine mem_image.mpr ⟨((b, d), (a, c)), memE hb hd ha hc rfl hbd.1.symm ?_, rfl⟩
      simpa only [add_comm a b, add_comm c d] using heq
    · refine mem_biUnion.mpr ⟨padicValRat p c, mem_image_of_mem _ hc, ?_⟩
      simp only [pieces, mem_union]
      apply Or.inr ∘ Or.inl
      exact mem_image.mpr ⟨((c, d), (a, b)), memD hc hd ha hb rfl hcd.1.symm heq.symm, rfl⟩
  have hbound (i : ℤ) : (pieces i).card ≤
      2 * sameSideCount (U i) A + 4 * Finset.addEnergy (U i) A := by
    have h₁ := card_union_le (D i) ((D i).image swapSides ∪
      ((E i).image ac ∪ ((E i).image ad ∪ ((E i).image bc ∪ (E i).image bd))))
    have h₂ := card_union_le ((D i).image swapSides)
      ((E i).image ac ∪ ((E i).image ad ∪ ((E i).image bc ∪ (E i).image bd)))
    have h₃ := card_union_le ((E i).image ac)
      ((E i).image ad ∪ ((E i).image bc ∪ (E i).image bd))
    have h₄ := card_union_le ((E i).image ad) ((E i).image bc ∪ (E i).image bd)
    have h₅ := card_union_le ((E i).image bc) ((E i).image bd)
    have hs := card_image_le (s := D i) (f := swapSides)
    have hac := card_image_le (s := E i) (f := ac)
    have had := card_image_le (s := E i) (f := ad)
    have hbc := card_image_le (s := E i) (f := bc)
    have hbd := card_image_le (s := E i) (f := bd)
    have hd : (D i).card = sameSideCount (U i) A := rfl
    have he : (E i).card = Finset.addEnergy (U i) A := rfl
    change (pieces i).card ≤ _ at h₁
    omega
  calc
    Finset.addEnergy A A = S.card := Finset.addEnergy_eq_card_filter A A
    _ ≤ ((A.image (padicValRat p)).biUnion pieces).card := card_le_card hcover
    _ ≤ ∑ i ∈ A.image (padicValRat p), (pieces i).card := card_biUnion_le
    _ ≤ ∑ i ∈ A.image (padicValRat p),
        (2 * sameSideCount (U i) A + 4 * Finset.addEnergy (U i) A) :=
      sum_le_sum fun i _ => hbound i


end ValuationEnergy

/- Audited component: ValuationSplitDraft.lean; input SHA256 319510cda724e1ca04e0e858bf8d7bfdf23b85aadc42136cf57637fd7f3e6deb. -/

namespace ValuationEnergy

open scoped BigOperators

theorem nat_le_sqrt_mul_of_sq_le {d u a : ℕ} (h : d ^ 2 ≤ u * a) :
    (d : ℝ) ≤ Real.sqrt (u : ℝ) * Real.sqrt (a : ℝ) := by
  have hc : (d : ℝ) ^ 2 ≤ (u : ℝ) * (a : ℝ) := by exact_mod_cast h
  simpa only [Real.sqrt_mul (show (0 : ℝ) ≤ u by positivity)] using
    Real.le_sqrt_of_sq_le hc

/-- The unweighted valuation-splitting inequality, assembled from the explicit
six-case cover and finite Cauchy inequalities. The whole set contains no zero;
its energy may vanish and its additive equations may have zero common sum. -/
theorem sqrt_addEnergy_le_sum_valuation_levels {p : ℕ} [Fact p.Prime]
    (A : Finset ℚ) (hA : ∀ a ∈ A, a ≠ 0) :
    Real.sqrt (Finset.addEnergy A A : ℝ) ≤
      6 * ∑ i ∈ A.image (padicValRat p),
        Real.sqrt (Finset.addEnergy (A.filter fun a => padicValRat p a = i)
          (A.filter fun a => padicValRat p a = i) : ℝ) := by
  classical
  let U (i : ℤ) := A.filter fun a => padicValRat p a = i
  let e := Real.sqrt (Finset.addEnergy A A : ℝ)
  let t := ∑ i ∈ A.image (padicValRat p), Real.sqrt (Finset.addEnergy (U i) (U i) : ℝ)
  change e ≤ 6 * t
  have he0 : 0 ≤ e := Real.sqrt_nonneg _
  have he2 : e ^ 2 = (Finset.addEnergy A A : ℝ) := Real.sq_sqrt (by positivity)
  have ht0 : 0 ≤ t := Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _
  have hc : (Finset.addEnergy A A : ℝ) ≤
      ∑ i ∈ A.image (padicValRat p),
        (2 * (sameSideCount (U i) A : ℝ) + 4 * (Finset.addEnergy (U i) A : ℝ)) := by
    exact_mod_cast addEnergy_le_sum_valuation_levels (p := p) A hA
  have hcount : (Finset.addEnergy A A : ℝ) ≤ 6 * t * e := by
    calc
      (Finset.addEnergy A A : ℝ) ≤ _ := hc
      _ ≤ ∑ i ∈ A.image (padicValRat p),
          (6 * Real.sqrt (Finset.addEnergy (U i) (U i) : ℝ) * e) := by
        apply Finset.sum_le_sum
        intro i _
        have hd := nat_le_sqrt_mul_of_sq_le (sameSideCount_sq_le (U i) A)
        have hm := nat_le_sqrt_mul_of_sq_le (addEnergy_sq_le (U i) A)
        change (sameSideCount (U i) A : ℝ) ≤
          Real.sqrt (Finset.addEnergy (U i) (U i) : ℝ) * e at hd
        change (Finset.addEnergy (U i) A : ℝ) ≤
          Real.sqrt (Finset.addEnergy (U i) (U i) : ℝ) * e at hm
        nlinarith
      _ = 6 * t * e := by simp only [t, Finset.mul_sum, Finset.sum_mul]
  by_cases he : e = 0
  · rw [he]
    positivity
  have hepos : 0 < e := lt_of_le_of_ne he0 (Ne.symm he)
  apply (mul_le_mul_iff_right₀ hepos).mp
  nlinarith


end ValuationEnergy

/- Audited component: TwoPrimeRecoveryDraft.lean; input SHA256 56922345087273b3a53d0f242d355c8d7a28ec163db3aac01935561d14871cf0. -/

/-!
Two prime valuations recover a positive natural number whose prime factors
belong to those two primes. The primes need not be distinct. The number 1 and
arbitrarily large prime powers are included; no height or exponent bound occurs.

This is a factorization/recovery component, not an additive-energy or
sum-product theorem. The rational valuation interface matches valuation splitting.
-/

namespace TwoPrimeRecovery

/-- The natural factorization exponent, cast to the integers, is the p-adic
valuation of the rational natural-number cast. This identity also holds at zero. -/
theorem factorization_eq_padicValRat {p : ℕ} (hp : p.Prime) (n : ℕ) :
    (n.factorization p : ℤ) = padicValRat p (n : ℚ) := by
  rw [Nat.factorization_def n hp, padicValRat.of_nat]

/-- Equal p- and q-valuations determine a positive natural supported on {p,q}.
When p=q this is the corresponding one-prime statement. -/
theorem eq_of_two_prime_valuations {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (ha : 0 < a) (hb : 0 < b)
    (hsa : a.primeFactors ⊆ ({p, q} : Finset ℕ))
    (hsb : b.primeFactors ⊆ ({p, q} : Finset ℕ))
    (hvp : padicValRat p (a : ℚ) = padicValRat p (b : ℚ))
    (hvq : padicValRat q (a : ℚ) = padicValRat q (b : ℚ)) : a = b := by
  apply Nat.eq_of_factorization_eq (Nat.ne_of_gt ha) (Nat.ne_of_gt hb)
  intro r
  by_cases hrp : r = p
  · subst r
    have h : (a.factorization p : ℤ) = (b.factorization p : ℤ) :=
      (factorization_eq_padicValRat hp a).trans
        (hvp.trans (factorization_eq_padicValRat hp b).symm)
    exact_mod_cast h
  by_cases hrq : r = q
  · subst r
    have h : (a.factorization q : ℤ) = (b.factorization q : ℤ) :=
      (factorization_eq_padicValRat hq a).trans
        (hvq.trans (factorization_eq_padicValRat hq b).symm)
    exact_mod_cast h
  have hout : r ∉ ({p, q} : Finset ℕ) := by simp [hrp, hrq]
  have har : a.factorization r = 0 := by
    apply Finsupp.notMem_support_iff.mp
    change r ∉ a.primeFactors
    exact fun hr => hout (hsa hr)
  have hbr : b.factorization r = 0 := by
    apply Finsupp.notMem_support_iff.mp
    change r ∉ b.primeFactors
    exact fun hr => hout (hsb hr)
  rw [har, hbr]

/-- The paired rational valuations form an injective coordinate map on any
finite family of positive naturals supported on the two fixed primes. -/
theorem two_prime_valuations_injOn {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (A : Finset ℕ) (hpos : ∀ a ∈ A, 0 < a)
    (hsupp : ∀ a ∈ A, a.primeFactors ⊆ ({p, q} : Finset ℕ)) :
    Set.InjOn (fun a : ℕ => (padicValRat p (a : ℚ), padicValRat q (a : ℚ)))
      (A : Set ℕ) := by
  intro a ha b hb heq
  exact eq_of_two_prime_valuations hp hq (hpos a ha) (hpos b hb)
    (hsupp a ha) (hsupp b hb) (congrArg Prod.fst heq) (congrArg Prod.snd heq)

/-- The same coordinate injectivity on the rational image, in the exact domain
used by the rational valuation-energy splitting theorem. -/
theorem two_prime_valuations_injOn_rat_image {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (G : Finset ℕ) (hpos : ∀ a ∈ G, 0 < a)
    (hsupp : ∀ a ∈ G, a.primeFactors ⊆ ({p, q} : Finset ℕ)) :
    Set.InjOn (fun a : ℚ => (padicValRat p a, padicValRat q a))
      ((G.image fun n : ℕ => (n : ℚ)) : Set ℚ) := by
  intro x hx y hy heq
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
  apply congrArg (fun n : ℕ => (n : ℚ))
  exact eq_of_two_prime_valuations hp hq (hpos a ha) (hpos b hb)
    (hsupp a ha) (hsupp b hb) (congrArg Prod.fst heq) (congrArg Prod.snd heq)


end TwoPrimeRecovery

/- Audited component: TwoValuationEnergyDraft.lean; input SHA256 b82b2a2aeda419a68bc9509b0fe1739b07a1c3cef20b0a936c5c4f1b740a8ad5. -/

namespace ValuationEnergy

open scoped BigOperators Pointwise

/-- One injective valuation query leaves singleton fibers. -/
theorem sqrt_addEnergy_le_of_valuation_injective {p : ℕ} [Fact p.Prime]
    (A : Finset ℚ) (hA : ∀ a ∈ A, a ≠ 0)
    (hinj : Set.InjOn (padicValRat p) (A : Set ℚ)) :
    Real.sqrt (Finset.addEnergy A A : ℝ) ≤ 6 * (A.card : ℝ) := by
  classical
  have hfiber : ∀ i ∈ A.image (padicValRat p),
      Real.sqrt (Finset.addEnergy (A.filter fun a => padicValRat p a = i)
        (A.filter fun a => padicValRat p a = i) : ℝ) ≤ 1 := by
    intro i hi
    obtain ⟨a, ha, hia⟩ := Finset.mem_image.mp hi
    have heq : A.filter (fun b => padicValRat p b = i) = {a} := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · intro hb
        exact hinj hb.1 ha (hb.2.trans hia.symm)
      · rintro rfl
        exact ⟨ha, hia⟩
    have henergy : Finset.addEnergy ({a} : Finset ℚ) {a} ≤ 1 := by
      unfold Finset.addEnergy
      exact (Finset.card_filter_le _ _).trans (by simp)
    rw [heq]
    have hsqrt := Real.sqrt_le_sqrt (show (Finset.addEnergy {a} {a} : ℝ) ≤ 1 by
      exact_mod_cast henergy)
    simpa using hsqrt
  have hsum : (∑ i ∈ A.image (padicValRat p),
      Real.sqrt (Finset.addEnergy (A.filter fun a => padicValRat p a = i)
        (A.filter fun a => padicValRat p a = i) : ℝ)) ≤ (A.card : ℝ) := by
    calc
      _ ≤ ∑ _i ∈ A.image (padicValRat p), (1 : ℝ) := Finset.sum_le_sum hfiber
      _ = ((A.image (padicValRat p)).card : ℝ) := by simp
      _ ≤ (A.card : ℝ) := by exact_mod_cast Finset.card_image_le (s := A) (f := padicValRat p)
  exact (sqrt_addEnergy_le_sum_valuation_levels (p := p) A hA).trans
    (mul_le_mul_of_nonneg_left hsum (by norm_num))

/-- Two valuation coordinates that jointly identify each element give a
constant additive-energy bound, without any bound on their numerical range. -/
theorem sqrt_addEnergy_le_of_two_valuations {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (A : Finset ℚ) (hA : ∀ a ∈ A, a ≠ 0)
    (hinj : Set.InjOn (fun a => (padicValRat p a, padicValRat q a)) (A : Set ℚ)) :
    Real.sqrt (Finset.addEnergy A A : ℝ) ≤ 36 * (A.card : ℝ) := by
  classical
  let U (i : ℤ) := A.filter fun a => padicValRat p a = i
  have hlocal (i : ℤ) : Real.sqrt (Finset.addEnergy (U i) (U i) : ℝ) ≤
      6 * ((U i).card : ℝ) := by
    apply sqrt_addEnergy_le_of_valuation_injective (p := q) (U i)
    · intro a ha
      exact hA a (Finset.mem_filter.mp ha).1
    · intro a ha b hb heq
      apply hinj (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1
      exact Prod.ext ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm) heq
  have hcard : (∑ i ∈ A.image (padicValRat p), ((U i).card : ℝ)) = (A.card : ℝ) := by
    exact_mod_cast (Finset.card_eq_sum_card_image (padicValRat p) A).symm
  calc
    Real.sqrt (Finset.addEnergy A A : ℝ) ≤
        6 * ∑ i ∈ A.image (padicValRat p), Real.sqrt (Finset.addEnergy (U i) (U i) : ℝ) :=
      sqrt_addEnergy_le_sum_valuation_levels (p := p) A hA
    _ ≤ 6 * ∑ i ∈ A.image (padicValRat p), 6 * ((U i).card : ℝ) := by
      apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hlocal i)
      norm_num
    _ = 36 * (A.card : ℝ) := by rw [← Finset.mul_sum, hcard]; ring

theorem addEnergy_le_of_two_valuations {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (A : Finset ℚ) (hA : ∀ a ∈ A, a ≠ 0)
    (hinj : Set.InjOn (fun a => (padicValRat p a, padicValRat q a)) (A : Set ℚ)) :
    Finset.addEnergy A A ≤ 1296 * A.card ^ 2 := by
  have h := sqrt_addEnergy_le_of_two_valuations (p := p) (q := q) A hA hinj
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ Finset.addEnergy A A by positivity)
  have hm := mul_nonneg (sub_nonneg.mpr h)
    (add_nonneg (show (0 : ℝ) ≤ 36 * A.card by positivity)
      (Real.sqrt_nonneg (Finset.addEnergy A A : ℝ)))
  have hr : (Finset.addEnergy A A : ℝ) ≤ 1296 * (A.card : ℝ) ^ 2 := by nlinarith
  exact_mod_cast hr

/-- Cauchy converts the constant energy bound into a quadratic sumset bound. -/
theorem card_sq_le_sumset_of_two_valuations {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (A : Finset ℚ) (hA : ∀ a ∈ A, a ≠ 0)
    (hinj : Set.InjOn (fun a => (padicValRat p a, padicValRat q a)) (A : Set ℚ)) :
    A.card ^ 2 ≤ 1296 * (A + A).card := by
  classical
  by_cases hzero : A.card = 0
  · simp [hzero]
  have hpos : 0 < A.card ^ 2 := pow_pos (Nat.pos_of_ne_zero hzero) _
  have he := addEnergy_le_of_two_valuations (p := p) (q := q) A hA hinj
  have hbound : A.card ^ 2 * A.card ^ 2 ≤ (1296 * (A + A).card) * A.card ^ 2 := by
    calc
      _ ≤ (A + A).card * Finset.addEnergy A A := Finset.le_card_add_mul_addEnergy A A
      _ ≤ (A + A).card * (1296 * A.card ^ 2) := Nat.mul_le_mul_left _ he
      _ = _ := by ring
  apply (mul_le_mul_iff_right₀ hpos).mp
  simpa only [mul_comm] using hbound

/-- Positive naturals supported on two fixed primes have a quadratic sumset.
The primes may coincide; one and arbitrarily large prime powers are allowed. -/
theorem card_sq_le_sumset_of_two_prime_support {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (G : Finset ℕ)
    (hpos : ∀ a ∈ G, 0 < a)
    (hsupp : ∀ a ∈ G, a.primeFactors ⊆ ({p, q} : Finset ℕ)) :
    G.card ^ 2 ≤ 1296 * (G + G).card := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  let A : Finset ℚ := G.image fun n : ℕ => (n : ℚ)
  have hA : ∀ a ∈ A, a ≠ 0 := by
    intro a ha
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ha
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hpos n hn))
  have hinj := TwoPrimeRecovery.two_prime_valuations_injOn_rat_image
    hp hq G hpos hsupp
  have h := card_sq_le_sumset_of_two_valuations (p := p) (q := q) A hA hinj
  have hcard : A.card = G.card := Finset.card_image_of_injective G Nat.cast_injective
  have himage : (G + G).image (fun n : ℕ => (n : ℚ)) = A + A :=
    Finset.image_add (Nat.castAddMonoidHom ℚ)
  have hsum : (A + A).card = (G + G).card := by
    rw [← himage]
    exact Finset.card_image_of_injective (G + G) Nat.cast_injective
  rwa [hcard, hsum] at h


end ValuationEnergy

/- Audited component: NaturalSupportChargeDraft.lean; input SHA256 b401c7f50ea5014514e560f7e987e6f2ef95932227c8f6c594b6d711e7675236. -/

namespace NaturalSupportCharge

open NaturalUnitPart
open DisjointSupport

/-- Casting a selected natural graph preserves its disjoint-support product cap,
including rational targets with no natural preimage. -/
theorem ratCast_product_fiber_card_le (T : Finset (ℕ × ℕ)) (k l : ℕ)
    (hpos : ∀ z ∈ T, z.1 ≠ 0 ∧ z.2 ≠ 0)
    (hdisjoint : ∀ z ∈ T, Disjoint z.1.primeFactors z.2.primeFactors)
    (hcard : ∀ z ∈ T, z.1.primeFactors.card ≤ k ∧ z.2.primeFactors.card ≤ l)
    (u : ℚ) :
    (((T.image fun z => ((z.1 : ℚ), (z.2 : ℚ))).filter
      fun z => z.1 * z.2 = u).card) ≤ 2 ^ (k + l) := by
  classical
  rw [Finset.filter_image]
  apply Finset.card_image_le.trans
  let F := T.filter fun z => (z.1 : ℚ) * (z.2 : ℚ) = u
  change F.card ≤ 2 ^ (k + l)
  by_cases hF : F.Nonempty
  · obtain ⟨z, hz⟩ := hF
    apply card_le_two_pow_support_bounds F (z.1 * z.2) k l
    · intro w hw
      exact hpos w (Finset.mem_filter.mp hw).1
    · intro w hw
      have heq := (Finset.mem_filter.mp hw).2.trans (Finset.mem_filter.mp hz).2.symm
      exact_mod_cast heq
    · intro w hw
      exact hdisjoint w (Finset.mem_filter.mp hw).1
    · intro w hw
      exact hcard w (Finset.mem_filter.mp hw).1
  · rw [Finset.not_nonempty_iff_eq_empty.mp hF]
    exact Nat.zero_le _

/-- The actual normalized cofactor projection has a bounded product fiber when
the complementary natural supports are disjoint and small. Exponents are free. -/
theorem normalized_projection_cap (p : ℕ) (hp : p.Prime)
    (R : Finset (ℕ × ℕ)) (k l : ℕ)
    (hpos : ∀ z ∈ R, z.1 ≠ 0 ∧ z.2 ≠ 0)
    (hdisjoint : ∀ z ∈ R, Disjoint
      (z.1 / p ^ z.1.factorization p).primeFactors
      (z.2 / p ^ z.2.factorization p).primeFactors)
    (hcard : ∀ z ∈ R,
      (z.1 / p ^ z.1.factorization p).primeFactors.card ≤ k ∧
      (z.2 / p ^ z.2.factorization p).primeFactors.card ≤ l)
    (u : ℚ) :
    (((R.image (fun z => ((z.1 : ℚ), (z.2 : ℚ)))).image
      (fun z => (CommonPrimeCore.QueryTransfer.unitPart p z.1, CommonPrimeCore.QueryTransfer.unitPart p z.2))).filter
        (fun z => z.1 * z.2 = u)).card ≤ 2 ^ (k + l) := by
  classical
  let T := R.image fun z =>
    (z.1 / p ^ z.1.factorization p, z.2 / p ^ z.2.factorization p)
  have heq : ((R.image fun z => ((z.1 : ℚ), (z.2 : ℚ))).image
      fun z => (CommonPrimeCore.QueryTransfer.unitPart p z.1, CommonPrimeCore.QueryTransfer.unitPart p z.2)) =
      T.image (fun z => ((z.1 : ℚ), (z.2 : ℚ))) := by
    simp only [T, Finset.image_image, Function.comp_def, unitPart_natCast_eq hp]
  rw [heq]
  apply ratCast_product_fiber_card_le T k l
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    exact ⟨(Nat.ordCompl_pos p (hpos w hw).1).ne',
      (Nat.ordCompl_pos p (hpos w hw).2).ne'⟩
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    exact hdisjoint w hw
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    exact hcard w hw

/-- An explicit epsilon charge for an actual natural graph. The cofactor cap is
derived from disjoint complementary supports, and its scale uses the original
vertex count. No density or common exponent range is assumed. -/
theorem natural_graph_charge_epsilon (p : ℕ) (hp : p.Prime)
    (A : Finset ℕ) (R : Finset (ℕ × ℕ)) (k l : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hRA : ∀ z ∈ R, z.1 ∈ A ∧ z.2 ∈ A)
    (hpos : ∀ a ∈ A, a ≠ 0)
    (hdisjoint : ∀ z ∈ R, Disjoint
      (z.1 / p ^ z.1.factorization p).primeFactors
      (z.2 / p ^ z.2.factorization p).primeFactors)
    (hcard : ∀ z ∈ R,
      (z.1 / p ^ z.1.factorization p).primeFactors.card ≤ k ∧
      (z.2 / p ^ z.2.factorization p).primeFactors.card ≤ l) :
    (R.card : ℝ) ≤ 64 * Real.exp (9 / ε) * (2 * (A.card : ℝ)) ^ ε *
      ((R.image fun z => z.1 + z.2).card +
        ((2 ^ (k + l) : ℕ) : ℝ) * (R.image fun z => z.1 * z.2).card) := by
  classical
  let Q := R.image fun z => ((z.1 : ℚ), (z.2 : ℚ))
  have hRpos : ∀ z ∈ R, z.1 ≠ 0 ∧ z.2 ≠ 0 := fun z hz =>
    ⟨hpos _ (hRA z hz).1, hpos _ (hRA z hz).2⟩
  have hQpos : ∀ z ∈ Q, z.1 ≠ 0 ∧ z.2 ≠ 0 := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    exact ⟨Nat.cast_ne_zero.mpr (hRpos w hw).1, Nat.cast_ne_zero.mpr (hRpos w hw).2⟩
  have hcap := normalized_projection_cap p hp R k l hRpos hdisjoint hcard
  have hcharge := QueryOptimizedCharge.rational_graph_charge_epsilon
    p hp Q (2 ^ (k + l)) ε hε hQpos hcap
  have hQcard : Q.card = R.card := by
    apply Finset.card_image_of_injective
    intro z w heq
    apply Prod.ext
    · exact Nat.cast_injective (congrArg Prod.fst heq)
    · exact Nat.cast_injective (congrArg Prod.snd heq)
  have hsum : (Q.image fun z => z.1 + z.2).card =
      (R.image fun z => z.1 + z.2).card := by
    have h := Finset.card_image_of_injective
      (R.image fun z => z.1 + z.2) (Nat.cast_injective (R := ℚ))
    simpa only [Q, Finset.image_image, Function.comp_def, Nat.cast_add] using h
  have hprod : (Q.image fun z => z.1 * z.2).card =
      (R.image fun z => z.1 * z.2).card := by
    have h := Finset.card_image_of_injective
      (R.image fun z => z.1 * z.2) (Nat.cast_injective (R := ℚ))
    simpa only [Q, Finset.image_image, Function.comp_def, Nat.cast_mul] using h
  let C := CommonPrimeCore.cofactorSet p Q
  have hCsub : C ⊆ A.image (fun a : ℕ => CommonPrimeCore.QueryTransfer.unitPart p (a : ℚ)) := by
    intro c hc
    rcases Finset.mem_union.mp hc with hc | hc
    · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hc
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_image.mpr ⟨w.1, (hRA w hw).1, rfl⟩
    · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hc
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_image.mpr ⟨w.2, (hRA w hw).2, rfl⟩
  have hCcard : C.card ≤ A.card := (Finset.card_le_card hCsub).trans Finset.card_image_le
  have hpow : (2 * (C.card : ℝ)) ^ ε ≤ (2 * (A.card : ℝ)) ^ ε := by
    apply Real.rpow_le_rpow (by positivity) _ hε.le
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hCcard) (by norm_num)
  rw [hQcard, hsum, hprod] at hcharge
  exact hcharge.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpow (by positivity)) (by positivity))


end NaturalSupportCharge

/- Audited component: OmegaTwoBoundDraft.lean; input SHA256 167040dfee18141b71529a109f7234eb82daed20401b22168335298bef5e6932. -/

namespace OmegaTwoBound

open scoped Pointwise

/-- A uniform near-quadratic bound for positive naturals with at most two
distinct prime factors each. The two primes may vary with the element. -/
theorem quadratic_le_scaled_images (A : Finset ℕ)
    (hpos : ∀ a ∈ A, 0 < a)
    (hsize : ∀ a ∈ A, a.primeFactors.card ≤ 2)
    (ε : ℝ) (hε : 0 < ε) :
    (A.card : ℝ) ^ 2 ≤ 82944 * Real.exp (9 / ε) * (2 * (A.card : ℝ)) ^ ε *
      ((A + A).card + (A * A).card) := by
  classical
  by_cases hzero : A.card = 0
  · simp [hzero, Real.zero_rpow hε.ne']
  let K : ℝ := 64 * Real.exp (9 / ε) * (2 * (A.card : ℝ)) ^ ε
  let M : ℝ := (A + A).card + (A * A).card
  have hN : (1 : ℝ) ≤ A.card := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hzero
  have he : 1 ≤ Real.exp (9 / ε) := Real.one_le_exp_iff.mpr (by positivity)
  have hr : 1 ≤ (2 * (A.card : ℝ)) ^ ε := Real.one_le_rpow (by linarith) hε.le
  have hK : 64 ≤ K := by
    calc
      (64 : ℝ) = 64 * 1 * 1 := by ring
      _ ≤ 64 * Real.exp (9 / ε) * (2 * (A.card : ℝ)) ^ ε :=
        mul_le_mul (mul_le_mul_of_nonneg_left he (by norm_num)) hr
          (by norm_num) (by positivity)
  have hK0 : 0 ≤ K := by linarith
  have hM0 : 0 ≤ M := by dsimp [M]; positivity
  have hS : ((A + A).card : ℝ) ≤ M := le_add_of_nonneg_right (by positivity)
  have hP : ((A * A).card : ℝ) ≤ M := le_add_of_nonneg_left (by positivity)
  suffices h : (A.card : ℝ) ^ 2 ≤ 1296 * K * M by
    calc
      _ ≤ 1296 * K * M := h
      _ = _ := by dsimp [K, M]; ring
  rcases OmegaTwoExtraction.extraction A hpos hsize with
    hlight | ⟨p, B, hp, hBA, _hdiv, hNB, hcases⟩
  · calc
      (A.card : ℝ) ^ 2 ≤ 32 * ((A * A).card : ℝ) := by exact_mod_cast hlight
      _ ≤ (1296 * K) * ((A * A).card : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ ≤ (1296 * K) * M := mul_le_mul_of_nonneg_left hP (by positivity)
  · rcases hcases with ⟨q, G, hq, hGB, hBG, hsupp⟩ | ⟨hgraph, hcof⟩
    · have hGA : G ⊆ A := hGB.trans hBA
      have hNG : A.card ≤ 8 * G.card := by omega
      have hn : A.card ^ 2 ≤ 64 * G.card ^ 2 := by
        calc
          _ ≤ (8 * G.card) ^ 2 := Nat.pow_le_pow_left hNG 2
          _ = _ := by ring
      have henergy := ValuationEnergy.card_sq_le_sumset_of_two_prime_support
        hp hq G (fun a ha => hpos a (hGA ha)) hsupp
      have hsum := Finset.card_le_card (Finset.add_subset_add hGA hGA)
      have hfinite : A.card ^ 2 ≤ 82944 * (A + A).card := by nlinarith
      calc
        (A.card : ℝ) ^ 2 ≤ 82944 * ((A + A).card : ℝ) := by exact_mod_cast hfinite
        _ ≤ (1296 * K) * ((A + A).card : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ ≤ (1296 * K) * M := mul_le_mul_of_nonneg_left hS (by positivity)
    · let R := (B ×ˢ B).filter fun z =>
        Disjoint (z.1 / p ^ z.1.factorization p).primeFactors
          (z.2 / p ^ z.2.factorization p).primeFactors
      have hR {z : ℕ × ℕ} (hz : z ∈ R) :
          z.1 ∈ B ∧ z.2 ∈ B ∧ Disjoint
            (z.1 / p ^ z.1.factorization p).primeFactors
            (z.2 / p ^ z.2.factorization p).primeFactors := by
        simpa only [R, Finset.mem_filter, Finset.mem_product, and_assoc] using hz
      have hNmass : A.card ^ 2 ≤ 32 * R.card := by
        have hh := Nat.pow_le_pow_left hNB 2
        change B.card ^ 2 ≤ 2 * R.card at hgraph
        nlinarith
      have hcharge := NaturalSupportCharge.natural_graph_charge_epsilon
        p hp A R 1 1 ε hε
        (fun z hz => ⟨hBA (hR hz).1, hBA (hR hz).2.1⟩)
        (fun a ha => Nat.ne_of_gt (hpos a ha))
        (fun _ hz => (hR hz).2.2)
        (fun z hz => ⟨hcof _ (hR hz).1, hcof _ (hR hz).2.1⟩)
      have hsum : (R.image fun z => z.1 + z.2).card ≤ (A + A).card := by
        apply Finset.card_le_card
        intro n hn
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hn
        exact Finset.add_mem_add (hBA (hR hz).1) (hBA (hR hz).2.1)
      have hprod : (R.image fun z => z.1 * z.2).card ≤ (A * A).card := by
        apply Finset.card_le_card
        intro n hn
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hn
        exact Finset.mul_mem_mul (hBA (hR hz).1) (hBA (hR hz).2.1)
      have himages : ((R.image fun z => z.1 + z.2).card : ℝ) +
          4 * (R.image fun z => z.1 * z.2).card ≤ 4 * M := by
        have hs : ((R.image fun z => z.1 + z.2).card : ℝ) ≤ (A + A).card := by
          exact_mod_cast hsum
        have hp' : ((R.image fun z => z.1 * z.2).card : ℝ) ≤ (A * A).card := by
          exact_mod_cast hprod
        dsimp [M]
        nlinarith [show (0 : ℝ) ≤ (A + A).card by positivity]
      have hRbound : (R.card : ℝ) ≤ 4 * K * M := by
        calc
          _ ≤ K * ((R.image fun z => z.1 + z.2).card +
              4 * (R.image fun z => z.1 * z.2).card) := by simpa [K] using hcharge
          _ ≤ K * (4 * M) := mul_le_mul_of_nonneg_left himages hK0
          _ = _ := by ring
      calc
        (A.card : ℝ) ^ 2 ≤ 32 * (R.card : ℝ) := by exact_mod_cast hNmass
        _ ≤ 32 * (4 * K * M) := mul_le_mul_of_nonneg_left hRbound (by norm_num)
        _ ≤ 1296 * K * M := by nlinarith [mul_nonneg hK0 hM0]

/-- The conjectured exponent shape on the support-at-most-two positive-natural
class, with one positive epsilon-dependent constant before all finite sets. -/
theorem exists_constant :
    ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ C : ℝ, 0 < C ∧ ∀ A : Finset ℕ,
      (∀ a ∈ A, 0 < a) → (∀ a ∈ A, a.primeFactors.card ≤ 2) →
      (max (A + A).card (A * A).card : ℝ) ≥ C * (A.card : ℝ) ^ (2 - ε) := by
  intro ε hε hε1
  let D : ℝ := 165888 * Real.exp (9 / ε) * (2 : ℝ) ^ ε
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨1 / D, one_div_pos.mpr hD, ?_⟩
  intro A hpos hsize
  by_cases hzero : A.card = 0
  · rw [hzero, Nat.cast_zero, Real.zero_rpow (by linarith : 2 - ε ≠ 0), mul_zero]
    positivity
  have hN : (0 : ℝ) < A.card := by exact_mod_cast Nat.pos_of_ne_zero hzero
  let M : ℝ := max ((A + A).card : ℝ) ((A * A).card : ℝ)
  have hSP : ((A + A).card : ℝ) + (A * A).card ≤ 2 * M := by
    have hs : ((A + A).card : ℝ) ≤ M := le_max_left _ _
    have hp : ((A * A).card : ℝ) ≤ M := le_max_right _ _
    linarith
  have hfinite := quadratic_le_scaled_images A hpos hsize ε hε
  have hbound : (A.card : ℝ) ^ 2 ≤ D * (A.card : ℝ) ^ ε * M := by
    calc
      _ ≤ 82944 * Real.exp (9 / ε) * (2 * (A.card : ℝ)) ^ ε *
          ((A + A).card + (A * A).card) := hfinite
      _ ≤ 82944 * Real.exp (9 / ε) * (2 * (A.card : ℝ)) ^ ε * (2 * M) :=
        mul_le_mul_of_nonneg_left hSP (by positivity)
      _ = _ := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hN.le]
        dsimp [D]
        ring
  have hid : (A.card : ℝ) ^ ε * (A.card : ℝ) ^ (2 - ε) = (A.card : ℝ) ^ 2 := by
    rw [← Real.rpow_add hN]
    have he : ε + (2 - ε) = 2 := by ring
    rw [he, Real.rpow_ofNat]
  have hlinear : (A.card : ℝ) ^ (2 - ε) ≤ D * M := by
    apply (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hN ε)).mp
    calc
      _ = (A.card : ℝ) ^ 2 := hid
      _ ≤ D * (A.card : ℝ) ^ ε * M := hbound
      _ = _ := by ring
  change (1 / D) * (A.card : ℝ) ^ (2 - ε) ≤ M
  calc
    _ = (A.card : ℝ) ^ (2 - ε) / D := by ring
    _ ≤ M := (div_le_iff₀ hD).mpr (by simpa only [mul_comm] using hlinear)


end OmegaTwoBound

/- Audited component: OmegaTwoIntegerCoreDraft.lean; input SHA256 087c3c8d2a3416d4ec6f6663eec8fce951a87b19caeb2726c67c14cba86a218b. -/

/-!
Extract a positive natural core from the larger strict sign part of an integer
set. Absolute value is injective on that sign part and commutes with addition
there, while it commutes with multiplication everywhere. No unrestricted
sum-product hypothesis or theorem is imported.
-/

namespace IntegerCore

open Finset
open scoped Pointwise

/-- On a set of one weak sign, absolute value preserves vertex cardinality.
The exact sum and product image identities imply the two cardinal bounds. -/
theorem natAbs_same_sign_counts (T : Finset ℤ)
    (hsign : (∀ a ∈ T, 0 ≤ a) ∨ (∀ a ∈ T, a ≤ 0)) :
    (T.image Int.natAbs).card = T.card ∧
      (T.image Int.natAbs + T.image Int.natAbs).card ≤ (T + T).card ∧
      (T.image Int.natAbs * T.image Int.natAbs).card ≤ (T * T).card := by
  have hinj : Set.InjOn Int.natAbs (T : Set ℤ) := by
    intro a ha b hb heq
    rcases Int.natAbs_eq_natAbs_iff.mp heq with heq | heq
    · exact heq
    · rcases hsign with h | h
      · have ha0 := h a ha
        have hb0 := h b hb
        omega
      · have ha0 := h a ha
        have hb0 := h b hb
        omega
  have hadd : ∀ a ∈ T, ∀ b ∈ T,
      (a + b).natAbs = a.natAbs + b.natAbs := by
    intro a ha b hb
    rcases hsign with h | h
    · exact Int.natAbs_add_of_nonneg (h a ha) (h b hb)
    · exact Int.natAbs_add_of_nonpos (h a ha) (h b hb)
  have hsum : (T + T).image Int.natAbs = T.image Int.natAbs + T.image Int.natAbs := by
    ext n
    constructor
    · intro hn
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hn
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_add.mp hz
      rw [hadd a ha b hb]
      exact add_mem_add (mem_image_of_mem _ ha) (mem_image_of_mem _ hb)
    · intro hn
      obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.mp hn
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
      obtain ⟨b, hb, rfl⟩ := mem_image.mp hy
      exact mem_image.mpr ⟨a + b, add_mem_add ha hb, hadd a ha b hb⟩
  have hprod : (T * T).image Int.natAbs = T.image Int.natAbs * T.image Int.natAbs :=
    image_image₂_distrib Int.natAbs_mul
  refine ⟨card_image_of_injOn hinj, ?_, ?_⟩
  · rw [← hsum]
    exact card_image_le
  · rw [← hprod]
    exact card_image_le

/-- Every integer set of size at least two with at most two prime factors in
each absolute value has a positive natural core of at least one third its size.
The core has no larger sumset or product set and retains the support bound. -/
theorem positive_natural_core (A : Finset ℤ) (hn : 2 ≤ A.card)
    (hsize : ∀ a ∈ A, a.natAbs.primeFactors.card ≤ 2) :
    ∃ B : Finset ℕ, (∀ b ∈ B, 0 < b) ∧
      (∀ b ∈ B, b.primeFactors.card ≤ 2) ∧
      B.card ≤ A.card ∧ A.card ≤ 3 * B.card ∧
      (B + B).card ≤ (A + A).card ∧ (B * B).card ≤ (A * A).card := by
  classical
  let P := A.filter fun a => 0 < a
  let Q := A.filter fun a => a < 0
  have hPA : P ⊆ A := filter_subset _ _
  have hQA : Q ⊆ A := filter_subset _ _
  have hcover : A ⊆ P ∪ Q ∪ {0} := by
    intro a ha
    simp only [P, Q, mem_union, mem_filter, mem_singleton]
    rcases lt_trichotomy a 0 with h | h | h
    · exact Or.inl (Or.inr ⟨ha, h⟩)
    · exact Or.inr h
    · exact Or.inl (Or.inl ⟨ha, h⟩)
  have hcount : A.card ≤ P.card + Q.card + 1 := by
    calc
      A.card ≤ (P ∪ Q ∪ {0}).card := card_le_card hcover
      _ ≤ (P ∪ Q).card + ({0} : Finset ℤ).card := card_union_le _ _
      _ ≤ P.card + Q.card + 1 := by
        simpa only [card_singleton] using Nat.add_le_add_right (card_union_le P Q) 1
  have hpart : ∃ T : Finset ℤ, T ⊆ A ∧
      ((∀ a ∈ T, 0 < a) ∨ (∀ a ∈ T, a < 0)) ∧ A.card ≤ 3 * T.card := by
    rcases le_total Q.card P.card with hQP | hPQ
    · refine ⟨P, hPA, Or.inl (fun a ha => (mem_filter.mp ha).2), ?_⟩
      omega
    · refine ⟨Q, hQA, Or.inr (fun a ha => (mem_filter.mp ha).2), ?_⟩
      omega
  obtain ⟨T, hTA, hsign, hlarge⟩ := hpart
  have hweak : (∀ a ∈ T, 0 ≤ a) ∨ (∀ a ∈ T, a ≤ 0) := by
    rcases hsign with h | h
    · exact Or.inl fun a ha => (h a ha).le
    · exact Or.inr fun a ha => (h a ha).le
  obtain ⟨hc, hs, hp⟩ := natAbs_same_sign_counts T hweak
  refine ⟨T.image Int.natAbs, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hb
    apply Int.natAbs_pos.mpr
    rcases hsign with h | h
    · exact ne_of_gt (h a ha)
    · exact ne_of_lt (h a ha)
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hb
    exact hsize a (hTA ha)
  · rw [hc]
    exact card_le_card hTA
  · rwa [hc]
  · exact hs.trans (card_le_card (add_subset_add hTA hTA))
  · exact hp.trans (card_le_card (mul_subset_mul hTA hTA))


end IntegerCore

/- Audited component: OmegaTwoIntegerDraft.lean; input SHA256 6bc905e9eb79b8eff5df175a1a8587e6f49115d5be65991be2691e78cfe49cd3. -/


open scoped Pointwise

/-- Integer sum-product with the conjectured exponent, restricted to integers
whose absolute values each have at most two distinct prime factors. Zero,
negative integers and arbitrary prime powers are included. -/
theorem proof :
    ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ C : ℝ, 0 < C ∧ ∀ A : Finset ℤ,
      (∀ a ∈ A, a.natAbs.primeFactors.card ≤ 2) →
      (max (A + A).card (A * A).card : ℝ) ≥ C * (A.card : ℝ) ^ (2 - ε) := by
  intro ε hε hε1
  obtain ⟨c, hc, hnatural⟩ :=
    OmegaTwoBound.exists_constant ε hε hε1
  let D : ℝ := (3 : ℝ) ^ (2 - ε)
  let C : ℝ := min 1 (c / D)
  have hD : 0 < D := by dsimp [D]; positivity
  have hC : 0 < C := lt_min (by norm_num) (div_pos hc hD)
  have hC1 : C ≤ 1 := min_le_left _ _
  have hCD : C * D ≤ c := (le_div_iff₀ hD).mp (min_le_right _ _)
  refine ⟨C, hC, ?_⟩
  intro A hsize
  by_cases hsmall : A.card ≤ 1
  · by_cases hzero : A.card = 0
    · rw [hzero, Nat.cast_zero, Real.zero_rpow (by linarith : 2 - ε ≠ 0), mul_zero]
      positivity
    · have hone : A.card = 1 := by omega
      obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hone
      simpa only [Finset.singleton_add_singleton, Finset.singleton_mul_singleton,
        Finset.card_singleton, max_self, Nat.cast_one, Real.one_rpow, mul_one] using hC1
  · have hn : 2 ≤ A.card := by omega
    obtain ⟨B, hpos, hsupport, _hle, hmass, hsum, hprod⟩ :=
      IntegerCore.positive_natural_core A hn hsize
    have hB := hnatural B hpos hsupport
    have hM : (max (B + B).card (B * B).card : ℝ) ≤
        (max (A + A).card (A * A).card : ℝ) := by
      exact_mod_cast max_le_max hsum hprod
    have hpow : (A.card : ℝ) ^ (2 - ε) ≤ D * (B.card : ℝ) ^ (2 - ε) := by
      have h := Real.rpow_le_rpow (show (0 : ℝ) ≤ A.card by positivity)
        (show (A.card : ℝ) ≤ 3 * (B.card : ℝ) by exact_mod_cast hmass)
        (show 0 ≤ 2 - ε by linarith)
      simpa only [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3)
        (show (0 : ℝ) ≤ B.card by positivity), D] using h
    calc
      C * (A.card : ℝ) ^ (2 - ε) ≤ C * (D * (B.card : ℝ) ^ (2 - ε)) :=
        mul_le_mul_of_nonneg_left hpow hC.le
      _ = (C * D) * (B.card : ℝ) ^ (2 - ε) := by ring
      _ ≤ c * (B.card : ℝ) ^ (2 - ε) := mul_le_mul_of_nonneg_right hCD (by positivity)
      _ ≤ (max (B + B).card (B * B).card : ℝ) := hB
      _ ≤ (max (A + A).card (A * A).card : ℝ) := hM



#print axioms proof

end Submissions.Erdos52OmegaTwo.Finite
