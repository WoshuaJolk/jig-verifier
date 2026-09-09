import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.BigOperators.Group.Finset

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

namespace Submissions.Erdos52CommonPrimeQuery.Finite

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

end Submissions.Erdos52CommonPrimeQuery.Finite
