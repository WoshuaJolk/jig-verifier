import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace Submissions.Erdos1159FourSecant.Moments

open Finset
open scoped BigOperators

namespace IncidenceCounts


variable {Point Line : Type*} [Fintype Line]
  (I : Point → Line → Prop) [DecidableRel I] (q : ℕ)

theorem first_moment
    (degree : ∀ p : Point, (univ.filter fun l => I p l).card = q + 1)
    (S : Finset Point) :
    (∑ l : Line, (S.filter fun p => I p l).card) = S.card * (q + 1) := by
  classical
  calc
    _ = ∑ p ∈ S, (univ.filter fun l => I p l).card := by
      simpa only [bipartiteAbove, bipartiteBelow] using
        (sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow I
          (s := S) (t := univ)).symm
    _ = S.card * (q + 1) := by simp [degree]

theorem common_lines [DecidableEq Point]
    (degree : ∀ p : Point, (univ.filter fun l => I p l).card = q + 1)
    (join : ∀ p r : Point, p ≠ r → ∃ l : Line, I p l ∧ I r l)
    (unique : ∀ p r : Point, ∀ l m : Line, p ≠ r →
      I p l → I r l → I p m → I r m → l = m)
    (p r : Point) :
    (univ.filter fun l => I p l ∧ I r l).card = if p = r then q + 1 else 1 := by
  classical
  by_cases h : p = r
  · subst r
    simpa using degree p
  · rw [if_neg h]
    obtain ⟨l, hlp, hlr⟩ := join p r h
    apply card_eq_one.mpr
    refine ⟨l, ?_⟩
    ext m
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · rintro ⟨hmp, hmr⟩
      exact (unique p r l m h hlp hlr hmp hmr).symm
    · intro hm
      subst m
      exact ⟨hlp, hlr⟩

theorem second_moment
    (degree : ∀ p : Point, (univ.filter fun l => I p l).card = q + 1)
    (join : ∀ p r : Point, p ≠ r → ∃ l : Line, I p l ∧ I r l)
    (unique : ∀ p r : Point, ∀ l m : Line, p ≠ r →
      I p l → I r l → I p m → I r m → l = m)
    (S : Finset Point) :
    (∑ l : Line, (S.filter fun p => I p l).card ^ 2) =
      S.card * (S.card + q) := by
  classical
  have expand (l : Line) :
      (S.filter fun p => I p l).card ^ 2 =
        ∑ p ∈ S, ∑ r ∈ S, if I p l ∧ I r l then 1 else 0 := by
    simp_rw [card_eq_sum_ones, sum_filter, pow_two, sum_mul, mul_sum]
    apply sum_congr rfl
    intro p hp
    apply sum_congr rfl
    intro r hr
    by_cases hpl : I p l <;> by_cases hrl : I r l <;> simp [hpl, hrl]
  calc
    _ = ∑ l : Line, ∑ p ∈ S, ∑ r ∈ S, if I p l ∧ I r l then 1 else 0 := by
      exact sum_congr rfl fun l _ => expand l
    _ = ∑ p ∈ S, ∑ r ∈ S, ∑ l : Line, if I p l ∧ I r l then 1 else 0 := by
      rw [sum_comm]
      apply sum_congr rfl
      intro p hp
      rw [sum_comm]
    _ = ∑ p ∈ S, ∑ r ∈ S, (univ.filter fun l => I p l ∧ I r l).card := by
      simp_rw [card_eq_sum_ones, sum_filter]
    _ = ∑ p ∈ S, ∑ r ∈ S, if p = r then q + 1 else 1 := by
      simp_rw [common_lines I q degree join unique]
    _ = ∑ p ∈ S, (S.card + q) := by
      apply sum_congr rfl
      intro p hp
      have split (r : Point) :
          (if p = r then q + 1 else 1) = (if p = r then q else 0) + 1 := by
        by_cases h : p = r <;> simp [h]
      simp_rw [split, sum_add_distrib]
      simp [hp, Nat.add_comm]
    _ = S.card * (S.card + q) := by simp

theorem line_count [Fintype Point] [Nonempty Line]
    (lineDegree : ∀ l : Line, (univ.filter fun p => I p l).card = q + 1)
    (pointDegree : ∀ p : Point, (univ.filter fun l => I p l).card = q + 1)
    (join : ∀ p r : Point, p ≠ r → ∃ l : Line, I p l ∧ I r l)
    (unique : ∀ p r : Point, ∀ l m : Line, p ≠ r →
      I p l → I r l → I p m → I r m → l = m) :
    Fintype.card Line = q * q + q + 1 := by
  classical
  have hfirst := first_moment I q pointDegree (univ : Finset Point)
  simp only [lineDegree, sum_const, card_univ, nsmul_eq_mul] at hfirst
  have hcard : Fintype.card Line = Fintype.card Point :=
    Nat.eq_of_mul_eq_mul_right (Nat.succ_pos q) hfirst
  have hsecond := second_moment I q pointDegree join unique (univ : Finset Point)
  simp only [lineDegree, sum_const, card_univ, nsmul_eq_mul] at hsecond
  rw [← hcard] at hsecond
  have heq : (q + 1) ^ 2 = Fintype.card Line + q :=
    Nat.eq_of_mul_eq_mul_left (Fintype.card_pos) hsecond
  nlinarith only [heq]


end IncidenceCounts



/-- The first two incidence moments force the blocking-set size into a quadratic interval. -/
theorem moment_bound {Line : Type*} [Fintype Line] (t : Line → ℕ) (n q C : ℕ)
    (hfirst : ∑ l, t l = n * (q + 1))
    (hsecond : ∑ l, t l * t l = n * (n + q))
    (hblock : ∀ l, 1 ≤ t l ∧ t l ≤ C) :
    n * n + C * Fintype.card Line ≤ (C * q + C + 1) * n := by
  have hpoint (l : Line) : t l * t l + C ≤ (C + 1) * t l := by
    have ht := Nat.sub_add_cancel (hblock l).1
    have hm := Nat.mul_le_mul_left (t l - 1) (hblock l).2
    nlinarith
  have hs := Finset.sum_le_sum (fun l (_ : l ∈ (univ : Finset Line)) => hpoint l)
  simp only [sum_add_distrib, sum_const, card_univ, Nat.nsmul_eq_mul, ← mul_sum,
    hfirst, hsecond] at hs
  nlinarith

/-- For q ≥ 5 the quadratic interval is empty at cap 3. -/
theorem cap_three_impossible (n q : ℕ) (hq : 5 ≤ q)
    (h : n * n + 3 * (q * q + q + 1) ≤ (3 * q + 3 + 1) * n) : False := by
  have hh : (n : ℤ) * n + 3 * (q * q + q + 1) ≤ (3 * q + 3 + 1) * n := by
    exact_mod_cast h
  have hq' : (5 : ℤ) ≤ q := by exact_mod_cast hq
  nlinarith [sq_nonneg (2 * (n : ℤ) - (3 * q + 4)), sq_nonneg ((q : ℤ) - 5)]



theorem proof :
  ∀ (Point Line : Type) [Fintype Point] [Fintype Line] [Nonempty Line]
    (I : Point → Line → Prop) [DecidableRel I] (q : ℕ),
    5 ≤ q →
    (∀ l : Line, (Finset.univ.filter fun p => I p l).card = q + 1) →
    (∀ p : Point, (Finset.univ.filter fun l => I p l).card = q + 1) →
    (∀ p r : Point, p ≠ r → ∃ l : Line, I p l ∧ I r l) →
    (∀ p r : Point, ∀ l m : Line, p ≠ r →
      I p l → I r l → I p m → I r m → l = m) →
    (∀ l m : Line, l ≠ m → ∃ p : Point, I p l ∧ I p m) →
    (∀ l m : Line, ∀ p r : Point, l ≠ m →
      I p l → I p m → I r l → I r m → p = r) →
    ∀ S : Finset Point,
      (∀ l : Line, 1 ≤ (S.filter fun p => I p l).card) →
      ∃ l : Line, 4 ≤ (S.filter fun p => I p l).card := by
  intro Point Line _ _ _ I _ q hq lineDegree pointDegree join unique _ _ S hblock
  classical
  by_contra hn
  have hupper (l : Line) : (S.filter fun p => I p l).card ≤ 3 :=
    Nat.le_of_lt_succ (Nat.lt_of_not_ge (not_exists.mp hn l))
  have hm := moment_bound (fun l : Line => (S.filter fun p => I p l).card)
    S.card q 3 (IncidenceCounts.first_moment I q pointDegree S)
    (by simpa only [pow_two] using IncidenceCounts.second_moment I q pointDegree join unique S)
    (fun l => ⟨hblock l, hupper l⟩)
  rw [IncidenceCounts.line_count I q lineDegree pointDegree join unique] at hm
  exact cap_three_impossible S.card q hq hm

end Submissions.Erdos1159FourSecant.Moments
