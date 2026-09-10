import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic.Linarith

/-
Standalone conditional counting reduction for the triple case of Jig #333.
Drafted without executing Lean. This does not prove the required structural
hypotheses for every avoiding family and does not resolve the original problem.

The pair universe and both incidence counts are defined from the actual family.
The two double-counting identities are proved below, not assumed.
No other submission or canonical statement is imported.
-/

namespace Submissions.Erdos643CoreCountingCriterion.Main

open scoped BigOperators

/-- Every member of the actual family is a three-element set. -/
def Uniform3 {n : ℕ} (F : Finset (Finset (Fin n))) : Prop :=
  ∀ E ∈ F, E.card = 3

/-- Every unordered pair of distinct ambient vertices, including uncovered pairs. -/
def allPairs (n : ℕ) : Finset (Finset (Fin n)) :=
  Finset.powersetCard 2 Finset.univ

/-- Vertices outside a pair whose insertion gives a member of F. -/
def extensionSet {n : ℕ} (F : Finset (Finset (Fin n)))
    (p : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun x => x ∉ p ∧ insert x p ∈ F

def codegree {n : ℕ} (F : Finset (Finset (Fin n)))
    (p : Finset (Fin n)) : ℕ :=
  (extensionSet F p).card

/-- Pair witnesses extending both vertices of the center pair p. -/
def commonLinkCount {n : ℕ} (F : Finset (Finset (Fin n)))
    (p : Finset (Fin n)) : ℕ :=
  ((allPairs n).filter fun w => p ⊆ extensionSet F w).card

@[simp] theorem mem_allPairs {n : ℕ} {p : Finset (Fin n)} :
    p ∈ allPairs n ↔ p.card = 2 := by
  simp [allPairs, Finset.mem_powersetCard]

@[simp] theorem card_allPairs (n : ℕ) :
    (allPairs n).card = Nat.choose n 2 := by
  simp [allPairs]

@[simp] theorem mem_extensionSet {n : ℕ}
    {F : Finset (Finset (Fin n))} {p : Finset (Fin n)} {x : Fin n} :
    x ∈ extensionSet F p ↔ x ∉ p ∧ insert x p ∈ F := by
  simp [extensionSet]

private theorem filter_allPairs_subset {n : ℕ} (s : Finset (Fin n)) :
    (allPairs n).filter (fun p => p ⊆ s) = Finset.powersetCard 2 s := by
  ext p
  simp only [Finset.mem_filter, mem_allPairs, Finset.mem_powersetCard]
  exact and_comm

/-- For a genuine pair, insertion bijects extensions with containing triples. -/
theorem codegree_eq_card_containing {n : ℕ}
    {F : Finset (Finset (Fin n))} (hF : Uniform3 F)
    {p : Finset (Fin n)} (hp : p.card = 2) :
    codegree F p = (F.filter fun E => p ⊆ E).card := by
  unfold codegree
  refine Finset.card_bij (fun x _ => insert x p) ?_ ?_ ?_
  · intro x hx
    obtain ⟨hxp, hxF⟩ := mem_extensionSet.mp hx
    exact Finset.mem_filter.mpr ⟨hxF, Finset.subset_insert x p⟩
  · intro x hx y hy hxy
    exact (Finset.insert_inj (mem_extensionSet.mp hx).1).mp hxy
  · intro E hE
    obtain ⟨hEF, hpE⟩ := Finset.mem_filter.mp hE
    have hEc : E.card = 3 := hF E hEF
    obtain ⟨x, hxE, hxp⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (show p.card < E.card by omega)
    have hIc : (insert x p).card = 3 := by
      rw [Finset.card_insert_of_notMem hxp, hp]
    have hI : insert x p = E := Finset.eq_of_subset_of_card_le
      (Finset.insert_subset_iff.mpr ⟨hxE, hpE⟩) (by omega)
    have hx : x ∈ extensionSet F p := by
      apply mem_extensionSet.mpr
      refine ⟨hxp, ?_⟩
      simpa only [hI] using hEF
    exact ⟨x, hx, hI⟩

/-- The actual pair–triple incidence count, including all ambient pairs. -/
theorem sum_codegree {n : ℕ} {F : Finset (Finset (Fin n))}
    (hF : Uniform3 F) :
    (∑ p ∈ allPairs n, codegree F p) = 3 * F.card := by
  calc
    (∑ p ∈ allPairs n, codegree F p) =
        ∑ p ∈ allPairs n, (F.filter fun E => p ⊆ E).card := by
      apply Finset.sum_congr rfl
      intro p hp
      exact codegree_eq_card_containing hF (mem_allPairs.mp hp)
    _ = ∑ E ∈ F, ((allPairs n).filter fun p => p ⊆ E).card := by
      simpa only [Finset.bipartiteAbove, Finset.bipartiteBelow] using
        (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
          (fun (p E : Finset (Fin n)) => p ⊆ E) (s := allPairs n) (t := F))
    _ = ∑ E ∈ F, Nat.choose E.card 2 := by
      apply Finset.sum_congr rfl
      intro E hE
      rw [filter_allPairs_subset, Finset.card_powersetCard]
    _ = ∑ _E ∈ F, 3 := by
      apply Finset.sum_congr rfl
      intro E hE
      norm_num [hF E hE]
    _ = 3 * F.card := by simp [Nat.mul_comm]

/-- Count center-pair/witness-pair incidences in the two directions. -/
theorem sum_commonLinkCount {n : ℕ} (F : Finset (Finset (Fin n))) :
    (∑ p ∈ allPairs n, commonLinkCount F p) =
      ∑ w ∈ allPairs n, Nat.choose (codegree F w) 2 := by
  calc
    (∑ p ∈ allPairs n, commonLinkCount F p) =
        ∑ w ∈ allPairs n,
          ((allPairs n).filter fun p => p ⊆ extensionSet F w).card := by
      simpa only [commonLinkCount, Finset.bipartiteAbove, Finset.bipartiteBelow] using
        (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
          (fun (p w : Finset (Fin n)) => p ⊆ extensionSet F w)
          (s := allPairs n) (t := allPairs n))
    _ = ∑ w ∈ allPairs n, Nat.choose (codegree F w) 2 := by
      apply Finset.sum_congr rfl
      intro w hw
      simp only [filter_allPairs_subset, Finset.card_powersetCard, codegree]

private theorem twice_choose_two (d : ℕ) :
    2 * (Nat.choose d 2 : ℤ) = (d : ℤ) * ((d : ℤ) - 1) := by
  induction d with
  | zero => norm_num
  | succ d ih =>
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
      simp only [Nat.cast_add, Nat.cast_succ]
      nlinarith

private theorem choose_two_ge_three_mul_sub_six (d : ℕ) :
    3 * (d : ℤ) - 6 ≤ (Nat.choose d 2 : ℤ) := by
  have hprod : 0 ≤ ((d : ℤ) - 3) * ((d : ℤ) - 4) := by
    by_cases hd : d ≤ 3
    · have hz : (d : ℤ) ≤ 3 := by exact_mod_cast hd
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    · have hz : (4 : ℤ) ≤ (d : ℤ) := by
        exact_mod_cast (show 4 ≤ d by omega)
      exact mul_nonneg (by linarith) (by linarith)
  nlinarith [twice_choose_two d]

private theorem choose_two_ge_two_mul_sub_three (d : ℕ) :
    2 * (d : ℤ) - 3 ≤ (Nat.choose d 2 : ℤ) := by
  have hprod : 0 ≤ ((d : ℤ) - 2) * ((d : ℤ) - 3) := by
    by_cases hd : d ≤ 2
    · have hz : (d : ℤ) ≤ 2 := by exact_mod_cast hd
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    · have hz : (3 : ℤ) ≤ (d : ℤ) := by
        exact_mod_cast (show 3 ≤ d by omega)
      exact mul_nonneg (by linarith) (by linarith)
  nlinarith [twice_choose_two d]

/-- A sufficient structural criterion for the exact finite triple upper bound.
Avoidance is not assumed here: establishing the two numeric hypotheses from
avoidance is the separate mathematical obligation. -/
theorem card_le_choose_of_core_counting {n : ℕ}
    (F : Finset (Finset (Fin n))) (hF : Uniform3 F)
    (C : Finset (Finset (Fin n))) (hC : C ⊆ allPairs n)
    (hCore : (∑ p ∈ C, commonLinkCount F p) ≤ ∑ p ∈ C, codegree F p)
    (hOutside : ∀ p ∈ allPairs n, p ∉ C → commonLinkCount F p ≤ 3) :
    F.card ≤ Nat.choose n 2 := by
  let B := allPairs n \ C
  have hsplit (f : Finset (Fin n) → ℤ) :
      (∑ p ∈ B, f p) + (∑ p ∈ C, f p) = ∑ p ∈ allPairs n, f p :=
    Finset.sum_sdiff hC
  have hcard : (B.card : ℤ) + (C.card : ℤ) = (Nat.choose n 2 : ℤ) := by
    have hn : B.card + C.card = Nat.choose n 2 := by
      change (allPairs n \ C).card + C.card = Nat.choose n 2
      rw [Finset.card_sdiff_add_card_eq_card hC, card_allPairs]
    exact_mod_cast hn
  have hcoreZ : (∑ p ∈ C, (commonLinkCount F p : ℤ)) ≤
      ∑ p ∈ C, (codegree F p : ℤ) := by
    exact_mod_cast hCore
  have hd : (∑ p ∈ B, (codegree F p : ℤ)) +
      (∑ p ∈ C, (codegree F p : ℤ)) = 3 * (F.card : ℤ) := by
    rw [hsplit]
    exact_mod_cast sum_codegree hF
  have hq : (∑ p ∈ B, (Nat.choose (codegree F p) 2 : ℤ)) +
      (∑ p ∈ C, (Nat.choose (codegree F p) 2 : ℤ)) =
      (∑ p ∈ B, (commonLinkCount F p : ℤ)) +
      (∑ p ∈ C, (commonLinkCount F p : ℤ)) := by
    rw [hsplit, hsplit]
    exact_mod_cast (sum_commonLinkCount F).symm
  have hlowC : 3 * (∑ p ∈ C, (codegree F p : ℤ)) - 6 * (C.card : ℤ) ≤
      ∑ p ∈ C, (Nat.choose (codegree F p) 2 : ℤ) := by
    have h := Finset.sum_le_sum (fun p (_hp : p ∈ C) =>
      choose_two_ge_three_mul_sub_six (codegree F p))
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, nsmul_eq_mul] at h
    nlinarith
  have hlowB : 2 * (∑ p ∈ B, (codegree F p : ℤ)) - 3 * (B.card : ℤ) ≤
      ∑ p ∈ B, (Nat.choose (codegree F p) 2 : ℤ) := by
    have h := Finset.sum_le_sum (fun p (_hp : p ∈ B) =>
      choose_two_ge_two_mul_sub_three (codegree F p))
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, nsmul_eq_mul] at h
    nlinarith
  have huppB : (∑ p ∈ B, (commonLinkCount F p : ℤ)) ≤ 3 * (B.card : ℤ) := by
    calc
      _ ≤ ∑ _p ∈ B, (3 : ℤ) := by
        apply Finset.sum_le_sum
        intro p hp
        have hp' : p ∈ allPairs n ∧ p ∉ C := Finset.mem_sdiff.mp hp
        exact_mod_cast hOutside p hp'.1 hp'.2
      _ = 3 * (B.card : ℤ) := by simp [mul_comm]
  have hm : (F.card : ℤ) ≤ (Nat.choose n 2 : ℤ) := by
    nlinarith
  exact_mod_cast hm

end Submissions.Erdos643CoreCountingCriterion.Main
