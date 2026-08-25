import Mathlib


/-! Flattened from Erdos788.Definitions. -/


/-!
# Exact finite formulation of Erdős Problem 788

The original paper defines `f(n)` as the largest *integer* with a universal
property.  We first maximize over natural numbers and then embed the result in
`ℤ`.  The final equivalence in this file proves that this is exactly the
integer maximum from the problem statement, including its quantifier order.
-/

namespace Erdos788

/-- The integer interval `I_n = (n, 2n) ∩ ℕ`. -/
def I (n : ℕ) : Finset ℕ :=
  Finset.Ioo n (2 * n)

/-- The integer interval `J_n = (2n, 4n) ∩ ℕ`. -/
def J (n : ℕ) : Finset ℕ :=
  Finset.Ioo (2 * n) (4 * n)

/-- `C` is `B`-admissible: it lies in `I n`, and no sum of two distinct
members of `C` belongs to `B`.  The assumption `B ⊆ J n` stays at the outer
quantifier, exactly as in the original definition. -/
def Admissible (n : ℕ) (B C : Finset ℕ) : Prop :=
  C ⊆ I n ∧
    ∀ ⦃c⦄, c ∈ C → ∀ ⦃c'⦄, c' ∈ C → c ≠ c' → c + c' ∉ B

/-- The natural-number form of the universal guarantee at threshold `t`. -/
def Guarantees (n t : ℕ) : Prop :=
  ∀ B : Finset ℕ, B ⊆ J n →
    ∃ C : Finset ℕ, Admissible n B C ∧ t ≤ B.card + C.card

/-- A uniform finite upper bound for every score `|B| + |C|`. -/
def scoreBound (n : ℕ) : ℕ :=
  (J n).card + (I n).card

theorem guarantees_zero (n : ℕ) : Guarantees n 0 := by
  intro B _hB
  refine ⟨∅, ?_, by simp⟩
  simp [Admissible]

theorem guarantees_le_scoreBound {n t : ℕ} (h : Guarantees n t) :
    t ≤ scoreBound n := by
  obtain ⟨C, hC, ht⟩ := h (J n) (by simp)
  exact ht.trans (Nat.add_le_add_left (Finset.card_le_card hC.1) _)

/-- The largest natural-number threshold with the universal property. -/
noncomputable def fNat (n : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (Guarantees n) (scoreBound n)

theorem fNat_guarantees (n : ℕ) : Guarantees n (fNat n) := by
  classical
  exact Nat.findGreatest_spec (Nat.zero_le _) (guarantees_zero n)

theorem le_fNat {n t : ℕ} (h : Guarantees n t) : t ≤ fNat n := by
  classical
  exact Nat.le_findGreatest (guarantees_le_scoreBound h) h

/-- The integer-valued function `f(n)` in the original problem. -/
noncomputable def f (n : ℕ) : ℤ :=
  (fNat n : ℤ)

/-- The paper's universal guarantee predicate for an arbitrary integer `t`. -/
def IntegerGuarantees (n : ℕ) (t : ℤ) : Prop :=
  ∀ B : Finset ℕ, B ⊆ J n →
    ∃ C : Finset ℕ, Admissible n B C ∧
      t ≤ ((B.card + C.card : ℕ) : ℤ)

theorem f_integerGuarantees (n : ℕ) : IntegerGuarantees n (f n) := by
  intro B hB
  obtain ⟨C, hC, hscore⟩ := fNat_guarantees n B hB
  refine ⟨C, hC, ?_⟩
  simpa [f] using (Int.ofNat_le.mpr hscore)

theorem integerGuarantees_le_f {n : ℕ} {t : ℤ}
    (h : IntegerGuarantees n t) : t ≤ f n := by
  by_cases ht : t ≤ 0
  · exact ht.trans (by simp [f])
  · have ht0 : 0 ≤ t := le_of_lt (lt_of_not_ge ht)
    let u : ℕ := t.toNat
    have hu_cast : (u : ℤ) = t := Int.toNat_of_nonneg ht0
    have hu : Guarantees n u := by
      intro B hB
      obtain ⟨C, hC, hscore⟩ := h B hB
      refine ⟨C, hC, ?_⟩
      exact_mod_cast (hu_cast ▸ hscore)
    have huf : u ≤ fNat n := le_fNat hu
    simpa [f, hu_cast] using (Int.ofNat_le.mpr huf)

/-- `f n` is the greatest integer having the universal guarantee. -/
theorem f_isGreatestIntegerGuarantee (n : ℕ) :
    IntegerGuarantees n (f n) ∧
      ∀ t : ℤ, IntegerGuarantees n t → t ≤ f n :=
  ⟨f_integerGuarantees n, fun _t ht ↦ integerGuarantees_le_f ht⟩

/-- An integer has the universal guarantee exactly when it is at most `f n`. -/
theorem integerGuarantees_iff_le_f {n : ℕ} {t : ℤ} :
    IntegerGuarantees n t ↔ t ≤ f n := by
  constructor
  · exact integerGuarantees_le_f
  · intro htf B hB
    obtain ⟨C, hC, hscore⟩ := f_integerGuarantees n B hB
    exact ⟨C, hC, htf.trans hscore⟩

end Erdos788


/-! Flattened from Erdos788.GraphFormulation. -/


/-!
# Exact graph formulation

This file proves the admissibility/independence correspondence and the exact
finite min--max identity from Section 2 of the paper.
-/

namespace Erdos788

open Finset

/-- The finite vertex type corresponding exactly to `I n`. -/
abbrev Vertex (n : ℕ) := {x : ℕ // x ∈ I n}

/-- Join two distinct elements of `I n` exactly when their sum belongs to
the palette `B`. -/
def paletteGraph (n : ℕ) (B : Finset ℕ) : SimpleGraph (Vertex n) :=
  SimpleGraph.fromRel fun x y ↦ x.1 + y.1 ∈ B

@[simp]
theorem paletteGraph_adj {n : ℕ} {B : Finset ℕ} {x y : Vertex n} :
    (paletteGraph n B).Adj x y ↔ x ≠ y ∧ x.1 + y.1 ∈ B := by
  simp [paletteGraph, add_comm]

/-- Forget the proofs that the vertices lie in `I n`. -/
def forgetVertices {n : ℕ} (C : Finset (Vertex n)) : Finset ℕ :=
  C.map ⟨Subtype.val, Subtype.val_injective⟩

@[simp]
theorem card_forgetVertices {n : ℕ} (C : Finset (Vertex n)) :
    (forgetVertices C).card = C.card := by
  simp [forgetVertices]

/-- Lift a finset contained in `I n` to the finite vertex type. -/
def liftVertices {n : ℕ} (C : Finset ℕ) (hC : C ⊆ I n) :
    Finset (Vertex n) :=
  C.attach.map
    { toFun := fun x ↦ ⟨x.1, hC x.2⟩
      inj' := by
        intro x y h
        apply Subtype.ext
        exact congrArg (fun z : Vertex n ↦ z.1) h }

@[simp]
theorem card_liftVertices {n : ℕ} (C : Finset ℕ) (hC : C ⊆ I n) :
    (liftVertices C hC).card = C.card := by
  simp [liftVertices]

/-- An independent vertex finset gives an admissible integer finset. -/
theorem admissible_forgetVertices {n : ℕ} {B : Finset ℕ}
    {D : Finset (Vertex n)}
    (hD : (paletteGraph n B).IsIndepSet (D : Set (Vertex n))) :
    Admissible n B (forgetVertices D) := by
  classical
  constructor
  · intro x hx
    rw [forgetVertices, mem_map] at hx
    obtain ⟨v, _hv, rfl⟩ := hx
    exact v.2
  · intro x hx y hy hxy hsum
    rw [forgetVertices, mem_map] at hx hy
    obtain ⟨v, hv, rfl⟩ := hx
    obtain ⟨w, hw, rfl⟩ := hy
    have hvw : v ≠ w := fun e ↦ hxy (congrArg Subtype.val e)
    exact hD hv hw hvw (paletteGraph_adj.mpr ⟨hvw, hsum⟩)

/-- An admissible integer finset gives an independent vertex finset. -/
theorem isIndepSet_liftVertices {n : ℕ} {B C : Finset ℕ}
    (hC : Admissible n B C) :
    (paletteGraph n B).IsIndepSet
      (liftVertices C hC.1 : Set (Vertex n)) := by
  classical
  intro v hv w hw hvw hadj
  change v ∈ liftVertices C hC.1 at hv
  change w ∈ liftVertices C hC.1 at hw
  rw [liftVertices, mem_map] at hv hw
  obtain ⟨x, hx, rfl⟩ := hv
  obtain ⟨y, hy, rfl⟩ := hw
  have hxy : x.1 ≠ y.1 := fun e ↦ hvw (Subtype.ext e)
  exact hC.2 x.2 y.2 hxy (paletteGraph_adj.mp hadj).2

/-- The score attached to one palette in the graph formulation. -/
noncomputable def graphScore (n : ℕ) (B : Finset ℕ) : ℕ :=
  B.card + (paletteGraph n B).indepNum

/-- A threshold has the original universal property exactly when it is at
most every graph score. -/
theorem guarantees_iff_forall_le_graphScore {n t : ℕ} :
    Guarantees n t ↔
      ∀ B : Finset ℕ, B ⊆ J n → t ≤ graphScore n B := by
  constructor
  · intro h B hB
    obtain ⟨C, hC, ht⟩ := h B hB
    have hInd := isIndepSet_liftVertices hC
    have hcard : C.card ≤ (paletteGraph n B).indepNum := by
      rw [← card_liftVertices C hC.1]
      exact hInd.card_le_indepNum
    exact ht.trans (Nat.add_le_add_left hcard B.card)
  · intro h B hB
    obtain ⟨D, hD⟩ := (paletteGraph n B).exists_isNIndepSet_indepNum
    refine ⟨forgetVertices D, admissible_forgetVertices hD.isIndepSet, ?_⟩
    simpa [graphScore, hD.card_eq] using h B hB

/-- The nonempty finite set of graph scores over all palettes in `J n`. -/
noncomputable def graphScores (n : ℕ) : Finset ℕ :=
  (J n).powerset.image (graphScore n)

theorem graphScores_nonempty (n : ℕ) : (graphScores n).Nonempty := by
  classical
  refine ⟨graphScore n ∅, ?_⟩
  exact mem_image.mpr ⟨∅, by simp, rfl⟩

/-- The right side of the finite min--max formula. -/
noncomputable def minGraphScore (n : ℕ) : ℕ :=
  (graphScores n).min' (graphScores_nonempty n)

theorem minGraphScore_le {n : ℕ} {B : Finset ℕ} (hB : B ⊆ J n) :
    minGraphScore n ≤ graphScore n B := by
  classical
  apply min'_le
  exact mem_image.mpr ⟨B, mem_powerset.mpr hB, rfl⟩

theorem exists_graphScore_eq_minGraphScore (n : ℕ) :
    ∃ B : Finset ℕ, B ⊆ J n ∧ graphScore n B = minGraphScore n := by
  classical
  have hmem := min'_mem (graphScores n) (graphScores_nonempty n)
  change minGraphScore n ∈ (J n).powerset.image (graphScore n) at hmem
  rw [mem_image] at hmem
  obtain ⟨B, hB, hscore⟩ := hmem
  exact ⟨B, mem_powerset.mp hB, hscore⟩

theorem guarantees_iff_le_minGraphScore {n t : ℕ} :
    Guarantees n t ↔ t ≤ minGraphScore n := by
  rw [guarantees_iff_forall_le_graphScore]
  constructor
  · intro h
    obtain ⟨B, hB, hscore⟩ := exists_graphScore_eq_minGraphScore n
    simpa [hscore] using h B hB
  · intro h B hB
    exact h.trans (minGraphScore_le hB)

/-- Proposition 2.1: the largest natural guarantee is the minimum graph
score over all palettes. -/
theorem fNat_eq_minGraphScore (n : ℕ) : fNat n = minGraphScore n := by
  apply le_antisymm
  · exact guarantees_iff_le_minGraphScore.mp (fNat_guarantees n)
  · exact le_fNat (guarantees_iff_le_minGraphScore.mpr le_rfl)

/-- Integer-valued form of the exact min--max identity. -/
theorem f_eq_minGraphScore (n : ℕ) : f n = (minGraphScore n : ℤ) := by
  simp [f, fNat_eq_minGraphScore]

end Erdos788


/-! Flattened from Erdos788.NormalizedGraph. -/


/-!
# Normalized sum graphs

The paper translates `I n` to `0, ..., n - 2`.  This file introduces the
corresponding graph on `Fin N` and proves the basic maximum-degree estimate.
-/

namespace Erdos788

open Finset

/-- The normalized sum graph on `0, ..., N - 1`. -/
def sumGraph (N : ℕ) (A : Finset ℕ) : SimpleGraph (Fin N) :=
  SimpleGraph.fromRel fun x y ↦ x.1 + y.1 ∈ A

@[simp]
theorem sumGraph_adj {N : ℕ} {A : Finset ℕ} {x y : Fin N} :
    (sumGraph N A).Adj x y ↔ x ≠ y ∧ x.1 + y.1 ∈ A := by
  simp [sumGraph, add_comm]

noncomputable instance sumGraphDecidableAdj (N : ℕ) (A : Finset ℕ) :
    DecidableRel (sumGraph N A).Adj :=
  Classical.decRel _

/-- Admissibility in normalized coordinates. -/
def NormalizedAdmissible {N : ℕ} (A : Finset ℕ)
    (C : Finset (Fin N)) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, x ≠ y → x.1 + y.1 ∉ A

theorem normalizedAdmissible_iff_isIndepSet
    {N : ℕ} {A : Finset ℕ} {C : Finset (Fin N)} :
    NormalizedAdmissible A C ↔
      (sumGraph N A).IsIndepSet (C : Set (Fin N)) := by
  rw [SimpleGraph.isIndepSet_iff]
  simp only [Set.Pairwise, Finset.mem_coe]
  constructor
  · intro h x hx y hy hxy
    exact sumGraph_adj.mp.mt fun hadj ↦ h x hx y hy hxy hadj.2
  · intro h x hx y hy hxy hsum
    exact h hx hy hxy (sumGraph_adj.mpr ⟨hxy, hsum⟩)

/-- Adding a fixed vertex to the vertex label is injective. -/
def addEmbedding {N : ℕ} (x : Fin N) : Fin N ↪ ℕ where
  toFun y := x.1 + y.1
  inj' := by
    intro y z h
    apply Fin.ext
    exact Nat.add_left_cancel h

/-- Equation (2.1): each selected sum supplies at most one neighbor of a
fixed vertex. -/
theorem degree_sumGraph_le_card {N : ℕ} (A : Finset ℕ) (x : Fin N) :
    (sumGraph N A).degree x ≤ A.card := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  rw [← card_map (addEmbedding x)]
  apply card_le_card
  intro s hs
  rw [mem_map] at hs
  obtain ⟨y, hy, rfl⟩ := hs
  have hadj : (sumGraph N A).Adj x y :=
    (SimpleGraph.mem_neighborFinset (G := sumGraph N A) (v := x) y).mp hy
  exact (sumGraph_adj.mp hadj).2

theorem maxDegree_sumGraph_le_card {N : ℕ} (A : Finset ℕ) :
    (sumGraph N A).maxDegree ≤ A.card := by
  exact SimpleGraph.maxDegree_le_of_forall_degree_le (G := sumGraph N A)
    A.card (degree_sumGraph_le_card A)

end Erdos788


/-! Flattened from Erdos788.TriangleCounting. -/


/-!
# Triangle counting and neighborhood incidence for normalized sum graphs

This module formalizes the triangle injection and the exact local and global
incidence identities used in the lower-bound argument.
-/

namespace Erdos788

open Finset

def pairSums {N : ℕ} (t : Finset (Fin N)) : Finset ℕ :=
  t.offDiag.image fun xy ↦ xy.1.1 + xy.2.1

theorem triple_pairSums {N : ℕ} {x y z : Fin N}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    pairSums {x, y, z} = {x.1 + y.1, x.1 + z.1, y.1 + z.1} := by
  classical
  ext q
  simp only [pairSums, mem_image, mem_offDiag, mem_insert, mem_singleton,
    Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨ha, hb, hab⟩, rfl⟩
    rcases ha with (rfl | rfl | rfl) <;>
      rcases hb with (rfl | rfl | rfl) <;>
      simp_all [add_comm]
  · rintro (rfl | rfl | rfl)
    · exact ⟨x, y, ⟨by simp, by simp, hxy⟩, rfl⟩
    · exact ⟨x, z, ⟨by simp, by simp, hxz⟩, rfl⟩
    · exact ⟨y, z, ⟨by simp, by simp, hyz⟩, rfl⟩

theorem card_pairSums_of_three {N : ℕ} {t : Finset (Fin N)} (ht : t.card = 3) :
    (pairSums t).card = 3 := by
  classical
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := card_eq_three.mp ht
  rw [triple_pairSums hxy hxz hyz]
  have hxy_xz : x.1 + y.1 ≠ x.1 + z.1 := by
    intro h
    exact hyz (Fin.ext (Nat.add_left_cancel h))
  have hxz_yz : x.1 + z.1 ≠ y.1 + z.1 := by
    intro h
    exact hxy (Fin.ext (Nat.add_right_cancel h))
  have hxy_yz : x.1 + y.1 ≠ y.1 + z.1 := by
    intro h
    have : x.1 = z.1 := by omega
    exact hxz (Fin.ext this)
  exact card_eq_three.mpr
    ⟨x.1 + y.1, x.1 + z.1, y.1 + z.1, hxy_xz, hxy_yz, hxz_yz, rfl⟩

theorem triple_eq_of_pairSum_finsets_eq
    {x y z u v w : ℕ}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (h : ({x + y, x + z, y + z} : Finset ℕ) =
      ({u + v, u + w, v + w} : Finset ℕ)) :
    ({x, y, z} : Finset ℕ) = {u, v, w} := by
  classical
  have hxy_xz : x + y ≠ x + z := fun e ↦ hyz (Nat.add_left_cancel e)
  have hxy_yz : x + y ≠ y + z := by omega
  have hxz_yz : x + z ≠ y + z := fun e ↦ hxy (Nat.add_right_cancel e)
  have huv_uw : u + v ≠ u + w := fun e ↦ hvw (Nat.add_left_cancel e)
  have huv_vw : u + v ≠ v + w := by omega
  have huw_vw : u + w ≠ v + w := fun e ↦ huv (Nat.add_right_cancel e)
  have hxy_not : x + y ∉ ({x + z, y + z} : Finset ℕ) := by
    simp only [mem_insert, mem_singleton, not_or]
    exact ⟨hxy_xz, hxy_yz⟩
  have hxz_not : x + z ∉ ({y + z} : Finset ℕ) := by
    simpa only [mem_singleton, not_false_eq_true] using hxz_yz
  have huv_not : u + v ∉ ({u + w, v + w} : Finset ℕ) := by
    simp only [mem_insert, mem_singleton, not_or]
    exact ⟨huv_uw, huv_vw⟩
  have huw_not : u + w ∉ ({v + w} : Finset ℕ) := by
    simpa only [mem_singleton, not_false_eq_true] using huw_vw
  have hsum_left :
      (∑ a ∈ ({x + y, x + z, y + z} : Finset ℕ), a) =
        (x + y) + (x + z) + (y + z) := by
    rw [sum_insert hxy_not, sum_insert hxz_not, sum_singleton]
    simp only [Nat.add_assoc]
  have hsum_right :
      (∑ a ∈ ({u + v, u + w, v + w} : Finset ℕ), a) =
        (u + v) + (u + w) + (v + w) := by
    rw [sum_insert huv_not, sum_insert huw_not, sum_singleton]
    simp only [Nat.add_assoc]
  have hpairs := congrArg (fun s : Finset ℕ ↦ ∑ a ∈ s, a) h
  rw [hsum_left, hsum_right] at hpairs
  have htotal : x + y + z = u + v + w := by omega
  apply Finset.Subset.antisymm
  · intro q hq
    simp only [mem_insert, mem_singleton] at hq ⊢
    rcases hq with (rfl | rfl | rfl)
    · have hm : y + z ∈ ({u + v, u + w, v + w} : Finset ℕ) := by
        rw [← h]
        simp
      simp only [mem_insert, mem_singleton] at hm
      rcases hm with (hm | hm | hm) <;> omega
    · have hm : x + z ∈ ({u + v, u + w, v + w} : Finset ℕ) := by
        rw [← h]
        simp
      simp only [mem_insert, mem_singleton] at hm
      rcases hm with (hm | hm | hm) <;> omega
    · have hm : x + y ∈ ({u + v, u + w, v + w} : Finset ℕ) := by
        rw [← h]
        simp
      simp only [mem_insert, mem_singleton] at hm
      rcases hm with (hm | hm | hm) <;> omega
  · intro q hq
    simp only [mem_insert, mem_singleton] at hq ⊢
    rcases hq with (rfl | rfl | rfl)
    · have hm : v + w ∈ ({x + y, x + z, y + z} : Finset ℕ) := by
        rw [h]
        simp
      simp only [mem_insert, mem_singleton] at hm
      rcases hm with (hm | hm | hm) <;> omega
    · have hm : u + w ∈ ({x + y, x + z, y + z} : Finset ℕ) := by
        rw [h]
        simp
      simp only [mem_insert, mem_singleton] at hm
      rcases hm with (hm | hm | hm) <;> omega
    · have hm : u + v ∈ ({x + y, x + z, y + z} : Finset ℕ) := by
        rw [h]
        simp
      simp only [mem_insert, mem_singleton] at hm
      rcases hm with (hm | hm | hm) <;> omega

theorem pairSums_mem_powersetCard_of_is3Clique
    {N : ℕ} {A : Finset ℕ} {t : Finset (Fin N)}
    (ht : (sumGraph N A).IsNClique 3 t) :
    pairSums t ∈ A.powersetCard 3 := by
  classical
  rw [mem_powersetCard]
  constructor
  · intro q hq
    rw [pairSums, mem_image] at hq
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := hq
    rw [mem_offDiag] at hxy
    exact (sumGraph_adj.mp (ht.isClique hxy.1 hxy.2.1 hxy.2.2)).2
  · exact card_pairSums_of_three ht.card_eq

theorem pairSums_injOn_card_three {N : ℕ} :
    Set.InjOn pairSums {t : Finset (Fin N) | t.card = 3} := by
  classical
  intro t ht u hu htu
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := card_eq_three.mp ht
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.mp hu
  rw [triple_pairSums hxy hxz hyz, triple_pairSums hab hac hbc] at htu
  have hvals : ({x.1, y.1, z.1} : Finset ℕ) = {a.1, b.1, c.1} :=
    triple_eq_of_pairSum_finsets_eq
      (fun h ↦ hxy (Fin.ext h)) (fun h ↦ hxz (Fin.ext h))
      (fun h ↦ hyz (Fin.ext h)) (fun h ↦ hab (Fin.ext h))
      (fun h ↦ hac (Fin.ext h)) (fun h ↦ hbc (Fin.ext h)) htu
  apply Finset.map_injective Fin.valEmbedding
  simpa using hvals

/-- Lemma 3.1 of the paper: triangles inject into the three-element subsets
of the selected sum palette. -/
theorem triangle_count_le_choose {N : ℕ} (A : Finset ℕ) :
    ((sumGraph N A).cliqueFinset 3).card ≤ A.card.choose 3 := by
  classical
  rw [← card_powersetCard 3 A]
  refine card_le_card_of_injOn pairSums ?_ ?_
  · intro t ht
    exact pairSums_mem_powersetCard_of_is3Clique
      (SimpleGraph.mem_cliqueFinset_iff.mp (by simpa only [Finset.mem_coe] using ht))
  · intro t ht u hu htu
    apply pairSums_injOn_card_three
    · exact (SimpleGraph.mem_cliqueFinset_iff.mp
        (by simpa only [Finset.mem_coe] using ht)).card_eq
    · exact (SimpleGraph.mem_cliqueFinset_iff.mp
        (by simpa only [Finset.mem_coe] using hu)).card_eq
    · exact htu

section TriangleIncidence

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Edges spanned by the neighborhood of `v`, represented as two-cliques. -/
def neighborhoodEdges (v : V) : Finset (Finset V) :=
  (G.cliqueFinset 2).filter fun e ↦ ∀ x ∈ e, G.Adj v x

/-- Triangles containing `v`. -/
def trianglesAt (v : V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter fun t ↦ v ∈ t

@[simp]
theorem mem_neighborhoodEdges {v : V} {e : Finset V} :
    e ∈ neighborhoodEdges G v ↔
      G.IsNClique 2 e ∧ ∀ x ∈ e, G.Adj v x := by
  simp [neighborhoodEdges]

@[simp]
theorem mem_trianglesAt {v : V} {t : Finset V} :
    t ∈ trianglesAt G v ↔ G.IsNClique 3 t ∧ v ∈ t := by
  simp [trianglesAt]

theorem insert_mem_trianglesAt_of_mem_neighborhoodEdges
    {v : V} {e : Finset V} (he : e ∈ neighborhoodEdges G v) :
    insert v e ∈ trianglesAt G v := by
  rw [mem_neighborhoodEdges] at he
  rw [mem_trianglesAt]
  have hvnot : v ∉ e := fun hv ↦ G.loopless.irrefl v (he.2 v hv)
  constructor
  · constructor
    · simpa only [Finset.coe_insert] using
        he.1.isClique.insert (fun x hx _hvx ↦ he.2 x hx)
    · rw [card_insert_of_notMem hvnot, he.1.card_eq]
  · exact mem_insert_self v e

theorem erase_mem_neighborhoodEdges_of_mem_trianglesAt
    {v : V} {t : Finset V} (ht : t ∈ trianglesAt G v) :
    t.erase v ∈ neighborhoodEdges G v := by
  rw [mem_trianglesAt] at ht
  rw [mem_neighborhoodEdges]
  constructor
  · constructor
    · exact ht.1.isClique.subset (erase_subset v t)
    · rw [card_erase_of_mem ht.2, ht.1.card_eq]
  · intro x hx
    exact ht.1.isClique ht.2 (mem_of_mem_erase hx) (mem_erase.mp hx).1.symm

/-- Exact local incidence identity: the number of triangles through a vertex
is the number of graph edges spanned by its neighborhood. -/
theorem card_trianglesAt_eq_card_neighborhoodEdges (v : V) :
    (trianglesAt G v).card = (neighborhoodEdges G v).card := by
  apply Nat.le_antisymm
  · refine card_le_card_of_injOn (fun t ↦ t.erase v) ?_ ?_
    · intro t ht
      exact erase_mem_neighborhoodEdges_of_mem_trianglesAt G
        (by simpa only [Finset.mem_coe] using ht)
    · intro t ht u hu htu
      have htv : v ∈ t := ((mem_trianglesAt G).mp
        (by simpa only [Finset.mem_coe] using ht)).2
      have huv : v ∈ u := ((mem_trianglesAt G).mp
        (by simpa only [Finset.mem_coe] using hu)).2
      change t.erase v = u.erase v at htu
      calc
        t = insert v (t.erase v) := (insert_erase htv).symm
        _ = insert v (u.erase v) := congrArg (insert v) htu
        _ = u := insert_erase huv
  · refine card_le_card_of_injOn (fun e ↦ insert v e) ?_ ?_
    · intro e he
      exact insert_mem_trianglesAt_of_mem_neighborhoodEdges G
        (by simpa only [Finset.mem_coe] using he)
    · intro e he f hf hef
      have hev : v ∉ e := by
        have he' : e ∈ neighborhoodEdges G v := by
          simpa only [Finset.mem_coe] using he
        rw [mem_neighborhoodEdges] at he'
        exact fun hv ↦ G.loopless.irrefl v (he'.2 v hv)
      have hfv : v ∉ f := by
        have hf' : f ∈ neighborhoodEdges G v := by
          simpa only [Finset.mem_coe] using hf
        rw [mem_neighborhoodEdges] at hf'
        exact fun hv ↦ G.loopless.irrefl v (hf'.2 v hv)
      simpa [hev, hfv] using congrArg (Finset.erase · v) hef

/-- Exact global incidence identity: counting triangle--vertex incidences by
vertices or by triangles gives `sum_v t_v = 3 T`. -/
theorem sum_card_trianglesAt :
    (∑ v : V, (trianglesAt G v).card) =
      3 * (G.cliqueFinset 3).card := by
  classical
  calc
    (∑ v : V, (trianglesAt G v).card) =
        ∑ v : V, ∑ t ∈ G.cliqueFinset 3, if v ∈ t then 1 else 0 := by
      apply sum_congr rfl
      intro v _hv
      rw [trianglesAt, card_eq_sum_ones, sum_filter]
    _ = ∑ t ∈ G.cliqueFinset 3, ∑ v : V, if v ∈ t then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ t ∈ G.cliqueFinset 3, t.card := by
      apply sum_congr rfl
      intro t _ht
      simp
    _ = ∑ _t ∈ G.cliqueFinset 3, 3 := by
      apply sum_congr rfl
      intro t ht
      exact (SimpleGraph.mem_cliqueFinset_iff.mp ht).card_eq
    _ = 3 * (G.cliqueFinset 3).card := by
      simp [Nat.mul_comm]

end TriangleIncidence

/-- For a sum graph, the total number of neighborhood edges is bounded by
three times the number of three-element palette subsets.  This is the exact
finite inequality used before the averaging step in the paper. -/
theorem sum_card_neighborhoodEdges_sumGraph_le {N : ℕ} (A : Finset ℕ) :
    (∑ v : Fin N, (neighborhoodEdges (sumGraph N A) v).card) ≤
      3 * A.card.choose 3 := by
  calc
    (∑ v : Fin N, (neighborhoodEdges (sumGraph N A) v).card) =
        ∑ v : Fin N, (trianglesAt (sumGraph N A) v).card := by
      apply sum_congr rfl
      intro v _hv
      exact (card_trianglesAt_eq_card_neighborhoodEdges (sumGraph N A) v).symm
    _ = 3 * ((sumGraph N A).cliqueFinset 3).card :=
      sum_card_trianglesAt (sumGraph N A)
    _ ≤ 3 * A.card.choose 3 :=
      Nat.mul_le_mul_left 3 (triangle_count_le_choose A)

section FiniteAveraging

variable {W : Type*} [Fintype W]

/-- Vertices whose value is at most twice the average, written without
division so that the definition also behaves correctly on empty types. -/
noncomputable def averageGood (t : W → ℕ) : Finset W := by
  classical
  exact Finset.univ.filter fun w ↦
    Fintype.card W * t w ≤ 2 * ∑ u : W, t u

/-- At least half the points have value at most twice the average.  The
conclusion is in the division-free form `|W| ≤ 2 |good|`. -/
theorem card_le_twice_card_averageGood (t : W → ℕ) :
    Fintype.card W ≤ 2 * (averageGood t).card := by
  classical
  let total : ℕ := ∑ w : W, t w
  let good : Finset W := averageGood t
  let bad : Finset W := Finset.univ.filter fun w ↦
    ¬(Fintype.card W * t w ≤ 2 * total)
  have hpart : good.card + bad.card = Fintype.card W := by
    simpa only [good, bad, averageGood, total, card_univ] using
      (card_filter_add_card_filter_not
        (s := (Finset.univ : Finset W))
        (fun w ↦ Fintype.card W * t w ≤ 2 * ∑ u : W, t u))
  have hpoint : ∀ w ∈ bad,
      2 * total + 1 ≤ Fintype.card W * t w := by
    intro w hw
    have hnle := (mem_filter.mp hw).2
    exact Nat.succ_le_iff.mpr (lt_of_not_ge hnle)
  have hsum :
      ∑ w ∈ bad, (2 * total + 1) ≤
        ∑ w ∈ bad, Fintype.card W * t w := by
    exact sum_le_sum fun w hw ↦ hpoint w hw
  have hbadSum : ∑ w ∈ bad, t w ≤ total := by
    exact sum_le_sum_of_subset (filter_subset _ _)
  have hbad : bad.card * (2 * total + 1) ≤ Fintype.card W * total := by
    calc
      bad.card * (2 * total + 1) = ∑ _w ∈ bad, (2 * total + 1) := by
        simp [Nat.mul_comm]
      _ ≤ ∑ w ∈ bad, Fintype.card W * t w := hsum
      _ = Fintype.card W * ∑ w ∈ bad, t w := by
        simp [Finset.mul_sum]
      _ ≤ Fintype.card W * total := Nat.mul_le_mul_left _ hbadSum
  by_contra hgood
  have hgood' : ¬(Fintype.card W ≤ 2 * good.card) := by
    simpa only [good] using hgood
  have hcardlt : 2 * good.card < Fintype.card W := lt_of_not_ge hgood'
  have hbadpos : 0 < bad.card := by omega
  have hNS : Fintype.card W * total ≤ (2 * bad.card) * total := by
    apply Nat.mul_le_mul_right total
    omega
  have hstrict : (2 * bad.card) * total < bad.card * (2 * total + 1) := by
    calc
      (2 * bad.card) * total = bad.card * (2 * total) := by
        simp [Nat.mul_assoc, Nat.mul_comm]
      _ < bad.card * (2 * total + 1) :=
        (Nat.mul_lt_mul_left hbadpos).mpr (Nat.lt_succ_self (2 * total))
  exact (not_lt_of_ge hbad) (hNS.trans_lt hstrict)

end FiniteAveraging

theorem six_mul_choose_three_le_cube (b : ℕ) :
    6 * b.choose 3 ≤ b ^ 3 := by
  calc
    6 * b.choose 3 = Nat.factorial 3 * b.choose 3 := by rfl
    _ = b.descFactorial 3 := (Nat.descFactorial_eq_factorial_mul_choose b 3).symm
    _ ≤ b ^ 3 := Nat.descFactorial_le_pow b 3

noncomputable section

/-- The division-free predicate saying that a vertex has at most twice the
average number of edges in its neighborhood. -/
def SumGraphGood (N : ℕ) (A : Finset ℕ) (v : Fin N) : Prop :=
  N * (neighborhoodEdges (sumGraph N A) v).card ≤
    2 * ∑ u : Fin N, (neighborhoodEdges (sumGraph N A) u).card

noncomputable instance sumGraphGoodDecidablePred (N : ℕ) (A : Finset ℕ) :
    DecidablePred (SumGraphGood N A) :=
  Classical.decPred _

/-- Good vertices after the triangle-incidence averaging step. -/
def sumGraphGoodVertices (N : ℕ) (A : Finset ℕ) : Finset (Fin N) :=
  Finset.univ.filter (SumGraphGood N A)

@[simp]
theorem mem_sumGraphGoodVertices {N : ℕ} {A : Finset ℕ} {v : Fin N} :
    v ∈ sumGraphGoodVertices N A ↔ SumGraphGood N A v := by
  simp [sumGraphGoodVertices]

theorem card_le_twice_card_sumGraphGoodVertices (N : ℕ) (A : Finset ℕ) :
    N ≤ 2 * (sumGraphGoodVertices N A).card := by
  have hgood : sumGraphGoodVertices N A =
      averageGood
        (fun v : Fin N ↦ (neighborhoodEdges (sumGraph N A) v).card) := by
    ext v
    simp [sumGraphGoodVertices, averageGood, SumGraphGood]
  rw [hgood]
  simpa using card_le_twice_card_averageGood
    (t := fun v : Fin N ↦ (neighborhoodEdges (sumGraph N A) v).card)

theorem half_le_card_sumGraphGoodVertices (N : ℕ) (A : Finset ℕ) :
    N / 2 ≤ (sumGraphGoodVertices N A).card := by
  have h := card_le_twice_card_sumGraphGoodVertices N A
  omega

theorem good_vertex_mul_local_le_cube_of_good
    {N : ℕ} {A : Finset ℕ} {v : Fin N} (hv : SumGraphGood N A v) :
    N * (neighborhoodEdges (sumGraph N A) v).card ≤ A.card ^ 3 := by
  calc
    N * (neighborhoodEdges (sumGraph N A) v).card ≤
        2 * ∑ u : Fin N, (neighborhoodEdges (sumGraph N A) u).card :=
      hv
    _ ≤ 2 * (3 * A.card.choose 3) :=
      Nat.mul_le_mul_left 2 (sum_card_neighborhoodEdges_sumGraph_le A)
    _ = 6 * A.card.choose 3 := by omega
    _ ≤ A.card ^ 3 := six_mul_choose_three_le_cube A.card

theorem good_vertex_mul_local_le_cube {N : ℕ} {A : Finset ℕ} {v : Fin N}
    (hv : v ∈ sumGraphGoodVertices N A) :
    N * (neighborhoodEdges (sumGraph N A) v).card ≤ A.card ^ 3 :=
  good_vertex_mul_local_le_cube_of_good (mem_sumGraphGoodVertices.mp hv)

theorem good_vertex_local_le_cube_div {N : ℕ} {A : Finset ℕ} {v : Fin N}
    (hN : 0 < N) (hv : v ∈ sumGraphGoodVertices N A) :
    (neighborhoodEdges (sumGraph N A) v).card ≤ A.card ^ 3 / N := by
  apply (Nat.le_div_iff_mul_le hN).2
  simpa [Nat.mul_comm] using good_vertex_mul_local_le_cube hv

section InducedNeighborhoodEdges

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (s : Set V) [DecidablePred (· ∈ s)]

def mapSubtypeFinsetEmbedding : Finset s ↪ Finset V where
  toFun e := e.map (Function.Embedding.subtype s)
  inj' := Finset.map_injective _

theorem map_neighborhoodEdges_induce_subset (v : s) :
    (neighborhoodEdges (G.induce s) v).map (mapSubtypeFinsetEmbedding s) ⊆
      neighborhoodEdges G v.1 := by
  intro e he
  rw [mem_map] at he
  obtain ⟨e, he, rfl⟩ := he
  rw [mem_neighborhoodEdges] at he ⊢
  constructor
  · exact he.1.map.mono (G.spanningCoe_induce_le s)
  · intro x hx
    change x ∈ e.map (Function.Embedding.subtype s) at hx
    rw [mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact SimpleGraph.induce_adj.mp (he.2 y hy)

theorem card_neighborhoodEdges_induce_le (v : s) :
    (neighborhoodEdges (G.induce s) v).card ≤
      (neighborhoodEdges G v.1).card := by
  calc
    (neighborhoodEdges (G.induce s) v).card =
        ((neighborhoodEdges (G.induce s) v).map
          (mapSubtypeFinsetEmbedding s)).card :=
      (card_map (mapSubtypeFinsetEmbedding s)).symm
    _ ≤ (neighborhoodEdges G v.1).card :=
      card_le_card (map_neighborhoodEdges_induce_subset G s v)

theorem degree_induce_le (v : s) :
    (G.induce s).degree v ≤ G.degree v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    ← SimpleGraph.card_neighborFinset_eq_degree]
  calc
    ((G.induce s).neighborFinset v).card =
        (((G.induce s).neighborFinset v).map
          (Function.Embedding.subtype s)).card :=
      (card_map (Function.Embedding.subtype s)).symm
    _ = (G.neighborFinset v.1 ∩ s.toFinset).card :=
      congrArg Finset.card (G.map_neighborFinset_induce v)
    _ ≤ (G.neighborFinset v.1).card :=
      card_le_card inter_subset_left

end InducedNeighborhoodEdges

abbrev SumGraphGoodVertex (N : ℕ) (A : Finset ℕ) :=
  {v : Fin N // SumGraphGood N A v}

/-- The induced graph on the vertices retained by averaging. -/
abbrev goodInducedSumGraph (N : ℕ) (A : Finset ℕ) :
    SimpleGraph (SumGraphGoodVertex N A) :=
  (sumGraph N A).induce {v | SumGraphGood N A v}

@[simp]
theorem goodInducedSumGraph_adj {N : ℕ} {A : Finset ℕ}
    {u v : SumGraphGoodVertex N A} :
    (goodInducedSumGraph N A).Adj u v ↔ (sumGraph N A).Adj u.1 v.1 := by
  exact SimpleGraph.induce_adj

@[simp]
theorem card_sumGraphGoodVertex (N : ℕ) (A : Finset ℕ) :
    Fintype.card (SumGraphGoodVertex N A) = (sumGraphGoodVertices N A).card := by
  simpa [SumGraphGoodVertex, sumGraphGoodVertices] using
    Fintype.card_subtype (SumGraphGood N A)

theorem half_le_card_sumGraphGoodVertex (N : ℕ) (A : Finset ℕ) :
    N / 2 ≤ Fintype.card (SumGraphGoodVertex N A) := by
  rw [card_sumGraphGoodVertex]
  exact half_le_card_sumGraphGoodVertices N A

theorem goodInduced_mul_local_le_cube {N : ℕ} {A : Finset ℕ}
    (v : SumGraphGoodVertex N A) :
    N * (neighborhoodEdges
      ((sumGraph N A).induce {v | SumGraphGood N A v}) v).card ≤
        A.card ^ 3 := by
  calc
    N * (neighborhoodEdges
        ((sumGraph N A).induce {v | SumGraphGood N A v}) v).card ≤
        N * (neighborhoodEdges (sumGraph N A) v.1).card :=
      Nat.mul_le_mul_left N
        (card_neighborhoodEdges_induce_le (sumGraph N A)
          {v | SumGraphGood N A v} v)
    _ ≤ A.card ^ 3 := good_vertex_mul_local_le_cube_of_good v.2

theorem goodInduced_local_le_cube_div {N : ℕ} {A : Finset ℕ}
    (hN : 0 < N) (v : SumGraphGoodVertex N A) :
    (neighborhoodEdges
      ((sumGraph N A).induce {v | SumGraphGood N A v}) v).card ≤
        A.card ^ 3 / N := by
  apply (Nat.le_div_iff_mul_le hN).2
  simpa [Nat.mul_comm] using goodInduced_mul_local_le_cube v

theorem degree_goodInducedSumGraph_le {N : ℕ} {A : Finset ℕ}
    (v : SumGraphGoodVertex N A) :
    ((sumGraph N A).induce
      {v | SumGraphGood N A v}).degree v ≤ A.card := by
  exact (degree_induce_le (sumGraph N A)
    {v | SumGraphGood N A v} v).trans
      (degree_sumGraph_le_card A v.1)

/-- Forget that vertices lie in the good-vertex subtype. -/
def liftGoodVertexFinset {N : ℕ} {A : Finset ℕ}
    (C : Finset (SumGraphGoodVertex N A)) : Finset (Fin N) :=
  C.map (Function.Embedding.subtype {v | SumGraphGood N A v})

@[simp]
theorem card_liftGoodVertexFinset {N : ℕ} {A : Finset ℕ}
    (C : Finset (SumGraphGoodVertex N A)) :
    (liftGoodVertexFinset C).card = C.card := by
  exact card_map _

theorem isIndepSet_liftGoodVertexFinset
    {N : ℕ} {A : Finset ℕ} {C : Finset (SumGraphGoodVertex N A)}
    (hC : (goodInducedSumGraph N A).IsIndepSet
      (C : Set (SumGraphGoodVertex N A))) :
    (sumGraph N A).IsIndepSet (liftGoodVertexFinset C : Set (Fin N)) := by
  rw [SimpleGraph.isIndepSet_iff] at hC ⊢
  intro x hx y hy hxy
  change x ∈ liftGoodVertexFinset C at hx
  change y ∈ liftGoodVertexFinset C at hy
  rw [liftGoodVertexFinset, mem_map] at hx hy
  obtain ⟨x, hx, rfl⟩ := hx
  obtain ⟨y, hy, rfl⟩ := hy
  have hxy' : x ≠ y := by
    intro h
    exact hxy (congrArg Subtype.val h)
  exact hC (by simpa using hx) (by simpa using hy) hxy'

theorem normalizedAdmissible_liftGoodVertexFinset
    {N : ℕ} {A : Finset ℕ} {C : Finset (SumGraphGoodVertex N A)}
    (hC : (goodInducedSumGraph N A).IsIndepSet
      (C : Set (SumGraphGoodVertex N A))) :
    NormalizedAdmissible A (liftGoodVertexFinset C) :=
  normalizedAdmissible_iff_isIndepSet.mpr
    (isIndepSet_liftGoodVertexFinset hC)

theorem indepNum_goodInducedSumGraph_le (N : ℕ) (A : Finset ℕ) :
    (goodInducedSumGraph N A).indepNum ≤ (sumGraph N A).indepNum := by
  obtain ⟨C, hC⟩ := SimpleGraph.exists_isNIndepSet_indepNum
    (G := goodInducedSumGraph N A)
  calc
    (goodInducedSumGraph N A).indepNum = C.card := hC.card_eq.symm
    _ = (liftGoodVertexFinset C).card := (card_liftGoodVertexFinset C).symm
    _ ≤ (sumGraph N A).indepNum :=
      (isIndepSet_liftGoodVertexFinset hC.isIndepSet).card_le_indepNum

end

end Erdos788


/-! Flattened from Erdos788.SparseNeighborhood. -/


namespace Erdos788

open Finset

section Families

variable {V : Type*} [DecidableEq V]

/-- Members of a finite family which are contained in `S`. -/
def containedCount (F : Finset (Finset V)) (S : Finset V) : ℕ :=
  (F.filter ( · ⊆ S)).card

@[simp]
theorem containedCount_empty (S : Finset V) : containedCount ∅ S = 0 := by
  simp [containedCount]

theorem sum_powerset_containedCount
    {U : Finset V} {F : Finset (Finset V)} {k : ℕ}
    (hFsub : ∀ e ∈ F, e ⊆ U)
    (hFcard : ∀ e ∈ F, e.card = k) :
    ∑ S ∈ U.powerset, containedCount F S =
      F.card * 2 ^ (U.card - k) := by
  classical
  have hcount (S : Finset V) :
      containedCount F S = ∑ e ∈ F, if e ⊆ S then 1 else 0 := by
    rw [containedCount, card_eq_sum_ones, sum_filter]
  simp_rw [hcount]
  rw [sum_comm]
  calc
    (∑ e ∈ F, ∑ S ∈ U.powerset, if e ⊆ S then 1 else 0) =
        ∑ _e ∈ F, 2 ^ (U.card - k) := by
      apply sum_congr rfl
      intro e he
      rw [sum_boole]
      change ((U.powerset).filter (e ⊆ ·)).card = _
      rw [← Icc_eq_filter_powerset, card_Icc_finset (hFsub e he), hFcard e he]
    _ = F.card * 2 ^ (U.card - k) := by simp

theorem pow_mul_sum_powerset_containedCount
    {U : Finset V} {F : Finset (Finset V)} {k : ℕ}
    (hFsub : ∀ e ∈ F, e ⊆ U)
    (hFcard : ∀ e ∈ F, e.card = k) :
    2 ^ k * (∑ S ∈ U.powerset, containedCount F S) =
      2 ^ U.card * F.card := by
  rw [sum_powerset_containedCount hFsub hFcard]
  by_cases hF : F = ∅
  · simp [hF]
  · have hFn : F.Nonempty := nonempty_iff_ne_empty.mpr hF
    obtain ⟨e, he⟩ := hFn
    have hk : k ≤ U.card := by
      rw [← hFcard e he]
      exact card_le_card (hFsub e he)
    have hp : 2 ^ k * 2 ^ (U.card - k) = 2 ^ U.card := by
      rw [← pow_add, Nat.add_sub_of_le hk]
    calc
      2 ^ k * (F.card * 2 ^ (U.card - k)) =
          F.card * (2 ^ k * 2 ^ (U.card - k)) := by ac_rfl
      _ = F.card * 2 ^ U.card := by rw [hp]
      _ = 2 ^ U.card * F.card := by ac_rfl

def singletonFamily (U : Finset V) : Finset (Finset V) :=
  U.image ({·} : V → Finset V)

@[simp]
theorem card_singletonFamily (U : Finset V) :
    (singletonFamily U).card = U.card := by
  rw [singletonFamily, card_image_of_injective]
  intro x y h
  simpa using h

theorem singletonFamily_sub (U : Finset V) :
    ∀ e ∈ singletonFamily U, e ⊆ U := by
  intro e he
  rw [singletonFamily, mem_image] at he
  obtain ⟨v, hv, rfl⟩ := he
  simpa using hv

theorem singletonFamily_card_one (U : Finset V) :
    ∀ e ∈ singletonFamily U, e.card = 1 := by
  intro e he
  rw [singletonFamily, mem_image] at he
  obtain ⟨v, _hv, rfl⟩ := he
  simp

theorem containedCount_singletonFamily {U S : Finset V} (hS : S ⊆ U) :
    containedCount (singletonFamily U) S = S.card := by
  classical
  have heq : (singletonFamily U).filter ( · ⊆ S) = singletonFamily S := by
    ext e
    simp only [singletonFamily, mem_filter, mem_image]
    constructor
    · rintro ⟨⟨v, hvU, rfl⟩, hvS⟩
      exact ⟨v, hvS (mem_singleton_self v), rfl⟩
    · rintro ⟨v, hvS, rfl⟩
      exact ⟨⟨v, hS hvS, rfl⟩, by simpa⟩
  rw [containedCount, heq, card_singletonFamily]

/-- Restrict a family of finite subsets to those contained in `S`. -/
def restrictFamily (F : Finset (Finset V)) (S : Finset V) : Finset (Finset V) :=
  F.filter (· ⊆ S)

@[simp]
theorem card_restrictFamily (F : Finset (Finset V)) (S : Finset V) :
    (restrictFamily F S).card = containedCount F S := by
  rfl

theorem restrictFamily_sub (F : Finset (Finset V)) (S : Finset V) :
    ∀ e ∈ restrictFamily F S, e ⊆ S := by
  simp [restrictFamily]

theorem restrictFamily_card {F : Finset (Finset V)} {S : Finset V} {k : ℕ}
    (hFcard : ∀ e ∈ F, e.card = k) :
  ∀ e ∈ restrictFamily F S, e.card = k := by
  intro e he
  exact hFcard e (mem_filter.mp he).1

theorem containedCount_restrictFamily {F : Finset (Finset V)} {R S : Finset V}
    (hRS : R ⊆ S) :
    containedCount (restrictFamily F S) R = containedCount F R := by
  simp only [containedCount, restrictFamily]
  congr 1
  ext e
  simp only [mem_filter]
  constructor
  · exact fun h ↦ ⟨h.1.1, h.2⟩
  · exact fun h ↦ ⟨⟨h.1, fun x hx ↦ hRS (h.2 hx)⟩, h.2⟩

/-- A linear score for a sampled subset, penalizing contained two- and
three-element features. -/
def subsetScore (a c d : ℚ) (F₂ F₃ : Finset (Finset V))
    (S : Finset V) : ℚ :=
  a * S.card - c * containedCount F₂ S - d * containedCount F₃ S

/-- One Bernoulli-halving step, proved by averaging over the powerset. -/
theorem exists_subset_score_ge_half
    (U : Finset V) (F₂ F₃ : Finset (Finset V))
    (hF₂sub : ∀ e ∈ F₂, e ⊆ U) (hF₂card : ∀ e ∈ F₂, e.card = 2)
    (hF₃sub : ∀ e ∈ F₃, e ⊆ U) (hF₃card : ∀ e ∈ F₃, e.card = 3)
    (a c d : ℚ) :
    ∃ S ∈ U.powerset,
      a * U.card / 2 - c * F₂.card / 4 - d * F₃.card / 8 ≤
        subsetScore a c d F₂ F₃ S := by
  classical
  have h₁n := pow_mul_sum_powerset_containedCount
    (singletonFamily_sub U) (singletonFamily_card_one U)
  have h₁count :
      (∑ S ∈ U.powerset, containedCount (singletonFamily U) S) =
        ∑ S ∈ U.powerset, S.card := by
    apply sum_congr rfl
    intro S hS
    exact containedCount_singletonFamily (mem_powerset.mp hS)
  rw [h₁count] at h₁n
  norm_num at h₁n
  have h₂n := pow_mul_sum_powerset_containedCount hF₂sub hF₂card
  have h₃n := pow_mul_sum_powerset_containedCount hF₃sub hF₃card
  have h₁ : ∑ S ∈ U.powerset, (S.card : ℚ) =
      (2 ^ U.card : ℚ) * U.card / 2 := by
    have h₁c : (2 : ℚ) * ∑ S ∈ U.powerset, (S.card : ℚ) =
        (2 ^ U.card : ℚ) * U.card := by exact_mod_cast h₁n
    linarith
  have h₂ : ∑ S ∈ U.powerset, (containedCount F₂ S : ℚ) =
      (2 ^ U.card : ℚ) * F₂.card / 4 := by
    norm_num at h₂n
    have h₂c : (4 : ℚ) *
        ∑ S ∈ U.powerset, (containedCount F₂ S : ℚ) =
          (2 ^ U.card : ℚ) * F₂.card := by exact_mod_cast h₂n
    linarith
  have h₃ : ∑ S ∈ U.powerset, (containedCount F₃ S : ℚ) =
      (2 ^ U.card : ℚ) * F₃.card / 8 := by
    norm_num at h₃n
    have h₃c : (8 : ℚ) *
        ∑ S ∈ U.powerset, (containedCount F₃ S : ℚ) =
          (2 ^ U.card : ℚ) * F₃.card := by exact_mod_cast h₃n
    linarith
  have hsum :
      (∑ S ∈ U.powerset, subsetScore a c d F₂ F₃ S) =
        (2 ^ U.card : ℚ) *
          (a * U.card / 2 - c * F₂.card / 4 - d * F₃.card / 8) := by
    calc
      (∑ S ∈ U.powerset, subsetScore a c d F₂ F₃ S) =
          a * (∑ S ∈ U.powerset, (S.card : ℚ)) -
          c * (∑ S ∈ U.powerset, (containedCount F₂ S : ℚ)) -
          d * (∑ S ∈ U.powerset, (containedCount F₃ S : ℚ)) := by
        simp [subsetScore, Finset.mul_sum, Finset.sum_sub_distrib]
      _ = _ := by rw [h₁, h₂, h₃]; ring
  obtain ⟨S, hSU, hSmax⟩ := exists_max_image U.powerset
    (subsetScore a c d F₂ F₃) ⟨∅, empty_mem_powerset U⟩
  refine ⟨S, hSU, ?_⟩
  have hsumle :
      (∑ R ∈ U.powerset, subsetScore a c d F₂ F₃ R) ≤
        U.powerset.card • subsetScore a c d F₂ F₃ S :=
    sum_le_card_nsmul _ _ _ hSmax
  rw [hsum, card_powerset, nsmul_eq_mul] at hsumle
  norm_num [Nat.cast_pow] at hsumle
  linarith

/-- Iterating the exact halving average realizes Bernoulli sampling with
parameter `2⁻ᵗ`, without introducing a probability space. -/
theorem exists_subset_score_ge_pow
    (t : ℕ) (U : Finset V) (F₂ F₃ : Finset (Finset V))
    (hF₂sub : ∀ e ∈ F₂, e ⊆ U) (hF₂card : ∀ e ∈ F₂, e.card = 2)
    (hF₃sub : ∀ e ∈ F₃, e ⊆ U) (hF₃card : ∀ e ∈ F₃, e.card = 3)
    (a c d : ℚ) :
    ∃ S ∈ U.powerset,
      a * U.card / 2 ^ t - c * F₂.card / 4 ^ t - d * F₃.card / 8 ^ t ≤
        subsetScore a c d F₂ F₃ S := by
  induction t generalizing U F₂ F₃ a c d with
  | zero =>
      refine ⟨U, mem_powerset.mpr Subset.rfl, ?_⟩
      have h₂ : containedCount F₂ U = F₂.card := by
        rw [containedCount, filter_eq_self.mpr hF₂sub]
      have h₃ : containedCount F₃ U = F₃.card := by
        rw [containedCount, filter_eq_self.mpr hF₃sub]
      simp [subsetScore, h₂, h₃]
  | succ t ih =>
      obtain ⟨R, hRU, hRbound⟩ := ih U F₂ F₃ hF₂sub hF₂card hF₃sub hF₃card
        (a / 2) (c / 4) (d / 8)
      let F₂R := restrictFamily F₂ R
      let F₃R := restrictFamily F₃ R
      obtain ⟨S, hSR, hSbound⟩ := exists_subset_score_ge_half R F₂R F₃R
        (restrictFamily_sub F₂ R) (restrictFamily_card hF₂card)
        (restrictFamily_sub F₃ R) (restrictFamily_card hF₃card) a c d
      have hSR' : S ⊆ R := mem_powerset.mp hSR
      have hRU' : R ⊆ U := mem_powerset.mp hRU
      refine ⟨S, mem_powerset.mpr (hSR'.trans hRU'), ?_⟩
      have h₂S : containedCount F₂R S = containedCount F₂ S := by
        exact containedCount_restrictFamily hSR'
      have h₃S : containedCount F₃R S = containedCount F₃ S := by
        exact containedCount_restrictFamily hSR'
      have h₂R : F₂R.card = containedCount F₂ R := by rfl
      have h₃R : F₃R.card = containedCount F₃ R := by rfl
      have hSbound' :
          a * R.card / 2 - c * F₂R.card / 4 - d * F₃R.card / 8 ≤
            subsetScore a c d F₂ F₃ S := by
        simpa only [subsetScore, h₂S, h₃S] using hSbound
      calc
        a * (U.card : ℚ) / 2 ^ (t + 1) -
              c * (F₂.card : ℚ) / 4 ^ (t + 1) -
              d * (F₃.card : ℚ) / 8 ^ (t + 1) =
            (a / 2) * U.card / 2 ^ t -
              (c / 4) * F₂.card / 4 ^ t -
              (d / 8) * F₃.card / 8 ^ t := by
                rw [pow_succ, pow_succ, pow_succ]
                ring
        _ ≤ subsetScore (a / 2) (c / 4) (d / 8) F₂ F₃ R := hRbound
        _ = a * R.card / 2 - c * F₂R.card / 4 - d * F₃R.card / 8 := by
          rw [h₂R, h₃R]
          simp only [subsetScore]
          ring
        _ ≤ subsetScore a c d F₂ F₃ S := hSbound'

end Families

section TwoCliques

variable {W : Type*} [Fintype W] [DecidableEq W]
variable (G : SimpleGraph W) [DecidableRel G.Adj]

/-- The two-cliques of a finite simple graph are its unordered edges. -/
theorem cliqueFinset_two_eq_edge_image :
    G.cliqueFinset 2 =
      G.edgeFinset.attach.image (fun e : G.edgeFinset ↦ e.1.toFinset) := by
  ext s
  simp only [SimpleGraph.mem_cliqueFinset_iff, mem_image, mem_attach, true_and]
  constructor
  · intro hs
    obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp hs.card_eq
    have hadj : G.Adj x y := hs.isClique (by simp) (by simp) hxy
    let e : G.edgeFinset := ⟨s(x, y), SimpleGraph.mem_edgeFinset.mpr hadj⟩
    refine ⟨e, ?_⟩
    simp [e, Sym2.toFinset_mk_eq]
  · rintro ⟨e, rfl⟩
    have hcard : e.1.toFinset.card = 2 :=
      G.card_toFinset_mem_edgeFinset e
    constructor
    · rcases e with ⟨e, he⟩
      induction e with
      | _ x y =>
          have hadj : G.Adj x y := SimpleGraph.mem_edgeFinset.mp he
          have hxy : x ≠ y := by
            intro h
            subst y
            exact G.loopless.irrefl x hadj
          simpa only [Sym2.toFinset_mk_eq, Finset.coe_insert,
            Finset.coe_singleton] using
            (SimpleGraph.isClique_pair.mpr fun _ ↦ hadj)
    · exact hcard

theorem card_cliqueFinset_two_eq_card_edgeFinset :
    (G.cliqueFinset 2).card = G.edgeFinset.card := by
  rw [cliqueFinset_two_eq_edge_image G]
  rw [card_image_of_injective]
  · simp
  · intro e f hef
    apply Subtype.ext
    apply Sym2.ext
    intro x
    change e.1.toFinset = f.1.toFinset at hef
    rw [← Sym2.mem_toFinset, ← Sym2.mem_toFinset, hef]

end TwoCliques

theorem two_mul_card_twoCliques_sumGraph_le {N : ℕ} (A : Finset ℕ) :
    2 * ((sumGraph N A).cliqueFinset 2).card ≤ N * A.card := by
  rw [card_cliqueFinset_two_eq_card_edgeFinset]
  rw [← SimpleGraph.sum_degrees_eq_twice_card_edges]
  calc
    (∑ v : Fin N, (sumGraph N A).degree v) ≤ ∑ _v : Fin N, A.card := by
      exact sum_le_sum fun v _ ↦ degree_sumGraph_le_card A v
    _ = N * A.card := by simp

section TriangleFreeCore

variable {W : Type*} [Fintype W] [DecidableEq W]
variable (G : SimpleGraph W) [DecidableRel G.Adj]

/-- All vertices lying in a triangle contained in the sampled set. -/
def triangleSupport (S : Finset W) : Finset W :=
  (restrictFamily (G.cliqueFinset 3) S).biUnion id

/-- Delete every vertex that lies in a sampled triangle. -/
def triangleFreeCore (S : Finset W) : Finset W :=
  S \ triangleSupport G S

theorem triangleFreeCore_subset (S : Finset W) :
    triangleFreeCore G S ⊆ S :=
  sdiff_subset

theorem card_triangleSupport_le (S : Finset W) :
    (triangleSupport G S).card ≤
      3 * containedCount (G.cliqueFinset 3) S := by
  classical
  calc
    (triangleSupport G S).card ≤
        ∑ t ∈ restrictFamily (G.cliqueFinset 3) S, t.card := by
      exact card_biUnion_le
    _ = ∑ _t ∈ restrictFamily (G.cliqueFinset 3) S, 3 := by
      apply sum_congr rfl
      intro t ht
      exact (SimpleGraph.mem_cliqueFinset_iff.mp (mem_filter.mp ht).1).card_eq
    _ = 3 * containedCount (G.cliqueFinset 3) S := by
      simp [Nat.mul_comm]

theorem card_sample_le_core_add_triangles (S : Finset W) :
    S.card ≤ (triangleFreeCore G S).card +
      3 * containedCount (G.cliqueFinset 3) S := by
  calc
    S.card ≤ (S \ triangleSupport G S).card + (triangleSupport G S).card :=
      card_le_card_sdiff_add_card
    _ ≤ (S \ triangleSupport G S).card +
        3 * containedCount (G.cliqueFinset 3) S :=
      Nat.add_le_add_left (card_triangleSupport_le G S) _
    _ = _ := rfl

omit [Fintype W] [DecidableEq W] [DecidableRel G.Adj] in
theorem isNClique_map_induce {s : Set W} [DecidablePred (· ∈ s)]
    {n : ℕ} {t : Finset s} (ht : (G.induce s).IsNClique n t) :
    G.IsNClique n (t.map (Function.Embedding.subtype s)) := by
  constructor
  · intro x hx y hy hxy
    change x ∈ t.map (Function.Embedding.subtype s) at hx
    change y ∈ t.map (Function.Embedding.subtype s) at hy
    rw [mem_map] at hx hy
    obtain ⟨x, hx, rfl⟩ := hx
    obtain ⟨y, hy, rfl⟩ := hy
    apply SimpleGraph.induce_adj.mp
    exact ht.isClique hx hy fun h ↦ hxy (congrArg Subtype.val h)
  · simpa using ht.card_eq

theorem triangleFree_induce_core (S : Finset W) :
    (G.induce (triangleFreeCore G S : Set W)).CliqueFree 3 := by
  classical
  intro t ht
  let t' : Finset W := t.map
    (Function.Embedding.subtype (triangleFreeCore G S : Set W))
  have ht' : G.IsNClique 3 t' := by
    exact isNClique_map_induce G ht
  have ht'sub : t' ⊆ S := by
    intro x hx
    simp only [t', mem_map] at hx
    obtain ⟨x, _hxt, rfl⟩ := hx
    exact triangleFreeCore_subset G S x.2
  have ht'mem : t' ∈ restrictFamily (G.cliqueFinset 3) S := by
    exact mem_filter.mpr
      ⟨SimpleGraph.mem_cliqueFinset_iff.mpr ht', ht'sub⟩
  have ht'pos : 0 < t'.card := by
    rw [ht'.card_eq]
    norm_num
  obtain ⟨x, hx⟩ := card_pos.mp ht'pos
  have hxsupport : x ∈ triangleSupport G S := by
    exact mem_biUnion.mpr ⟨t', ht'mem, hx⟩
  have hxcore : x ∈ triangleFreeCore G S := by
    simp only [t', mem_map] at hx
    obtain ⟨x, _hxt, rfl⟩ := hx
    exact x.2
  exact (mem_sdiff.mp hxcore).2 hxsupport

theorem card_twoCliques_induce_core_le (S : Finset W) :
    ((G.induce (triangleFreeCore G S : Set W)).cliqueFinset 2).card ≤
      containedCount (G.cliqueFinset 2) S := by
  classical
  let emb := Function.Embedding.subtype (triangleFreeCore G S : Set W)
  refine card_le_card_of_injOn (fun e : Finset (triangleFreeCore G S : Set W) ↦
    e.map emb) ?_ ?_
  · intro e he
    have hec : (G.induce (triangleFreeCore G S : Set W)).IsNClique 2 e :=
      SimpleGraph.mem_cliqueFinset_iff.mp (by simpa only [Finset.mem_coe] using he)
    apply mem_filter.mpr
    constructor
    · exact SimpleGraph.mem_cliqueFinset_iff.mpr (isNClique_map_induce G hec)
    · intro x hx
      rw [mem_map] at hx
      obtain ⟨x, _hxe, rfl⟩ := hx
      exact triangleFreeCore_subset G S x.2
  · intro e _he f _hf hef
    exact Finset.map_injective emb hef

/-- Forget the subtype proof after taking an independent set in an induced
graph. -/
def liftInducedFinset (S : Finset W)
    (C : Finset (S : Set W)) : Finset W :=
  C.map (Function.Embedding.subtype (S : Set W))

omit [Fintype W] [DecidableEq W] in
@[simp]
theorem card_liftInducedFinset (S : Finset W) (C : Finset (S : Set W)) :
    (liftInducedFinset S C).card = C.card := by
  exact card_map _

omit [Fintype W] [DecidableEq W] [DecidableRel G.Adj] in
theorem isIndepSet_liftInducedFinset {S : Finset W}
    {C : Finset (S : Set W)}
    (hC : (G.induce (S : Set W)).IsIndepSet (C : Set (S : Set W))) :
    G.IsIndepSet (liftInducedFinset S C : Set W) := by
  rw [SimpleGraph.isIndepSet_iff] at hC ⊢
  intro x hx y hy hxy
  change x ∈ liftInducedFinset S C at hx
  change y ∈ liftInducedFinset S C at hy
  rw [liftInducedFinset, mem_map] at hx hy
  obtain ⟨x, hx, rfl⟩ := hx
  obtain ⟨y, hy, rfl⟩ := hy
  have hxy' : x ≠ y := fun h ↦ hxy (congrArg Subtype.val h)
  exact hC (by simpa using hx) (by simpa using hy) hxy'

omit [DecidableEq W] [DecidableRel G.Adj] in
theorem indepNum_induce_finset_le (S : Finset W) :
    (G.induce (S : Set W)).indepNum ≤ G.indepNum := by
  obtain ⟨C, hC⟩ := SimpleGraph.exists_isNIndepSet_indepNum
    (G := G.induce (S : Set W))
  calc
    (G.induce (S : Set W)).indepNum = C.card := hC.card_eq.symm
    _ = (liftInducedFinset S C).card := (card_liftInducedFinset S C).symm
    _ ≤ G.indepNum := (isIndepSet_liftInducedFinset G hC.isIndepSet).card_le_indepNum

end TriangleFreeCore

theorem sampling_penalty_lower
    {n b e tri q : ℚ}
    (hn : 0 ≤ n) (hb : 0 ≤ b)
    (hq : 0 < q)
    (hedges : 2 * e ≤ n * b)
    (htriangles : 6 * tri ≤ b ^ 3)
    (hscale : 2 * b ^ 3 ≤ n * q ^ 2) :
    n / (2 * q) ≤
      n / q - (q / (2 * (b + 1))) * e / q ^ 2 - 3 * tri / q ^ 3 := by
  have hb1 : 0 < b + 1 := by linarith
  have hq0 : 0 ≤ q := hq.le
  have hedge' : 2 * e ≤ n * (b + 1) := by
    exact hedges.trans (mul_le_mul_of_nonneg_left (by linarith) hn)
  have hedgeMul := mul_le_mul_of_nonneg_right hedge' hq0
  have hedgeTerm : (q / (2 * (b + 1))) * e / q ^ 2 ≤ n / (4 * q) := by
    have hid : (q / (2 * (b + 1))) * e / q ^ 2 =
        e / (2 * (b + 1) * q) := by
      field_simp
    rw [hid, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have htri12 : 12 * tri ≤ n * q ^ 2 := by
    nlinarith
  have htriMul := mul_le_mul_of_nonneg_right htri12 hq0
  have htriTerm : 3 * tri / q ^ 3 ≤ n / (4 * q) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg q]
  have hnid : n / q = n / (2 * q) + n / (2 * q) := by
    field_simp
    ring
  have hquarter : n / (4 * q) + n / (4 * q) = n / (2 * q) := by
    field_simp
    ring
  linarith

/-- Exact finite sampling-and-deletion statement for a normalized sum graph.
The first inequality retains half the expected sample, and the second one
controls the average degree of the triangle-free core. -/
theorem exists_triangleFree_sample {N : ℕ} (A : Finset ℕ) (t : ℕ)
    (hscale : 2 * A.card ^ 3 ≤ N * (2 ^ t) ^ 2) :
    ∃ R : Finset (Fin N),
      ((sumGraph N A).induce (R : Set (Fin N))).CliqueFree 3 ∧
      (N : ℚ) / (2 * (2 : ℚ) ^ t) ≤ (R.card : ℚ) ∧
      (2 ^ t) *
          (((sumGraph N A).induce (R : Set (Fin N))).cliqueFinset 2).card ≤
        2 * (A.card + 1) * R.card := by
  classical
  let G := sumGraph N A
  let F₂ := G.cliqueFinset 2
  let F₃ := G.cliqueFinset 3
  let q : ℚ := (2 : ℚ) ^ t
  have h₂sub : ∀ e ∈ F₂, e ⊆ (Finset.univ : Finset (Fin N)) := by
    intro e _he
    exact subset_univ e
  have h₂card : ∀ e ∈ F₂, e.card = 2 := by
    intro e he
    exact (SimpleGraph.mem_cliqueFinset_iff.mp he).card_eq
  have h₃sub : ∀ e ∈ F₃, e ⊆ (Finset.univ : Finset (Fin N)) := by
    intro e _he
    exact subset_univ e
  have h₃card : ∀ e ∈ F₃, e.card = 3 := by
    intro e he
    exact (SimpleGraph.mem_cliqueFinset_iff.mp he).card_eq
  obtain ⟨S, _hSuniv, hS⟩ := exists_subset_score_ge_pow t
    (Finset.univ : Finset (Fin N)) F₂ F₃ h₂sub h₂card h₃sub h₃card
    1 (q / (2 * (A.card + 1))) 3
  have hpow4 : (4 : ℚ) ^ t = q ^ 2 := by
    calc
      (4 : ℚ) ^ t = ((2 : ℚ) ^ 2) ^ t := by norm_num
      _ = (2 : ℚ) ^ (2 * t) := (pow_mul (2 : ℚ) 2 t).symm
      _ = (2 : ℚ) ^ (t * 2) := by rw [Nat.mul_comm]
      _ = q ^ 2 := pow_mul (2 : ℚ) t 2
  have hpow8 : (8 : ℚ) ^ t = q ^ 3 := by
    calc
      (8 : ℚ) ^ t = ((2 : ℚ) ^ 3) ^ t := by norm_num
      _ = (2 : ℚ) ^ (3 * t) := (pow_mul (2 : ℚ) 3 t).symm
      _ = (2 : ℚ) ^ (t * 3) := by rw [Nat.mul_comm]
      _ = q ^ 3 := pow_mul (2 : ℚ) t 3
  have hedgeNat : 2 * F₂.card ≤ N * A.card := by
    simpa only [G, F₂] using two_mul_card_twoCliques_sumGraph_le A
  have htriNat : 6 * F₃.card ≤ A.card ^ 3 := by
    calc
      6 * F₃.card ≤ 6 * A.card.choose 3 := by
        exact Nat.mul_le_mul_left 6 (by
          simpa only [G, F₃] using triangle_count_le_choose A)
      _ ≤ A.card ^ 3 := six_mul_choose_three_le_cube A.card
  have hedgeQ : (2 : ℚ) * F₂.card ≤ (N : ℚ) * A.card := by
    exact_mod_cast hedgeNat
  have htriQ : (6 : ℚ) * F₃.card ≤ (A.card : ℚ) ^ 3 := by
    exact_mod_cast htriNat
  have hscaleQ : (2 : ℚ) * (A.card : ℚ) ^ 3 ≤ (N : ℚ) * q ^ 2 := by
    dsimp only [q]
    exact_mod_cast hscale
  have hpenalty := sampling_penalty_lower
    (n := (N : ℚ)) (b := (A.card : ℚ)) (e := (F₂.card : ℚ))
    (tri := (F₃.card : ℚ)) (q := q)
    (by positivity) (by positivity) (by positivity)
    hedgeQ htriQ hscaleQ
  have hsampleScore :
      (N : ℚ) / (2 * q) ≤ subsetScore 1
        (q / (2 * (A.card + 1))) 3 F₂ F₃ S := by
    exact hpenalty.trans (by
      simpa only [card_univ, Fintype.card_fin, one_mul, hpow4, hpow8, q]
        using hS)
  let R := triangleFreeCore G S
  have hcardLossNat : S.card ≤ R.card + 3 * containedCount F₃ S := by
    simpa only [R, G, F₃] using card_sample_le_core_add_triangles G S
  have hcardLossQ : (S.card : ℚ) ≤
      (R.card : ℚ) + 3 * containedCount F₃ S := by
    exact_mod_cast hcardLossNat
  have hcombined :
      (N : ℚ) / (2 * q) +
          (q / (2 * (A.card + 1))) * containedCount F₂ S ≤ R.card := by
    simp only [subsetScore, one_mul] at hsampleScore
    linarith
  have hRcard : (N : ℚ) / (2 * q) ≤ (R.card : ℚ) := by
    have hnonneg : 0 ≤
        (q / (2 * (A.card + 1))) * containedCount F₂ S := by positivity
    linarith
  have hedgeSampleQ : q * containedCount F₂ S ≤
      2 * (A.card + 1) * R.card := by
    have hterm : (q / (2 * (A.card + 1))) * containedCount F₂ S ≤
        (R.card : ℚ) := by
      have hNterm : 0 ≤ (N : ℚ) / (2 * q) := by positivity
      linarith
    have hbpos : (0 : ℚ) < 2 * ((A.card : ℚ) + 1) := by positivity
    calc
      q * containedCount F₂ S =
          (2 * ((A.card : ℚ) + 1)) *
            ((q / (2 * (A.card + 1))) * containedCount F₂ S) := by
              field_simp
      _ ≤ (2 * ((A.card : ℚ) + 1)) * R.card :=
        mul_le_mul_of_nonneg_left hterm hbpos.le
  have hedgeCoreNat :
      (((sumGraph N A).induce (R : Set (Fin N))).cliqueFinset 2).card ≤
        containedCount F₂ S := by
    simpa only [G, F₂, R] using card_twoCliques_induce_core_le G S
  have hedgeCoreQ : q *
      (((sumGraph N A).induce (R : Set (Fin N))).cliqueFinset 2).card ≤
        2 * (A.card + 1) * R.card := by
    exact (mul_le_mul_of_nonneg_left (by exact_mod_cast hedgeCoreNat)
      (by positivity : 0 ≤ q)).trans hedgeSampleQ
  have hedgeCoreNat' : (2 ^ t) *
      (((sumGraph N A).induce (R : Set (Fin N))).cliqueFinset 2).card ≤
        2 * (A.card + 1) * R.card := by
    have hcast :
        (((2 ^ t) *
          (((sumGraph N A).induce (R : Set (Fin N))).cliqueFinset 2).card : ℕ) : ℚ) ≤
          ((2 * (A.card + 1) * R.card : ℕ) : ℚ) := by
      push_cast
      simpa only [q] using hedgeCoreQ
    exact_mod_cast hcast
  refine ⟨R, ?_, hRcard, hedgeCoreNat'⟩
  simpa only [G, R] using triangleFree_induce_core G S

/-- A power-of-two sampling denominator which is minimal up to a factor of
two.  The second inequality is the quantitative information obtained from
minimality. -/
theorem exists_sampling_exponent (N b : ℕ) (hN : 0 < N) :
    ∃ t : ℕ,
      2 * b ^ 3 ≤ N * (2 ^ t) ^ 2 ∧
        (t = 0 ∨ N * (2 ^ t) ^ 2 < 8 * b ^ 3) := by
  let p : ℕ → Prop := fun t ↦ 2 * b ^ 3 ≤ N * (2 ^ t) ^ 2
  have hex : ∃ t, p t := by
    obtain ⟨t, ht⟩ := pow_unbounded_of_one_lt (2 * b ^ 3) (by norm_num : 1 < (2 : ℕ))
    refine ⟨t, ?_⟩
    have hq : 1 ≤ 2 ^ t := Nat.one_le_two_pow
    calc
      2 * b ^ 3 ≤ 2 ^ t := ht.le
      _ ≤ (2 ^ t) ^ 2 := by nlinarith
      _ = 1 * (2 ^ t) ^ 2 := by simp
      _ ≤ N * (2 ^ t) ^ 2 := Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr hN)
  let t := Nat.find hex
  refine ⟨t, Nat.find_spec hex, ?_⟩
  by_cases ht : t = 0
  · exact Or.inl ht
  · right
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero ht
    have hpred : ¬p k := by
      intro hk
      have hmin : Nat.find hex ≤ k := Nat.find_min' hex hk
      change t ≤ k at hmin
      omega
    simp only [p, not_le] at hpred
    rw [hk]
    simpa only [pow_succ] using
      (show N * (2 ^ k * 2) ^ 2 < 8 * b ^ 3 by nlinarith)

end Erdos788


/-! Flattened from Erdos788.Shearer. -/


/-!
# A harmonic weight for the triangle-free Shearer induction

The weight is deliberately a factor `1 / 2`
below the sharp Shearer weight; in return its two required inequalities have
short elementary proofs.
-/

namespace Erdos788.AKSRoute

open Finset

universe u

/-- The weight used in the closed-neighborhood deletion induction. -/
noncomputable def shearerWeight (d : ℕ) : ℚ :=
  if d = 0 then 1 else harmonic d / (2 * (d : ℚ))

@[simp]
theorem shearerWeight_zero : shearerWeight 0 = 1 := by
  simp [shearerWeight]

theorem shearerWeight_of_pos {d : ℕ} (hd : 0 < d) :
    shearerWeight d = harmonic d / (2 * (d : ℚ)) := by
  simp [shearerWeight, hd.ne']

@[simp]
theorem shearerWeight_succ (d : ℕ) :
    shearerWeight (d + 1) = harmonic (d + 1) / (2 * ((d + 1 : ℕ) : ℚ)) := by
  exact shearerWeight_of_pos (Nat.zero_lt_succ d)

theorem harmonic_le_natCast (d : ℕ) : harmonic d ≤ (d : ℚ) := by
  rw [harmonic]
  calc
    ∑ i ∈ range d, ((i + 1 : ℕ) : ℚ)⁻¹ ≤ ∑ _i ∈ range d, (1 : ℚ) := by
      apply sum_le_sum
      intro i _hi
      exact (inv_le_one₀ (by positivity)).2 (by norm_num)
    _ = (d : ℚ) := by simp

theorem one_le_harmonic_succ (d : ℕ) : (1 : ℚ) ≤ harmonic (d + 1) := by
  induction d with
  | zero => norm_num [harmonic, Finset.sum_range_succ]
  | succ d ih =>
      rw [show d + 1 + 1 = (d + 1) + 1 by rfl, harmonic_succ]
      exact ih.trans (le_add_of_nonneg_right (by positivity))

theorem three_halves_le_harmonic {d : ℕ} (hd : 2 ≤ d) :
    (3 / 2 : ℚ) ≤ harmonic d := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hd
  clear hd
  induction k with
  | zero => norm_num [harmonic, Finset.sum_range_succ]
  | succ k ih =>
      rw [show 2 + (k + 1) = (2 + k) + 1 by omega, harmonic_succ]
      exact ih.trans (le_add_of_nonneg_right (by positivity))

/-- The local residual in the Shearer potential calculation is nonnegative.
For positive `d` it is exactly `(d - harmonic d) / (2*d)`. -/
theorem shearerWeight_residual_nonneg (d : ℕ) :
    0 ≤ 1 - ((d + 1 : ℕ) : ℚ) * shearerWeight d +
      (d : ℚ) * ((d - 1 : ℕ) : ℚ) *
        (shearerWeight (d - 1) - shearerWeight d) := by
  rcases d with (_ | d)
  · simp
  rcases d with (_ | d)
  · norm_num [shearerWeight, harmonic, Finset.sum_range_succ]
  have hdpos : 0 < d + 2 := by omega
  have hdpred : 0 < d + 2 - 1 := by omega
  rw [shearerWeight_of_pos hdpos, shearerWeight_of_pos hdpred]
  have hh : harmonic (d + 2) =
      harmonic (d + 2 - 1) + (((d + 2 : ℕ) : ℚ))⁻¹ := by
    have heq : d + 2 - 1 = d + 1 := by omega
    rw [heq]
    exact harmonic_succ (d + 1)
  have hid :
      1 - (((d + 2) + 1 : ℕ) : ℚ) *
          (harmonic (d + 2) / (2 * (((d + 2 : ℕ) : ℚ)))) +
          ((d + 2 : ℕ) : ℚ) * (((d + 2 - 1 : ℕ) : ℚ)) *
            (harmonic (d + 2 - 1) / (2 * (((d + 2 - 1 : ℕ) : ℚ))) -
              harmonic (d + 2) / (2 * (((d + 2 : ℕ) : ℚ)))) =
        (((d + 2 : ℕ) : ℚ) - harmonic (d + 2)) /
          (2 * (((d + 2 : ℕ) : ℚ))) := by
    rw [hh]
    push_cast
    field_simp
    ring
  rw [hid]
  apply div_nonneg
  · exact sub_nonneg.mpr (harmonic_le_natCast (d + 2))
  · positivity

/-- The successive drops of `shearerWeight` decrease.  This is the discrete
convexity input in the closed-neighborhood deletion proof. -/
theorem shearerWeight_drop_antitone (d : ℕ) :
    shearerWeight d - shearerWeight (d + 1) ≥
      shearerWeight (d + 1) - shearerWeight (d + 2) := by
  rcases d with (_ | d)
  · norm_num [shearerWeight, harmonic, Finset.sum_range_succ]
  let k : ℕ := d + 1
  have hk : 2 ≤ k + 1 := by omega
  have hkpos : 0 < k := by omega
  have hk1pos : 0 < k + 1 := by omega
  have hk2pos : 0 < k + 2 := by omega
  rw [show d + 1 = k by rfl, show d + 2 = k + 1 by omega]
  rw [shearerWeight_of_pos hkpos, shearerWeight_of_pos hk1pos,
    shearerWeight_of_pos hk2pos]
  have hh1 : harmonic (k + 1) = harmonic k + (((k + 1 : ℕ) : ℚ))⁻¹ :=
    harmonic_succ k
  have hh2 : harmonic (k + 2) =
      harmonic (k + 1) + (((k + 2 : ℕ) : ℚ))⁻¹ :=
    harmonic_succ (k + 1)
  have hh0 : harmonic k =
      harmonic (k + 1) - (((k + 1 : ℕ) : ℚ))⁻¹ := by
    linarith
  rw [hh0, hh2]
  have hH := three_halves_le_harmonic hk
  push_cast at hH ⊢
  field_simp
  nlinarith

theorem shearerWeight_drop_nonneg (d : ℕ) :
    0 ≤ shearerWeight d - shearerWeight (d + 1) := by
  rcases d with (_ | d)
  · norm_num [shearerWeight, harmonic, Finset.sum_range_succ]
  rw [shearerWeight_of_pos (by omega : 0 < d + 1),
    shearerWeight_of_pos (by omega : 0 < d + 2), harmonic_succ (d + 1)]
  have hH := one_le_harmonic_succ d
  push_cast at hH ⊢
  field_simp
  nlinarith

theorem shearerWeight_antitone : Antitone shearerWeight :=
  antitone_nat_of_succ_le fun d ↦ sub_nonneg.mp (shearerWeight_drop_nonneg d)

theorem shearerWeight_telescoping {d k : ℕ} (hk : k ≤ d) :
    (k : ℚ) * (shearerWeight (d - 1) - shearerWeight d) ≤
      shearerWeight (d - k) - shearerWeight d := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hkd : k ≤ d := by omega
      have hpos : 0 < d - k := by omega
      have hidx : d - (k + 1) = d - k - 1 := by omega
      have hstep :
          shearerWeight (d - 1) - shearerWeight d ≤
            shearerWeight (d - k - 1) - shearerWeight (d - k) := by
        have hle : d - k - 1 ≤ d - 1 := by omega
        have hdrop : Antitone
            (fun n ↦ shearerWeight n - shearerWeight (n + 1)) :=
          antitone_nat_of_succ_le fun n ↦ by
            simpa [Nat.add_assoc] using shearerWeight_drop_antitone n
        have hres := hdrop hle
        have h1 : d - 1 + 1 = d := by omega
        have h2 : d - k - 1 + 1 = d - k := by omega
        dsimp only at hres
        rw [h1, h2] at hres
        exact hres
      rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, hidx]
      calc
        (k : ℚ) * (shearerWeight (d - 1) - shearerWeight d) +
            (shearerWeight (d - 1) - shearerWeight d) ≤
            (shearerWeight (d - k) - shearerWeight d) +
              (shearerWeight (d - k - 1) - shearerWeight (d - k)) :=
          add_le_add (ih hkd) hstep
        _ = shearerWeight (d - k - 1) - shearerWeight d := by ring

/-- The harmonic weight already contains the logarithmic factor needed in
the final analytic estimate. -/
theorem log_le_two_mul_nat_mul_shearerWeight {d : ℕ} (hd : 0 < d) :
    Real.log (d + 1 : ℝ) ≤
      (2 * d : ℝ) * (shearerWeight d : ℝ) := by
  rw [shearerWeight_of_pos hd]
  norm_cast
  field_simp
  exact_mod_cast log_add_one_le_harmonic d

section FiniteGraph

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def closedNeighborFinset (x : V) : Finset V :=
  insert x (G.neighborFinset x)

def outsideClosedNeighborFinset (x : V) : Finset V :=
  Finset.univ \ closedNeighborFinset G x

def degreeOutsideClosed (x z : V) : ℕ :=
  (G.neighborFinset z \ closedNeighborFinset G x).card

@[simp]
theorem mem_closedNeighborFinset {x z : V} :
    z ∈ closedNeighborFinset G x ↔ z = x ∨ G.Adj x z := by
  simp [closedNeighborFinset]

@[simp]
theorem mem_outsideClosedNeighborFinset {x z : V} :
    z ∈ outsideClosedNeighborFinset G x ↔ z ≠ x ∧ ¬G.Adj x z := by
  simp [outsideClosedNeighborFinset]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem not_adj_endpoints_of_twoPath (htri : G.CliqueFree 3)
    {x y z : V} (hxy : G.Adj x y) (hyz : G.Adj y z) (hxz : x ≠ z) :
    ¬G.Adj x z := by
  have hi := G.isIndepSet_neighborSet_of_triangleFree htri y
  exact hi hxy.symm hyz hxz

omit [DecidableEq V] in
/-- Swap the two ends of a sum over directed edges. -/
theorem sum_neighborFinset_swap (f : V → V → ℚ) :
    (∑ x : V, ∑ y ∈ G.neighborFinset x, f x y) =
      ∑ y : V, ∑ x ∈ G.neighborFinset y, f x y := by
  classical
  have hn (x : V) : G.neighborFinset x = Finset.univ.filter (G.Adj x) := by
    ext y
    simp
  simp_rw [hn, sum_filter]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro y _hy
  apply sum_congr rfl
  intro x _hx
  by_cases h : G.Adj x y
  · simp [h, h.symm]
  · have h' : ¬G.Adj y x := fun hyx ↦ h hyx.symm
    simp [h, h']

omit [Fintype V] in
/-- A function of the second coordinate is counted `|s|-1` times on the
ordered off-diagonal of `s`. -/
theorem sum_erase_second (s : Finset V) (f : V → ℚ) :
    (∑ x ∈ s, ∑ z ∈ s.erase x, f z) =
      ∑ z ∈ s, ((s.card - 1 : ℕ) : ℚ) * f z := by
  classical
  have he (x : V) : s.erase x = s.filter fun z ↦ z ≠ x := by
    ext z
    simp only [mem_erase, mem_filter]
    constructor <;> aesop
  calc
    (∑ x ∈ s, ∑ z ∈ s.erase x, f z) =
        ∑ x ∈ s, ∑ z ∈ s, if z ≠ x then f z else 0 := by
      simp_rw [he, sum_filter]
    _ = ∑ z ∈ s, ∑ x ∈ s, if z ≠ x then f z else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ z ∈ s, ∑ x ∈ s.erase z, f z := by
      apply sum_congr rfl
      intro z _hz
      rw [he, sum_filter]
      apply sum_congr rfl
      intro x _hx
      by_cases h : z = x
      · simp [h]
      · have h' : x ≠ z := fun hxz ↦ h hxz.symm
        simp [h, h']
    _ = ∑ z ∈ s, ((s.card - 1 : ℕ) : ℚ) * f z := by
      apply sum_congr rfl
      intro z hz
      rw [sum_const, nsmul_eq_mul, card_erase_of_mem hz]

def commonNeighborCount (x z : V) : ℕ :=
  (G.neighborFinset x ∩ G.neighborFinset z).card

noncomputable def vertexDrop (z : V) : ℚ :=
  shearerWeight (G.degree z - 1) - shearerWeight (G.degree z)

theorem degreeOutsideClosed_eq_sub_common {x z : V}
    (hz : z ∈ outsideClosedNeighborFinset G x) :
    degreeOutsideClosed G x z = G.degree z - commonNeighborCount G x z := by
  have hxz : ¬G.Adj x z := (mem_outsideClosedNeighborFinset G).mp hz |>.2
  have hxnot : x ∉ G.neighborFinset z := by
    simpa [G.adj_comm] using hxz
  rw [degreeOutsideClosed, card_sdiff, SimpleGraph.card_neighborFinset_eq_degree,
    commonNeighborCount]
  congr 1
  apply congrArg Finset.card
  ext y
  simp [closedNeighborFinset, hxnot]

theorem commonNeighborCount_le_degree (x z : V) :
    commonNeighborCount G x z ≤ G.degree z := by
  rw [commonNeighborCount, ← SimpleGraph.card_neighborFinset_eq_degree]
  exact card_le_card inter_subset_right

theorem local_weight_change_lower {x z : V}
    (hz : z ∈ outsideClosedNeighborFinset G x) :
    (commonNeighborCount G x z : ℚ) * vertexDrop G z ≤
      shearerWeight (degreeOutsideClosed G x z) - shearerWeight (G.degree z) := by
  rw [degreeOutsideClosed_eq_sub_common G hz, vertexDrop]
  exact shearerWeight_telescoping (commonNeighborCount_le_degree G x z)

omit [DecidableEq V] in
theorem edge_pair_drop_ineq {y z : V} (hyz : G.Adj y z) :
    (((G.degree y - 1 : ℕ) : ℚ) * vertexDrop G z +
        ((G.degree z - 1 : ℕ) : ℚ) * vertexDrop G y) ≥
      (((G.degree y - 1 : ℕ) : ℚ) * vertexDrop G y +
        ((G.degree z - 1 : ℕ) : ℚ) * vertexDrop G z) := by
  have hypos : 0 < G.degree y := hyz.degree_pos_left
  have hzpos : 0 < G.degree z := hyz.degree_pos_right
  by_cases hdeg : G.degree y ≤ G.degree z
  · have hidx : G.degree y - 1 ≤ G.degree z - 1 := by omega
    have hdrop : vertexDrop G z ≤ vertexDrop G y := by
      rw [vertexDrop, vertexDrop]
      have hanti : Antitone
          (fun n ↦ shearerWeight n - shearerWeight (n + 1)) :=
        antitone_nat_of_succ_le fun n ↦ by
          simpa [Nat.add_assoc] using shearerWeight_drop_antitone n
      have h := hanti hidx
      have hy : G.degree y - 1 + 1 = G.degree y := by omega
      have hz : G.degree z - 1 + 1 = G.degree z := by omega
      dsimp only at h
      rw [hy, hz] at h
      exact h
    have hycast : (((G.degree y - 1 : ℕ) : ℚ)) = (G.degree y : ℚ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    have hzcast : (((G.degree z - 1 : ℕ) : ℚ)) = (G.degree z : ℚ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    have hdegq : (G.degree y : ℚ) ≤ (G.degree z : ℚ) := by exact_mod_cast hdeg
    rw [hycast, hzcast]
    nlinarith
  · have hzy : G.degree z ≤ G.degree y := by omega
    have hidx : G.degree z - 1 ≤ G.degree y - 1 := by omega
    have hdrop : vertexDrop G y ≤ vertexDrop G z := by
      rw [vertexDrop, vertexDrop]
      have hanti : Antitone
          (fun n ↦ shearerWeight n - shearerWeight (n + 1)) :=
        antitone_nat_of_succ_le fun n ↦ by
          simpa [Nat.add_assoc] using shearerWeight_drop_antitone n
      have h := hanti hidx
      have hy : G.degree y - 1 + 1 = G.degree y := by omega
      have hz : G.degree z - 1 + 1 = G.degree z := by omega
      dsimp only at h
      rw [hy, hz] at h
      exact h
    have hycast : (((G.degree y - 1 : ℕ) : ℚ)) = (G.degree y : ℚ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    have hzcast : (((G.degree z - 1 : ℕ) : ℚ)) = (G.degree z : ℚ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    have hdegq : (G.degree z : ℚ) ≤ (G.degree y : ℚ) := by exact_mod_cast hzy
    rw [hycast, hzcast]
    nlinarith

noncomputable def pathDropSum : ℚ :=
  ∑ y : V, ∑ x ∈ G.neighborFinset y,
    ∑ z ∈ (G.neighborFinset y).erase x, vertexDrop G z

theorem pathDropSum_eq_oriented :
    pathDropSum G =
      ∑ z : V, ∑ y ∈ G.neighborFinset z,
        (((G.degree y - 1 : ℕ) : ℚ) * vertexDrop G z) := by
  rw [pathDropSum]
  calc
    (∑ y : V, ∑ x ∈ G.neighborFinset y,
        ∑ z ∈ (G.neighborFinset y).erase x, vertexDrop G z) =
        ∑ y : V, ∑ z ∈ G.neighborFinset y,
          (((G.degree y - 1 : ℕ) : ℚ) * vertexDrop G z) := by
      apply sum_congr rfl
      intro y _hy
      simpa only [SimpleGraph.card_neighborFinset_eq_degree] using
        sum_erase_second (G.neighborFinset y) (vertexDrop G)
    _ = ∑ z : V, ∑ y ∈ G.neighborFinset z,
          (((G.degree y - 1 : ℕ) : ℚ) * vertexDrop G z) :=
      sum_neighborFinset_swap G
        (fun y z ↦ (((G.degree y - 1 : ℕ) : ℚ) * vertexDrop G z))

theorem pathDropSum_lower_degree_residual :
    pathDropSum G ≥
      ∑ z : V, (G.degree z : ℚ) * (((G.degree z - 1 : ℕ) : ℚ) *
        vertexDrop G z) := by
  let A : ℚ := ∑ z : V, ∑ y ∈ G.neighborFinset z,
    (((G.degree y - 1 : ℕ) : ℚ) * vertexDrop G z)
  let A' : ℚ := ∑ z : V, ∑ y ∈ G.neighborFinset z,
    (((G.degree z - 1 : ℕ) : ℚ) * vertexDrop G y)
  let B : ℚ := ∑ z : V, ∑ y ∈ G.neighborFinset z,
    (((G.degree z - 1 : ℕ) : ℚ) * vertexDrop G z)
  let B' : ℚ := ∑ z : V, ∑ y ∈ G.neighborFinset z,
    (((G.degree y - 1 : ℕ) : ℚ) * vertexDrop G y)
  have hAA' : A' = A := by
    exact sum_neighborFinset_swap G
      (fun z y ↦ (((G.degree z - 1 : ℕ) : ℚ) * vertexDrop G y))
  have hBB' : B' = B := by
    exact sum_neighborFinset_swap G
      (fun z y ↦ (((G.degree y - 1 : ℕ) : ℚ) * vertexDrop G y))
  have hpairs : B + B' ≤ A + A' := by
    dsimp only [A, A', B, B']
    simp_rw [← sum_add_distrib]
    apply sum_le_sum
    intro z _hz
    apply sum_le_sum
    intro y hy
    simpa [add_comm] using edge_pair_drop_ineq G
      ((SimpleGraph.mem_neighborFinset (G := G) (v := z) y).mp hy).symm
  have hB : B = ∑ z : V,
      (G.degree z : ℚ) * (((G.degree z - 1 : ℕ) : ℚ) * vertexDrop G z) := by
    dsimp only [B]
    apply sum_congr rfl
    intro z _hz
    rw [sum_const, nsmul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree]
  rw [pathDropSum_eq_oriented]
  change A ≥ _
  rw [← hB]
  linarith

abbrev VertexTriple (V : Type*) := Σ _x : V, Σ _z : V, V

def rotateVertexTriple : VertexTriple V ≃ VertexTriple V where
  toFun p := ⟨p.2.2, ⟨p.1, p.2.1⟩⟩
  invFun p := ⟨p.2.1, ⟨p.2.2, p.1⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

def commonTriples : Finset (VertexTriple V) :=
  Finset.univ.sigma fun x ↦
    (outsideClosedNeighborFinset G x).sigma fun z ↦
      G.neighborFinset x ∩ G.neighborFinset z

def pathTriples : Finset (VertexTriple V) :=
  Finset.univ.sigma fun y ↦
    (G.neighborFinset y).sigma fun x ↦
      (G.neighborFinset y).erase x

noncomputable def commonDropSum : ℚ :=
  ∑ p ∈ commonTriples G, vertexDrop G p.2.1

theorem commonDropSum_eq_counted :
    commonDropSum G =
      ∑ x : V, ∑ z ∈ outsideClosedNeighborFinset G x,
        (commonNeighborCount G x z : ℚ) * vertexDrop G z := by
  rw [commonDropSum, commonTriples, Finset.sum_sigma]
  apply sum_congr rfl
  intro x _hx
  rw [Finset.sum_sigma]
  apply sum_congr rfl
  intro z _hz
  change (∑ _y ∈ G.neighborFinset x ∩ G.neighborFinset z, vertexDrop G z) = _
  rw [sum_const, nsmul_eq_mul, commonNeighborCount]

theorem pathDropSum_eq_triples :
    pathDropSum G = ∑ p ∈ pathTriples G, vertexDrop G p.2.2 := by
  rw [pathDropSum, pathTriples, Finset.sum_sigma]
  apply sum_congr rfl
  intro y _hy
  rw [Finset.sum_sigma]

theorem rotate_mem_pathTriples_iff_mem_commonTriples
    (htri : G.CliqueFree 3) (p : VertexTriple V) :
    rotateVertexTriple p ∈ pathTriples G ↔ p ∈ commonTriples G := by
  rcases p with ⟨x, ⟨z, y⟩⟩
  simp only [rotateVertexTriple, pathTriples, commonTriples, mem_sigma, mem_univ,
    true_and, mem_inter, mem_erase]
  constructor
  · rintro ⟨hyx, hzx, hzy⟩
    have hxy : G.Adj x y :=
      (SimpleGraph.mem_neighborFinset (G := G) (v := y) x).mp hyx |>.symm
    have hyz : G.Adj y z :=
      (SimpleGraph.mem_neighborFinset (G := G) (v := y) z).mp hzy
    have hxz : x ≠ z := hzx.symm
    have hnadj := not_adj_endpoints_of_twoPath G htri hxy hyz hxz
    refine ⟨(mem_outsideClosedNeighborFinset G).mpr ⟨hxz.symm, hnadj⟩, ?_, ?_⟩
    · exact (SimpleGraph.mem_neighborFinset (G := G) (v := x) y).mpr hxy
    · exact (SimpleGraph.mem_neighborFinset (G := G) (v := z) y).mpr hyz.symm
  · rintro ⟨hzout, hyx, hyz⟩
    have hout := (mem_outsideClosedNeighborFinset G).mp hzout
    refine ⟨?_, hout.1, ?_⟩
    · exact (SimpleGraph.mem_neighborFinset (G := G) (v := y) x).mpr
        ((SimpleGraph.mem_neighborFinset (G := G) (v := x) y).mp hyx).symm
    · exact (SimpleGraph.mem_neighborFinset (G := G) (v := y) z).mpr
        ((SimpleGraph.mem_neighborFinset (G := G) (v := z) y).mp hyz).symm

theorem commonDropSum_eq_pathDropSum (htri : G.CliqueFree 3) :
    commonDropSum G = pathDropSum G := by
  rw [pathDropSum_eq_triples]
  exact Finset.sum_equiv (rotateVertexTriple (V := V))
    (fun p ↦ (rotate_mem_pathTriples_iff_mem_commonTriples G htri p).symm)
    (fun _p _hp ↦ rfl)

noncomputable def graphWeight : ℚ :=
  ∑ v : V, shearerWeight (G.degree v)

noncomputable def baseDeletionTerm (x : V) : ℚ :=
  1 - shearerWeight (G.degree x) -
    ∑ y ∈ G.neighborFinset x, shearerWeight (G.degree y)

noncomputable def changeDeletionTerm (x : V) : ℚ :=
  ∑ z ∈ outsideClosedNeighborFinset G x,
    (shearerWeight (degreeOutsideClosed G x z) - shearerWeight (G.degree z))

noncomputable def closedDeletionGain (x : V) : ℚ :=
  baseDeletionTerm G x + changeDeletionTerm G x

omit [DecidableEq V] in
theorem sum_baseDeletionTerm :
    (∑ x : V, baseDeletionTerm G x) =
      ∑ x : V, (1 - (((G.degree x + 1 : ℕ) : ℚ) *
        shearerWeight (G.degree x))) := by
  have hneighbor :
      (∑ x : V, ∑ y ∈ G.neighborFinset x, shearerWeight (G.degree y)) =
        ∑ x : V, (G.degree x : ℚ) * shearerWeight (G.degree x) := by
    calc
      (∑ x : V, ∑ y ∈ G.neighborFinset x, shearerWeight (G.degree y)) =
          ∑ y : V, ∑ x ∈ G.neighborFinset y, shearerWeight (G.degree y) :=
        sum_neighborFinset_swap G
          (fun _x y ↦ shearerWeight (G.degree y))
      _ = ∑ y : V, (G.degree y : ℚ) * shearerWeight (G.degree y) := by
        apply sum_congr rfl
        intro y _hy
        rw [sum_const, nsmul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree]
  simp only [baseDeletionTerm]
  rw [Finset.sum_sub_distrib, hneighbor]
  rw [← Finset.sum_sub_distrib]
  apply sum_congr rfl
  intro x _hx
  push_cast
  ring

theorem commonDropSum_le_sum_changeDeletionTerm :
    commonDropSum G ≤ ∑ x : V, changeDeletionTerm G x := by
  rw [commonDropSum_eq_counted]
  apply sum_le_sum
  intro x _hx
  rw [changeDeletionTerm]
  apply sum_le_sum
  intro z hz
  exact local_weight_change_lower G hz

omit [DecidableEq V] in
theorem sum_pointwiseResidual_nonneg :
    0 ≤ ∑ x : V,
      (1 - (((G.degree x + 1 : ℕ) : ℚ) * shearerWeight (G.degree x)) +
        (G.degree x : ℚ) * (((G.degree x - 1 : ℕ) : ℚ) * vertexDrop G x)) := by
  apply sum_nonneg
  intro x _hx
  rw [vertexDrop]
  simpa only [mul_assoc] using shearerWeight_residual_nonneg (G.degree x)

set_option maxHeartbeats 800000 in
theorem pointwiseResidualSum_le_base_add_common (htri : G.CliqueFree 3) :
    (∑ x : V,
      (1 - (((G.degree x + 1 : ℕ) : ℚ) * shearerWeight (G.degree x)) +
        (G.degree x : ℚ) * (((G.degree x - 1 : ℕ) : ℚ) * vertexDrop G x))) ≤
      (∑ x : V, baseDeletionTerm G x) + commonDropSum G := by
  rw [sum_add_distrib, sum_baseDeletionTerm,
    commonDropSum_eq_pathDropSum G htri]
  apply add_le_add_right
  exact pathDropSum_lower_degree_residual G

theorem sum_closedDeletionGain_nonneg (htri : G.CliqueFree 3) :
    0 ≤ ∑ x : V, closedDeletionGain G x := by
  have hchange := commonDropSum_le_sum_changeDeletionTerm G
  have hnonneg : 0 ≤ (∑ x : V, baseDeletionTerm G x) + commonDropSum G :=
    (sum_pointwiseResidual_nonneg G).trans
      (pointwiseResidualSum_le_base_add_common G htri)
  have hfinal : 0 ≤ (∑ x : V, baseDeletionTerm G x) +
      ∑ x : V, changeDeletionTerm G x :=
    hnonneg.trans (add_le_add_right hchange _)
  simpa only [closedDeletionGain, sum_add_distrib] using hfinal

theorem exists_nonneg_closedDeletionGain [Nonempty V]
    (htri : G.CliqueFree 3) :
    ∃ x : V, 0 ≤ closedDeletionGain G x := by
  have hsum := sum_closedDeletionGain_nonneg G htri
  have huniv : (Finset.univ : Finset V).Nonempty := Finset.univ_nonempty
  have hzsum : (∑ _x : V, (0 : ℚ)) ≤
      ∑ x : V, closedDeletionGain G x := by
    simpa only [sum_const_zero] using hsum
  obtain ⟨x, _hx, hx⟩ := Finset.exists_le_of_sum_le
    (s := (Finset.univ : Finset V)) (f := fun _x ↦ (0 : ℚ))
      (g := closedDeletionGain G) huniv hzsum
  exact ⟨x, hx⟩

abbrev outsideSet (x : V) : Set V :=
  (outsideClosedNeighborFinset G x : Set V)

abbrev OutsideVertex (x : V) :=
  outsideSet G x

abbrev outsideGraph (x : V) : SimpleGraph (OutsideVertex G x) :=
  G.induce (outsideSet G x)

set_option maxHeartbeats 800000 in
theorem degree_outsideGraph (x : V) (z : OutsideVertex G x) :
    (outsideGraph G x).degree z = degreeOutsideClosed G x z.1 := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree, degreeOutsideClosed]
  calc
    ((outsideGraph G x).neighborFinset z).card =
        (((outsideGraph G x).neighborFinset z).map
          (Function.Embedding.subtype
            (outsideClosedNeighborFinset G x : Set V))).card :=
      (card_map _).symm
    _ = (G.neighborFinset z.1 ∩ outsideClosedNeighborFinset G x).card := by
      congr 1
      ext y
      constructor
      · intro hy
        rw [Finset.mem_map] at hy
        obtain ⟨w, hw, hwy⟩ := hy
        have hwy' : w.1 = y := by
          exact (Function.Embedding.subtype_apply w).symm.trans hwy
        subst y
        have hw' : G.Adj z.1 w.1 := by
          have hwAdj : (outsideGraph G x).Adj z w :=
            (SimpleGraph.mem_neighborFinset
              (G := outsideGraph G x) (v := z) w).mp hw
          change G.Adj z.1 w.1 at hwAdj
          exact hwAdj
        exact Finset.mem_inter.mpr
          ⟨(SimpleGraph.mem_neighborFinset (G := G) (v := z.1) w.1).mpr hw',
            w.property⟩
      · intro hy
        obtain ⟨hyN, hyout⟩ := Finset.mem_inter.mp hy
        let w : OutsideVertex G x := ⟨y, by simpa [outsideSet] using hyout⟩
        rw [Finset.mem_map]
        exact ⟨w, by simpa [outsideGraph] using hyN, rfl⟩
    _ = (G.neighborFinset z.1 \ closedNeighborFinset G x).card := by
      congr 1
      ext y
      simp [outsideClosedNeighborFinset]

set_option maxHeartbeats 800000 in
theorem graphWeight_outsideGraph (x : V) :
    graphWeight (outsideGraph G x) =
      ∑ z ∈ outsideClosedNeighborFinset G x,
        shearerWeight (degreeOutsideClosed G x z) := by
  rw [graphWeight]
  calc
    (∑ z : OutsideVertex G x, shearerWeight ((outsideGraph G x).degree z)) =
        ∑ z : OutsideVertex G x, shearerWeight (degreeOutsideClosed G x z.1) := by
      apply sum_congr rfl
      intro z _hz
      rw [degree_outsideGraph]
    _ = ∑ z ∈ outsideClosedNeighborFinset G x,
          shearerWeight (degreeOutsideClosed G x z) := by
      symm
      exact Finset.sum_subtype (outsideClosedNeighborFinset G x)
        (fun _z ↦ Iff.rfl) (fun z ↦ shearerWeight (degreeOutsideClosed G x z))

theorem closedDeletionGain_eq (x : V) :
    closedDeletionGain G x =
      1 + graphWeight (outsideGraph G x) - graphWeight G := by
  have hsubset : closedNeighborFinset G x ⊆ (Finset.univ : Finset V) := subset_univ _
  have hpartition :
      (∑ z ∈ (Finset.univ : Finset V) \ closedNeighborFinset G x,
          shearerWeight (G.degree z)) +
        ∑ z ∈ closedNeighborFinset G x, shearerWeight (G.degree z) =
          ∑ z : V, shearerWeight (G.degree z) :=
    Finset.sum_sdiff hsubset
  have hxnot : x ∉ G.neighborFinset x := G.notMem_neighborFinset_self x
  rw [closedDeletionGain, baseDeletionTerm, changeDeletionTerm,
    graphWeight_outsideGraph, graphWeight]
  simp only [outsideClosedNeighborFinset] at hpartition ⊢
  rw [closedNeighborFinset, sum_insert hxnot] at hpartition
  rw [Finset.sum_sub_distrib]
  simp only [closedNeighborFinset]
  linear_combination -hpartition

set_option maxHeartbeats 800000 in
/-- The harmonic graph weight is bounded by the independence number in every
triangle-free finite graph. -/
theorem graphWeight_le_indepNum (htri : G.CliqueFree 3) :
    graphWeight G ≤ (G.indepNum : ℚ) := by
  classical
  let P (α : Type u) [Fintype α] : Prop :=
    ∀ [DecidableEq α] (H : SimpleGraph α) [DecidableRel H.Adj],
      H.CliqueFree 3 → graphWeight H ≤ (H.indepNum : ℚ)
  refine Fintype.induction_subsingleton_or_nontrivial (P := P) V ?_ ?_ G htri
  · intro α _ _ _ H _ _htri
    have hind : H.IsIndepSet ((Finset.univ : Finset α) : Set α) := by
      intro a _ha b _hb hab
      exact (hab (Subsingleton.elim a b)).elim
    calc
      graphWeight H = (Fintype.card α : ℚ) := by
        simp [graphWeight]
      _ ≤ (H.indepNum : ℚ) := by
        exact_mod_cast hind.card_le_indepNum
  · intro α _ _ ih _ H _ htriH
    obtain ⟨x, hxgain⟩ := exists_nonneg_closedDeletionGain H htriH
    have hcard : Fintype.card (OutsideVertex H x) < Fintype.card α := by
      have hproper : outsideClosedNeighborFinset H x ⊂ (Finset.univ : Finset α) := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨Finset.subset_univ _, ?_⟩
        intro heq
        have hxmem : x ∈ outsideClosedNeighborFinset H x := by
          rw [heq]
          simp
        exact (mem_outsideClosedNeighborFinset (G := H).mp hxmem).1 rfl
      let ecard : OutsideVertex H x ≃ ↥(outsideClosedNeighborFinset H x) :=
        { toFun := fun z ↦ ⟨z.1, z.property⟩
          invFun := fun z ↦ ⟨z.1, z.property⟩
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl }
      calc
        Fintype.card (OutsideVertex H x) =
            Fintype.card ↥(outsideClosedNeighborFinset H x) :=
          Fintype.card_congr ecard
        _ = (outsideClosedNeighborFinset H x).card :=
          Fintype.card_coe _
        _ < Fintype.card α := by
          have hc := Finset.card_lt_card hproper
          rw [Finset.card_univ] at hc
          exact hc
    have htriOut : (outsideGraph H x).CliqueFree 3 :=
      SimpleGraph.CliqueFree.comap
        (SimpleGraph.Embedding.induce (outsideSet H x)).isContained htriH
    have ihOut : graphWeight (outsideGraph H x) ≤
        ((outsideGraph H x).indepNum : ℚ) :=
      ih (OutsideVertex H x) hcard (outsideGraph H x) htriOut
    obtain ⟨C, hC⟩ := (outsideGraph H x).exists_isNIndepSet_indepNum
    let e : OutsideVertex H x ↪ α := Function.Embedding.subtype _
    let D : Finset α := C.map e
    have hD : H.IsIndepSet (D : Set α) := by
      intro a ha b hb hab
      simp only [D, Finset.mem_coe, Finset.mem_map] at ha hb
      obtain ⟨a', ha'C, rfl⟩ := ha
      obtain ⟨b', hb'C, rfl⟩ := hb
      exact hC.isIndepSet ha'C hb'C (fun heq ↦ hab (congrArg Subtype.val heq))
    have hxD : x ∉ D := by
      intro hx
      change x ∈ C.map e at hx
      rw [Finset.mem_map] at hx
      obtain ⟨z, _hzC, hzx⟩ := hx
      exact (mem_outsideClosedNeighborFinset (G := H).mp z.property).1
        (by simpa [e] using hzx)
    have hIns : H.IsIndepSet ((insert x D : Finset α) : Set α) := by
      rw [Finset.coe_insert]
      let _ : Std.Symm (fun v w ↦ ¬H.Adj v w) :=
        ⟨fun _ _ hab hba ↦ hab hba.symm⟩
      apply hD.insert_of_symm
      intro b hb _hxb
      simp only [D, Finset.mem_coe, Finset.mem_map] at hb
      obtain ⟨z, _hzC, rfl⟩ := hb
      exact (mem_outsideClosedNeighborFinset (G := H).mp z.property).2
    have hnat : (outsideGraph H x).indepNum + 1 ≤ H.indepNum := by
      calc
        (outsideGraph H x).indepNum + 1 = C.card + 1 :=
          congrArg (· + 1) hC.card_eq.symm
        _ = D.card + 1 := by simp [D]
        _ = (insert x D).card := by rw [card_insert_of_notMem hxD]
        _ ≤ H.indepNum := hIns.card_le_indepNum
    have hdelete : graphWeight H ≤ 1 + graphWeight (outsideGraph H x) := by
      rw [closedDeletionGain_eq] at hxgain
      linarith
    calc
      graphWeight H ≤ 1 + graphWeight (outsideGraph H x) := hdelete
      _ ≤ 1 + ((outsideGraph H x).indepNum : ℚ) := by linarith
      _ = (((outsideGraph H x).indepNum + 1 : ℕ) : ℚ) := by push_cast; ring
      _ ≤ (H.indepNum : ℚ) := by exact_mod_cast hnat

end FiniteGraph

end Erdos788.AKSRoute


/-! Flattened from Erdos788.ShearerAverage. -/


/-!
# Extracting an average-degree bound from the Shearer weight

This file isolates the elementary truncation argument used after the
triangle-free induction.  It requires only an upper bound for the total
degree and the already established comparison between graph weight and
independence number.
-/

namespace Erdos788.AKSRoute

open Finset

theorem shearerWeight_nonneg (d : ℕ) : 0 ≤ shearerWeight d := by
  rcases d with (_ | d)
  · simp
  · rw [shearerWeight_succ]
    exact div_nonneg (by linarith [one_le_harmonic_succ d]) (by positivity)

section FiniteGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in
/-- At least half the vertices have degree below twice any valid average
degree bound. -/
theorem card_le_two_mul_card_degree_lt
    {K : ℕ} (hK : 0 < K)
    (hdegree : ∑ v : V, G.degree v ≤ K * Fintype.card V) :
    Fintype.card V ≤
      2 * ((Finset.univ : Finset V).filter (fun v ↦ G.degree v < 2 * K)).card := by
  let bad := (Finset.univ : Finset V).filter (fun v ↦ 2 * K ≤ G.degree v)
  let good := (Finset.univ : Finset V).filter (fun v ↦ G.degree v < 2 * K)
  have hbadDegree : 2 * K * bad.card ≤ ∑ v : V, G.degree v := by
    calc
      2 * K * bad.card = ∑ _v ∈ bad, 2 * K := by simp [mul_comm]
      _ ≤ ∑ v ∈ bad, G.degree v := by
        apply Finset.sum_le_sum
        intro v hv
        exact (Finset.mem_filter.mp hv).2
      _ ≤ ∑ v : V, G.degree v := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro v _hv _hbad
        exact Nat.zero_le _
  have hbadScaled : K * (2 * bad.card) ≤ K * Fintype.card V := by
    calc
      K * (2 * bad.card) = 2 * K * bad.card := by ring
      _ ≤ ∑ v : V, G.degree v := hbadDegree
      _ ≤ K * Fintype.card V := hdegree
  have hbad : 2 * bad.card ≤ Fintype.card V := by
    exact Nat.le_of_mul_le_mul_left hbadScaled hK
  have hpartition : bad.card + good.card = Fintype.card V := by
    simpa [bad, good, not_le] using
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset V)) (fun v ↦ 2 * K ≤ G.degree v))
  change Fintype.card V ≤ 2 * good.card
  omega

omit [DecidableEq V] in
/-- A total-degree bound converts the harmonic graph weight into a global
independence estimate, without a Jensen inequality. -/
theorem card_mul_shearerWeight_le_two_mul_indepNum
    {K : ℕ} (hK : 0 < K)
    (hdegree : ∑ v : V, G.degree v ≤ K * Fintype.card V)
    (hweight : graphWeight G ≤ (G.indepNum : ℚ)) :
    (Fintype.card V : ℚ) * shearerWeight (2 * K) ≤
      2 * (G.indepNum : ℚ) := by
  let good := (Finset.univ : Finset V).filter (fun v ↦ G.degree v < 2 * K)
  have hgoodCard : Fintype.card V ≤ 2 * good.card := by
    simpa [good] using card_le_two_mul_card_degree_lt G hK hdegree
  have hw0 : (0 : ℚ) ≤ shearerWeight (2 * K) :=
    shearerWeight_nonneg _
  have hcard : (Fintype.card V : ℚ) * shearerWeight (2 * K) ≤
      (2 * good.card : ℕ) * shearerWeight (2 * K) := by
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hgoodCard) hw0
  have hgoodWeight : (good.card : ℚ) * shearerWeight (2 * K) ≤
      ∑ v ∈ good, shearerWeight (G.degree v) := by
    calc
      (good.card : ℚ) * shearerWeight (2 * K) =
          ∑ _v ∈ good, shearerWeight (2 * K) := by simp
      _ ≤ ∑ v ∈ good, shearerWeight (G.degree v) := by
        apply Finset.sum_le_sum
        intro v hv
        exact shearerWeight_antitone
          (Nat.le_of_lt (Finset.mem_filter.mp hv).2)
  have hgoodLe : (∑ v ∈ good, shearerWeight (G.degree v)) ≤
      graphWeight G := by
    rw [graphWeight]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro v _hv _hgood
    exact shearerWeight_nonneg _
  calc
    (Fintype.card V : ℚ) * shearerWeight (2 * K) ≤
        (2 * good.card : ℕ) * shearerWeight (2 * K) := hcard
    _ = 2 * ((good.card : ℚ) * shearerWeight (2 * K)) := by
      push_cast
      ring
    _ ≤ 2 * (∑ v ∈ good, shearerWeight (G.degree v)) := by gcongr
    _ ≤ 2 * graphWeight G := by gcongr
    _ ≤ 2 * (G.indepNum : ℚ) := by gcongr

omit [DecidableEq V] in
/-- Real-valued logarithmic form of the preceding truncation estimate. -/
theorem card_mul_log_le_eight_mul_average_mul_indepNum
    {K : ℕ} (hK : 0 < K)
    (hdegree : ∑ v : V, G.degree v ≤ K * Fintype.card V)
    (hweight : graphWeight G ≤ (G.indepNum : ℚ)) :
    (Fintype.card V : ℝ) * Real.log (2 * K + 1 : ℕ) ≤
      8 * K * (G.indepNum : ℝ) := by
  have hw := card_mul_shearerWeight_le_two_mul_indepNum
    G hK hdegree hweight
  have hwR : (Fintype.card V : ℝ) * (shearerWeight (2 * K) : ℝ) ≤
      2 * (G.indepNum : ℝ) := by
    exact_mod_cast hw
  have hlog := log_le_two_mul_nat_mul_shearerWeight
    (d := 2 * K) (by positivity)
  have hlog' : Real.log ((2 * K + 1 : ℕ) : ℝ) ≤
      (2 * (2 * K) : ℝ) * (shearerWeight (2 * K) : ℝ) := by
    push_cast at hlog ⊢
    exact hlog
  calc
    (Fintype.card V : ℝ) * Real.log (2 * K + 1 : ℕ) ≤
        (Fintype.card V : ℝ) *
          ((2 * (2 * K) : ℝ) * (shearerWeight (2 * K) : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog' (by positivity)
    _ = (4 * K : ℝ) *
        ((Fintype.card V : ℝ) * (shearerWeight (2 * K) : ℝ)) := by
      ring
    _ ≤ (4 * K : ℝ) * (2 * (G.indepNum : ℝ)) := by gcongr
    _ = 8 * K * (G.indepNum : ℝ) := by
      ring

end FiniteGraph

end Erdos788.AKSRoute


/-! Flattened from Erdos788.SampledShearer. -/


/-!
# A logarithmic lower bound from the triangle-free sample

This file combines the exact finite sampling statement with the harmonic
weight bound for triangle-free graphs.  The only rounding loss comes from
replacing the sampled average degree by an integer upper bound.
-/

namespace Erdos788

open Finset

/-- Clearing a positive natural denominator, with one unit of rounding,
turns an edge bound into a total-degree bound. -/
private theorem two_mul_le_rounded_average
    {q B e r : ℕ} (hq : 0 < q) (hedge : q * e ≤ 2 * B * r) :
    2 * e ≤ (2 * (2 * B / q + 1)) * r := by
  have hround : 2 * B ≤ q * (2 * B / q + 1) :=
    (Nat.lt_mul_div_succ (2 * B) hq).le
  have hqedge : q * e ≤ q * ((2 * B / q + 1) * r) := by
    calc
      q * e ≤ 2 * B * r := hedge
      _ ≤ (q * (2 * B / q + 1)) * r :=
        Nat.mul_le_mul_right r hround
      _ = q * ((2 * B / q + 1) * r) := by
        simp only [mul_assoc]
  have he : e ≤ (2 * B / q + 1) * r :=
    Nat.le_of_mul_le_mul_left hqedge hq
  calc
    2 * e ≤ 2 * ((2 * B / q + 1) * r) := Nat.mul_le_mul_left 2 he
    _ = (2 * (2 * B / q + 1)) * r := by simp only [mul_assoc]

/-- Exact sampling followed by the triangle-free Shearer estimate.  Here
`q = 2^t`, `B = |A| + 1`, and `K` is an integral upper bound for the average
degree of the triangle-free sample. -/
theorem sumGraph_indepNum_log_lower {N : ℕ} (A : Finset ℕ) (t : ℕ)
    (hscale : 2 * A.card ^ 3 ≤ N * (2 ^ t) ^ 2) :
    let q : ℕ := 2 ^ t
    let B : ℕ := A.card + 1
    let K : ℕ := 2 * (2 * B / q + 1)
    (N : ℝ) * Real.log (2 * K + 1 : ℕ) ≤
      16 * q * K * ((sumGraph N A).indepNum : ℝ) := by
  classical
  let q : ℕ := 2 ^ t
  let B : ℕ := A.card + 1
  let K : ℕ := 2 * (2 * B / q + 1)
  change (N : ℝ) * Real.log (2 * K + 1 : ℕ) ≤
    16 * q * K * ((sumGraph N A).indepNum : ℝ)
  have hq : 0 < q := by
    simp [q]
  have hK : 0 < K := by
    simp [K]
  obtain ⟨R, htriangleFree, hcard, hedge⟩ :=
    exists_triangleFree_sample A t hscale
  let H := (sumGraph N A).induce (R : Set (Fin N))
  have hedge' : q * (H.cliqueFinset 2).card ≤ 2 * B * R.card := by
    simpa only [q, B, H] using hedge
  have hRtypeCard : Fintype.card ↑(R : Set (Fin N)) = R.card := by
    rw [← Set.toFinset_card]
    simp
  have hdegree : ∑ v, H.degree v ≤ K * Fintype.card ↑(R : Set (Fin N)) := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges]
    rw [← card_cliqueFinset_two_eq_card_edgeFinset (G := H)]
    rw [hRtypeCard]
    simpa only [K] using
      (two_mul_le_rounded_average hq hedge')
  have hweight : AKSRoute.graphWeight H ≤ (H.indepNum : ℚ) :=
    AKSRoute.graphWeight_le_indepNum H (by simpa only [H] using htriangleFree)
  have hsampleLog :=
    AKSRoute.card_mul_log_le_eight_mul_average_mul_indepNum
      H hK hdegree hweight
  have hsampleLog' :
      (R.card : ℝ) * Real.log (2 * K + 1 : ℕ) ≤
        8 * K * (H.indepNum : ℝ) := by
    rw [← hRtypeCard]
    exact hsampleLog
  have hcardQ : (N : ℚ) / (2 * (q : ℚ)) ≤ (R.card : ℚ) := by
    simpa only [q, Nat.cast_pow, Nat.cast_ofNat] using hcard
  have hcardR : (N : ℝ) / (2 * (q : ℝ)) ≤ (R.card : ℝ) := by
    have hcardRcast := (Rat.cast_le (K := ℝ)).2 hcardQ
    push_cast at hcardRcast
    exact hcardRcast
  have hNle : (N : ℝ) ≤ (R.card : ℝ) * (2 * q) :=
    (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * q)).mp hcardR
  have hlogNonneg : 0 ≤ Real.log ((2 * K + 1 : ℕ) : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ 2 * K + 1 by omega)
  have hind : (H.indepNum : ℝ) ≤ ((sumGraph N A).indepNum : ℝ) := by
    exact_mod_cast (by
      simpa only [H] using
        (indepNum_induce_finset_le (G := sumGraph N A) R))
  calc
    (N : ℝ) * Real.log (2 * K + 1 : ℕ) ≤
        ((R.card : ℝ) * (2 * q)) * Real.log (2 * K + 1 : ℕ) :=
      mul_le_mul_of_nonneg_right hNle hlogNonneg
    _ = (2 * q) *
        ((R.card : ℝ) * Real.log (2 * K + 1 : ℕ)) := by ring
    _ ≤ (2 * q) * (8 * K * (H.indepNum : ℝ)) := by
      gcongr
    _ ≤ (2 * q) *
        (8 * K * ((sumGraph N A).indepNum : ℝ)) := by
      gcongr
    _ = 16 * q * K * ((sumGraph N A).indepNum : ℝ) := by ring

end Erdos788


/-! Flattened from Erdos788.LowerArithmetic. -/


/-!
# Arithmetic estimates for the lower bound

These lemmas turn the minimal power-of-two sampling scale into a logarithmic
degree cutoff.  They are kept separate from the finite graph argument.
-/

namespace Erdos788

/-- The average-degree cutoff forced by a minimal sampling exponent grows
at least like the square root of `N / b`. -/
theorem cutoff_growth {N b q : ℕ} (hN : 0 < N) (hq : 0 < q)
    (hupper : N * q ^ 2 < 8 * b ^ 3) :
    8 * N < b * (8 * (b + 1) / q + 1) ^ 2 := by
  let D := 8 * (b + 1) / q
  have hdiv : 8 * (b + 1) < q * (D + 1) := by
    exact Nat.lt_mul_div_succ _ hq
  have hsq : (8 * (b + 1)) ^ 2 < (q * (D + 1)) ^ 2 :=
    Nat.pow_lt_pow_left hdiv (by norm_num)
  have hchain : N * (8 * (b + 1)) ^ 2 <
      (8 * b ^ 3) * (D + 1) ^ 2 := by
    calc
      N * (8 * (b + 1)) ^ 2 < N * (q * (D + 1)) ^ 2 :=
        (Nat.mul_lt_mul_left hN).2 hsq
      _ = (N * q ^ 2) * (D + 1) ^ 2 := by ring
      _ < (8 * b ^ 3) * (D + 1) ^ 2 :=
        (Nat.mul_lt_mul_right (by positivity : 0 < (D + 1) ^ 2)).2 hupper
  have hcancel : 8 * N * (b + 1) ^ 2 < b ^ 3 * (D + 1) ^ 2 := by
    nlinarith
  have hb : 0 < b := by
    have hleft : 0 < N * q ^ 2 := Nat.mul_pos hN (pow_pos hq _)
    have hright : 0 < 8 * b ^ 3 := hleft.trans hupper
    by_contra hb
    simp only [Nat.not_lt, Nat.le_zero] at hb
    simp [hb] at hright
  have hbsq : b ^ 2 ≤ (b + 1) ^ 2 := by nlinarith
  have hmul : b ^ 2 * (8 * N) < b ^ 2 * (b * (D + 1) ^ 2) := by
    calc
      b ^ 2 * (8 * N) ≤ 8 * N * (b + 1) ^ 2 := by
        nlinarith
      _ < b ^ 3 * (D + 1) ^ 2 := hcancel
      _ = b ^ 2 * (b * (D + 1) ^ 2) := by ring
  have hb2 : 0 < b ^ 2 := by positivity
  have := (Nat.mul_lt_mul_left hb2).mp hmul
  simpa only [D] using this

/-- In the small-palette branch, the cutoff furnished by minimal sampling
has logarithm comparable with `log N`. -/
theorem log_le_eight_log_cutoff {N b d : ℕ} (hN : 2 ≤ N)
    (hcut : 8 * N < b * d ^ 2)
    (hb : (b : ℝ) ≤ Real.sqrt ((N : ℝ) * Real.log (N : ℝ))) :
    Real.log (N : ℝ) ≤ 8 * Real.log (d : ℝ) := by
  let n : ℝ := N
  let br : ℝ := b
  let dr : ℝ := d
  let L : ℝ := Real.log n
  let s : ℝ := Real.sqrt n
  have hn : 0 < n := by positivity
  have hnone : (1 : ℝ) ≤ n := by
    simpa [n] using (show (1 : ℝ) ≤ (N : ℝ) by
      exact_mod_cast (show 1 ≤ N by omega))
  have hL : 0 ≤ L := Real.log_nonneg hnone
  have htarget : 0 ≤ n * L := mul_nonneg hn.le hL
  have htargetSq : (Real.sqrt (n * L)) ^ 2 = n * L := Real.sq_sqrt htarget
  have hb0 : 0 ≤ br := by positivity
  have hbSq : br ^ 2 ≤ n * L := by
    calc
      br ^ 2 ≤ (Real.sqrt (n * L)) ^ 2 :=
        (sq_le_sq₀ hb0 (Real.sqrt_nonneg _)).2 (by simpa [br, n, L] using hb)
      _ = n * L := htargetSq
  have hcutR : (8 : ℝ) * n < br * dr ^ 2 := by
    simpa [n, br, dr] using
      (show (8 : ℝ) * (N : ℝ) < (b : ℝ) * (d : ℝ) ^ 2 by
        exact_mod_cast hcut)
  have hcutSq : ((8 : ℝ) * n) ^ 2 < (br * dr ^ 2) ^ 2 := by
    simpa [pow_two] using mul_self_lt_mul_self (by positivity) hcutR
  have hfirst : ((8 : ℝ) * n) ^ 2 < (n * L) * dr ^ 4 := by
    calc
      ((8 : ℝ) * n) ^ 2 < (br * dr ^ 2) ^ 2 := hcutSq
      _ = br ^ 2 * dr ^ 4 := by ring
      _ ≤ (n * L) * dr ^ 4 :=
        mul_le_mul_of_nonneg_right hbSq (by positivity)
  have hfirst' : n * ((64 : ℝ) * n) < n * (L * dr ^ 4) := by
    nlinarith
  have h64 : (64 : ℝ) * n < L * dr ^ 4 :=
    lt_of_mul_lt_mul_left hfirst' hn.le
  have hlogSqrt : L ≤ 2 * s := by
    simpa [L, n, s, Real.sqrt_eq_rpow, mul_comm] using
      (Real.log_natCast_le_rpow_div N (by norm_num : (0 : ℝ) < 1 / 2))
  have h64' : (64 : ℝ) * n < (2 * s) * dr ^ 4 :=
    h64.trans_le (mul_le_mul_of_nonneg_right hlogSqrt (by positivity))
  have hspos : 0 < s := Real.sqrt_pos.2 hn
  have hsSq : s ^ 2 = n := Real.sq_sqrt hn.le
  have hcancelForm : (2 * s) * (32 * s) < (2 * s) * dr ^ 4 := by
    nlinarith
  have h32 : (32 : ℝ) * s < dr ^ 4 :=
    lt_of_mul_lt_mul_left hcancelForm (by positivity)
  have hsq2 : ((32 : ℝ) * s) ^ 2 < (dr ^ 4) ^ 2 := by
    simpa [pow_two] using mul_self_lt_mul_self (by positivity) h32
  have hNd : n < dr ^ 8 := by
    nlinarith
  have hd : 0 < d := by
    by_contra hd
    simp only [Nat.not_lt, Nat.le_zero] at hd
    simp [hd] at hcut
  have hdr : 0 < dr := by
    simpa [dr] using (show (0 : ℝ) < (d : ℝ) by positivity)
  calc
    Real.log (N : ℝ) = L := by rfl
    _ ≤ Real.log (dr ^ 8) := Real.log_le_log hn hNd.le
    _ = 8 * Real.log (d : ℝ) := by
      rw [Real.log_pow]
      norm_num [dr]

end Erdos788


/-! Flattened from Erdos788.LowerAnalytic. -/


/-! # Elementary analytic comparisons for the lower bound -/

namespace Erdos788

/-- For `N ≥ 2`, the square-root logarithmic scale is at most `N`. -/
theorem sqrt_mul_log_le_self {N : ℕ} (hN : 2 ≤ N) :
    Real.sqrt ((N : ℝ) * Real.log (N : ℝ)) ≤ (N : ℝ) := by
  let n : ℝ := N
  have hn : 0 < n := by positivity
  have hlogNonneg : 0 ≤ Real.log n := by
    apply Real.log_nonneg
    simpa [n] using
      (show (1 : ℝ) ≤ (N : ℝ) by exact_mod_cast (show 1 ≤ N by omega))
  have hlog : Real.log n ≤ n := by
    have := Real.log_le_sub_one_of_pos hn
    linarith
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · have hmul := mul_le_mul_of_nonneg_left hlog hn.le
    nlinarith

/-- If `b⁴ ≤ N`, multiplying the square-root logarithmic scale by `b + 1`
still costs only a constant multiple of `N`. -/
theorem add_one_mul_sqrt_mul_log_le_four {N b : ℕ} (hN : 2 ≤ N)
    (hb4 : b ^ 4 ≤ N) :
    ((b + 1 : ℕ) : ℝ) * Real.sqrt ((N : ℝ) * Real.log (N : ℝ)) ≤
      4 * (N : ℝ) := by
  let n : ℝ := N
  let br : ℝ := b
  let r : ℝ := Real.sqrt n
  let L : ℝ := Real.log n
  let s : ℝ := Real.sqrt (n * L)
  have hn : 0 < n := by positivity
  have hnOne : 1 ≤ n := by
    simpa [n] using
      (show (1 : ℝ) ≤ (N : ℝ) by exact_mod_cast (show 1 ≤ N by omega))
  have hL : 0 ≤ L := Real.log_nonneg hnOne
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hrSq : r ^ 2 = n := by
    exact Real.sq_sqrt hn.le
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hsSq : s ^ 2 = n * L := by
    exact Real.sq_sqrt (mul_nonneg hn.le hL)
  have hlog : L ≤ 2 * r := by
    simpa [L, n, r, Real.sqrt_eq_rpow, mul_comm] using
      (Real.log_natCast_le_rpow_div N (by norm_num : (0 : ℝ) < 1 / 2))
  by_cases hb : b = 0
  · subst b
    have hsmall := sqrt_mul_log_le_self hN
    dsimp [n, br, r, L, s] at *
    norm_num at *
    nlinarith
  · have hbNat : 1 ≤ b := Nat.one_le_iff_ne_zero.mpr hb
    have hbrOne : 1 ≤ br := by
      simpa [br] using (show (1 : ℝ) ≤ (b : ℝ) by exact_mod_cast hbNat)
    have hb4R : br ^ 4 ≤ n := by
      simpa [br, n] using
        (show (b : ℝ) ^ 4 ≤ (N : ℝ) by exact_mod_cast hb4)
    have hbrSqSq : (br ^ 2) ^ 2 ≤ r ^ 2 := by
      nlinarith [hb4R, hrSq]
    have hbrSq : br ^ 2 ≤ r := by
      exact (sq_le_sq₀ (sq_nonneg br) hr).mp hbrSqSq
    have hbrLog : br ^ 2 * L ≤ 2 * n := by
      calc
        br ^ 2 * L ≤ r * (2 * r) :=
          mul_le_mul hbrSq hlog hL hr
        _ = 2 * n := by rw [← hrSq]; ring
    have haddSq : (br + 1) ^ 2 ≤ 4 * br ^ 2 := by
      nlinarith
    have hscale : (br + 1) ^ 2 * (n * L) ≤
        (4 * br ^ 2) * (n * L) :=
      mul_le_mul_of_nonneg_right haddSq (mul_nonneg hn.le hL)
    have hbound : (4 * br ^ 2) * (n * L) ≤ 8 * n ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_left hbrLog
        (show 0 ≤ 4 * n by positivity)
      nlinarith
    have hsqBound : ((br + 1) * s) ^ 2 ≤ (4 * n) ^ 2 := by
      calc
        ((br + 1) * s) ^ 2 = (br + 1) ^ 2 * (n * L) := by
          rw [mul_pow, hsSq]
        _ ≤ (4 * br ^ 2) * (n * L) := hscale
        _ ≤ 8 * n ^ 2 := hbound
        _ ≤ (4 * n) ^ 2 := by nlinarith [sq_nonneg n]
    have hmain : (br + 1) * s ≤ 4 * n := by
      exact (sq_le_sq₀ (mul_nonneg (by positivity) hs) (by positivity)).mp hsqBound
    simpa [br, s, n, L] using hmain

/-- If `N` is below `b⁴` and `d ≥ b`, then `log d` controls `log N`. -/
theorem log_le_four_log_of_lt_fourth_power {N b d : ℕ}
    (hN : 0 < N) (hNb : N < b ^ 4) (hbd : b ≤ d) :
    Real.log (N : ℝ) ≤ 4 * Real.log (d : ℝ) := by
  have hNdNat : N ≤ d ^ 4 :=
    hNb.le.trans (Nat.pow_le_pow_left hbd 4)
  have hNR : (0 : ℝ) < (N : ℝ) := by positivity
  have hNdR : (N : ℝ) ≤ (d : ℝ) ^ 4 := by
    exact_mod_cast hNdNat
  calc
    Real.log (N : ℝ) ≤ Real.log ((d : ℝ) ^ 4) :=
      Real.log_le_log hNR hNdR
    _ = 4 * Real.log (d : ℝ) := by
      rw [Real.log_pow]
      norm_num

end Erdos788


/-! Flattened from Erdos788.Normalization. -/


/-!
# Exact normalization for Erdős Problem 788

This production module proves that translating `I n` by `n + 1` identifies its vertex
type with `Fin (n - 1)`.  It also records the exact attainable sum interval,
the two palette translations, the resulting graph isomorphism, and the fact
that deleting colors which occur on no edge can only decrease the graph
score.
-/

namespace Erdos788

open Finset

/-- The constant term in the identity
`(n + 1 + x) + (n + 1 + y) = sumOffset n + x + y`. -/
def sumOffset (n : ℕ) : ℕ :=
  2 * n + 2

/-- Exact translation of `(n,2n) ∩ ℕ` to `0, ..., n - 2`.

The equivalence is valid for every `n`; for `n = 0,1` both types are empty.
-/
def vertexEquivFin (n : ℕ) : Vertex n ≃ Fin (n - 1) where
  toFun c := ⟨c.1 - (n + 1), by
    have hc := Finset.mem_Ioo.mp c.2
    omega⟩
  invFun x := ⟨n + 1 + x.1, by
    rw [show I n = Finset.Ioo n (2 * n) from rfl, Finset.mem_Ioo]
    omega⟩
  left_inv c := by
    apply Subtype.ext
    have hc := Finset.mem_Ioo.mp c.2
    simp only
    omega
  right_inv x := by
    apply Fin.ext
    simp only
    omega

@[simp]
theorem vertexEquivFin_apply_val (n : ℕ) (c : Vertex n) :
    (vertexEquivFin n c).1 = c.1 - (n + 1) :=
  rfl

@[simp]
theorem vertexEquivFin_symm_val (n : ℕ) (x : Fin (n - 1)) :
    ((vertexEquivFin n).symm x).1 = n + 1 + x.1 :=
  rfl

/-- Endpoint form of the vertex normalization: `c = n + 1 + x`. -/
theorem vertex_eq_offset_add_normalized (n : ℕ) (c : Vertex n) :
    c.1 = n + 1 + (vertexEquivFin n c).1 := by
  have hc := Finset.mem_Ioo.mp c.2
  simp only [vertexEquivFin_apply_val]
  omega

/-- Distinct (indeed arbitrary) pair sums translate by `2n+2`. -/
theorem vertex_sum_eq_normalized (n : ℕ) (c c' : Vertex n) :
    c.1 + c'.1 =
      sumOffset n + (vertexEquivFin n c).1 + (vertexEquivFin n c').1 := by
  rw [vertex_eq_offset_add_normalized n c,
    vertex_eq_offset_add_normalized n c']
  simp only [sumOffset]
  omega

/-- The proposition that `s` is the sum of two distinct elements of `Fin N`. -/
def IsAttainableNormalizedSum (N s : ℕ) : Prop :=
  ∃ x y : Fin N, x ≠ y ∧ x.1 + y.1 = s

/-- The exact interval of normalized sums supplied by distinct pairs. -/
def attainableNormalizedSums (N : ℕ) : Finset ℕ :=
  Finset.Icc 1 (2 * N - 3)

/-- Distinct elements of `Fin N` have precisely the sums
`1, ..., 2N - 3`.  The statement includes `N = 0,1`, where both sides are
empty. -/
theorem isAttainableNormalizedSum_iff_mem (N s : ℕ) :
    IsAttainableNormalizedSum N s ↔ s ∈ attainableNormalizedSums N := by
  rw [attainableNormalizedSums, Finset.mem_Icc]
  constructor
  · rintro ⟨x, y, hxy, rfl⟩
    have hx := x.2
    have hy := y.2
    have hval : x.1 ≠ y.1 := fun h ↦ hxy (Fin.ext h)
    omega
  · rintro ⟨hs1, hsmax⟩
    by_cases hsN : s < N
    · let x : Fin N := ⟨0, by omega⟩
      let y : Fin N := ⟨s, hsN⟩
      refine ⟨x, y, ?_, ?_⟩
      · intro hxy
        have := congrArg Fin.val hxy
        simp only [x, y] at this
        omega
      · simp [x, y]
    · let x : Fin N := ⟨N - 1, by omega⟩
      let y : Fin N := ⟨s - (N - 1), by omega⟩
      refine ⟨x, y, ?_, ?_⟩
      · intro hxy
        have := congrArg Fin.val hxy
        simp only [x, y] at this
        omega
      · simp only [x, y]
        omega

/-- Set-level wording of the exact attainable-sum result. -/
theorem mem_attainableNormalizedSums_iff (N s : ℕ) :
    s ∈ attainableNormalizedSums N ↔
      ∃ x y : Fin N, x ≠ y ∧ x.1 + y.1 = s := by
  exact (isAttainableNormalizedSum_iff_mem N s).symm

/-- The selected normalized colors: retain exactly the attainable normalized
sums whose translate by `2n+2` belongs to `B`. -/
def normalizePalette (n : ℕ) (B : Finset ℕ) : Finset ℕ :=
  (attainableNormalizedSums (n - 1)).filter
    fun s ↦ sumOffset n + s ∈ B

/-- Translate a normalized palette back by adding `2n+2`; normalized colors
outside the attainable interval are discarded. -/
def denormalizePalette (n : ℕ) (A : Finset ℕ) : Finset ℕ :=
  (A.filter fun s ↦ s ∈ attainableNormalizedSums (n - 1)).image
    fun s ↦ sumOffset n + s

@[simp]
theorem mem_normalizePalette {n s : ℕ} {B : Finset ℕ} :
    s ∈ normalizePalette n B ↔
      s ∈ attainableNormalizedSums (n - 1) ∧ sumOffset n + s ∈ B := by
  simp [normalizePalette]

@[simp]
theorem mem_denormalizePalette {n b : ℕ} {A : Finset ℕ} :
    b ∈ denormalizePalette n A ↔
      ∃ s, s ∈ A ∧ s ∈ attainableNormalizedSums (n - 1) ∧
        sumOffset n + s = b := by
  simp only [denormalizePalette, Finset.mem_image, Finset.mem_filter]
  aesop

/-- Translating to original coordinates and back retains exactly the
attainable part of a normalized palette. -/
theorem normalizePalette_denormalizePalette (n : ℕ) (A : Finset ℕ) :
    normalizePalette n (denormalizePalette n A) =
      A.filter fun s ↦ s ∈ attainableNormalizedSums (n - 1) := by
  ext s
  simp only [mem_normalizePalette, mem_denormalizePalette, Finset.mem_filter]
  constructor
  · rintro ⟨hsatt, t, htA, htatt, heq⟩
    have hst : s = t := by omega
    simpa [hst] using ⟨htA, htatt⟩
  · rintro ⟨hsA, hsatt⟩
    exact ⟨hsatt, s, hsA, hsatt, rfl⟩

/-- The part of `B` which is the sum of an actual pair of distinct original
vertices. -/
def activePalette (n : ℕ) (B : Finset ℕ) : Finset ℕ :=
  B.filter fun b ↦ ∃ c c' : Vertex n, c ≠ c' ∧ c.1 + c'.1 = b

@[simp]
theorem mem_activePalette {n b : ℕ} {B : Finset ℕ} :
    b ∈ activePalette n B ↔
      b ∈ B ∧ ∃ c c' : Vertex n, c ≠ c' ∧ c.1 + c'.1 = b := by
  simp [activePalette]

/-- Translating an original palette down and back gives precisely its active
part. -/
theorem denormalizePalette_normalizePalette (n : ℕ) (B : Finset ℕ) :
    denormalizePalette n (normalizePalette n B) = activePalette n B := by
  ext b
  simp only [mem_denormalizePalette, mem_normalizePalette, mem_activePalette]
  constructor
  · rintro ⟨s, ⟨hsatt, hsB⟩, _hsatt', hsb⟩
    refine ⟨?_, ?_⟩
    · simpa [hsb] using hsB
    · obtain ⟨x, y, hxy, hsum⟩ :=
        (mem_attainableNormalizedSums_iff (n - 1) s).mp hsatt
      let c : Vertex n := (vertexEquivFin n).symm x
      let c' : Vertex n := (vertexEquivFin n).symm y
      refine ⟨c, c', ?_, ?_⟩
      · exact fun h ↦ hxy ((vertexEquivFin n).symm.injective h)
      · rw [vertex_sum_eq_normalized n c c']
        simp only [c, c', Equiv.apply_symm_apply]
        omega
  · rintro ⟨hbB, c, c', hcc', rfl⟩
    let x : Fin (n - 1) := vertexEquivFin n c
    let y : Fin (n - 1) := vertexEquivFin n c'
    have hxy : x ≠ y := fun h ↦ hcc' ((vertexEquivFin n).injective h)
    have hsatt : x.1 + y.1 ∈ attainableNormalizedSums (n - 1) :=
      (mem_attainableNormalizedSums_iff (n - 1) (x.1 + y.1)).mpr
        ⟨x, y, hxy, rfl⟩
    refine ⟨x.1 + y.1, ⟨hsatt, ?_⟩, hsatt, ?_⟩
    · rw [show sumOffset n + (x.1 + y.1) = c.1 + c'.1 by
          simpa [x, y, Nat.add_assoc] using
            (vertex_sum_eq_normalized n c c').symm]
      exact hbB
    · simpa [x, y, Nat.add_assoc] using
        (vertex_sum_eq_normalized n c c').symm

/-- Adding the fixed offset is injective, so denormalization preserves the
cardinality of the attainable part of a normalized palette. -/
theorem card_denormalizePalette (n : ℕ) (A : Finset ℕ) :
    (denormalizePalette n A).card =
      (A.filter fun s ↦ s ∈ attainableNormalizedSums (n - 1)).card := by
  rw [denormalizePalette]
  apply Finset.card_image_of_injective
  intro s t hst
  exact Nat.add_left_cancel hst

/-- The active original palette and its normalized translate have exactly
the same number of colors. -/
theorem card_activePalette_eq_card_normalizePalette
    (n : ℕ) (B : Finset ℕ) :
    (activePalette n B).card = (normalizePalette n B).card := by
  calc
    (activePalette n B).card =
        (denormalizePalette n (normalizePalette n B)).card :=
      congrArg Finset.card (denormalizePalette_normalizePalette n B).symm
    _ = ((normalizePalette n B).filter
          fun s ↦ s ∈ attainableNormalizedSums (n - 1)).card :=
      card_denormalizePalette n (normalizePalette n B)
    _ = (normalizePalette n B).card := by
      congr 1
      apply Finset.filter_eq_self.mpr
      intro s hs
      exact (mem_normalizePalette.mp hs).1

/-- The original palette graph is exactly the normalized sum graph, up to
the coordinate equivalence. -/
def paletteGraphIso (n : ℕ) (B : Finset ℕ) :
    paletteGraph n B ≃g sumGraph (n - 1) (normalizePalette n B) where
  toEquiv := vertexEquivFin n
  map_rel_iff' := by
    intro c c'
    rw [paletteGraph_adj, sumGraph_adj]
    constructor
    · rintro ⟨hxy, hmem⟩
      have hcc' : c ≠ c' := fun h ↦ hxy (congrArg (vertexEquivFin n) h)
      refine ⟨hcc', ?_⟩
      have htranslated := vertex_sum_eq_normalized n c c'
      rw [htranslated]
      simpa [Nat.add_assoc] using (mem_normalizePalette.mp hmem).2
    · rintro ⟨hcc', hmem⟩
      have hxy : vertexEquivFin n c ≠ vertexEquivFin n c' :=
        fun h ↦ hcc' ((vertexEquivFin n).injective h)
      refine ⟨hxy, ?_⟩
      apply mem_normalizePalette.mpr
      constructor
      · exact (mem_attainableNormalizedSums_iff (n - 1)
          ((vertexEquivFin n c).1 + (vertexEquivFin n c').1)).mpr
          ⟨vertexEquivFin n c, vertexEquivFin n c', hxy, rfl⟩
      · rw [show sumOffset n +
            ((vertexEquivFin n c).1 + (vertexEquivFin n c').1) =
            c.1 + c'.1 by
              simpa [Nat.add_assoc] using
                (vertex_sum_eq_normalized n c c').symm]
        exact hmem

/-- A finite graph isomorphism preserves the independence number. -/
theorem indepNum_eq_of_iso {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) :
    G.indepNum = H.indepNum := by
  apply le_antisymm
  · obtain ⟨S, hS⟩ := G.exists_isNIndepSet_indepNum
    let T : Finset W := S.map e.toEquiv.toEmbedding
    have hTind : H.IsIndepSet (T : Set W) := by
      intro u hu v hv huv hadj
      simp only [T, Finset.mem_coe, Finset.mem_map] at hu hv
      obtain ⟨x, hxS, rfl⟩ := hu
      obtain ⟨y, hyS, rfl⟩ := hv
      have hxy : x ≠ y := fun h ↦ huv (congrArg e h)
      exact hS.isIndepSet hxS hyS hxy (e.map_adj_iff.mp hadj)
    have hcard : T.card = S.card := Finset.card_map _
    rw [← hS.card_eq, ← hcard]
    exact hTind.card_le_indepNum
  · obtain ⟨T, hT⟩ := H.exists_isNIndepSet_indepNum
    let S : Finset V := T.map e.symm.toEquiv.toEmbedding
    have hSind : G.IsIndepSet (S : Set V) := by
      intro u hu v hv huv hadj
      simp only [S, Finset.mem_coe, Finset.mem_map] at hu hv
      obtain ⟨x, hxT, rfl⟩ := hu
      obtain ⟨y, hyT, rfl⟩ := hv
      have hxy : x ≠ y := fun h ↦ huv (congrArg e.symm h)
      exact hT.isIndepSet hxT hyT hxy (e.symm.map_adj_iff.mp hadj)
    have hcard : S.card = T.card := Finset.card_map _
    rw [← hT.card_eq, ← hcard]
    exact hSind.card_le_indepNum

/-- Exact independence-number equality between original and normalized
coordinates. -/
theorem indepNum_paletteGraph_eq_sumGraph (n : ℕ) (B : Finset ℕ) :
    (paletteGraph n B).indepNum =
      (sumGraph (n - 1) (normalizePalette n B)).indepNum :=
  indepNum_eq_of_iso (paletteGraphIso n B)

/-- Removing colors which label no edge does not change the graph. -/
theorem paletteGraph_activePalette (n : ℕ) (B : Finset ℕ) :
    paletteGraph n (activePalette n B) = paletteGraph n B := by
  ext c c'
  simp only [paletteGraph_adj, mem_activePalette]
  constructor
  · rintro ⟨hcc', hb, _⟩
    exact ⟨hcc', hb⟩
  · rintro ⟨hcc', hb⟩
    exact ⟨hcc', hb, c, c', hcc', rfl⟩

/-- The active palette is a subpalette of the original palette. -/
theorem activePalette_subset (n : ℕ) (B : Finset ℕ) :
    activePalette n B ⊆ B :=
  Finset.filter_subset _ _

/-- Deleting unattainable colors cannot increase the graph score: the graph
and its independence number stay fixed, while the palette cardinality can
only decrease. -/
theorem graphScore_activePalette_le (n : ℕ) (B : Finset ℕ) :
    graphScore n (activePalette n B) ≤ graphScore n B := by
  rw [graphScore, graphScore, paletteGraph_activePalette n B]
  exact Nat.add_le_add_right
    (Finset.card_le_card (activePalette_subset n B)) _

/-- Exact normalized form of the score after inactive colors are deleted. -/
theorem graphScore_activePalette_eq_normalized (n : ℕ) (B : Finset ℕ) :
    graphScore n (activePalette n B) =
      (normalizePalette n B).card +
        (sumGraph (n - 1) (normalizePalette n B)).indepNum := by
  rw [graphScore, paletteGraph_activePalette n B,
    indepNum_paletteGraph_eq_sumGraph n B,
    card_activePalette_eq_card_normalizePalette n B]

/-- Palette support remains inside `J n` after inactive colors are deleted. -/
theorem activePalette_subset_J {n : ℕ} {B : Finset ℕ} (hB : B ⊆ J n) :
    activePalette n B ⊆ J n :=
  (activePalette_subset n B).trans hB

end Erdos788


/-! Flattened from Erdos788.LowerFinal. -/


/-!
# The quantitative lower bound

This module joins the exact sampling--Shearer inequality to the
elementary optimization and then transfers the result through the exact
normalization/min--max identity.
-/

namespace Erdos788

open Finset

private theorem samplingPower_le_three_mul_succ_alt {N b t : ℕ}
    (hbN : b ≤ N)
    (hmin : t = 0 ∨ N * (2 ^ t) ^ 2 < 8 * b ^ 3) :
    2 ^ t ≤ 3 * (b + 1) := by
  rcases hmin with (rfl | hupper)
  · omega
  by_cases hb : b = 0
  · subst b
    simp at hupper
  have hbpos : 0 < b := Nat.pos_of_ne_zero hb
  have hmul : b * (2 ^ t) ^ 2 < b * (8 * b ^ 2) := by
    calc
      b * (2 ^ t) ^ 2 ≤ N * (2 ^ t) ^ 2 :=
        Nat.mul_le_mul_right _ hbN
      _ < 8 * b ^ 3 := hupper
      _ = b * (8 * b ^ 2) := by ring
  have hsq : (2 ^ t) ^ 2 < 8 * b ^ 2 :=
    (Nat.mul_lt_mul_left hbpos).mp hmul
  have hlt : 2 ^ t < 3 * b := by nlinarith
  omega

private theorem samplingPower_mul_averageCutoff_le_alt
    {b q : ℕ} (hqB : q ≤ 3 * (b + 1)) :
    q * (2 * (2 * (b + 1) / q + 1)) ≤ 10 * (b + 1) := by
  have hdiv : q * (2 * (b + 1) / q) ≤ 2 * (b + 1) := by
    simpa [mul_comm] using Nat.div_mul_le_self (2 * (b + 1)) q
  nlinarith

private theorem arithmeticCutoff_le_shearerCutoff_alt {b q : ℕ}
    (hq : 0 < q) :
    8 * (b + 1) / q + 1 ≤
      2 * (2 * (2 * (b + 1) / q + 1)) + 1 := by
  let U := 2 * (b + 1)
  let V := 4 * (U / q + 1)
  have hbase : U < q * (U / q + 1) := Nat.lt_mul_div_succ U hq
  have hscaled : 4 * U < q * V := by
    dsimp only [V]
    nlinarith
  have hdiv : 4 * U / q < V := by
    by_contra h
    have hle : V ≤ 4 * U / q := Nat.le_of_not_gt h
    have hmul : V * q ≤ 4 * U := (Nat.le_div_iff_mul_le hq).mp hle
    nlinarith
  calc
    8 * (b + 1) / q + 1 = 4 * U / q + 1 := by
      congr 2
      simp only [U]
      ring
    _ ≤ V + 1 := Nat.add_le_add_right hdiv.le 1
    _ = 2 * (2 * (2 * (b + 1) / q + 1)) + 1 := by
      simp only [V, U]
      ring

set_option maxHeartbeats 1000000
/-- Every normalized sum graph has score at least a fixed multiple of the
square-root logarithmic scale. -/
theorem normalizedScore_lower {N : ℕ} (A : Finset ℕ) (hN : 2 ≤ N) :
    (1 / 1000 : ℝ) * Real.sqrt ((N : ℝ) * Real.log (N : ℝ)) ≤
      (A.card : ℝ) + ((sumGraph N A).indepNum : ℝ) := by
  let b : ℕ := A.card
  let a : ℕ := (sumGraph N A).indepNum
  let X : ℝ := Real.sqrt ((N : ℝ) * Real.log (N : ℝ))
  have hNpos : 0 < N := by omega
  have hlogN : 0 ≤ Real.log (N : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ N by omega)
  have hXnonneg : 0 ≤ X := Real.sqrt_nonneg _
  have hXsq : X ^ 2 = (N : ℝ) * Real.log (N : ℝ) := by
    exact Real.sq_sqrt (mul_nonneg (by positivity) hlogN)
  have hXleN : X ≤ (N : ℝ) := by
    simpa only [X] using sqrt_mul_log_le_self hN
  have haOne : 1 ≤ a := by
    let v : Fin N := ⟨0, by omega⟩
    have hv : (sumGraph N A).IsIndepSet ({v} : Finset (Fin N)) := by
      simp
    simpa only [a, card_singleton] using hv.card_le_indepNum
  by_cases hlarge : X ≤ 1000 * (b : ℝ)
  · change (1 / 1000 : ℝ) * X ≤ (b : ℝ) + (a : ℝ)
    have haNonneg : (0 : ℝ) ≤ a := by positivity
    norm_num at ⊢
    nlinarith
  · have hsmall : 1000 * (b : ℝ) < X := lt_of_not_ge hlarge
    have hbX : (b : ℝ) ≤ X := by
      have hbNonneg : (0 : ℝ) ≤ b := by positivity
      nlinarith
    have hbNR : (b : ℝ) ≤ (N : ℝ) := hbX.trans hXleN
    have hbN : b ≤ N := by exact_mod_cast hbNR
    obtain ⟨t, hscale, hminimal⟩ := exists_sampling_exponent N b hNpos
    let q : ℕ := 2 ^ t
    let B : ℕ := b + 1
    let K : ℕ := 2 * (2 * B / q + 1)
    have hqpos : 0 < q := by simp [q]
    have hqB : q ≤ 3 * B := by
      simpa only [q, B] using
        samplingPower_le_three_mul_succ_alt hbN hminimal
    have hqK : q * K ≤ 10 * B := by
      simpa only [K, B] using
        samplingPower_mul_averageCutoff_le_alt hqB
    have hsample :
        (N : ℝ) * Real.log (2 * K + 1 : ℕ) ≤
          16 * q * K * (a : ℝ) := by
      simpa only [q, B, K, b, a] using
        sumGraph_indepNum_log_lower A t hscale
    have hqKR : (q : ℝ) * (K : ℝ) ≤ 10 * (B : ℝ) := by
      exact_mod_cast hqK
    have hmaster :
        (N : ℝ) * Real.log (2 * K + 1 : ℕ) ≤
          160 * (B : ℝ) * (a : ℝ) := by
      calc
        (N : ℝ) * Real.log (2 * K + 1 : ℕ) ≤
            16 * (q : ℝ) * (K : ℝ) * (a : ℝ) := hsample
        _ = 16 * ((q : ℝ) * (K : ℝ)) * (a : ℝ) := by ring
        _ ≤ 16 * (10 * (B : ℝ)) * (a : ℝ) := by gcongr
        _ = 160 * (B : ℝ) * (a : ℝ) := by ring
    have hBscore : (B : ℝ) ≤ (b : ℝ) + (a : ℝ) := by
      have hBNat : B ≤ b + a := by
        simp only [B]
        omega
      exact_mod_cast hBNat
    have hascore : (a : ℝ) ≤ (b : ℝ) + (a : ℝ) := by
      have hbNonneg : (0 : ℝ) ≤ b := by positivity
      linarith
    have hscoreNonneg : (0 : ℝ) ≤ (b : ℝ) + (a : ℝ) := by
      positivity
    have finish_of_square
        (hsq : X ^ 2 ≤ 1280 * (B : ℝ) * (a : ℝ)) :
        (1 / 1000 : ℝ) * X ≤ (b : ℝ) + (a : ℝ) := by
      have hprod : (B : ℝ) * (a : ℝ) ≤
          ((b : ℝ) + (a : ℝ)) ^ 2 := by
        calc
          (B : ℝ) * (a : ℝ) ≤
              ((b : ℝ) + (a : ℝ)) *
                ((b : ℝ) + (a : ℝ)) :=
            mul_le_mul hBscore hascore (by positivity) hscoreNonneg
          _ = ((b : ℝ) + (a : ℝ)) ^ 2 := by ring
      have hsq' : X ^ 2 ≤
          (1000 * ((b : ℝ) + (a : ℝ))) ^ 2 := by
        calc
          X ^ 2 ≤ 1280 * (B : ℝ) * (a : ℝ) := hsq
          _ ≤ 1280 * (((b : ℝ) + (a : ℝ)) ^ 2) := by
            have hm := mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 1280)
            simpa only [mul_assoc] using hm
          _ ≤ (1000 * ((b : ℝ) + (a : ℝ))) ^ 2 := by
            nlinarith [sq_nonneg ((b : ℝ) + (a : ℝ))]
      have hXbound : X ≤ 1000 * ((b : ℝ) + (a : ℝ)) :=
        (sq_le_sq₀ hXnonneg (mul_nonneg (by norm_num) hscoreNonneg)).mp hsq'
      norm_num at ⊢
      nlinarith
    rcases hminimal with (htZero | hupper)
    · subst t
      by_cases hbFourth : b ^ 4 ≤ N
      · have hBX : (B : ℝ) * X ≤ 4 * (N : ℝ) := by
          simpa only [B, b, X] using
            add_one_mul_sqrt_mul_log_le_four hN hbFourth
        have hfourK : 4 ≤ 2 * K + 1 := by
          have hK : 2 ≤ K := by simp [K]
          omega
        have hlogFour : Real.log (4 : ℝ) ≤
            Real.log ((2 * K + 1 : ℕ) : ℝ) := by
          apply Real.log_le_log (by norm_num)
          exact_mod_cast hfourK
        have hlogD : (1 : ℝ) ≤ Real.log (2 * K + 1 : ℕ) := by
          have hlogFourEq : Real.log (4 : ℝ) = 2 * Real.log 2 := by
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
            norm_num
          rw [hlogFourEq] at hlogFour
          nlinarith [Real.log_two_gt_d9]
        have hNmaster : (N : ℝ) ≤
            160 * (B : ℝ) * (a : ℝ) := by
          calc
            (N : ℝ) ≤ (N : ℝ) * Real.log (2 * K + 1 : ℕ) := by
              nlinarith
            _ ≤ 160 * (B : ℝ) * (a : ℝ) := hmaster
        have hcancel : (B : ℝ) * X ≤
            (B : ℝ) * (640 * (a : ℝ)) := by
          calc
            (B : ℝ) * X ≤ 4 * (N : ℝ) := hBX
            _ ≤ 4 * (160 * (B : ℝ) * (a : ℝ)) := by gcongr
            _ = (B : ℝ) * (640 * (a : ℝ)) := by ring
        have hBpos : (0 : ℝ) < (B : ℝ) := by
          exact_mod_cast (show 0 < B by simp [B])
        have hXa : X ≤ 640 * (a : ℝ) :=
          le_of_mul_le_mul_left hcancel hBpos
        change (1 / 1000 : ℝ) * X ≤ (b : ℝ) + (a : ℝ)
        norm_num at ⊢
        have hbNonneg : (0 : ℝ) ≤ b := by positivity
        nlinarith
      · have hNbFourth : N < b ^ 4 := Nat.lt_of_not_ge hbFourth
        have hbD : b ≤ 2 * K + 1 := by
          simp only [K, q, pow_zero, Nat.div_one, B]
          omega
        have hlog : Real.log (N : ℝ) ≤
            4 * Real.log (2 * K + 1 : ℕ) :=
          log_le_four_log_of_lt_fourth_power
            hNpos hNbFourth hbD
        have hsq : X ^ 2 ≤ 1280 * (B : ℝ) * (a : ℝ) := by
          rw [hXsq]
          calc
            (N : ℝ) * Real.log (N : ℝ) ≤
                (N : ℝ) * (4 * Real.log (2 * K + 1 : ℕ)) := by gcongr
            _ = 4 * ((N : ℝ) * Real.log (2 * K + 1 : ℕ)) := by ring
            _ ≤ 4 * (160 * (B : ℝ) * (a : ℝ)) := by gcongr
            _ ≤ 1280 * (B : ℝ) * (a : ℝ) := by
              have hBa : (0 : ℝ) ≤ (B : ℝ) * (a : ℝ) := by positivity
              nlinarith
        exact finish_of_square hsq
    · let d : ℕ := 8 * B / q + 1
      have hcut : 8 * N < b * d ^ 2 := by
        simpa only [d, B] using cutoff_growth hNpos hqpos hupper
      have hlogCut : Real.log (N : ℝ) ≤ 8 * Real.log (d : ℕ) :=
        log_le_eight_log_cutoff hN hcut hbX
      have hdD : d ≤ 2 * K + 1 := by
        simpa only [d, K, B] using
          arithmeticCutoff_le_shearerCutoff_alt (b := b) (q := q) hqpos
      have hdpos : 0 < d := by simp [d]
      have hlogMono : Real.log (d : ℕ) ≤
          Real.log (2 * K + 1 : ℕ) := by
        apply Real.log_le_log (by positivity)
        exact_mod_cast hdD
      have hlog : Real.log (N : ℝ) ≤
          8 * Real.log (2 * K + 1 : ℕ) := by
        calc
          Real.log (N : ℝ) ≤ 8 * Real.log (d : ℕ) := hlogCut
          _ ≤ 8 * Real.log (2 * K + 1 : ℕ) := by gcongr
      have hsq : X ^ 2 ≤ 1280 * (B : ℝ) * (a : ℝ) := by
        rw [hXsq]
        calc
          (N : ℝ) * Real.log (N : ℝ) ≤
              (N : ℝ) * (8 * Real.log (2 * K + 1 : ℕ)) := by gcongr
          _ = 8 * ((N : ℝ) * Real.log (2 * K + 1 : ℕ)) := by ring
          _ ≤ 8 * (160 * (B : ℝ) * (a : ℝ)) := by gcongr
          _ = 1280 * (B : ℝ) * (a : ℝ) := by ring
      exact finish_of_square hsq

/-- The normalized estimate transferred to the exact finite min--max score,
still at the natural vertex scale `n - 1`. -/
theorem fNat_lower_at_normalizedScale {n : ℕ} (hn : 3 ≤ n) :
    (1 / 1000 : ℝ) *
        Real.sqrt (((n - 1 : ℕ) : ℝ) * Real.log ((n - 1 : ℕ) : ℝ)) ≤
      (fNat n : ℝ) := by
  obtain ⟨B, _hB, hBscore⟩ := exists_graphScore_eq_minGraphScore n
  let A : Finset ℕ := normalizePalette n B
  have hN : 2 ≤ n - 1 := by omega
  have hnormalized := normalizedScore_lower A hN
  have hscoreNat :
      A.card + (sumGraph (n - 1) A).indepNum ≤ minGraphScore n := by
    calc
      A.card + (sumGraph (n - 1) A).indepNum =
          graphScore n (activePalette n B) := by
        symm
        exact graphScore_activePalette_eq_normalized n B
      _ ≤ graphScore n B := graphScore_activePalette_le n B
      _ = minGraphScore n := hBscore
  have hscoreReal :
      (A.card : ℝ) + ((sumGraph (n - 1) A).indepNum : ℝ) ≤
        (fNat n : ℝ) := by
    rw [fNat_eq_minGraphScore]
    exact_mod_cast hscoreNat
  exact hnormalized.trans hscoreReal

/-- Replacing `n - 1` by `n` costs only a factor of two. -/
theorem sqrt_scale_le_two_normalizedScale {n : ℕ} (hn : 3 ≤ n) :
    Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤
      2 * Real.sqrt (((n - 1 : ℕ) : ℝ) *
        Real.log ((n - 1 : ℕ) : ℝ)) := by
  let N : ℕ := n - 1
  let S : ℝ := Real.sqrt ((n : ℝ) * Real.log (n : ℝ))
  let T : ℝ := Real.sqrt ((N : ℝ) * Real.log (N : ℝ))
  have hN : 2 ≤ N := by simp only [N]; omega
  have hnpos : (0 : ℝ) < n := by positivity
  have hNpos : (0 : ℝ) < N := by positivity
  have hlogn : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hlogN : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hnTwoN : (n : ℝ) ≤ 2 * (N : ℝ) := by
    exact_mod_cast (show n ≤ 2 * N by simp only [N]; omega)
  have hnNSq : n ≤ N ^ 2 := by
    have hnEq : n = N + 1 := by
      simp only [N]
      omega
    rw [hnEq]
    nlinarith
  have hlog : Real.log (n : ℝ) ≤ 2 * Real.log (N : ℝ) := by
    calc
      Real.log (n : ℝ) ≤ Real.log ((N : ℝ) ^ 2) := by
        apply Real.log_le_log hnpos
        exact_mod_cast hnNSq
      _ = 2 * Real.log (N : ℝ) := by
        rw [Real.log_pow]
        norm_num
  have hproduct : (n : ℝ) * Real.log (n : ℝ) ≤
      4 * ((N : ℝ) * Real.log (N : ℝ)) := by
    calc
      (n : ℝ) * Real.log (n : ℝ) ≤
          (2 * (N : ℝ)) * (2 * Real.log (N : ℝ)) :=
        mul_le_mul hnTwoN hlog hlogn (by positivity)
      _ = 4 * ((N : ℝ) * Real.log (N : ℝ)) := by ring
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hT0 : 0 ≤ T := Real.sqrt_nonneg _
  have hSsq : S ^ 2 = (n : ℝ) * Real.log (n : ℝ) := by
    exact Real.sq_sqrt (mul_nonneg hnpos.le hlogn)
  have hTsq : T ^ 2 = (N : ℝ) * Real.log (N : ℝ) := by
    exact Real.sq_sqrt (mul_nonneg hNpos.le hlogN)
  have hsquares : S ^ 2 ≤ (2 * T) ^ 2 := by
    calc
      S ^ 2 = (n : ℝ) * Real.log (n : ℝ) := hSsq
      _ ≤ 4 * ((N : ℝ) * Real.log (N : ℝ)) := hproduct
      _ = 4 * T ^ 2 := by rw [hTsq]
      _ = (2 * T) ^ 2 := by ring
  have hST : S ≤ 2 * T :=
    (sq_le_sq₀ hS0 (mul_nonneg (by norm_num) hT0)).mp hsquares
  simpa only [S, T, N] using hST

/-- Explicit lower bound for the natural-valued extremal function. -/
theorem cast_fNat_lower {n : ℕ} (hn : 3 ≤ n) :
    (1 / 2000 : ℝ) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤
      (fNat n : ℝ) := by
  have hscale := sqrt_scale_le_two_normalizedScale hn
  have hnormalized := fNat_lower_at_normalizedScale hn
  calc
    (1 / 2000 : ℝ) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤
        (1 / 2000 : ℝ) *
          (2 * Real.sqrt (((n - 1 : ℕ) : ℝ) *
            Real.log ((n - 1 : ℕ) : ℝ))) := by gcongr
    _ = (1 / 1000 : ℝ) *
        Real.sqrt (((n - 1 : ℕ) : ℝ) *
          Real.log ((n - 1 : ℕ) : ℝ)) := by ring
    _ ≤ (fNat n : ℝ) := hnormalized

/-- The same explicit lower bound for the integer-valued function in the
problem statement. -/
theorem cast_f_lower {n : ℕ} (hn : 3 ≤ n) :
    (1 / 2000 : ℝ) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤
      (f n : ℝ) := by
  simpa [f] using cast_fNat_lower hn

/-- Eventual quantified form of the lower bound. -/
theorem exists_lowerBound_threshold :
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      (1 / 2000 : ℝ) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤
        (f n : ℝ) := by
  exact ⟨3, by norm_num, fun _n hn ↦ cast_f_lower hn⟩

end Erdos788


/-! Flattened from Erdos788.FiniteCounting. -/


/-!
# Elementary finite counting interfaces

The reconstruction and carry arguments repeatedly factor an output through a
finite description type.  The lemmas here make those cardinality steps
explicit.
-/

open scoped BigOperators

namespace Erdos788

theorem local_row_has_suffix_slack {m t tail : ℕ}
    (ht : t < m) (hblock : m - 1 ≤ tail) :
    t ≤ (m - t - 1) + tail := by
  omega

theorem sum_of_unit_costs_le_card {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w : ι → ℕ) (hw : ∀ i ∈ s, w i ≤ 1) :
    ∑ i ∈ s, w i ≤ s.card := by
  simpa using Finset.sum_le_sum hw

theorem card_binary_assignments (t : ℕ) :
    Fintype.card (Fin t → Bool) = 2 ^ t := by
  simp

theorem card_binary_tables (p t : ℕ) [NeZero p] :
    Fintype.card ((Fin t → Bool) → ZMod p) = p ^ (2 ^ t) := by
  simp

theorem bertrand_interface (Q : ℕ) (hQ : Q ≠ 0) :
    ∃ q : ℕ, q.Prime ∧ Q < q ∧ q ≤ 2 * Q :=
  Nat.exists_prime_lt_and_le_two_mul Q hQ

theorem fixed_length_digit_words_card {p : ℕ} (hp : 1 < p) (k : ℕ) :
    (List.fixedLengthDigits hp k).card = p ^ k :=
  List.card_fixedLengthDigits hp k

theorem one_bit_raw_carry {a b p : ℕ} (hp : 0 < p)
    (ha : a < p) (hb : b < p) :
    (a + b) / p ≤ 1 := by
  have hsum : a + b < 2 * p := by omega
  have hquot : (a + b) / p < 2 :=
    (Nat.div_lt_iff_lt_mul hp).2 (by simpa [Nat.mul_comm] using hsum)
  omega

theorem card_image_of_factorization {α β γ : Type*}
    [Fintype α] [Fintype β] [DecidableEq γ]
    (output : α → γ) (code : α → β) (decode : β → γ)
    (hfactor : ∀ x, output x = decode (code x)) :
    (Finset.univ.image output).card ≤ Fintype.card β := by
  calc
    (Finset.univ.image output).card
        ≤ (Finset.univ.image decode).card := by
          apply Finset.card_le_card
          intro z hz
          simp only [Finset.mem_image, Finset.mem_univ, true_and] at hz ⊢
          obtain ⟨x, rfl⟩ := hz
          exact ⟨code x, (hfactor x).symm⟩
    _ ≤ Fintype.card β := by
      simpa using Finset.card_image_le
        (s := (Finset.univ : Finset β)) (f := decode)

theorem carry_description_bound {α γ : Type*} [Fintype α] [DecidableEq γ]
    (k : ℕ) (output : α → γ) (carry : α → (Fin k → Bool))
    (decode : (Fin k → Bool) → γ)
    (hfactor : ∀ x, output x = decode (carry x)) :
    (Finset.univ.image output).card ≤ 2 ^ k := by
  simpa [card_binary_assignments] using
    card_image_of_factorization output carry decode hfactor

end Erdos788


/-! Flattened from Erdos788.FiniteField. -/


/-!
# Finite-field interfaces for the upper construction

These lemmas isolate the two algebraic facts used later: distinct affine
graphs meet in at most one point, and a surjective map
`𝔽_p^(2r) → 𝔽_p^r` has a kernel of size `p^r`.
-/

open scoped BigOperators

namespace Erdos788

theorem affine_graph_eq_unique {K : Type*} [Field K]
    {a b c d x y : K} (hcoeff : (a, b) ≠ (c, d))
    (hx : a * x + b = c * x + d)
    (hy : a * y + b = c * y + d) : x = y := by
  have hprod : (a - c) * (x - y) = 0 := by
    linear_combination hx - hy
  rcases mul_eq_zero.mp hprod with hac | hxy
  · have ha : a = c := sub_eq_zero.mp hac
    have hb : b = d := by
      rw [ha] at hx
      exact add_left_cancel hx
    exact (hcoeff (Prod.ext ha hb)).elim
  · exact sub_eq_zero.mp hxy

section Kernel

variable (p r : ℕ) [Fact p.Prime]

theorem kernel_card_of_surjective
    (F : (Fin (2 * r) → ZMod p) →ₗ[ZMod p] (Fin r → ZMod p))
    (hF : Function.Surjective F) :
    Nat.card F.ker = p ^ r := by
  have hrange : F.range = ⊤ := LinearMap.range_eq_top.mpr hF
  have hfrange : Module.finrank (ZMod p) F.range = r := by
    rw [hrange, finrank_top, Module.finrank_fintype_fun_eq_card]
    simp
  have hfdomain :
      Module.finrank (ZMod p) (Fin (2 * r) → ZMod p) = 2 * r := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  have hfker : Module.finrank (ZMod p) F.ker = r := by
    have h := F.finrank_range_add_finrank_ker
    rw [hfrange, hfdomain] at h
    omega
  rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := F.ker),
    Nat.card_zmod, hfker]

/-- The kernel represented as a finset of the ambient vector space. -/
def kernelFinset
    (F : (Fin (2 * r) → ZMod p) →ₗ[ZMod p] (Fin r → ZMod p)) :
    Finset (Fin (2 * r) → ZMod p) :=
  {x | F x = 0}.toFinset

theorem kernelFinset_card_of_surjective
    (F : (Fin (2 * r) → ZMod p) →ₗ[ZMod p] (Fin r → ZMod p))
    (hF : Function.Surjective F) :
    (kernelFinset p r F).card = p ^ r := by
  rw [kernelFinset, Set.toFinset_card, ← Nat.card_eq_fintype_card]
  exact kernel_card_of_surjective p r F hF

/-- The union of `|Y|` surjective kernels has size at most `|Y| p^r`. -/
theorem kernel_palette_card_le {ι : Type*} [DecidableEq ι]
    (Y : Finset ι)
    (F : ι → (Fin (2 * r) → ZMod p) →ₗ[ZMod p] (Fin r → ZMod p))
    (hF : ∀ y ∈ Y, Function.Surjective (F y)) :
    (Y.biUnion (kernelFinset p r ∘ F)).card ≤ Y.card * p ^ r := by
  calc
    (Y.biUnion (kernelFinset p r ∘ F)).card
        ≤ ∑ y ∈ Y, (kernelFinset p r (F y)).card := Finset.card_biUnion_le
    _ = ∑ _y ∈ Y, p ^ r := by
      apply Finset.sum_congr rfl
      intro y hy
      exact kernelFinset_card_of_surjective p r (F y) (hF y hy)
    _ = Y.card * p ^ r := by simp

end Kernel

end Erdos788


/-! Flattened from Erdos788.SuffixSlackDesign. -/


/-!
# Ordered suffix-slack designs

This file formalizes the ordered weak design used in the upper bound for
Erdős Problem 788.  Rows are divided recursively into a first block of
ceiling half the remaining rows and a suffix of floor half the remaining
rows.  Each block is an affine-graph design over a prime field, and distinct
blocks use disjoint coordinate types.
-/

open scoped BigOperators
open Function

set_option linter.style.haveILetI false

namespace Erdos788

/-- A total predecessor index.  In the only place where it is used, `j` lies
in `range i.val`, so this is definitionally the row with natural index `j`. -/
def priorIndex {r : ℕ} (i : Fin r) (j : ℕ) : Fin r :=
  ⟨min j i.val, lt_of_le_of_lt (min_le_right _ _) i.isLt⟩

@[simp]
theorem priorIndex_val_of_lt {r j : ℕ} (i : Fin r) (hj : j < i.val) :
    (priorIndex i j).val = j := by
  simp [priorIndex, min_eq_left hj.le]

/-- The contribution of one earlier row to the overlap excess. -/
def overlapCost {Coord : Type*} [DecidableEq Coord]
    (S T : Finset Coord) : ℕ :=
  2 ^ (S ∩ T).card - 1

/-- An ordered family of `ell`-sets whose overlap excess at row `i` fits in
the unused suffix after `i`. -/
structure SuffixDesign (ell r : ℕ) where
  Coord : Type
  [instFintypeCoord : Fintype Coord]
  [instDecidableEqCoord : DecidableEq Coord]
  row : Fin r → Finset Coord
  row_card : ∀ i, (row i).card = ell
  suffix_slack : ∀ i : Fin r,
    (∑ j ∈ Finset.range i.val, overlapCost (row i) (row (priorIndex i j))) ≤
      r - 1 - i.val

namespace SuffixDesign

/-- Cardinality of the coordinate type carried by a suffix design. -/
def coordCard {ell r : ℕ} (D : SuffixDesign ell r) : ℕ :=
  @Fintype.card D.Coord D.instFintypeCoord

theorem coordCard_transport {ell r s : ℕ} (h : r = s)
    (D : SuffixDesign ell r) : (h ▸ D).coordCard = D.coordCard := by
  subst s
  rfl

theorem overlapCost_map {Coord Coord' : Type*}
    [DecidableEq Coord] [DecidableEq Coord']
    (f : Coord ↪ Coord') (S T : Finset Coord) :
    overlapCost (S.map f) (T.map f) = overlapCost S T := by
  rw [overlapCost, overlapCost, ← Finset.map_inter]
  simp

theorem overlapCost_map_inl_inr {Coord Coord' : Type*}
    [DecidableEq Coord] [DecidableEq Coord']
    (S : Finset Coord) (T : Finset Coord') :
    overlapCost (S.map Embedding.inl) (T.map Embedding.inr) = 0 := by
  have hdisj : Disjoint (S.map Embedding.inl) (T.map Embedding.inr) :=
    Finset.disjoint_map_inl_map_inr S T
  rw [overlapCost, Finset.disjoint_iff_inter_eq_empty.mp hdisj]
  simp

theorem overlapCost_comm {Coord : Type*} [DecidableEq Coord]
    (S T : Finset Coord) : overlapCost S T = overlapCost T S := by
  simp only [overlapCost, Finset.inter_comm]

theorem overlapCost_map_inr_inl {Coord Coord' : Type*}
    [DecidableEq Coord] [DecidableEq Coord']
    (S : Finset Coord) (T : Finset Coord') :
    overlapCost (T.map Embedding.inr) (S.map Embedding.inl) = 0 := by
  rw [overlapCost_comm, overlapCost_map_inl_inr]

theorem overlapCost_le_one_of_inter_card_le_one
    {Coord : Type*} [DecidableEq Coord] {S T : Finset Coord}
    (hcard : (S ∩ T).card ≤ 1) : overlapCost S T ≤ 1 := by
  have hcases : (S ∩ T).card = 0 ∨ (S ∩ T).card = 1 := by omega
  rcases hcases with hzero | hone
  · simp [overlapCost, hzero]
  · simp [overlapCost, hone]

/-- The unique design on no rows. -/
def empty (ell : ℕ) : SuffixDesign ell 0 where
  Coord := Empty
  row := Fin.elim0
  row_card := fun i ↦ Fin.elim0 i
  suffix_slack := fun i ↦ Fin.elim0 i

@[simp]
theorem empty_coordCard (ell : ℕ) : (empty ell).coordCard = 0 :=
  rfl

/-- A block design in which distinct rows meet in at most one coordinate. -/
structure UnitIntersectionBlock (ell m : ℕ) where
  Coord : Type
  [instFintypeCoord : Fintype Coord]
  [instDecidableEqCoord : DecidableEq Coord]
  row : Fin m → Finset Coord
  row_card : ∀ i, (row i).card = ell
  inter_card_le_one : ∀ {i j}, i ≠ j → (row i ∩ row j).card ≤ 1

/-- The first `m` coefficient pairs in a `q` by `q` square, embedded in the
prime field. -/
noncomputable def affineCoeffEmbedding
    (q m : ℕ) [Fact q.Prime] (hm : m ≤ q * q) :
    Fin m ↪ ZMod q × ZMod q where
  toFun t :=
    let uv : Fin q × Fin q := finProdFinEquiv.symm (Fin.castLE hm t)
    ((uv.1.val : ZMod q), (uv.2.val : ZMod q))
  inj' := by
    intro s t hst
    let us : Fin q × Fin q := finProdFinEquiv.symm (Fin.castLE hm s)
    let ut : Fin q × Fin q := finProdFinEquiv.symm (Fin.castLE hm t)
    change ((us.1.val : ZMod q), (us.2.val : ZMod q)) =
      ((ut.1.val : ZMod q), (ut.2.val : ZMod q)) at hst
    have hstFst : (us.1.val : ZMod q) = (ut.1.val : ZMod q) :=
      congrArg Prod.fst hst
    have hstSnd : (us.2.val : ZMod q) = (ut.2.val : ZMod q) :=
      congrArg Prod.snd hst
    have hfst : us.1 = ut.1 := by
      apply Fin.ext
      exact CharP.natCast_injOn_Iio (ZMod q) q us.1.isLt ut.1.isLt hstFst
    have hsnd : us.2 = ut.2 := by
      apply Fin.ext
      exact CharP.natCast_injOn_Iio (ZMod q) q us.2.isLt ut.2.isLt hstSnd
    have huv : us = ut := Prod.ext hfst hsnd
    exact Fin.castLE_injective hm (finProdFinEquiv.symm.injective huv)

/-- The graph, over the first `ell` field elements, of the affine function
with coefficient pair assigned to row `t`. -/
noncomputable def affineRow
    (ell q m : ℕ) [Fact q.Prime] (hm : m ≤ q * q)
    (t : Fin m) : Finset (Fin ell × ZMod q) :=
  (Finset.univ : Finset (Fin ell)).map
    { toFun := fun x ↦
        (x, (affineCoeffEmbedding q m hm t).1 * (x.val : ZMod q) +
          (affineCoeffEmbedding q m hm t).2)
      inj' := fun _ _ h ↦ congrArg Prod.fst h }

@[simp]
theorem card_affineRow
    (ell q m : ℕ) [Fact q.Prime] (hm : m ≤ q * q) (t : Fin m) :
    (affineRow ell q m hm t).card = ell := by
  simp [affineRow]

theorem mem_affineRow_iff
    {ell q m : ℕ} [Fact q.Prime] {hm : m ≤ q * q}
    {t : Fin m} {z : Fin ell × ZMod q} :
    z ∈ affineRow ell q m hm t ↔
      z.2 = (affineCoeffEmbedding q m hm t).1 * (z.1.val : ZMod q) +
        (affineCoeffEmbedding q m hm t).2 := by
  simp only [affineRow, Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, rfl⟩
    rfl
  · intro hz
    refine ⟨z.1, ?_⟩
    exact Prod.ext rfl hz.symm

/-- Distinct affine rows meet in at most one coordinate. -/
theorem affineRow_inter_card_le_one
    {ell q m : ℕ} [Fact q.Prime] (hellq : ell ≤ q)
    (hm : m ≤ q * q) {s t : Fin m} (hst : s ≠ t) :
    (affineRow ell q m hm s ∩ affineRow ell q m hm t).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro u v hu hv
  have huS := mem_affineRow_iff.mp (Finset.mem_inter.mp hu).1
  have huT := mem_affineRow_iff.mp (Finset.mem_inter.mp hu).2
  have hvS := mem_affineRow_iff.mp (Finset.mem_inter.mp hv).1
  have hvT := mem_affineRow_iff.mp (Finset.mem_inter.mp hv).2
  have hcoeff : affineCoeffEmbedding q m hm s ≠
      affineCoeffEmbedding q m hm t := by
    exact fun h ↦ hst ((affineCoeffEmbedding q m hm).injective h)
  have huvCast : (u.1.val : ZMod q) = (v.1.val : ZMod q) :=
    affine_graph_eq_unique hcoeff (huS.symm.trans huT) (hvS.symm.trans hvT)
  have huvVal : u.1.val = v.1.val :=
    CharP.natCast_injOn_Iio (ZMod q) q
      (u.1.isLt.trans_le hellq) (v.1.isLt.trans_le hellq) huvCast
  have huvFirst : u.1 = v.1 := Fin.ext huvVal
  apply Prod.ext huvFirst
  rw [huS, hvS, huvFirst]

/-- The affine graph construction as a unit-intersection block. -/
noncomputable def affineBlock
    (ell q m : ℕ) [Fact q.Prime] (hellq : ell ≤ q)
    (hm : m ≤ q * q) : UnitIntersectionBlock ell m where
  Coord := Fin ell × ZMod q
  row := affineRow ell q m hm
  row_card := card_affineRow ell q m hm
  inter_card_le_one := affineRow_inter_card_le_one hellq hm

/-- Cardinality of the coordinate type carried by a unit-intersection block. -/
def UnitIntersectionBlock.coordCard {ell m : ℕ}
    (B : UnitIntersectionBlock ell m) : ℕ :=
  @Fintype.card B.Coord B.instFintypeCoord

@[simp]
theorem card_affineBlock_coord
    (ell q m : ℕ) [Fact q.Prime] (hellq : ell ≤ q)
    (hm : m ≤ q * q) :
    (affineBlock ell q m hellq hm).coordCard = ell * q := by
  change Fintype.card (Fin ell × ZMod q) = ell * q
  simp

/-- The Bertrand threshold for a block.  `sqrt m + 1` is the integer ceiling
needed to guarantee at least `m` coefficient pairs. -/
def blockPrimeThreshold (ell m : ℕ) : ℕ :=
  max 2 (max ell (Nat.sqrt m + 1))

theorem blockPrimeThreshold_pos (ell m : ℕ) :
    0 < blockPrimeThreshold ell m := by
  simp [blockPrimeThreshold]

/-- A deterministic (via classical choice) prime in the Bertrand interval. -/
noncomputable def blockPrime (ell m : ℕ) : ℕ :=
  Classical.choose
    (bertrand_interface (blockPrimeThreshold ell m)
      (Nat.ne_of_gt (blockPrimeThreshold_pos ell m)))

theorem blockPrime_prime (ell m : ℕ) : (blockPrime ell m).Prime :=
  (Classical.choose_spec
    (bertrand_interface (blockPrimeThreshold ell m)
      (Nat.ne_of_gt (blockPrimeThreshold_pos ell m)))).1

theorem blockPrimeThreshold_lt (ell m : ℕ) :
    blockPrimeThreshold ell m < blockPrime ell m :=
  (Classical.choose_spec
    (bertrand_interface (blockPrimeThreshold ell m)
      (Nat.ne_of_gt (blockPrimeThreshold_pos ell m)))).2.1

theorem blockPrime_le_twice_threshold (ell m : ℕ) :
    blockPrime ell m ≤ 2 * blockPrimeThreshold ell m :=
  (Classical.choose_spec
    (bertrand_interface (blockPrimeThreshold ell m)
      (Nat.ne_of_gt (blockPrimeThreshold_pos ell m)))).2.2

theorem ell_le_blockPrime (ell m : ℕ) : ell ≤ blockPrime ell m := by
  have hEll : ell ≤ blockPrimeThreshold ell m := by
    simp [blockPrimeThreshold]
  exact hEll.trans (blockPrimeThreshold_lt ell m).le

theorem blockSize_le_blockPrime_sq (ell m : ℕ) :
    m ≤ blockPrime ell m * blockPrime ell m := by
  have hsqrt : Nat.sqrt m + 1 ≤ blockPrimeThreshold ell m := by
    simp [blockPrimeThreshold]
  have hq : Nat.sqrt m + 1 ≤ blockPrime ell m :=
    hsqrt.trans (blockPrimeThreshold_lt ell m).le
  have hm : m < (Nat.sqrt m + 1) * (Nat.sqrt m + 1) :=
    Nat.lt_succ_sqrt m
  exact hm.le.trans (Nat.mul_le_mul hq hq)

/-- The affine block selected for the recursive construction. -/
noncomputable def chosenAffineBlock (ell m : ℕ) :
    UnitIntersectionBlock ell m := by
  letI : Fact (blockPrime ell m).Prime := ⟨blockPrime_prime ell m⟩
  exact affineBlock ell (blockPrime ell m) m
    (ell_le_blockPrime ell m) (blockSize_le_blockPrime_sq ell m)

theorem chosenAffineBlock_coordCard (ell m : ℕ) :
    (chosenAffineBlock ell m).coordCard = ell * blockPrime ell m := by
  letI : Fact (blockPrime ell m).Prime := ⟨blockPrime_prime ell m⟩
  exact card_affineBlock_coord ell (blockPrime ell m) m
    (ell_le_blockPrime ell m) (blockSize_le_blockPrime_sq ell m)

theorem chosenAffineBlock_coordCard_le (ell m : ℕ) :
    (chosenAffineBlock ell m).coordCard ≤
      2 * ell * blockPrimeThreshold ell m := by
  rw [chosenAffineBlock_coordCard]
  have h := Nat.mul_le_mul_left ell (blockPrime_le_twice_threshold ell m)
  simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h

section Prepend

variable {ell m t : ℕ} (B : UnitIntersectionBlock ell m)
  (D : SuffixDesign ell t)

local instance blockFintypeCoord : Fintype B.Coord := B.instFintypeCoord
local instance blockDecidableEqCoord : DecidableEq B.Coord := B.instDecidableEqCoord
local instance suffixFintypeCoord : Fintype D.Coord := D.instFintypeCoord
local instance suffixDecidableEqCoord : DecidableEq D.Coord := D.instDecidableEqCoord

/-- Put a unit-intersection block before an already constructed suffix,
tagging the two coordinate universes by the two summands. -/
noncomputable def prependRow (i : Fin (m + t)) :
    Finset (B.Coord ⊕ D.Coord) := by
  letI := B.instDecidableEqCoord
  letI := D.instDecidableEqCoord
  exact if hi : i.val < m then
    (B.row ⟨i.val, hi⟩).map Embedding.inl
  else
    (D.row ⟨i.val - m, by omega⟩).map Embedding.inr

theorem prependRow_of_lt (i : Fin (m + t)) (hi : i.val < m) :
    prependRow B D i = (B.row ⟨i.val, hi⟩).map Embedding.inl := by
  letI := B.instDecidableEqCoord
  letI := D.instDecidableEqCoord
  simp [prependRow, hi]

theorem prependRow_of_ge (i : Fin (m + t)) (hi : m ≤ i.val) :
    prependRow B D i =
      (D.row ⟨i.val - m, by omega⟩).map Embedding.inr := by
  letI := B.instDecidableEqCoord
  letI := D.instDecidableEqCoord
  simp [prependRow, Nat.not_lt.mpr hi]

theorem card_prependRow (i : Fin (m + t)) :
    (prependRow B D i).card = ell := by
  letI := B.instDecidableEqCoord
  letI := D.instDecidableEqCoord
  by_cases hi : i.val < m
  · rw [prependRow_of_lt B D i hi, Finset.card_map, B.row_card]
  · rw [prependRow_of_ge B D i (Nat.le_of_not_gt hi), Finset.card_map,
      D.row_card]

/-- The first-block/suffix splice preserves the suffix-slack inequalities
provided the suffix has at least `m-1` rows. -/
theorem prepend_suffix_slack (hblock : m - 1 ≤ t) (i : Fin (m + t)) :
    (∑ j ∈ Finset.range i.val,
      overlapCost (prependRow B D i) (prependRow B D (priorIndex i j))) ≤
      m + t - 1 - i.val := by
  letI := B.instDecidableEqCoord
  letI := D.instDecidableEqCoord
  by_cases hi : i.val < m
  · have hunit : ∀ j ∈ Finset.range i.val,
        overlapCost (prependRow B D i) (prependRow B D (priorIndex i j)) ≤ 1 := by
      intro j hj
      have hji : j < i.val := Finset.mem_range.mp hj
      have hjm : (priorIndex i j).val < m := by
        rw [priorIndex_val_of_lt i hji]
        omega
      rw [prependRow_of_lt B D i hi,
        prependRow_of_lt B D (priorIndex i j) hjm,
        overlapCost_map]
      apply overlapCost_le_one_of_inter_card_le_one
      apply B.inter_card_le_one
      intro heq
      have hval := congrArg Fin.val heq
      have hij : i.val = j := by
        simpa [priorIndex_val_of_lt i hji] using hval
      omega
    calc
      (∑ j ∈ Finset.range i.val,
          overlapCost (prependRow B D i) (prependRow B D (priorIndex i j)))
          ≤ (Finset.range i.val).card :=
        sum_of_unit_costs_le_card (Finset.range i.val) _ hunit
      _ = i.val := Finset.card_range i.val
      _ ≤ m + t - 1 - i.val := by
        have hlocal := local_row_has_suffix_slack hi hblock
        omega
  · have him : m ≤ i.val := Nat.le_of_not_gt hi
    let k : ℕ := i.val - m
    have hk : k < t := by
      dsimp [k]
      omega
    let ik : Fin t := ⟨k, hk⟩
    have hi_eq : i.val = m + k := by
      dsimp [k]
      omega
    have hfirst :
        (∑ j ∈ Finset.range m,
          overlapCost (prependRow B D i) (prependRow B D (priorIndex i j))) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hjm : j < m := Finset.mem_range.mp hj
      have hji : j < i.val := hjm.trans_le him
      have hpj : (priorIndex i j).val < m := by
        rw [priorIndex_val_of_lt i hji]
        exact hjm
      rw [prependRow_of_ge B D i him,
        prependRow_of_lt B D (priorIndex i j) hpj,
        overlapCost_map_inr_inl]
    have hsecond :
        (∑ j ∈ Finset.range k,
          overlapCost (prependRow B D i)
            (prependRow B D (priorIndex i (m + j)))) =
        (∑ j ∈ Finset.range k,
          overlapCost (D.row ik) (D.row (priorIndex ik j))) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjk : j < k := Finset.mem_range.mp hj
      have hmji : m + j < i.val := by omega
      have hpriorGe : m ≤ (priorIndex i (m + j)).val := by
        rw [priorIndex_val_of_lt i hmji]
        omega
      rw [prependRow_of_ge B D i him,
        prependRow_of_ge B D (priorIndex i (m + j)) hpriorGe,
        overlapCost_map]
      have hleft :
          (⟨i.val - m, by omega⟩ : Fin t) = ik := by
        apply Fin.ext
        rfl
      have hright :
          (⟨(priorIndex i (m + j)).val - m, by omega⟩ : Fin t) =
            priorIndex ik j := by
        apply Fin.ext
        change (priorIndex i (m + j)).val - m = (priorIndex ik j).val
        rw [priorIndex_val_of_lt i hmji, priorIndex_val_of_lt ik hjk]
        omega
      rw [hleft, hright]
    rw [hi_eq, Finset.sum_range_add, hfirst, hsecond, zero_add]
    have hD := D.suffix_slack ik
    dsimp [ik] at hD ⊢
    omega

/-- Prepend a unit-intersection block to a suffix design. -/
noncomputable def prepend (hblock : m - 1 ≤ t) : SuffixDesign ell (m + t) := by
  letI := B.instFintypeCoord
  letI := B.instDecidableEqCoord
  letI := D.instFintypeCoord
  letI := D.instDecidableEqCoord
  exact
    { Coord := B.Coord ⊕ D.Coord
      row := prependRow B D
      row_card := card_prependRow B D
      suffix_slack := prepend_suffix_slack (B := B) (D := D) hblock }

theorem prepend_coordCard (hblock : m - 1 ≤ t) :
    (prepend (B := B) (D := D) hblock).coordCard =
      B.coordCard + D.coordCard := by
  change Fintype.card (B.Coord ⊕ D.Coord) =
    @Fintype.card B.Coord B.instFintypeCoord +
      @Fintype.card D.Coord D.instFintypeCoord
  letI := B.instFintypeCoord
  letI := D.instFintypeCoord
  exact Fintype.card_sum

end Prepend

/-- Ceiling half and floor half of the remaining rows. -/
def firstBlockSize (r : ℕ) : ℕ := (r + 1) / 2

def suffixSize (r : ℕ) : ℕ := r / 2

theorem firstBlockSize_add_suffixSize (r : ℕ) :
    firstBlockSize r + suffixSize r = r := by
  simp only [firstBlockSize, suffixSize]
  omega

theorem firstBlockSize_pred_le_suffixSize (r : ℕ) :
    firstBlockSize r - 1 ≤ suffixSize r := by
  simp only [firstBlockSize, suffixSize]
  omega

theorem suffixSize_lt {r : ℕ} (hr : 0 < r) : suffixSize r < r := by
  simp only [suffixSize]
  omega

/-- The recursive ordered construction.  The first ceiling-half block is an
affine graph block, and the floor-half suffix is constructed recursively. -/
noncomputable def build (ell : ℕ) (r : ℕ) : SuffixDesign ell r :=
  if hr : r = 0 then
    hr ▸ empty ell
  else
    let m := firstBlockSize r
    let t := suffixSize r
    have hsum : m + t = r := firstBlockSize_add_suffixSize r
    hsum ▸ prepend (B := chosenAffineBlock ell m) (D := build ell t)
      (firstBlockSize_pred_le_suffixSize r)
termination_by r
decreasing_by exact suffixSize_lt (Nat.pos_of_ne_zero hr)

theorem build_coordCard_eq {ell r : ℕ} (hr : 0 < r) :
    (build ell r).coordCard =
      (chosenAffineBlock ell (firstBlockSize r)).coordCard +
        (build ell (suffixSize r)).coordCard := by
  rw [build]
  simp only [dif_neg (Nat.ne_of_gt hr)]
  rw [coordCard_transport]
  rw [prepend_coordCard]

/-- A convenient explicit cap for the coordinate cost of the first block. -/
def designBlockCap (ell r : ℕ) : ℕ :=
  2 * ell * (ell + Nat.sqrt r + 3)

/-- A deliberately simple quantitative coordinate bound.  It is slightly
coarser than the paper's geometric-series estimate by a logarithmic factor,
but remains `r^(1/2+o(1))` and is sufficient for the final exponent. -/
def designCoordBound (ell r : ℕ) : ℕ :=
  designBlockCap ell r * (Nat.log 2 r + 1)

theorem firstBlockSize_le {r : ℕ} (hr : 0 < r) :
    firstBlockSize r ≤ r := by
  simp only [firstBlockSize]
  omega

theorem chosenAffineBlock_coordCard_le_designBlockCap
    (ell : ℕ) {r : ℕ} (hr : 0 < r) :
    (chosenAffineBlock ell (firstBlockSize r)).coordCard ≤
      designBlockCap ell r := by
  refine (chosenAffineBlock_coordCard_le ell (firstBlockSize r)).trans ?_
  have hsqrt : Nat.sqrt (firstBlockSize r) ≤ Nat.sqrt r :=
    Nat.sqrt_le_sqrt (firstBlockSize_le hr)
  have hthreshold : blockPrimeThreshold ell (firstBlockSize r) ≤
      ell + Nat.sqrt r + 3 := by
    simp only [blockPrimeThreshold]
    apply max_le
    · omega
    · apply max_le
      · omega
      · omega
  exact Nat.mul_le_mul_left (2 * ell) hthreshold

theorem designBlockCap_suffix_le (ell r : ℕ) :
    designBlockCap ell (suffixSize r) ≤ designBlockCap ell r := by
  unfold designBlockCap suffixSize
  exact Nat.mul_le_mul_left (2 * ell)
    (Nat.add_le_add_right
      (Nat.add_le_add_left (Nat.sqrt_le_sqrt (Nat.div_le_self r 2)) ell) 3)

theorem log_suffix_add_one {r : ℕ} (hr : 2 ≤ r) :
    Nat.log 2 (suffixSize r) + 1 = Nat.log 2 r := by
  rw [suffixSize, Nat.log_div_base]
  have hlog : 0 < Nat.log 2 r := Nat.log_pos Nat.one_lt_two hr
  omega

/-- Explicit size estimate for the recursive suffix-slack design. -/
theorem build_coordCard_le_designCoordBound (ell r : ℕ) :
    (build ell r).coordCard ≤ designCoordBound ell r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
      by_cases hr0 : r = 0
      · subst r
        simp [build, designCoordBound]
      have hr : 0 < r := Nat.pos_of_ne_zero hr0
      by_cases hr1 : r = 1
      · subst r
        rw [build_coordCard_eq (by norm_num : 0 < 1)]
        have hblock :=
          chosenAffineBlock_coordCard_le_designBlockCap ell
            (by norm_num : 0 < 1)
        simpa [firstBlockSize, suffixSize, build, designCoordBound,
          designBlockCap] using hblock
      have hr2 : 2 ≤ r := by omega
      have htlt : suffixSize r < r := suffixSize_lt hr
      have hsuffix := ih (suffixSize r) htlt
      have hblock := chosenAffineBlock_coordCard_le_designBlockCap ell hr
      rw [build_coordCard_eq hr]
      calc
        (chosenAffineBlock ell (firstBlockSize r)).coordCard +
            (build ell (suffixSize r)).coordCard ≤
            designBlockCap ell r + designCoordBound ell (suffixSize r) :=
          Nat.add_le_add hblock hsuffix
        _ ≤ designBlockCap ell r +
            designBlockCap ell r * Nat.log 2 r := by
          apply Nat.add_le_add_left
          rw [designCoordBound, log_suffix_add_one hr2]
          exact Nat.mul_le_mul_right _ (designBlockCap_suffix_le ell r)
        _ = designCoordBound ell r := by
          rw [designCoordBound]
          ring

/-- Scale below which the remaining logarithmic number of blocks is charged
to the `ell^2 log ell` tail. -/
def designTailScale (ell : ℕ) : ℕ :=
  16 * (ell + 3) ^ 2

/-- The real-valued sharp bound used in the final asymptotic parameter
calculation. -/
noncomputable def designStrongBound (ell r : ℕ) : ℝ :=
  10 * ell * Real.sqrt r +
    10 * ell * (ell + 3) * (Nat.log 2 (designTailScale ell) + 1)

theorem natSqrt_firstBlockSize_le {r : ℕ} (hr : 2 ≤ r) :
    (Nat.sqrt (firstBlockSize r) : ℝ) ≤
      (7 / 8 : ℝ) * Real.sqrt r := by
  calc
    (Nat.sqrt (firstBlockSize r) : ℝ) ≤
        Real.sqrt (firstBlockSize r : ℝ) :=
      Real.nat_sqrt_le_real_sqrt
    _ ≤ (7 / 8 : ℝ) * Real.sqrt r := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · have hmNat : 4 * firstBlockSize r ≤ 3 * r := by
          simp only [firstBlockSize]
          omega
        have hm : (4 : ℝ) * firstBlockSize r ≤ 3 * r := by
          exact_mod_cast hmNat
        rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ r)]
        norm_num at hm ⊢
        nlinarith

theorem natSqrt_suffixSize_le {r : ℕ} (hr : 2 ≤ r) :
    (Nat.sqrt (suffixSize r) : ℝ) ≤
      (3 / 4 : ℝ) * Real.sqrt r := by
  calc
    (Nat.sqrt (suffixSize r) : ℝ) ≤ Real.sqrt (suffixSize r : ℝ) :=
      Real.nat_sqrt_le_real_sqrt
    _ ≤ (3 / 4 : ℝ) * Real.sqrt r := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · have htNat : 2 * suffixSize r ≤ r := by
          simp only [suffixSize]
          omega
        have ht : (2 : ℝ) * suffixSize r ≤ r := by
          exact_mod_cast htNat
        rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ r)]
        norm_num at ht ⊢
        nlinarith

theorem realSqrt_suffixSize_le {r : ℕ} (hr : 2 ≤ r) :
    Real.sqrt (suffixSize r : ℝ) ≤
      (3 / 4 : ℝ) * Real.sqrt r := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · have htNat : 2 * suffixSize r ≤ r := by
      simp only [suffixSize]
      omega
    have ht : (2 : ℝ) * suffixSize r ≤ r := by
      exact_mod_cast htNat
    rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ r)]
    norm_num at ht ⊢
    nlinarith

theorem quarter_sqrt_ge_of_designTailScale_le
    {ell r : ℕ} (hlarge : designTailScale ell ≤ r) :
    (ell + 3 : ℝ) ≤ (1 / 4 : ℝ) * Real.sqrt r := by
  rw [← sq_le_sq₀ (by positivity : (0 : ℝ) ≤ ell + 3)
    (by positivity : (0 : ℝ) ≤ (1 / 4 : ℝ) * Real.sqrt r)]
  rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ r)]
  have hlargeR : (designTailScale ell : ℝ) ≤ r := by
    exact_mod_cast hlarge
  rw [designTailScale] at hlargeR
  norm_num at hlargeR ⊢
  nlinarith

theorem chosenAffineBlock_coordCard_real_le_of_large
    (ell : ℕ) {r : ℕ} (hlarge : designTailScale ell ≤ r) :
    ((chosenAffineBlock ell (firstBlockSize r)).coordCard : ℝ) ≤
      (9 / 4 : ℝ) * ell * Real.sqrt r := by
  have hscalePos : 0 < designTailScale ell := by
    simp [designTailScale]
  have hr2 : 2 ≤ r := by
    have hsq : 1 ≤ (ell + 3) ^ 2 :=
      one_le_pow₀ (by omega : 1 ≤ ell + 3)
    have : 2 ≤ designTailScale ell := by
      rw [designTailScale]
      omega
    exact this.trans hlarge
  have hthreshold : blockPrimeThreshold ell (firstBlockSize r) ≤
      (ell + 3) + Nat.sqrt (firstBlockSize r) := by
    simp only [blockPrimeThreshold]
    apply max_le
    · omega
    · apply max_le <;> omega
  have hblockNat :
      (chosenAffineBlock ell (firstBlockSize r)).coordCard ≤
        2 * ell * ((ell + 3) + Nat.sqrt (firstBlockSize r)) :=
    (chosenAffineBlock_coordCard_le ell (firstBlockSize r)).trans
      (Nat.mul_le_mul_left (2 * ell) hthreshold)
  have hblock :
      ((chosenAffineBlock ell (firstBlockSize r)).coordCard : ℝ) ≤
        2 * ell * ((ell + 3 : ℝ) + Nat.sqrt (firstBlockSize r)) := by
    exact_mod_cast hblockNat
  have hsum : (ell + 3 : ℝ) + Nat.sqrt (firstBlockSize r) ≤
      (9 / 8 : ℝ) * Real.sqrt r := by
    nlinarith [quarter_sqrt_ge_of_designTailScale_le hlarge,
      natSqrt_firstBlockSize_le hr2]
  calc
    ((chosenAffineBlock ell (firstBlockSize r)).coordCard : ℝ) ≤
        2 * ell * ((ell + 3 : ℝ) + Nat.sqrt (firstBlockSize r)) := hblock
    _ ≤ 2 * ell * ((9 / 8 : ℝ) * Real.sqrt r) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (9 / 4 : ℝ) * ell * Real.sqrt r := by ring

theorem designCoordBound_le_tail_of_lt
    (ell : ℕ) {r : ℕ} (hsmall : r < designTailScale ell) :
    designCoordBound ell r ≤
      10 * ell * (ell + 3) * (Nat.log 2 (designTailScale ell) + 1) := by
  have hsqrt : Nat.sqrt r < 4 * (ell + 3) := by
    apply Nat.sqrt_lt'.2
    have hsquare : (4 * (ell + 3)) ^ 2 = designTailScale ell := by
      rw [designTailScale]
      ring
    rwa [hsquare]
  have hcap : designBlockCap ell r ≤ 10 * ell * (ell + 3) := by
    rw [designBlockCap]
    have hsum : ell + Nat.sqrt r + 3 ≤ 5 * (ell + 3) := by omega
    calc
      2 * ell * (ell + Nat.sqrt r + 3) ≤
          2 * ell * (5 * (ell + 3)) := Nat.mul_le_mul_left _ hsum
      _ = 10 * ell * (ell + 3) := by ring
  have hlog : Nat.log 2 r + 1 ≤
      Nat.log 2 (designTailScale ell) + 1 :=
    Nat.add_le_add_right (Nat.log_monotone hsmall.le) 1
  rw [designCoordBound]
  exact Nat.mul_le_mul hcap hlog

/-- The recursive construction has the paper's required
`O(ell*sqrt r + ell^2*log ell)` size, with explicit constants. -/
theorem build_coordCard_le_designStrongBound (ell r : ℕ) :
    ((build ell r).coordCard : ℝ) ≤ designStrongBound ell r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
      by_cases hsmall : r < designTailScale ell
      · have hnat := (build_coordCard_le_designCoordBound ell r).trans
          (designCoordBound_le_tail_of_lt ell hsmall)
        have hreal : ((build ell r).coordCard : ℝ) ≤
            10 * ell * (ell + 3) *
              (Nat.log 2 (designTailScale ell) + 1) := by
          exact_mod_cast hnat
        rw [designStrongBound]
        exact hreal.trans (le_add_of_nonneg_left (by positivity))
      · have hlarge : designTailScale ell ≤ r := Nat.le_of_not_gt hsmall
        have hr : 0 < r := (show 0 < designTailScale ell by
          simp [designTailScale]).trans_le hlarge
        have hr2 : 2 ≤ r := by
          have hsq : 1 ≤ (ell + 3) ^ 2 :=
            one_le_pow₀ (by omega : 1 ≤ ell + 3)
          have : 2 ≤ designTailScale ell := by
            rw [designTailScale]
            omega
          exact this.trans hlarge
        have htlt : suffixSize r < r := suffixSize_lt hr
        have hsuffix := ih (suffixSize r) htlt
        have hblock := chosenAffineBlock_coordCard_real_le_of_large ell hlarge
        rw [designStrongBound] at hsuffix ⊢
        rw [build_coordCard_eq hr]
        push_cast
        have hsqrt := realSqrt_suffixSize_le hr2
        have hscaled : 10 * (ell : ℝ) * Real.sqrt (suffixSize r) ≤
            10 * ell * ((3 / 4 : ℝ) * Real.sqrt r) :=
          mul_le_mul_of_nonneg_left hsqrt (by positivity)
        calc
          ((chosenAffineBlock ell (firstBlockSize r)).coordCard : ℝ) +
              ((build ell (suffixSize r)).coordCard : ℝ) ≤
              (9 / 4 : ℝ) * ell * Real.sqrt r +
                (10 * ell * Real.sqrt (suffixSize r) +
                  10 * ell * (ell + 3) *
                    (Nat.log 2 (designTailScale ell) + 1)) :=
            add_le_add hblock hsuffix
          _ ≤ 10 * ell * Real.sqrt r +
                10 * ell * (ell + 3) *
                  (Nat.log 2 (designTailScale ell) + 1) := by
            have hnonneg : 0 ≤ (ell : ℝ) * Real.sqrt r := by positivity
            nlinarith

end SuffixDesign

end Erdos788


/-! Flattened from Erdos788.TrevisanParameters. -/


/-!
# Exact integer parameters for the Trevisan construction

The ceilings needed for the seed length and entropy slack are represented by
`Nat.clog`.  Keeping them integral makes the later finite construction exact;
the elementary bounds below remove the ceilings before asymptotic estimates.
-/

namespace Erdos788

/-- Prediction/list-decoding advantage used in reconstruction. -/
noncomputable def trevisanEta (p r : ℕ) : ℝ :=
  1 / (40 * (p : ℝ) * r)

/-- Least exponent that can encode all binary design seeds over `𝔽_p`. -/
def trevisanSeedExponent (p D : ℕ) : ℕ :=
  Nat.clog p (2 ^ D)

/-- The integral factor whose absorption into `p^s` is exactly what the
reconstruction counting argument needs. -/
def trevisanSlackThreshold (p r D : ℕ) : ℕ :=
  40 * r * 2 ^ D * (3200 * p ^ 2 * r ^ 2 + 1)

/-- Least entropy-slack exponent that absorbs every reconstruction
description and every candidate in its agreement list. -/
def trevisanSlackExponent (p r D : ℕ) : ℕ :=
  Nat.clog p (trevisanSlackThreshold p r D)

theorem trevisanEta_pos {p r : ℕ} (hp : 0 < p) (hr : 0 < r) :
    0 < trevisanEta p r := by
  rw [trevisanEta]
  positivity

theorem trevisanEta_lt_half {p r : ℕ} (hp : 2 < p) (hr : 0 < r) :
    trevisanEta p r < 1 / 2 := by
  rw [trevisanEta]
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hden : (2 : ℝ) < 40 * p * r := by nlinarith
  exact one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 2) hden

theorem seedThreshold_le_pow_seedExponent {p D : ℕ} (hp : 1 < p) :
    2 ^ D ≤ p ^ trevisanSeedExponent p D := by
  exact Nat.le_pow_clog hp _

theorem slackThreshold_pos {p r D : ℕ} (hr : 0 < r) :
    0 < trevisanSlackThreshold p r D := by
  rw [trevisanSlackThreshold]
  positivity

theorem slackThreshold_le_pow_slackExponent {p r D : ℕ}
    (hp : 1 < p) :
    trevisanSlackThreshold p r D ≤
      p ^ trevisanSlackExponent p r D := by
  exact Nat.le_pow_clog hp _

/-- Removing a ceiling logarithm costs at most one factor of its base. -/
theorem pow_clog_le_base_mul {p x : ℕ} (hp : 1 < p) (hx : 0 < x) :
    p ^ Nat.clog p x ≤ p * x := by
  by_cases hx1 : x = 1
  · subst x
    rw [Nat.clog_one_right, pow_zero, mul_one]
    omega
  · have hxgt : 1 < x := by omega
    have hcpos : 0 < Nat.clog p x := Nat.clog_pos hp hxgt
    have hpred : p ^ (Nat.clog p x).pred < x :=
      Nat.pow_pred_clog_lt_self hp hxgt
    have hc : Nat.clog p x = (Nat.clog p x).pred + 1 := by
      simpa [Nat.succ_eq_add_one] using
        (Nat.succ_pred_eq_of_pos hcpos).symm
    rw [hc,
      pow_succ, Nat.mul_comm]
    exact Nat.mul_le_mul_left p hpred.le

theorem pow_seedExponent_le {p D : ℕ} (hp : 1 < p) :
    p ^ trevisanSeedExponent p D ≤ p * 2 ^ D := by
  exact pow_clog_le_base_mul hp (by positivity)

theorem pow_slackExponent_le {p r D : ℕ}
    (hp : 1 < p) (hr : 0 < r) :
    p ^ trevisanSlackExponent p r D ≤
      p * trevisanSlackThreshold p r D := by
  exact pow_clog_le_base_mul hp (slackThreshold_pos hr)

theorem slackExponent_le_iff {p r D R : ℕ} (hp : 1 < p) :
    trevisanSlackExponent p r D ≤ R ↔
      trevisanSlackThreshold p r D ≤ p ^ R := by
  exact Nat.clog_le_iff_le_pow hp

/-- Real upper bound for an integral ceiling logarithm. -/
theorem cast_clog_lt_logb_add_one {b n : ℕ}
    (hb : 1 < b) (hn : 1 ≤ n) :
    ((Nat.clog b n : ℕ) : ℝ) < Real.logb b n + 1 := by
  have hbR : (1 : ℝ) < b := by exact_mod_cast hb
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [← Real.natCeil_logb_natCast]
  exact Nat.ceil_lt_add_one (Real.logb_nonneg hbR hnR)

theorem cast_seedExponent_lt {p D : ℕ} (hp : 1 < p) :
    ((trevisanSeedExponent p D : ℕ) : ℝ) <
      (D : ℝ) * Real.logb p 2 + 1 := by
  have hpowpos : 0 < 2 ^ D := pow_pos (by omega) D
  have h := cast_clog_lt_logb_add_one hp (by omega : 1 ≤ 2 ^ D)
  simpa [trevisanSeedExponent, Real.logb_pow] using h

/-- The ceiling choice of `trevisanSlackExponent` implies exactly the real
counting inequality consumed by the reconstruction theorem. -/
theorem trevisan_reconstruction_count {p r D : ℕ}
    (hp : 2 < p) (hr : 0 < r) :
    ((((2 ^ D * p ^ (r - 1) : ℕ) : ℝ) *
          (2 / trevisanEta p r ^ 2 + 1))) ≤
      trevisanEta p r *
        (p ^ (r + trevisanSlackExponent p r D) : ℕ) := by
  let s := trevisanSlackExponent p r D
  have hp0 : 0 < p := by omega
  have hp1 : 1 < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hden : (0 : ℝ) < 40 * p * r := by positivity
  have hlist : 2 / trevisanEta p r ^ 2 + 1 =
      3200 * (p : ℝ) ^ 2 * (r : ℝ) ^ 2 + 1 := by
    rw [trevisanEta]
    field_simp
    ring
  have hKnat : trevisanSlackThreshold p r D ≤ p ^ s := by
    exact slackThreshold_le_pow_slackExponent hp1
  have hK : ((trevisanSlackThreshold p r D : ℕ) : ℝ) ≤
      ((p ^ s : ℕ) : ℝ) := by
    exact_mod_cast hKnat
  have hmul : ((p ^ r : ℕ) : ℝ) *
        (trevisanSlackThreshold p r D : ℕ) ≤
      ((p ^ r : ℕ) : ℝ) * (p ^ s : ℕ) :=
    mul_le_mul_of_nonneg_left hK (by positivity)
  have hpowNat : p ^ (r - 1) * p = p ^ r := by
    rw [← pow_succ]
    congr 1
    omega
  have hpowR : ((p ^ (r - 1) : ℕ) : ℝ) * p =
      ((p ^ r : ℕ) : ℝ) := by
    exact_mod_cast hpowNat
  push_cast at hpowR
  rw [hlist, trevisanEta, one_div, inv_mul_eq_div]
  apply (le_div_iff₀ hden).2
  have hleft :
      (((2 ^ D * p ^ (r - 1) : ℕ) : ℝ) *
          (3200 * (p : ℝ) ^ 2 * (r : ℝ) ^ 2 + 1)) *
          (40 * (p : ℝ) * r) =
        ((p ^ r : ℕ) : ℝ) *
          (trevisanSlackThreshold p r D : ℕ) := by
    rw [trevisanSlackThreshold]
    push_cast
    calc
      2 ^ D * (p : ℝ) ^ (r - 1) *
            (3200 * (p : ℝ) ^ 2 * (r : ℝ) ^ 2 + 1) *
            (40 * p * r) =
          ((p : ℝ) ^ (r - 1) * p) *
            (40 * r * 2 ^ D *
              (3200 * (p : ℝ) ^ 2 * (r : ℝ) ^ 2 + 1)) := by ring
      _ = (p : ℝ) ^ r *
            (40 * r * 2 ^ D *
              (3200 * (p : ℝ) ^ 2 * (r : ℝ) ^ 2 + 1)) := by
            rw [hpowR]
  have hright :
      ((p ^ (r + s) : ℕ) : ℝ) =
        ((p ^ r : ℕ) : ℝ) * (p ^ s : ℕ) := by
    rw [Nat.pow_add]
    push_cast
    ring
  rw [hleft, hright]
  exact hmul

end Erdos788


/-! Flattened from Erdos788.Statement. -/


/-!
# Exact quantified theorem statements

The displayed quantitative theorem uses explicit constants and an explicit
eventual threshold.  `HasExponentOneHalf` records the paper's stated
`n^(1/2+o(1))` consequence with its full epsilon quantifiers.
-/

namespace Erdos788

/-- The exponent correction in the quantitatively strong paper. -/
noncomputable def exponentCorrection (n : ℕ) : ℝ :=
  (Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)) ^ (1 / 3 : ℝ)

/-- The explicit lower-bound constant stated in the strong paper. -/
noncomputable def finalLowerBoundConstant : ℝ :=
  1 / 2000

/-- The fully quantified two-sided conclusion of the main theorem. -/
def QuantitativeMainTheorem : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      c * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤ (f n : ℝ) ∧
        (f n : ℝ) ≤
          (n : ℝ) ^ ((1 / 2 : ℝ) + C * exponentCorrection n)

/-- Explicit epsilon quantifiers for `f(n) = n^(1/2+o(1))`. -/
def HasExponentOneHalf : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
    (n : ℝ) ^ ((1 / 2 : ℝ) - ε) ≤ (f n : ℝ) ∧
      (f n : ℝ) ≤ (n : ℝ) ^ ((1 / 2 : ℝ) + ε)

/-- The precise epsilon-quantified upper-bound question on the original
Erdős Problems page. -/
def AnswersOriginalUpperQuestion : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
    (f n : ℝ) ≤ (n : ℝ) ^ ((1 / 2 : ℝ) + ε)

/-- The theorem stated in the strong paper: the explicit lower bound holds
for every `n ≥ 3`, the quantitative upper bound holds for all sufficiently
large positive integers, and the resulting exponent is one half. -/
def PaperMainTheorem : Prop :=
  (∀ n : ℕ, 3 ≤ n →
    finalLowerBoundConstant * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤
      (f n : ℝ)) ∧
  (∃ C : ℝ, 0 < C ∧
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      finalLowerBoundConstant *
          Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤ (f n : ℝ) ∧
        (f n : ℝ) ≤
          (n : ℝ) ^ ((1 / 2 : ℝ) + C * exponentCorrection n)) ∧
  HasExponentOneHalf

/-- The complete final statement: the strong paper theorem together with the
original upper-bound question in its exact epsilon-quantified form. -/
def MainTheorem : Prop :=
  PaperMainTheorem ∧ AnswersOriginalUpperQuestion

end Erdos788


/-! Flattened from Erdos788.PrimeParameters. -/


/-!
# Prime and dimension choices for every interval length

The field size is selected by Bertrand's postulate.  The ambient dimension is
an integral ceiling logarithm, so coverage of the first `N` vertices is an
exact natural-number inequality.
-/

namespace Erdos788

/-- The nonnegative reciprocal-correction scale. -/
noncomputable def inverseCorrectionScale (N : ℕ) : ℝ :=
  max 0 (exponentCorrection N)⁻¹

/-- We add `log log N`, a lower-order term, to make the later comparison
`log r ≤ log p` completely transparent. -/
noncomputable def primeLogScale (N : ℕ) : ℝ :=
  inverseCorrectionScale N + max 0 (Real.log (Real.log (N : ℝ)))

theorem exponentCorrection_pos {N : ℕ}
    (hL : 0 < Real.log (N : ℝ))
    (hLL : 0 < Real.log (Real.log (N : ℝ))) :
    0 < exponentCorrection N := by
  rw [exponentCorrection]
  exact Real.rpow_pos_of_pos (div_pos hLL hL) _

theorem exponentCorrection_pow_three {N : ℕ}
    (hL : 0 < Real.log (N : ℝ))
    (hLL : 0 < Real.log (Real.log (N : ℝ))) :
    exponentCorrection N ^ 3 =
      Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ) := by
  rw [exponentCorrection]
  have hbase : 0 ≤
      Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ) :=
    (div_pos hLL hL).le
  simpa [one_div] using
    (Real.rpow_inv_natCast_pow hbase (by norm_num : (3 : ℕ) ≠ 0))

theorem correction_mul_inverseCorrectionScale {N : ℕ}
    (hL : 0 < Real.log (N : ℝ))
    (hLL : 0 < Real.log (Real.log (N : ℝ))) :
    exponentCorrection N * inverseCorrectionScale N = 1 := by
  have hδ := exponentCorrection_pos hL hLL
  rw [inverseCorrectionScale, max_eq_right (inv_nonneg.mpr hδ.le), mul_inv_cancel₀]
  exact hδ.ne'

/-- Integral threshold to which Bertrand's postulate is applied. -/
noncomputable def primeThreshold (N : ℕ) : ℕ :=
  max 2 ⌈Real.exp (primeLogScale N)⌉₊

theorem two_le_primeThreshold (N : ℕ) : 2 ≤ primeThreshold N := by
  simp [primeThreshold]

theorem primeThreshold_ne_zero (N : ℕ) : primeThreshold N ≠ 0 := by
  exact Nat.ne_of_gt (lt_of_lt_of_le (by omega) (two_le_primeThreshold N))

/-- A deterministic prime between the threshold and twice the threshold. -/
noncomputable def parameterPrime (N : ℕ) : ℕ :=
  Classical.choose
    (Nat.exists_prime_lt_and_le_two_mul
      (primeThreshold N) (primeThreshold_ne_zero N))

theorem parameterPrime_prime (N : ℕ) : (parameterPrime N).Prime :=
  (Classical.choose_spec
    (Nat.exists_prime_lt_and_le_two_mul
      (primeThreshold N) (primeThreshold_ne_zero N))).1

theorem primeThreshold_lt_parameterPrime (N : ℕ) :
    primeThreshold N < parameterPrime N :=
  (Classical.choose_spec
    (Nat.exists_prime_lt_and_le_two_mul
      (primeThreshold N) (primeThreshold_ne_zero N))).2.1

theorem parameterPrime_le_two_mul_threshold (N : ℕ) :
    parameterPrime N ≤ 2 * primeThreshold N :=
  (Classical.choose_spec
    (Nat.exists_prime_lt_and_le_two_mul
      (primeThreshold N) (primeThreshold_ne_zero N))).2.2

theorem two_lt_parameterPrime (N : ℕ) : 2 < parameterPrime N :=
  (two_le_primeThreshold N).trans_lt (primeThreshold_lt_parameterPrime N)

theorem primeLogScale_nonneg (N : ℕ) : 0 ≤ primeLogScale N := by
  rw [primeLogScale]
  exact add_nonneg (le_max_left _ _) (le_max_left _ _)

theorem cast_primeThreshold_le_two_mul_exp (N : ℕ) :
    (primeThreshold N : ℝ) ≤ 2 * Real.exp (primeLogScale N) := by
  have hexp1 : (1 : ℝ) ≤ Real.exp (primeLogScale N) :=
    Real.one_le_exp (primeLogScale_nonneg N)
  have hceil : (⌈Real.exp (primeLogScale N)⌉₊ : ℝ) ≤
      2 * Real.exp (primeLogScale N) := by
    have h : (⌈Real.exp (primeLogScale N)⌉₊ : ℝ) <
        Real.exp (primeLogScale N) + 1 :=
      Nat.ceil_lt_add_one (Real.exp_pos (primeLogScale N)).le
    nlinarith
  rw [primeThreshold, Nat.cast_max]
  apply max_le
  · simpa using
      (mul_le_mul_of_nonneg_left hexp1 (by norm_num : (0 : ℝ) ≤ 2))
  · exact hceil

theorem cast_parameterPrime_le_four_mul_exp (N : ℕ) :
    (parameterPrime N : ℝ) ≤ 4 * Real.exp (primeLogScale N) := by
  have hp : (parameterPrime N : ℝ) ≤ 2 * primeThreshold N := by
    exact_mod_cast parameterPrime_le_two_mul_threshold N
  have hP := cast_primeThreshold_le_two_mul_exp N
  nlinarith

theorem primeLogScale_lt_log_parameterPrime (N : ℕ) :
    primeLogScale N < Real.log (parameterPrime N) := by
  have hexpP : Real.exp (primeLogScale N) ≤ (primeThreshold N : ℝ) := by
    calc
      Real.exp (primeLogScale N) ≤
          (⌈Real.exp (primeLogScale N)⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (primeThreshold N : ℝ) := by
        exact_mod_cast (le_max_right 2 ⌈Real.exp (primeLogScale N)⌉₊)
  have hPp : (primeThreshold N : ℝ) < parameterPrime N := by
    exact_mod_cast primeThreshold_lt_parameterPrime N
  have hlog := Real.log_lt_log (Real.exp_pos _) (hexpP.trans_lt hPp)
  simpa using hlog

theorem log_parameterPrime_le_scale_add_log_four (N : ℕ) :
    Real.log (parameterPrime N) ≤ primeLogScale N + Real.log 4 := by
  have hp0 : (0 : ℝ) < parameterPrime N := by
    exact_mod_cast (Nat.zero_lt_of_lt (two_lt_parameterPrime N))
  have hupper := cast_parameterPrime_le_four_mul_exp N
  have hlog := Real.log_le_log hp0 hupper
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (Real.exp_ne_zero _),
    Real.log_exp] at hlog
  linarith

theorem loglog_le_log_parameterPrime (N : ℕ) :
    Real.log (Real.log (N : ℝ)) ≤ Real.log (parameterPrime N) := by
  have hscale : Real.log (Real.log (N : ℝ)) ≤ primeLogScale N := by
    rw [primeLogScale]
    calc
      Real.log (Real.log (N : ℝ)) ≤
          max 0 (Real.log (Real.log (N : ℝ))) := le_max_right _ _
      _ ≤ inverseCorrectionScale N +
          max 0 (Real.log (Real.log (N : ℝ))) :=
        le_add_of_nonneg_left (le_max_left _ _)
  exact hscale.trans (primeLogScale_lt_log_parameterPrime N).le

theorem log_parameterPrime_le_two_div_correction {N : ℕ}
    (hL : 0 < Real.log (N : ℝ))
    (hLL : 0 < Real.log (Real.log (N : ℝ)))
    (hsmall : exponentCorrection N *
        (Real.log (Real.log (N : ℝ)) + Real.log 4) ≤ 1) :
    Real.log (parameterPrime N) ≤ 2 / exponentCorrection N := by
  have hδ := exponentCorrection_pos hL hLL
  have hbase := log_parameterPrime_le_scale_add_log_four N
  rw [primeLogScale, inverseCorrectionScale,
    max_eq_right (inv_nonneg.mpr hδ.le), max_eq_right hLL.le] at hbase
  have hinv : exponentCorrection N * (exponentCorrection N)⁻¹ = 1 :=
    mul_inv_cancel₀ hδ.ne'
  have haux : (exponentCorrection N)⁻¹ +
      Real.log (Real.log (N : ℝ)) + Real.log 4 ≤
        2 / exponentCorrection N := by
    rw [div_eq_mul_inv]
    nlinarith
  exact hbase.trans haux

theorem one_div_log_parameterPrime_lt_correction {N : ℕ}
    (hL : 0 < Real.log (N : ℝ))
    (hLL : 0 < Real.log (Real.log (N : ℝ))) :
    1 / Real.log (parameterPrime N) < exponentCorrection N := by
  have hδ : 0 < exponentCorrection N := exponentCorrection_pos hL hLL
  have hinv : (exponentCorrection N)⁻¹ ≤ primeLogScale N := by
    rw [primeLogScale, inverseCorrectionScale,
      max_eq_right (inv_nonneg.mpr hδ.le)]
    exact le_add_of_nonneg_right (le_max_left _ _)
  have hinvpos : 0 < (exponentCorrection N)⁻¹ := inv_pos.mpr hδ
  have hinvlog : (exponentCorrection N)⁻¹ <
      Real.log (parameterPrime N) :=
    hinv.trans_lt (primeLogScale_lt_log_parameterPrime N)
  have h' := one_div_lt_one_div_of_lt hinvpos hinvlog
  simpa [one_div] using h'

noncomputable instance parameterPrimeFact (N : ℕ) :
    Fact (parameterPrime N).Prime :=
  ⟨parameterPrime_prime N⟩

/-- Least `r` for which the `p^(2r)`-vertex finite-field model covers `N`. -/
noncomputable def parameterDimension (N : ℕ) : ℕ :=
  Nat.clog ((parameterPrime N) ^ 2) N

theorem parameterDimension_cover (N : ℕ) :
    N ≤ parameterPrime N ^ (2 * parameterDimension N) := by
  have hp1 : 1 < parameterPrime N :=
    (by omega : 1 < 2).trans (two_lt_parameterPrime N)
  have hbase : 1 < parameterPrime N ^ 2 := by
    exact Nat.one_lt_pow (by norm_num) hp1
  have h := Nat.le_pow_clog hbase N
  simpa [parameterDimension, pow_mul] using h

theorem parameterDimension_pos {N : ℕ} (hN : 1 < N) :
    0 < parameterDimension N := by
  have hp1 : 1 < parameterPrime N :=
    (by omega : 1 < 2).trans (two_lt_parameterPrime N)
  apply Nat.clog_pos
  · exact Nat.one_lt_pow (by norm_num) hp1
  · exact hN

/-- The exact real ceiling bound for the chosen dimension. -/
theorem cast_parameterDimension_lt_logb_add_one {N : ℕ} (hN : 1 ≤ N) :
    ((parameterDimension N : ℕ) : ℝ) <
      Real.logb (parameterPrime N ^ 2) N + 1 := by
  have hp1 : 1 < parameterPrime N :=
    (by omega : 1 < 2).trans (two_lt_parameterPrime N)
  have hbase : 1 < parameterPrime N ^ 2 :=
    Nat.one_lt_pow (by norm_num) hp1
  simpa [parameterDimension, Nat.cast_pow] using
    (cast_clog_lt_logb_add_one
      (b := parameterPrime N ^ 2) (n := N) hbase hN)

theorem cast_parameterDimension_lt_log_div_add_one {N : ℕ} (hN : 1 ≤ N) :
    ((parameterDimension N : ℕ) : ℝ) <
      Real.log (N : ℝ) / (2 * Real.log (parameterPrime N)) + 1 := by
  have h := cast_parameterDimension_lt_logb_add_one hN
  rw [Real.logb] at h
  norm_num [Nat.cast_pow, Real.log_pow] at h ⊢
  exact h

theorem log_div_le_cast_parameterDimension {N : ℕ} (hN : 0 < N) :
    Real.log (N : ℝ) / (2 * Real.log (parameterPrime N)) ≤
      (parameterDimension N : ℝ) := by
  have hpR : (1 : ℝ) < parameterPrime N := by
    exact_mod_cast ((by omega : 1 < 2).trans (two_lt_parameterPrime N))
  have hden : 0 < 2 * Real.log (parameterPrime N) := by
    exact mul_pos (by norm_num) (Real.log_pos hpR)
  have hcoverR : (N : ℝ) ≤
      (parameterPrime N ^ (2 * parameterDimension N) : ℕ) := by
    exact_mod_cast parameterDimension_cover N
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog := Real.log_le_log hNreal hcoverR
  rw [Nat.cast_pow, Real.log_pow] at hlog
  apply (div_le_iff₀ hden).2
  push_cast at hlog ⊢
  nlinarith

end Erdos788


/-! Flattened from Erdos788.CodeGeometry. -/


/-!
# Finite Euclidean bookkeeping for list decoding

This module packages the Cauchy--Schwarz calculation used in the paper's
simplex proof of the short code list bound.  It is independent of the later
choice of alphabet and encoder.
-/

namespace Erdos788

open scoped BigOperators

/-- The ordinary dot product of two real vectors on a finite type. -/
noncomputable def finiteDot {κ : Type*} [Fintype κ]
    (u v : κ → ℝ) : ℝ :=
  ∑ k, u k * v k

theorem finiteDot_sum_left {κ ι : Type*} [Fintype κ]
    (L : Finset ι) (v : ι → κ → ℝ) (w : κ → ℝ) :
    finiteDot (fun k ↦ ∑ i ∈ L, v i k) w =
      ∑ i ∈ L, finiteDot (v i) w := by
  classical
  simp only [finiteDot, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem finiteDot_sum_norm_expand {κ ι : Type*} [Fintype κ]
    (L : Finset ι) (v : ι → κ → ℝ) :
    (∑ k, (∑ i ∈ L, v i k) ^ 2) =
      ∑ i ∈ L, ∑ j ∈ L, finiteDot (v i) (v j) := by
  classical
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum, finiteDot]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _hj
  apply Finset.sum_congr rfl
  intro k _hk
  rw [mul_comm]

/-- Abstract simplex/Johnson calculation.  If all listed unit vectors have
pairwise inner product at most `β` and correlate with one unit received word
by more than `γ`, then the list has the standard rational size bound. -/
theorem card_lt_simplex_list_bound
    {κ ι : Type*} [Fintype κ] [DecidableEq ι]
    (L : Finset ι) (v : ι → κ → ℝ) (w : κ → ℝ)
    (β γ : ℝ)
    (hL : L.Nonempty)
    (hw : ∑ k, w k ^ 2 = 1)
    (hdiag : ∀ i ∈ L, finiteDot (v i) (v i) ≤ 1)
    (hoff : ∀ i ∈ L, ∀ j ∈ L, i ≠ j → finiteDot (v i) (v j) ≤ β)
    (hcorr : ∀ i ∈ L, γ < finiteDot (v i) w)
    (hγ : 0 ≤ γ) (hgap : β < γ ^ 2) :
    (L.card : ℝ) < (1 - β) / (γ ^ 2 - β) := by
  classical
  let S : κ → ℝ := fun k ↦ ∑ i ∈ L, v i k
  have hcardposNat : 0 < L.card := Finset.card_pos.mpr hL
  have hcardpos : (0 : ℝ) < L.card := by exact_mod_cast hcardposNat
  have hcorrSum : (L.card : ℝ) * γ < finiteDot S w := by
    rw [finiteDot_sum_left]
    obtain ⟨i₀, hi₀⟩ := hL
    have hsum : ∑ _i ∈ L, γ < ∑ i ∈ L, finiteDot (v i) w :=
      Finset.sum_lt_sum (fun i hi ↦ (hcorr i hi).le)
        ⟨i₀, hi₀, hcorr i₀ hi₀⟩
    simpa using hsum
  have hleft_nonneg : 0 ≤ (L.card : ℝ) * γ :=
    mul_nonneg hcardpos.le hγ
  have hdotpos : 0 < finiteDot S w := hleft_nonneg.trans_lt hcorrSum
  have hsquareStrict : ((L.card : ℝ) * γ) ^ 2 < (finiteDot S w) ^ 2 := by
    nlinarith
  have hcauchy : (finiteDot S w) ^ 2 ≤
      (∑ k, S k ^ 2) * ∑ k, w k ^ 2 := by
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ S w
  rw [hw, mul_one] at hcauchy
  have hrow : ∀ i ∈ L,
      (∑ j ∈ L, finiteDot (v i) (v j)) ≤
        1 + (L.card - 1 : ℕ) * β := by
    intro i hi
    rw [← Finset.sum_erase_add _ _ hi]
    have hoffsum : ∑ j ∈ L.erase i, finiteDot (v i) (v j) ≤
        ∑ _j ∈ L.erase i, β := by
      exact Finset.sum_le_sum fun j hj ↦
        hoff i hi j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj).symm
    calc
      (∑ j ∈ L.erase i, finiteDot (v i) (v j)) + finiteDot (v i) (v i)
          ≤ (∑ _j ∈ L.erase i, β) + 1 :=
        add_le_add hoffsum (hdiag i hi)
      _ = 1 + (L.card - 1 : ℕ) * β := by
        rw [Finset.sum_const, Finset.card_erase_of_mem hi]
        simp only [nsmul_eq_mul]
        ring
  have hnorm : ∑ k, S k ^ 2 ≤
      (L.card : ℝ) * (1 + (L.card - 1 : ℕ) * β) := by
    rw [finiteDot_sum_norm_expand]
    calc
      (∑ i ∈ L, ∑ j ∈ L, finiteDot (v i) (v j)) ≤
          ∑ _i ∈ L, (1 + (L.card - 1 : ℕ) * β) :=
        Finset.sum_le_sum hrow
      _ = (L.card : ℝ) * (1 + (L.card - 1 : ℕ) * β) := by
        rw [Finset.sum_const]
        simp only [nsmul_eq_mul]
  have hmaster : ((L.card : ℝ) * γ) ^ 2 <
      (L.card : ℝ) * (1 + (L.card - 1 : ℕ) * β) :=
    hsquareStrict.trans_le (hcauchy.trans hnorm)
  have hcastSub : ((L.card - 1 : ℕ) : ℝ) = (L.card : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [hcastSub] at hmaster
  have hdenom : 0 < γ ^ 2 - β := sub_pos.mpr hgap
  apply (lt_div_iff₀ hdenom).2
  nlinarith

/-- Scale-invariant form of `card_lt_simplex_list_bound`.  This avoids
introducing square roots when the regular-simplex vectors all have the same
positive squared norm `q`. -/
theorem card_lt_simplex_list_bound_scaled
    {κ ι : Type*} [Fintype κ] [DecidableEq ι]
    (L : Finset ι) (v : ι → κ → ℝ) (w : κ → ℝ)
    (q β γ : ℝ)
    (hL : L.Nonempty) (hq : 0 < q)
    (hw : ∑ k, w k ^ 2 = q)
    (hdiag : ∀ i ∈ L, finiteDot (v i) (v i) ≤ q)
    (hoff : ∀ i ∈ L, ∀ j ∈ L, i ≠ j →
      finiteDot (v i) (v j) ≤ q * β)
    (hcorr : ∀ i ∈ L, q * γ < finiteDot (v i) w)
    (hγ : 0 ≤ γ) (hgap : β < γ ^ 2) :
    (L.card : ℝ) < (1 - β) / (γ ^ 2 - β) := by
  classical
  let S : κ → ℝ := fun k ↦ ∑ i ∈ L, v i k
  have hcardposNat : 0 < L.card := Finset.card_pos.mpr hL
  have hcardpos : (0 : ℝ) < L.card := by exact_mod_cast hcardposNat
  have hcorrSum : (L.card : ℝ) * (q * γ) < finiteDot S w := by
    rw [finiteDot_sum_left]
    obtain ⟨i₀, hi₀⟩ := hL
    have hsum : ∑ _i ∈ L, q * γ < ∑ i ∈ L, finiteDot (v i) w :=
      Finset.sum_lt_sum (fun i hi ↦ (hcorr i hi).le)
        ⟨i₀, hi₀, hcorr i₀ hi₀⟩
    simpa using hsum
  have hleft_nonneg : 0 ≤ (L.card : ℝ) * (q * γ) :=
    mul_nonneg hcardpos.le (mul_nonneg hq.le hγ)
  have hdotpos : 0 < finiteDot S w := hleft_nonneg.trans_lt hcorrSum
  have hsquareStrict : ((L.card : ℝ) * (q * γ)) ^ 2 <
      (finiteDot S w) ^ 2 := by
    nlinarith
  have hcauchy : (finiteDot S w) ^ 2 ≤
      (∑ k, S k ^ 2) * ∑ k, w k ^ 2 := by
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ S w
  rw [hw] at hcauchy
  have hrow : ∀ i ∈ L,
      (∑ j ∈ L, finiteDot (v i) (v j)) ≤
        q * (1 + (L.card - 1 : ℕ) * β) := by
    intro i hi
    rw [← Finset.sum_erase_add _ _ hi]
    have hoffsum : ∑ j ∈ L.erase i, finiteDot (v i) (v j) ≤
        ∑ _j ∈ L.erase i, q * β := by
      exact Finset.sum_le_sum fun j hj ↦
        hoff i hi j (Finset.mem_of_mem_erase hj)
          (Finset.ne_of_mem_erase hj).symm
    calc
      (∑ j ∈ L.erase i, finiteDot (v i) (v j)) + finiteDot (v i) (v i)
          ≤ (∑ _j ∈ L.erase i, q * β) + q :=
        add_le_add hoffsum (hdiag i hi)
      _ = q * (1 + (L.card - 1 : ℕ) * β) := by
        rw [Finset.sum_const, Finset.card_erase_of_mem hi]
        simp only [nsmul_eq_mul]
        ring
  have hnorm : ∑ k, S k ^ 2 ≤
      (L.card : ℝ) * (q * (1 + (L.card - 1 : ℕ) * β)) := by
    rw [finiteDot_sum_norm_expand]
    calc
      (∑ i ∈ L, ∑ j ∈ L, finiteDot (v i) (v j)) ≤
          ∑ _i ∈ L, q * (1 + (L.card - 1 : ℕ) * β) :=
        Finset.sum_le_sum hrow
      _ = (L.card : ℝ) *
          (q * (1 + (L.card - 1 : ℕ) * β)) := by
        rw [Finset.sum_const]
        simp only [nsmul_eq_mul]
  have hmaster : ((L.card : ℝ) * (q * γ)) ^ 2 <
      ((L.card : ℝ) * (q * (1 + (L.card - 1 : ℕ) * β))) * q :=
    hsquareStrict.trans_le (hcauchy.trans (mul_le_mul_of_nonneg_right hnorm hq.le))
  have hmasterNormalized : ((L.card : ℝ) * γ) ^ 2 <
      (L.card : ℝ) * (1 + (L.card - 1 : ℕ) * β) := by
    apply (mul_lt_mul_iff_right₀ (sq_pos_of_pos hq)).mp
    calc
      q ^ 2 * ((L.card : ℝ) * γ) ^ 2 =
          ((L.card : ℝ) * (q * γ)) ^ 2 := by ring
      _ < ((L.card : ℝ) *
          (q * (1 + (L.card - 1 : ℕ) * β))) * q := hmaster
      _ = q ^ 2 *
          ((L.card : ℝ) * (1 + (L.card - 1 : ℕ) * β)) := by ring
  have hcastSub : ((L.card - 1 : ℕ) : ℝ) = (L.card : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [hcastSub] at hmasterNormalized
  have hdenom : 0 < γ ^ 2 - β := sub_pos.mpr hgap
  apply (lt_div_iff₀ hdenom).2
  nlinarith

end Erdos788


/-! Flattened from Erdos788.SimplexCode. -/


/-!
# The regular-simplex list bound for `ZMod p` words

This is the deterministic half of the short-code lemma.  A code with the
stated near-Plotkin distance automatically has the list bound needed by the
extractor reconstruction.
-/

namespace Erdos788

open scoped BigOperators

/-- The binary strings used as code-coordinate labels. -/
abbrev BinaryCoord (ell : ℕ) := Fin ell → Bool

/-- An unnormalized regular-simplex coordinate for one `ZMod p` symbol. -/
noncomputable def simplexEntry (p : ℕ) (a c : ZMod p) : ℝ :=
  if a = c then (p : ℝ) - 1 else -1

theorem sum_simplexEntry_mul {p : ℕ} [NeZero p] (a b : ZMod p) :
    (∑ c : ZMod p, simplexEntry p a c * simplexEntry p b c) =
      if a = b then (p : ℝ) * (p - 1) else -(p : ℝ) := by
  classical
  by_cases hab : a = b
  · subst b
    have hpoint : ∀ c : ZMod p,
        simplexEntry p a c * simplexEntry p a c =
          if a = c then ((p : ℝ) - 1) ^ 2 else 1 := by
      intro c
      by_cases hac : a = c <;> simp [simplexEntry, hac, pow_two]
    have hsame :
        (Finset.univ.filter fun c : ZMod p ↦ a = c).card = 1 := by
      rw [show (Finset.univ.filter fun c : ZMod p ↦ a = c) = {a} by
        ext c
        simp [eq_comm]]
      simp
    have hsplitNat :
        (Finset.univ.filter fun c : ZMod p ↦ a = c).card +
            (Finset.univ.filter fun c : ZMod p ↦ ¬a = c).card = p := by
      simpa only [Finset.card_univ, ZMod.card] using
        (Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset (ZMod p))) (fun c ↦ a = c))
    have hsplit :
        ((Finset.univ.filter fun c : ZMod p ↦ a = c).card : ℝ) +
            ((Finset.univ.filter fun c : ZMod p ↦ ¬a = c).card : ℝ) =
          (p : ℝ) := by
      exact_mod_cast hsplitNat
    rw [Finset.sum_congr rfl fun c _hc ↦ hpoint c]
    rw [Finset.sum_ite]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hsame] at hsplit ⊢
    norm_num at hsplit ⊢
    nlinarith
  · have hpoint : ∀ c : ZMod p,
        simplexEntry p a c * simplexEntry p b c =
          if a = c then 1 - (p : ℝ)
          else if b = c then 1 - (p : ℝ) else 1 := by
      intro c
      by_cases hac : a = c
      · have hbc : b ≠ c := by
          intro hbc
          exact hab (hac.trans hbc.symm)
        simp [simplexEntry, hac, hbc]
      · by_cases hbc : b = c <;> simp [simplexEntry, hac, hbc]
    let A : Finset (ZMod p) :=
      Finset.univ.filter fun c ↦ a = c
    let R : Finset (ZMod p) :=
      Finset.univ.filter fun c ↦ ¬a = c
    let B : Finset (ZMod p) := R.filter fun c ↦ b = c
    let C : Finset (ZMod p) := R.filter fun c ↦ ¬b = c
    have hA : A.card = 1 := by
      rw [show A = {a} by
        ext c
        simp [A, eq_comm]]
      simp
    have hB : B.card = 1 := by
      rw [show B = {b} by
        ext c
        simp only [B, R, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_singleton]
        constructor
        · rintro ⟨_hac, hbc⟩
          exact hbc.symm
        · intro hcb
          subst c
          exact ⟨hab, rfl⟩]
      simp
    have hAR : A.card + R.card = p := by
      simpa only [A, R, Finset.card_univ, ZMod.card] using
        (Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset (ZMod p))) (fun c ↦ a = c))
    have hBC : B.card + C.card = R.card := by
      simpa only [B, C] using
        (Finset.card_filter_add_card_filter_not
          (s := R) (fun c ↦ b = c))
    have htotalNat : A.card + B.card + C.card = p := by omega
    have htotal : (A.card : ℝ) + (B.card : ℝ) + (C.card : ℝ) = (p : ℝ) := by
      exact_mod_cast htotalNat
    rw [Finset.sum_congr rfl fun c _hc ↦ hpoint c]
    rw [Finset.sum_ite]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [Finset.sum_ite]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    change (A.card : ℝ) * (1 - (p : ℝ)) +
        ((B.card : ℝ) * (1 - (p : ℝ)) + (C.card : ℝ)) =
          if a = b then (p : ℝ) * (p - 1) else -(p : ℝ)
    rw [if_neg hab]
    rw [hA, hB] at htotal ⊢
    norm_num at htotal ⊢
    nlinarith

/-- Number of coordinates at which two words agree. -/
noncomputable def agreementCount {p ell : ℕ}
    (u v : BinaryCoord ell → ZMod p) : ℕ := by
  classical
  exact (Finset.univ.filter fun z ↦ u z = v z).card

/-- Fraction of coordinates at which two words agree. -/
noncomputable def agreement {p ell : ℕ}
    (u v : BinaryCoord ell → ZMod p) : ℝ :=
  (agreementCount u v : ℝ) / Fintype.card (BinaryCoord ell)

@[simp]
theorem agreementCount_self {p ell : ℕ}
    (u : BinaryCoord ell → ZMod p) :
    agreementCount u u = Fintype.card (BinaryCoord ell) := by
  classical
  simp [agreementCount]

@[simp]
theorem agreement_self {p ell : ℕ}
    (u : BinaryCoord ell → ZMod p) : agreement u u = 1 := by
  rw [agreement, agreementCount_self]
  exact div_self (by
    exact_mod_cast
      (Nat.ne_of_gt (Fintype.card_pos : 0 < Fintype.card (BinaryCoord ell))))

/-- The common squared norm of the unnormalized simplex word vectors. -/
noncomputable def simplexWordScale (p ell : ℕ) : ℝ :=
  (Fintype.card (BinaryCoord ell) : ℝ) * p * (p - 1)

theorem simplexWordScale_pos {p ell : ℕ} (hp : 1 < p) :
    0 < simplexWordScale p ell := by
  have hcoord : (0 : ℝ) < Fintype.card (BinaryCoord ell) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (BinaryCoord ell))
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  rw [simplexWordScale]
  exact mul_pos (mul_pos hcoord (by positivity)) (sub_pos.mpr hpR)

/-- The unnormalized concatenated simplex vector of a word. -/
noncomputable def wordSimplexRaw {p ell : ℕ}
    (u : BinaryCoord ell → ZMod p) :
    BinaryCoord ell × ZMod p → ℝ :=
  fun q ↦ simplexEntry p (u q.1) q.2

theorem finiteDot_wordSimplexRaw {p ell : ℕ} [NeZero p]
    (u v : BinaryCoord ell → ZMod p) :
    finiteDot (wordSimplexRaw u) (wordSimplexRaw v) =
      (p : ℝ) *
        ((p : ℝ) * agreementCount u v -
          Fintype.card (BinaryCoord ell)) := by
  classical
  rw [finiteDot]
  rw [Fintype.sum_prod_type]
  simp_rw [wordSimplexRaw, sum_simplexEntry_mul]
  let same : Finset (BinaryCoord ell) :=
    Finset.univ.filter fun z ↦ u z = v z
  let diff : Finset (BinaryCoord ell) :=
    Finset.univ.filter fun z ↦ ¬u z = v z
  have hsplit : same.card + diff.card = Fintype.card (BinaryCoord ell) := by
    simpa only [same, diff, Finset.card_univ] using
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (BinaryCoord ell)))
        (fun z ↦ u z = v z))
  have hsame : same.card = agreementCount u v := rfl
  have hsplitR : (same.card : ℝ) + (diff.card : ℝ) =
      (Fintype.card (BinaryCoord ell) : ℝ) := by
    exact_mod_cast hsplit
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul]
  change (same.card : ℝ) * ((p : ℝ) * (p - 1)) +
    (diff.card : ℝ) * (-(p : ℝ)) = _
  rw [hsame] at hsplitR ⊢
  nlinarith

theorem finiteDot_wordSimplexRaw_eq_scale_mul {p ell : ℕ} [NeZero p]
    (hp : 1 < p) (u v : BinaryCoord ell → ZMod p) :
    finiteDot (wordSimplexRaw u) (wordSimplexRaw v) =
      simplexWordScale p ell *
        (((p : ℝ) * agreement u v - 1) / ((p : ℝ) - 1)) := by
  rw [finiteDot_wordSimplexRaw, agreement, simplexWordScale]
  have hcoord : (0 : ℝ) < Fintype.card (BinaryCoord ell) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (BinaryCoord ell))
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  field_simp [ne_of_gt hcoord, ne_of_gt (sub_pos.mpr hpR)]

theorem finiteDot_wordSimplexRaw_le_of_agreement_le
    {p ell : ℕ} [NeZero p] (hp : 1 < p)
    (u v : BinaryCoord ell → ZMod p) (a : ℝ)
    (h : agreement u v ≤ a) :
    finiteDot (wordSimplexRaw u) (wordSimplexRaw v) ≤
      simplexWordScale p ell *
        (((p : ℝ) * a - 1) / ((p : ℝ) - 1)) := by
  rw [finiteDot_wordSimplexRaw_eq_scale_mul hp]
  apply mul_le_mul_of_nonneg_left _ (simplexWordScale_pos hp).le
  apply (div_le_div_iff_of_pos_right (by
    exact sub_pos.mpr (by exact_mod_cast hp))).2
  have hp0 : (0 : ℝ) ≤ p := by positivity
  nlinarith

theorem finiteDot_wordSimplexRaw_lt_of_agreement_lt
    {p ell : ℕ} [NeZero p] (hp : 1 < p)
    (u v : BinaryCoord ell → ZMod p) (a : ℝ)
    (h : agreement u v < a) :
    finiteDot (wordSimplexRaw u) (wordSimplexRaw v) <
      simplexWordScale p ell *
        (((p : ℝ) * a - 1) / ((p : ℝ) - 1)) := by
  rw [finiteDot_wordSimplexRaw_eq_scale_mul hp]
  apply mul_lt_mul_of_pos_left _ (simplexWordScale_pos hp)
  apply (div_lt_div_iff_of_pos_right (by
    exact sub_pos.mpr (by exact_mod_cast hp))).2
  have hp0 : (0 : ℝ) < p := by positivity
  nlinarith

theorem scale_mul_lt_finiteDot_wordSimplexRaw_of_lt_agreement
    {p ell : ℕ} [NeZero p] (hp : 1 < p)
    (u v : BinaryCoord ell → ZMod p) (a : ℝ)
    (h : a < agreement u v) :
    simplexWordScale p ell *
        (((p : ℝ) * a - 1) / ((p : ℝ) - 1)) <
      finiteDot (wordSimplexRaw u) (wordSimplexRaw v) := by
  rw [finiteDot_wordSimplexRaw_eq_scale_mul hp]
  apply mul_lt_mul_of_pos_left _ (simplexWordScale_pos hp)
  apply (div_lt_div_iff_of_pos_right (by
    exact sub_pos.mpr (by exact_mod_cast hp))).2
  have hp0 : (0 : ℝ) < p := by positivity
  nlinarith

theorem sum_sq_wordSimplexRaw {p ell : ℕ} [NeZero p]
    (u : BinaryCoord ell → ZMod p) :
    (∑ q, wordSimplexRaw u q ^ 2) = simplexWordScale p ell := by
  rw [show (∑ q, wordSimplexRaw u q ^ 2) =
      finiteDot (wordSimplexRaw u) (wordSimplexRaw u) by
    simp only [finiteDot, pow_two]]
  rw [finiteDot_wordSimplexRaw, agreementCount_self, simplexWordScale]
  ring

theorem finiteDot_wordSimplexRaw_self {p ell : ℕ} [NeZero p]
    (u : BinaryCoord ell → ZMod p) :
    finiteDot (wordSimplexRaw u) (wordSimplexRaw u) =
      simplexWordScale p ell := by
  rw [finiteDot_wordSimplexRaw, agreementCount_self, simplexWordScale]
  ring

/-- The deterministic list-decoding implication used by the short-code
construction.  A near-Plotkin pairwise agreement bound forces every strict
agreement list to have the paper's explicit size bound. -/
theorem card_lt_two_div_sq_add_one_of_pairwise_agreement
    {p ell : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Fact p.Prime]
    (η τ : ℝ) (hη : 0 < η)
    (hτ : τ = (p : ℝ) * η ^ 2 / (2 * ((p : ℝ) - 1)))
    (L : Finset ι)
    (word : ι → BinaryCoord ell → ZMod p)
    (Q : BinaryCoord ell → ZMod p)
    (hpair : ∀ i ∈ L, ∀ j ∈ L, i ≠ j →
      agreement (word i) (word j) ≤ 1 / (p : ℝ) + τ)
    (hcorr : ∀ i ∈ L,
      1 / (p : ℝ) + η < agreement (word i) Q) :
    (L.card : ℝ) < 2 / η ^ 2 + 1 := by
  classical
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  let _ : NeZero p := ⟨by omega⟩
  by_cases hL : L.Nonempty
  · let q : ℝ := simplexWordScale p ell
    let β : ℝ := (p : ℝ) * τ / ((p : ℝ) - 1)
    let γ : ℝ := (p : ℝ) * η / ((p : ℝ) - 1)
    have hpR : (1 : ℝ) < p := by exact_mod_cast hp
    have hpR0 : (0 : ℝ) < p := by positivity
    have hden : (0 : ℝ) < (p : ℝ) - 1 := sub_pos.mpr hpR
    have hq : 0 < q := simplexWordScale_pos hp
    have hγ : 0 < γ := by
      dsimp [γ]
      positivity
    have hβeq : β = γ ^ 2 / 2 := by
      dsimp [β, γ]
      rw [hτ]
      field_simp [ne_of_gt hpR0, ne_of_gt hden]
    have hgap : β < γ ^ 2 := by
      rw [hβeq]
      nlinarith [sq_pos_of_pos hγ]
    have hw : ∑ k, wordSimplexRaw Q k ^ 2 = q :=
      sum_sq_wordSimplexRaw Q
    have hdiag : ∀ i ∈ L,
        finiteDot (wordSimplexRaw (word i)) (wordSimplexRaw (word i)) ≤ q := by
      intro i _hi
      exact (finiteDot_wordSimplexRaw_self (word i)).le
    have hoff : ∀ i ∈ L, ∀ j ∈ L, i ≠ j →
        finiteDot (wordSimplexRaw (word i)) (wordSimplexRaw (word j)) ≤
          q * β := by
      intro i hi j hj hij
      calc
        finiteDot (wordSimplexRaw (word i)) (wordSimplexRaw (word j)) ≤
            q * (((p : ℝ) * (1 / (p : ℝ) + τ) - 1) /
              ((p : ℝ) - 1)) :=
          finiteDot_wordSimplexRaw_le_of_agreement_le hp _ _ _
            (hpair i hi j hj hij)
        _ = q * β := by
          dsimp [β]
          field_simp [ne_of_gt hpR0]
          ring
    have hcorrRaw : ∀ i ∈ L, q * γ <
        finiteDot (wordSimplexRaw (word i)) (wordSimplexRaw Q) := by
      intro i hi
      calc
        q * γ = q * (((p : ℝ) * (1 / (p : ℝ) + η) - 1) /
            ((p : ℝ) - 1)) := by
          dsimp [γ]
          field_simp [ne_of_gt hpR0]
          ring
        _ < finiteDot (wordSimplexRaw (word i)) (wordSimplexRaw Q) :=
          scale_mul_lt_finiteDot_wordSimplexRaw_of_lt_agreement hp _ _ _
            (hcorr i hi)
    have hgeom := card_lt_simplex_list_bound_scaled
      L (fun i ↦ wordSimplexRaw (word i)) (wordSimplexRaw Q)
      q β γ hL hq hw hdiag hoff hcorrRaw hγ.le hgap
    have hβnonneg : 0 ≤ β := by
      rw [hβeq]
      positivity
    have hgeomDen : 0 < γ ^ 2 - β := sub_pos.mpr hgap
    have hratioOne : (1 - β) / (γ ^ 2 - β) ≤
        1 / (γ ^ 2 - β) := by
      exact (div_le_div_iff_of_pos_right hgeomDen).2 (by nlinarith)
    have hdenEq : γ ^ 2 - β = γ ^ 2 / 2 := by
      rw [hβeq]
      ring
    have hηleγ : η ≤ γ := by
      dsimp [γ]
      apply (le_div_iff₀ hden).2
      nlinarith
    have hsq : η ^ 2 ≤ γ ^ 2 := by nlinarith
    have htwo : 2 / γ ^ 2 ≤ 2 / η ^ 2 := by
      exact div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hη) hsq
    have hratio : (1 - β) / (γ ^ 2 - β) ≤ 2 / η ^ 2 := by
      calc
        (1 - β) / (γ ^ 2 - β) ≤ 1 / (γ ^ 2 - β) := hratioOne
        _ = 2 / γ ^ 2 := by rw [hdenEq]; field_simp
        _ ≤ 2 / η ^ 2 := htwo
    exact hgeom.trans_le (hratio.trans (by linarith))
  · rw [Finset.not_nonempty_iff_eq_empty.mp hL]
    simp only [Finset.card_empty, Nat.cast_zero]
    have hetaSq : 0 < η ^ 2 := sq_pos_of_pos hη
    positivity

end Erdos788


/-! Flattened from Erdos788.ShortLinearCode. -/


/-!
# Short linear codes over `ZMod p`

This file formalizes the probabilistic part of the short-code lemma.  A
matrix is represented by its list of rows.  For every fixed nonzero input,
its row evaluations are independent uniform field elements; Hoeffding's
inequality and a finite union bound then give one matrix having the required
near-Plotkin distance.  The deterministic simplex argument converting that
distance into an agreement-list bound is proved at the end of the file.
-/

namespace Erdos788

open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory

/-- Evaluation against a fixed vector, viewed as a linear functional in the
row variable. -/
def rowDotLinear (p m : ℕ) [Fact p.Prime]
    (x : Fin m → ZMod p) : (Fin m → ZMod p) →ₗ[ZMod p] ZMod p where
  toFun a := ∑ j, a j * x j
  map_add' a b := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    ring

@[simp]
theorem rowDotLinear_apply {p m : ℕ} [Fact p.Prime]
    (x a : Fin m → ZMod p) :
    rowDotLinear p m x a = ∑ j, a j * x j := rfl

theorem rowDotLinear_surjective {p m : ℕ} [Fact p.Prime]
    {x : Fin m → ZMod p} (hx : x ≠ 0) :
    Function.Surjective (rowDotLinear p m x) := by
  classical
  have hex : ∃ j, x j ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  obtain ⟨j, hj⟩ := hex
  intro c
  let a : Fin m → ZMod p := fun i ↦ if i = j then c / x j else 0
  refine ⟨a, ?_⟩
  simp only [rowDotLinear_apply, a]
  rw [Finset.sum_eq_single j]
  · simp [hj]
  · intro i _hi hij
    simp [hij]
  · simp

/-- A nonzero linear functional on `m` field coordinates has exactly
`p^(m-1)` zeros. -/
theorem card_rowDotLinear_eq_zero {p m : ℕ} [Fact p.Prime]
    {x : Fin m → ZMod p} (hx : x ≠ 0) :
    Fintype.card {a : Fin m → ZMod p // rowDotLinear p m x a = 0} =
      p ^ (m - 1) := by
  have hm : 0 < m := by
    by_contra h
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos h
    subst m
    exact hx (Subsingleton.elim _ _)
  let F := rowDotLinear p m x
  have hsurj : Function.Surjective F := rowDotLinear_surjective hx
  have hrange : F.range = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hfrange : Module.finrank (ZMod p) F.range = 1 := by
    rw [hrange, finrank_top]
    simp
  have hfdomain : Module.finrank (ZMod p) (Fin m → ZMod p) = m := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  have hfker : Module.finrank (ZMod p) F.ker = m - 1 := by
    have h := F.finrank_range_add_finrank_ker
    rw [hfrange, hfdomain] at h
    omega
  change Fintype.card {a : Fin m → ZMod p // F a = 0} = p ^ (m - 1)
  rw [← Nat.card_eq_fintype_card]
  change Nat.card F.ker = p ^ (m - 1)
  rw [
    Module.natCard_eq_pow_finrank (K := ZMod p) (V := F.ker),
    Nat.card_zmod, hfker]

/-- The exact finite average of the zero indicator of a nonzero row
functional is `1/p`. -/
theorem average_rowDotLinear_eq_zero {p m : ℕ} [Fact p.Prime]
    {x : Fin m → ZMod p} (hx : x ≠ 0) :
    (Fintype.card (Fin m → ZMod p) : ℝ)⁻¹ *
        (∑ a : Fin m → ZMod p,
          if rowDotLinear p m x a = 0 then (1 : ℝ) else 0) =
      1 / p := by
  classical
  have hm : 0 < m := by
    by_contra h
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos h
    subst m
    exact hx (Subsingleton.elim _ _)
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hsum :
      (∑ a : Fin m → ZMod p,
          if rowDotLinear p m x a = 0 then (1 : ℝ) else 0) =
        ((p ^ (m - 1) : ℕ) : ℝ) := by
    rw [← card_rowDotLinear_eq_zero hx]
    norm_cast
    change (∑ a ∈ (Finset.univ : Finset (Fin m → ZMod p)),
      if rowDotLinear p m x a = 0 then (1 : ℕ) else 0) = _
    rw [Finset.sum_boole]
    simpa only [rowDotLinear_apply, Nat.cast_id] using
      (Fintype.card_subtype (fun a : Fin m → ZMod p ↦
        rowDotLinear p m x a = 0)).symm
  rw [hsum]
  simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card]
  have hm' : m - 1 + 1 = m := Nat.sub_add_cancel hm
  rw [← hm', pow_succ]
  push_cast
  field_simp

/-- The real-valued indicator that a row annihilates `x`. -/
noncomputable def rowZeroIndicator {p m : ℕ} [Fact p.Prime]
    (x a : Fin m → ZMod p) : ℝ :=
  if rowDotLinear p m x a = 0 then 1 else 0

theorem integral_rowZeroIndicator_uniform {p m : ℕ} [Fact p.Prime]
    [MeasurableSpace (Fin m → ZMod p)]
    [MeasurableSingletonClass (Fin m → ZMod p)]
    {x : Fin m → ZMod p} (hx : x ≠ 0) :
    ∫ a, rowZeroIndicator x a ∂(PMF.uniformOfFintype
        (Fin m → ZMod p)).toMeasure = 1 / p := by
  rw [PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, smul_eq_mul]
  rw [← Finset.mul_sum]
  exact average_rowDotLinear_eq_zero hx

/-- A finite product of uniform random rows contains a matrix for which every
nonzero input has agreement with zero at most `1/p + τ`, as soon as the
explicit Hoeffding union bound is below one. -/
theorem exists_rows_nearPlotkin_of_exponential_bound
    (p m R : ℕ) [Fact p.Prime] (hR : 0 < R) (τ : ℝ) (hτ : 0 ≤ τ)
    (hbound :
      (Fintype.card {x : Fin m → ZMod p // x ≠ 0} : ℝ) *
          Real.exp (-2 * R * τ ^ 2) < 1) :
    ∃ T : Fin R → (Fin m → ZMod p),
      ∀ x : Fin m → ZMod p, x ≠ 0 →
        (∑ i, rowZeroIndicator x (T i)) ≤
          (R : ℝ) * (1 / p + τ) := by
  classical
  let Row := Fin m → ZMod p
  let _ : MeasurableSpace Row := ⊤
  let μ₀ : Measure Row := (PMF.uniformOfFintype Row).toMeasure
  let _ : IsProbabilityMeasure μ₀ := inferInstance
  let μ : Measure (Fin R → Row) := Measure.pi (fun _ ↦ μ₀)
  let _ : IsProbabilityMeasure μ := inferInstance
  let bad (x : {x : Fin m → ZMod p // x ≠ 0}) :
      Set (Fin R → Row) :=
    {T | (R : ℝ) * (1 / p + τ) <
      ∑ i, rowZeroIndicator x.1 (T i)}
  have htail (x : {x : Fin m → ZMod p // x ≠ 0}) :
      μ.real (bad x) ≤ Real.exp (-2 * R * τ ^ 2) := by
    let X₀ : Fin R → Row → ℝ := fun _ a ↦
      rowZeroIndicator x.1 a - 1 / p
    have hmean : ∀ i : Fin R,
        ∫ a, rowZeroIndicator x.1 a ∂μ₀ = 1 / p := by
      intro i
      exact integral_rowZeroIndicator_uniform x.2
    have hcomponent : ∀ i : Fin R,
        HasSubgaussianMGF (X₀ i) (1 / 4 : ℝ≥0) μ₀ := by
      intro i
      have hm : AEMeasurable (fun a : Row ↦ rowZeroIndicator x.1 a) μ₀ :=
        (measurable_of_finite _).aemeasurable
      have hrange : ∀ᵐ a ∂μ₀,
          rowZeroIndicator x.1 a ∈ Set.Icc (0 : ℝ) 1 := by
        filter_upwards [] with a
        simp only [rowZeroIndicator]
        split <;> simp
      have hs := hasSubgaussianMGF_of_mem_Icc hm hrange
      rw [hmean i] at hs
      convert hs using 1
      all_goals norm_num [X₀]
    have hind : iIndepFun
        (fun i (T : Fin R → Row) ↦ X₀ i (T i)) μ := by
      apply iIndepFun_pi
      intro i
      exact (measurable_of_finite _).aemeasurable
    have hsub : ∀ i ∈ (Finset.univ : Finset (Fin R)),
        HasSubgaussianMGF
          (fun T : Fin R → Row ↦ X₀ i (T i)) (1 / 4 : ℝ≥0) μ := by
      intro i _hi
      have hmapped : HasSubgaussianMGF (X₀ i) (1 / 4 : ℝ≥0)
          (μ.map (fun T : Fin R → Row ↦ T i)) := by
        rw [(measurePreserving_eval (fun _ : Fin R ↦ μ₀) i).map_eq]
        exact hcomponent i
      change HasSubgaussianMGF
        ((X₀ i) ∘ fun T : Fin R → Row ↦ T i) (1 / 4 : ℝ≥0) μ
      exact HasSubgaussianMGF.of_map
        (X := X₀ i) (Y := fun T : Fin R → Row ↦ T i)
        (measurable_pi_apply i).aemeasurable hmapped
    have hhoeff := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind hsub
      (s := (Finset.univ : Finset (Fin R)))
      (c := fun _ ↦ (1 / 4 : ℝ≥0))
      (hε := mul_nonneg (by positivity : (0 : ℝ) ≤ R) hτ)
      ( ε := (R : ℝ) * τ)
    have hclosed :
        μ.real {T : Fin R → Row |
            (R : ℝ) * τ ≤ ∑ i, X₀ i (T i)} ≤
          Real.exp (-2 * R * τ ^ 2) := by
      calc
        μ.real {T : Fin R → Row |
            (R : ℝ) * τ ≤ ∑ i, X₀ i (T i)} ≤
            Real.exp (-((R : ℝ) * τ) ^ 2 /
              (2 * ((R : ℝ) * (1 / 4)))) := by
                simpa only [Finset.sum_const, Finset.card_univ,
                  Fintype.card_fin, nsmul_eq_mul, NNReal.coe_mul,
                  NNReal.coe_natCast, NNReal.coe_ofNat, NNReal.coe_div,
                  NNReal.coe_one] using hhoeff
        _ = Real.exp (-2 * R * τ ^ 2) := by
          congr 1
          have hRne : (R : ℝ) ≠ 0 := by positivity
          field_simp
          ring
    apply (measureReal_mono ?_).trans hclosed
    intro T hT
    change (R : ℝ) * (1 / p + τ) <
      ∑ i, rowZeroIndicator x.1 (T i) at hT
    change (R : ℝ) * τ ≤ ∑ i, X₀ i (T i)
    simp only [X₀, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    linarith
  have hunion : μ.real (⋃ x, bad x) < 1 := by
    calc
      μ.real (⋃ x, bad x) ≤ ∑ x, μ.real (bad x) :=
        measureReal_iUnion_fintype_le bad
      _ ≤ ∑ _x : {x : Fin m → ZMod p // x ≠ 0},
          Real.exp (-2 * R * τ ^ 2) := Finset.sum_le_sum fun x _hx ↦ htail x
      _ = (Fintype.card {x : Fin m → ZMod p // x ≠ 0} : ℝ) *
          Real.exp (-2 * R * τ ^ 2) := by simp
      _ < 1 := hbound
  by_contra hgood
  push Not at hgood
  have hall : (⋃ x, bad x) = Set.univ := by
    ext T
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨x, hx, hbad⟩ := hgood T
    exact ⟨⟨x, hx⟩, hbad⟩
  rw [hall, probReal_univ] at hunion
  exact (lt_irrefl (1 : ℝ) hunion).elim

theorem exponential_union_bound_of_length
    (p m R : ℕ) [Fact p.Prime] (τ : ℝ) (hτ : 0 < τ)
    (hR : (m + 1 : ℝ) * Real.log p / (2 * τ ^ 2) < R) :
    (Fintype.card {x : Fin m → ZMod p // x ≠ 0} : ℝ) *
        Real.exp (-2 * R * τ ^ 2) < 1 := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos hpR
  have hscale : 0 < 2 * τ ^ 2 := by positivity
  have hexpArg : -2 * (R : ℝ) * τ ^ 2 <
      -(m + 1 : ℝ) * Real.log p := by
    have := (div_lt_iff₀ hscale).mp hR
    nlinarith
  have hexp : Real.exp (-2 * (R : ℝ) * τ ^ 2) <
      ((p : ℝ) ^ (m + 1))⁻¹ := by
    calc
      Real.exp (-2 * (R : ℝ) * τ ^ 2) <
          Real.exp (-(m + 1 : ℝ) * Real.log p) :=
        Real.exp_lt_exp.mpr hexpArg
      _ = (Real.exp ((m + 1 : ℝ) * Real.log p))⁻¹ := by
        rw [show -(m + 1 : ℝ) * Real.log p =
          -((m + 1 : ℝ) * Real.log p) by ring, Real.exp_neg]
      _ = ((p : ℝ) ^ (m + 1))⁻¹ := by
        rw [show (m + 1 : ℝ) * Real.log p =
          (m + 1 : ℕ) * Real.log p by norm_num,
          Real.exp_nat_mul, Real.exp_log (by positivity : (0 : ℝ) < p)]
  have hcard :
      Fintype.card {x : Fin m → ZMod p // x ≠ 0} ≤ p ^ m := by
    calc
      Fintype.card {x : Fin m → ZMod p // x ≠ 0} ≤
          Fintype.card (Fin m → ZMod p) := Fintype.card_subtype_le _
      _ = p ^ m := by simp [ZMod.card]
  have hpowpos : (0 : ℝ) < (p : ℝ) ^ m := by positivity
  calc
    (Fintype.card {x : Fin m → ZMod p // x ≠ 0} : ℝ) *
        Real.exp (-2 * R * τ ^ 2)
        ≤ (p : ℝ) ^ m * Real.exp (-2 * R * τ ^ 2) := by
          gcongr
          exact_mod_cast hcard
    _ < (p : ℝ) ^ m * ((p : ℝ) ^ (m + 1))⁻¹ :=
      mul_lt_mul_of_pos_left hexp hpowpos
    _ = (p : ℝ)⁻¹ := by
      rw [pow_succ]
      field_simp
    _ < 1 := inv_lt_one_of_one_lt₀ hpR

/-- Binary-coordinate version of the random near-Plotkin construction.
The displayed length estimate is an explicit real inequality; in particular
the block length is polynomial in `m`, `log p`, and `1/τ`. -/
theorem exists_binary_rows_nearPlotkin
    (p m : ℕ) [Fact p.Prime] (τ : ℝ) (hτ : 0 < τ) :
    ∃ ell : ℕ, ∃ T : BinaryCoord ell → (Fin m → ZMod p),
      (∀ x : Fin m → ZMod p, x ≠ 0 →
        (∑ z, rowZeroIndicator x (T z)) ≤
          (2 ^ ell : ℝ) * (1 / p + τ)) ∧
      (2 ^ ell : ℝ) < (m + 1 : ℝ) * Real.log p / τ ^ 2 + 4 := by
  classical
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos hpR
  let A : ℝ := (m + 1 : ℝ) * Real.log p / (2 * τ ^ 2)
  have hA : 0 < A := by
    dsimp [A]
    positivity
  let n : ℕ := ⌈A⌉₊ + 1
  have hn2 : 2 ≤ n := by
    dsimp [n]
    have : 1 ≤ ⌈A⌉₊ := (Nat.one_le_ceil_iff).2 hA
    omega
  let ell : ℕ := Nat.clog 2 n
  let R : ℕ := 2 ^ ell
  have hnR : n ≤ R := by
    exact Nat.le_pow_clog (by omega) n
  have hAR : A < R := by
    have hAce : A ≤ (⌈A⌉₊ : ℝ) := Nat.le_ceil A
    have hAn : A < (n : ℝ) := by
      dsimp [n]
      push_cast
      linarith
    exact hAn.trans_le (by exact_mod_cast hnR)
  have hRpos : 0 < R := pow_pos (by omega) _
  have hbound := exponential_union_bound_of_length p m R τ hτ (by
    simpa [A] using hAR)
  obtain ⟨T₀, hT₀⟩ := exists_rows_nearPlotkin_of_exponential_bound
    p m R hRpos τ hτ.le hbound
  have hcard : Fintype.card (BinaryCoord ell) = R := by
    simp [BinaryCoord, R]
  let e : BinaryCoord ell ≃ Fin R := Fintype.equivOfCardEq (by simpa using hcard)
  let T : BinaryCoord ell → (Fin m → ZMod p) := fun z ↦ T₀ (e z)
  refine ⟨ell, T, ?_, ?_⟩
  · intro x hx
    have hsum : (∑ z, rowZeroIndicator x (T z)) =
        ∑ i, rowZeroIndicator x (T₀ i) := by
      exact Fintype.sum_equiv e _ _ (fun z ↦ rfl)
    rw [hsum]
    simpa [R] using hT₀ x hx
  · have hellpos : 0 < ell := by
      exact Nat.clog_pos (by omega) (lt_of_lt_of_le (by omega) hn2)
    have hpred : 2 ^ (ell - 1) < n := by
      simpa [ell] using Nat.pow_pred_clog_lt_self (b := 2) (by omega) (by omega : 1 < n)
    have hRlt : R < 2 * n := by
      change 2 ^ ell < 2 * n
      calc
        2 ^ ell = 2 * 2 ^ (ell - 1) := by
          calc
            2 ^ ell = 2 ^ (ell - 1 + 1) := by
              exact congrArg (fun k ↦ 2 ^ k) (Nat.sub_add_cancel hellpos).symm
            _ = 2 * 2 ^ (ell - 1) := by rw [pow_succ]; omega
        _ < 2 * n :=
          (Nat.mul_lt_mul_left (by norm_num : 0 < 2)).2 hpred
    have hnA : (n : ℝ) < A + 2 := by
      have hc := Nat.ceil_lt_add_one hA.le
      dsimp [n]
      push_cast
      linarith
    have hRreal : (R : ℝ) < 2 * (A + 2) := by
      have : (R : ℝ) < 2 * n := by exact_mod_cast hRlt
      nlinarith
    dsimp [A] at hRreal
    simpa [R] using (show (R : ℝ) <
      (m + 1 : ℝ) * Real.log p / τ ^ 2 + 4 by
        convert hRreal using 1
        all_goals field_simp
        all_goals ring)

/-- The linear encoder whose coordinate `z` is evaluation against row
`T z`. -/
def binaryRowEncoder (p m ell : ℕ) [Fact p.Prime]
    (T : BinaryCoord ell → (Fin m → ZMod p)) :
    (Fin m → ZMod p) →ₗ[ZMod p] (BinaryCoord ell → ZMod p) where
  toFun x z := ∑ j, T z j * x j
  map_add' x y := by
    funext z
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    funext z
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    ring

@[simp]
theorem binaryRowEncoder_apply {p m ell : ℕ} [Fact p.Prime]
    (T : BinaryCoord ell → (Fin m → ZMod p))
    (x : Fin m → ZMod p) (z : BinaryCoord ell) :
    binaryRowEncoder p m ell T x z = ∑ j, T z j * x j := rfl

theorem sum_rowZeroIndicator_sub_eq_agreementCount
    {p m ell : ℕ} [Fact p.Prime]
    (T : BinaryCoord ell → (Fin m → ZMod p))
    (x y : Fin m → ZMod p) :
    (∑ z, rowZeroIndicator (x - y) (T z)) =
      (agreementCount (binaryRowEncoder p m ell T x)
        (binaryRowEncoder p m ell T y) : ℕ) := by
  classical
  have hiff (z : BinaryCoord ell) :
      rowDotLinear p m (x - y) (T z) = 0 ↔
        binaryRowEncoder p m ell T x z =
          binaryRowEncoder p m ell T y z := by
    change binaryRowEncoder p m ell T (x - y) z = 0 ↔
      binaryRowEncoder p m ell T x z = binaryRowEncoder p m ell T y z
    rw [(binaryRowEncoder p m ell T).map_sub, Pi.sub_apply, sub_eq_zero]
  rw [agreementCount]
  simp only [rowZeroIndicator, hiff]
  norm_cast
  change (∑ z ∈ (Finset.univ : Finset (BinaryCoord ell)),
    if binaryRowEncoder p m ell T x z =
      binaryRowEncoder p m ell T y z then 1 else 0) = _
  rw [Finset.sum_boole]
  simp only [Nat.cast_id]

/-- A packaged binary-coordinate linear code with a checked near-Plotkin
pairwise-agreement bound. -/
structure NearPlotkinCode (p m : ℕ) [Fact p.Prime] (τ : ℝ) where
  ell : ℕ
  encoder : (Fin m → ZMod p) →ₗ[ZMod p]
    (BinaryCoord ell → ZMod p)
  injective : Function.Injective encoder
  pairAgreement : ∀ x y, x ≠ y →
    agreement (encoder x) (encoder y) ≤ 1 / p + τ
  length_lt : (2 ^ ell : ℝ) <
    (m + 1 : ℝ) * Real.log p / τ ^ 2 + 4

theorem exists_nearPlotkinCode
    (p m : ℕ) [Fact p.Prime] (τ : ℝ) (hτ : 0 < τ)
    (hsmall : 1 / (p : ℝ) + τ < 1) :
    Nonempty (NearPlotkinCode p m τ) := by
  classical
  obtain ⟨ell, T, hT, hlength⟩ := exists_binary_rows_nearPlotkin p m τ hτ
  let E := binaryRowEncoder p m ell T
  have hpair : ∀ x y, x ≠ y →
      agreement (E x) (E y) ≤ 1 / p + τ := by
    intro x y hxy
    have hsub : x - y ≠ 0 := sub_ne_zero.mpr hxy
    rw [agreement, ← sum_rowZeroIndicator_sub_eq_agreementCount T x y]
    have hN : (0 : ℝ) < Fintype.card (BinaryCoord ell) := by positivity
    apply (div_le_iff₀ hN).2
    simpa [BinaryCoord, mul_comm] using hT (x - y) hsub
  have hinj : Function.Injective E := by
    intro x y hE
    by_contra hxy
    have hb := hpair x y hxy
    rw [hE, agreement_self] at hb
    exact (not_le_of_gt hsmall hb).elim
  exact ⟨⟨ell, E, hinj, hpair, hlength⟩⟩

/-- Inputs whose codeword has agreement strictly above `1/p + η` with a
received word. -/
noncomputable def codeAgreementList {p m ell : ℕ} [Fact p.Prime]
    (E : (Fin m → ZMod p) →ₗ[ZMod p] (BinaryCoord ell → ZMod p))
    (Q : BinaryCoord ell → ZMod p) (η : ℝ) :
    Finset (Fin m → ZMod p) := by
  classical
  exact Finset.univ.filter fun x ↦ 1 / (p : ℝ) + η < agreement (E x) Q

/-- The regular-simplex calculation: a near-Plotkin pairwise-agreement
bound implies a uniform agreement-list bound. -/
theorem card_codeAgreementList_lt
    {p m ell : ℕ} [Fact p.Prime]
    (E : (Fin m → ZMod p) →ₗ[ZMod p] (BinaryCoord ell → ZMod p))
    (Q : BinaryCoord ell → ZMod p) (η τ : ℝ)
    (hη : 0 < η)
    (hτ : τ = (p : ℝ) * η ^ 2 / (2 * ((p : ℝ) - 1)))
    (hpair : ∀ x y, x ≠ y →
      agreement (E x) (E y) ≤ 1 / (p : ℝ) + τ) :
    ((codeAgreementList E Q η).card : ℝ) < 2 / η ^ 2 + 1 := by
  classical
  let L := codeAgreementList E Q η
  apply card_lt_two_div_sq_add_one_of_pairwise_agreement
    η τ hη hτ L (fun x ↦ E x) Q
  · intro x _hx y _hy hxy
    exact hpair x y hxy
  · intro x hx
    exact (Finset.mem_filter.mp hx).2

/-- The complete short-code object used by reconstruction. -/
structure ShortLinearCode (p m : ℕ) [Fact p.Prime] (η : ℝ) where
  ell : ℕ
  encoder : (Fin m → ZMod p) →ₗ[ZMod p]
    (BinaryCoord ell → ZMod p)
  injective : Function.Injective encoder
  listBound : ∀ Q : BinaryCoord ell → ZMod p,
    ((codeAgreementList encoder Q η).card : ℝ) < 2 / η ^ 2 + 1
  length_lt : (2 ^ ell : ℝ) <
    9 * m * Real.log p / η ^ 4

/-- Short binary-coordinate linear list-decodable code.  This is the exact
finite existence statement needed in reconstruction: every received word
has fewer than `2/η²` messages above agreement `1/p+η`, and the block
length is at most an absolute constant times `m log(p)/η⁴`. -/
theorem exists_shortLinearCode
    (p m : ℕ) [Fact p.Prime] (hm : 1 ≤ m)
    (η : ℝ) (hη : 0 < η) (hηhalf : η < 1 / 2) :
    Nonempty (ShortLinearCode p m η) := by
  have hpNat : 1 < p := (Fact.out : p.Prime).one_lt
  have hp : (1 : ℝ) < p := by exact_mod_cast hpNat
  have hp0 : (0 : ℝ) < p := hp.trans' zero_lt_one
  have hp1 : (0 : ℝ) < p - 1 := sub_pos.mpr hp
  let τ : ℝ := (p : ℝ) * η ^ 2 / (2 * (p - 1))
  have hτ : 0 < τ := by
    dsimp [τ]
    positivity
  have hpRatio : (p : ℝ) / ((p : ℝ) - 1) ≤ 2 := by
    apply (div_le_iff₀ hp1).2
    have hp2Nat : 2 ≤ p := by omega
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp2Nat
    nlinarith
  have hηsq : η ^ 2 < 1 / 4 := by
    have hs := (sq_lt_sq₀ hη.le
      (by norm_num : (0 : ℝ) ≤ 1 / 2)).2 hηhalf
    norm_num at hs ⊢
    exact hs
  have hτquarter : τ < 1 / 4 := by
    calc
      τ = ((p : ℝ) / ((p : ℝ) - 1)) * η ^ 2 / 2 := by
        dsimp [τ]
        field_simp
      _ ≤ 2 * η ^ 2 / 2 := by gcongr
      _ = η ^ 2 := by ring
      _ < 1 / 4 := hηsq
  have hinvp : (p : ℝ)⁻¹ ≤ 1 / 2 := by
    simpa [one_div] using
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
        (by
          have hp2Nat : 2 ≤ p := by omega
          exact_mod_cast hp2Nat))
  have hsmall : 1 / (p : ℝ) + τ < 1 := by
    rw [one_div]
    nlinarith
  obtain ⟨C⟩ := exists_nearPlotkinCode p m τ hτ hsmall
  have hlist (Q : BinaryCoord C.ell → ZMod p) :
      ((codeAgreementList C.encoder Q η).card : ℝ) < 2 / η ^ 2 + 1 := by
    apply card_codeAgreementList_lt C.encoder Q η τ hη rfl
    exact C.pairAgreement
  have hlogLower : (1 / 2 : ℝ) ≤ Real.log p := by
    have hlog := Real.one_sub_inv_le_log_of_pos hp0
    nlinarith
  have hηfour : η ^ 4 < 1 / 16 := by
    have hsquare : (η ^ 2) ^ 2 < (1 / 4 : ℝ) ^ 2 :=
      (sq_lt_sq₀ (sq_nonneg η) (by norm_num : (0 : ℝ) ≤ 1 / 4)).2 hηsq
    nlinarith
  have heta4pos : 0 < η ^ 4 := by positivity
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hfour : (4 : ℝ) ≤ (m : ℝ) * Real.log p / η ^ 4 := by
    apply (le_div_iff₀ heta4pos).2
    have hmLog : (1 / 2 : ℝ) ≤ (m : ℝ) * Real.log p := by
      calc
        (1 / 2 : ℝ) = 1 * (1 / 2) := by ring
        _ ≤ (m : ℝ) * Real.log p :=
          mul_le_mul hmR hlogLower (by norm_num) (by positivity)
    nlinarith
  have htauSq : τ ^ 2 =
      (p : ℝ) ^ 2 * η ^ 4 / (4 * (p - 1) ^ 2) := by
    dsimp [τ]
    field_simp
    ring
  have hbase :
      (m + 1 : ℝ) * Real.log p / τ ^ 2 ≤
        8 * m * Real.log p / η ^ 4 := by
    have hm2 : (m + 1 : ℝ) ≤ 2 * m := by
      exact_mod_cast (show m + 1 ≤ 2 * m by omega)
    have hsquares : ((p : ℝ) - 1) ^ 2 ≤ p ^ 2 := by nlinarith
    rw [htauSq]
    have hpSq : 0 < (p : ℝ) ^ 2 := by positivity
    have hp1Sq : 0 < ((p : ℝ) - 1) ^ 2 := by positivity
    have hlogpos : 0 < Real.log (p : ℝ) := Real.log_pos hp
    field_simp
    nlinarith [mul_le_mul_of_nonneg_left hsquares (by positivity :
      (0 : ℝ) ≤ 2 * m * Real.log p)]
  have hlength : (2 ^ C.ell : ℝ) <
      9 * m * Real.log p / η ^ 4 := by
    calc
      (2 ^ C.ell : ℝ) <
          (m + 1 : ℝ) * Real.log p / τ ^ 2 + 4 := C.length_lt
      _ ≤ 8 * m * Real.log p / η ^ 4 +
          m * Real.log p / η ^ 4 := add_le_add hbase hfour
      _ = 9 * m * Real.log p / η ^ 4 := by ring
  exact ⟨⟨C.ell, C.encoder, C.injective, hlist, hlength⟩⟩

end Erdos788


/-! Flattened from Erdos788.CodeLengthBounds. -/


/-!
# Explicit logarithmic bound for the short-code coordinate length
-/

namespace Erdos788

/-- At the reconstruction value `η = 1/(40pr)`, the binary coordinate length
is at most an explicit constant times `log(pr)`. -/
theorem shortLinearCode_ell_lt_log_mul
    {p r : ℕ} [Fact p.Prime]
    (hp : 2 < p) (hr : 0 < r)
    (C : ShortLinearCode p (2 * r) (trevisanEta p r)) :
    (C.ell : ℝ) < 100 * Real.log ((p * r : ℕ) : ℝ) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hr1R : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hpR
  have heta :
      9 * (2 * r : ℝ) * Real.log p / trevisanEta p r ^ 4 =
        46080000 * (p : ℝ) ^ 4 * (r : ℝ) ^ 5 * Real.log p := by
    rw [trevisanEta]
    field_simp
    ring
  have hlength : (2 ^ C.ell : ℝ) <
      50000000 * (p : ℝ) ^ 4 * (r : ℝ) ^ 5 * Real.log p := by
    calc
      (2 ^ C.ell : ℝ) <
          9 * (2 * r : ℝ) * Real.log p / trevisanEta p r ^ 4 := by
            simpa only [Nat.cast_mul, Nat.cast_ofNat] using C.length_lt
      _ = 46080000 * (p : ℝ) ^ 4 * (r : ℝ) ^ 5 * Real.log p := heta
      _ ≤ 50000000 * (p : ℝ) ^ 4 * (r : ℝ) ^ 5 * Real.log p := by
        have : 0 ≤ (p : ℝ) ^ 4 * (r : ℝ) ^ 5 * Real.log p := by positivity
        nlinarith
  have hlog := Real.log_lt_log
    (by positivity : (0 : ℝ) < (2 : ℝ) ^ C.ell) hlength
  have hlogExpand :
      Real.log
          (50000000 * (p : ℝ) ^ 4 * (r : ℝ) ^ 5 * Real.log p) =
        Real.log 50000000 + 4 * Real.log p +
          5 * Real.log r + Real.log (Real.log p) := by
    calc
      Real.log
          (((50000000 : ℝ) * p ^ 4 * r ^ 5) * Real.log p) =
          Real.log ((50000000 : ℝ) * p ^ 4 * r ^ 5) +
            Real.log (Real.log p) := by
              rw [Real.log_mul (by positivity) (by positivity)]
      _ = (Real.log ((50000000 : ℝ) * p ^ 4) + Real.log (r ^ 5)) +
            Real.log (Real.log p) := by
              rw [Real.log_mul (by positivity) (by positivity)]
      _ = ((Real.log 50000000 + Real.log (p ^ 4)) + Real.log (r ^ 5)) +
            Real.log (Real.log p) := by
              rw [Real.log_mul (by positivity) (by positivity)]
      _ = Real.log 50000000 + 4 * Real.log p +
          5 * Real.log r + Real.log (Real.log p) := by
            rw [Real.log_pow, Real.log_pow]
            ring
  rw [Real.log_pow, hlogExpand] at hlog
  have hconstNat : 50000000 ≤ 2 ^ 26 := by norm_num
  have hconstR : (50000000 : ℝ) ≤ (2 : ℝ) ^ 26 := by
    exact_mod_cast hconstNat
  have hconst : Real.log 50000000 ≤ 26 * Real.log 2 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 50000000) hconstR
    simpa [Real.log_pow] using h
  have hp_le_pr : p ≤ p * r := by
    simpa [mul_comm] using Nat.mul_le_mul_left p (show 1 ≤ r by omega)
  have hr_le_pr : r ≤ p * r := by
    exact Nat.le_mul_of_pos_left r (show 0 < p by omega)
  have hlogp_le : Real.log (p : ℝ) ≤ Real.log (p * r : ℕ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hp_le_pr
  have hlogr_le : Real.log (r : ℝ) ≤ Real.log (p * r : ℕ) := by
    apply Real.log_le_log hrR
    exact_mod_cast hr_le_pr
  have hloglogp_le : Real.log (Real.log p) ≤ Real.log p := by
    have h := Real.log_le_sub_one_of_pos hlogp
    linarith
  have htwo_le_pr : 2 ≤ p * r := by
    have : 3 ≤ p := by omega
    nlinarith [show 1 ≤ r by omega]
  have hlogtwo_le : Real.log 2 ≤ Real.log (p * r : ℕ) := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast htwo_le_pr
  have hlogpr : 0 ≤ Real.log (p * r : ℕ) :=
    (Real.log_pos (by exact_mod_cast (show 1 < p * r by omega))).le
  have h36 :
      Real.log 50000000 + 4 * Real.log p +
          5 * Real.log r + Real.log (Real.log p) ≤
        36 * Real.log (p * r : ℕ) := by
    nlinarith
  have hell36 : (C.ell : ℝ) * Real.log 2 <
      36 * Real.log (p * r : ℕ) := hlog.trans_le h36
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcoef : (36 : ℝ) ≤ 100 * Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hell100 : (C.ell : ℝ) * Real.log 2 <
      Real.log 2 * (100 * Real.log (p * r : ℕ)) := by
    calc
      (C.ell : ℝ) * Real.log 2 < 36 * Real.log (p * r : ℕ) := hell36
      _ ≤ Real.log 2 * (100 * Real.log (p * r : ℕ)) := by
        nlinarith
  nlinarith

end Erdos788


/-! Flattened from Erdos788.DesignLengthBounds. -/


/-!
# Explicit analytic size bound for the suffix-slack design
-/

namespace Erdos788

private theorem designTail_log_factor_le
    {ell : ℕ} {u : ℝ} (hu : 1 ≤ u)
    (hell : (ell : ℝ) ≤ 100 * u) :
    ((Nat.log 2 (SuffixDesign.designTailScale ell) + 1 : ℕ) : ℝ) ≤
      19 + 4 * Real.log u := by
  have hu0 : 0 < u := zero_lt_one.trans_le hu
  have hlogu : 0 ≤ Real.log u := Real.log_nonneg hu
  have hell3 : (ell + 3 : ℕ) ≤ (103 : ℝ) * u := by
    push_cast
    nlinarith
  have hlogell : Real.log (ell + 3 : ℕ) ≤ Real.log (103 * u) := by
    apply Real.log_le_log (by positivity)
    exact hell3
  have hlog103 : Real.log 103 ≤ 7 * Real.log 2 := by
    have hnat : (103 : ℕ) ≤ 2 ^ 7 := by norm_num
    have hreal : (103 : ℝ) ≤ (2 : ℝ) ^ 7 := by exact_mod_cast hnat
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 103) hreal
    simpa [Real.log_pow] using h
  have hlogell' : Real.log (ell + 3 : ℕ) ≤
      7 * Real.log 2 + Real.log u := by
    rw [Real.log_mul (by norm_num : (103 : ℝ) ≠ 0) (ne_of_gt hu0)] at hlogell
    linarith
  have hscale :
      Real.log (SuffixDesign.designTailScale ell : ℕ) ≤
        18 * Real.log 2 + 2 * Real.log u := by
    rw [SuffixDesign.designTailScale]
    have hexpand : Real.log ((16 * (ell + 3) ^ 2 : ℕ) : ℝ) =
        4 * Real.log 2 + 2 * Real.log (ell + 3 : ℕ) := by
      push_cast
      rw [Real.log_mul (by norm_num : (16 : ℝ) ≠ 0) (by positivity),
        show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow, Real.log_pow]
      ring
    rw [hexpand]
    nlinarith
  have hnat := Real.natLog_le_logb (SuffixDesign.designTailScale ell) 2
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hquot : Real.log (SuffixDesign.designTailScale ell : ℕ) /
      Real.log 2 ≤ 18 + 4 * Real.log u := by
    apply (div_le_iff₀ hlogtwo).2
    nlinarith [Real.log_two_gt_d9]
  rw [Real.logb] at hnat
  have hmain : (Nat.log 2 (SuffixDesign.designTailScale ell) : ℝ) ≤
      18 + 4 * Real.log u := hnat.trans hquot
  push_cast
  linarith

/-- Combining the short-code estimate with the strong recursive design
bound gives the two terms used in the paper's parameter calculation. -/
theorem builtDesign_coordCard_le_log_bound
    {p r : ℕ} [Fact p.Prime]
    (hp : 2 < p) (hr : 0 < r)
    (C : ShortLinearCode p (2 * r) (trevisanEta p r)) :
    (((SuffixDesign.build C.ell r).coordCard : ℕ) : ℝ) ≤
      1000 * Real.log ((p * r : ℕ) : ℝ) * Real.sqrt r +
        2000000 * Real.log ((p * r : ℕ) : ℝ) ^ 2 *
          (1 + Real.log (Real.log ((p * r : ℕ) : ℝ))) := by
  let u : ℝ := Real.log ((p * r : ℕ) : ℝ)
  have hpr : 3 ≤ p * r := by
    have hp3 : 3 ≤ p := by omega
    have hr1 : 1 ≤ r := by omega
    simpa using Nat.mul_le_mul hp3 hr1
  have hu : 1 ≤ u := by
    dsimp [u]
    exact ((Real.lt_log_iff_exp_lt
      (by positivity : (0 : ℝ) < (p * r : ℕ))).2
        (Real.exp_one_lt_three.trans_le (by exact_mod_cast hpr))).le
  have hu0 : 0 < u := zero_lt_one.trans_le hu
  have hlogu : 0 ≤ Real.log u := Real.log_nonneg hu
  have hell : (C.ell : ℝ) ≤ 100 * u :=
    (shortLinearCode_ell_lt_log_mul hp hr C).le
  have hell3 : (C.ell : ℝ) + 3 ≤ 103 * u := by nlinarith
  have htail := designTail_log_factor_le hu hell
  have hD := SuffixDesign.build_coordCard_le_designStrongBound C.ell r
  rw [SuffixDesign.designStrongBound] at hD
  have hsqrt : 0 ≤ Real.sqrt (r : ℝ) := Real.sqrt_nonneg _
  have hfirst : 10 * (C.ell : ℝ) * Real.sqrt r ≤
      1000 * u * Real.sqrt r := by
    exact mul_le_mul_of_nonneg_right
      (by nlinarith : 10 * (C.ell : ℝ) ≤ 1000 * u) hsqrt
  have hpair : (C.ell : ℝ) * (C.ell + 3) ≤ 10300 * u ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ (C.ell : ℝ) by positivity)
      (show 0 ≤ (C.ell : ℝ) + 3 by positivity)]
  have htail0 : 0 ≤
      ((Nat.log 2 (SuffixDesign.designTailScale C.ell) + 1 : ℕ) : ℝ) := by
    exact_mod_cast
      (Nat.zero_le (Nat.log 2 (SuffixDesign.designTailScale C.ell) + 1))
  have htailUpper0 : 0 ≤ 19 + 4 * Real.log u := by linarith
  have hsecondRaw :
      (C.ell : ℝ) * (C.ell + 3) *
          ((Nat.log 2 (SuffixDesign.designTailScale C.ell) + 1 : ℕ) : ℝ) ≤
        (10300 * u ^ 2) * (19 + 4 * Real.log u) :=
    mul_le_mul hpair htail htail0 (by positivity)
  have hsecond :
      10 * (C.ell : ℝ) * (C.ell + 3) *
          ((Nat.log 2 (SuffixDesign.designTailScale C.ell) + 1 : ℕ) : ℝ) ≤
        2000000 * u ^ 2 * (1 + Real.log u) := by
    have hscaled := mul_le_mul_of_nonneg_left hsecondRaw (by norm_num : (0 : ℝ) ≤ 10)
    have hcoef : 103000 * (19 + 4 * Real.log u) ≤
        2000000 * (1 + Real.log u) := by linarith
    calc
      10 * (C.ell : ℝ) * (C.ell + 3) *
          ((Nat.log 2 (SuffixDesign.designTailScale C.ell) + 1 : ℕ) : ℝ) =
          10 * ((C.ell : ℝ) * (C.ell + 3) *
            ((Nat.log 2 (SuffixDesign.designTailScale C.ell) + 1 : ℕ) : ℝ)) := by ring
      _ ≤ 10 * ((10300 * u ^ 2) * (19 + 4 * Real.log u)) := hscaled
      _ = u ^ 2 * (103000 * (19 + 4 * Real.log u)) := by ring
      _ ≤ u ^ 2 * (2000000 * (1 + Real.log u)) :=
        mul_le_mul_of_nonneg_left hcoef (sq_nonneg u)
      _ = 2000000 * u ^ 2 * (1 + Real.log u) := by ring
  push_cast at hsecond
  change ((SuffixDesign.build C.ell r).coordCard : ℝ) ≤ _
  change _ ≤ 1000 * u * Real.sqrt r +
    2000000 * u ^ 2 * (1 + Real.log u)
  exact hD.trans (add_le_add hfirst hsecond)

end Erdos788


/-! Flattened from Erdos788.ChosenParameterBounds. -/


/-!
# Pointwise bounds for the chosen field and dimension

The hypotheses in `ParameterRegular` are elementary eventual inequalities.
They are separated from the finite construction so the final asymptotic
argument only has to establish them once.
-/

namespace Erdos788

def ParameterRegular (N : ℕ) : Prop :=
  0 < Real.log (N : ℝ) ∧
  2 ≤ Real.log (Real.log (N : ℝ)) ∧
  exponentCorrection N *
      (Real.log (Real.log (N : ℝ)) + Real.log 4) ≤ 1 ∧
  400000000 * exponentCorrection N ≤ 1

theorem parameterRegular_correction_pos {N : ℕ} (h : ParameterRegular N) :
    0 < exponentCorrection N :=
  exponentCorrection_pos h.1 (by linarith [h.2])

theorem parameterRegular_correction_le_one {N : ℕ} (h : ParameterRegular N) :
    exponentCorrection N ≤ 1 := by
  have hδ := parameterRegular_correction_pos h
  nlinarith [h.2.2.2]

theorem parameterRegular_log_mul_correction {N : ℕ}
    (h : ParameterRegular N) :
    2 ≤ Real.log (N : ℝ) * exponentCorrection N := by
  let L := Real.log (N : ℝ)
  let q := Real.log L
  let δ := exponentCorrection N
  have hL : 0 < L := h.1
  have hq : 2 ≤ q := h.2.1
  have hδ : 0 < δ := parameterRegular_correction_pos h
  have hδ1 : δ ≤ 1 := parameterRegular_correction_le_one h
  have hcube : δ ^ 3 = q / L := by
    simpa [L, q, δ] using
      exponentCorrection_pow_three h.1 (by linarith [h.2.1])
  have hrel : L * δ ^ 3 = q := by
    rw [hcube]
    field_simp
  have hcubed_le : δ ^ 3 ≤ δ := by
    nlinarith [sq_nonneg δ]
  dsimp only [L, δ] at hL hδ hδ1 hrel hcubed_le ⊢
  nlinarith

theorem parameterDimension_le_log_mul_correction {N : ℕ}
    (h : ParameterRegular N) :
    ((parameterDimension N : ℕ) : ℝ) ≤
      Real.log (N : ℝ) * exponentCorrection N := by
  have hδ := parameterRegular_correction_pos h
  have hA := parameterRegular_log_mul_correction h
  have hnR : (1 : ℝ) < N :=
    (Real.log_pos_iff (by positivity : (0 : ℝ) ≤ N)).mp h.1
  have hn : 1 < N := by exact_mod_cast hnR
  have hrUpper := cast_parameterDimension_lt_log_div_add_one hn.le
  have hinv := one_div_log_parameterPrime_lt_correction h.1
    (by linarith [h.2.1])
  have hfrac : Real.log (N : ℝ) /
      (2 * Real.log (parameterPrime N)) <
        Real.log (N : ℝ) * exponentCorrection N / 2 := by
    have hhalf : 0 < Real.log (N : ℝ) / 2 :=
      div_pos h.1 (by norm_num)
    calc
      Real.log (N : ℝ) / (2 * Real.log (parameterPrime N)) =
          (Real.log (N : ℝ) / 2) *
            (1 / Real.log (parameterPrime N)) := by ring
      _ < (Real.log (N : ℝ) / 2) * exponentCorrection N :=
        mul_lt_mul_of_pos_left hinv hhalf
      _ = Real.log (N : ℝ) * exponentCorrection N / 2 := by ring
  linarith

theorem parameterDimension_le_log {N : ℕ} (h : ParameterRegular N) :
    ((parameterDimension N : ℕ) : ℝ) ≤ Real.log (N : ℝ) := by
  have hδ1 := parameterRegular_correction_le_one h
  have hr := parameterDimension_le_log_mul_correction h
  exact hr.trans (by
    calc
      Real.log (N : ℝ) * exponentCorrection N ≤
          Real.log (N : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hδ1 h.1.le
      _ = Real.log (N : ℝ) := by ring)

theorem log_parameterProduct_le_two_logPrime {N : ℕ}
    (h : ParameterRegular N) :
    Real.log ((parameterPrime N * parameterDimension N : ℕ) : ℝ) ≤
      2 * Real.log (parameterPrime N) := by
  have hδ := parameterRegular_correction_pos h
  have hnR : (1 : ℝ) < N :=
    (Real.log_pos_iff (by positivity : (0 : ℝ) ≤ N)).mp h.1
  have hn : 1 < N := by exact_mod_cast hnR
  have hrNat : 0 < parameterDimension N := parameterDimension_pos hn
  have hrR : (0 : ℝ) < parameterDimension N := by exact_mod_cast hrNat
  have hlogr : Real.log (parameterDimension N : ℝ) ≤
      Real.log (Real.log (N : ℝ)) := by
    apply Real.log_le_log hrR
    exact parameterDimension_le_log h
  have hqP := loglog_le_log_parameterPrime N
  have hpR : (0 : ℝ) < parameterPrime N := by
    exact_mod_cast (Nat.zero_lt_of_lt (two_lt_parameterPrime N))
  rw [Nat.cast_mul, Real.log_mul hpR.ne' hrR.ne']
  linarith

theorem log_parameterProduct_le_four_div_correction {N : ℕ}
    (h : ParameterRegular N) :
    Real.log ((parameterPrime N * parameterDimension N : ℕ) : ℝ) ≤
      4 / exponentCorrection N := by
  have hpLog := log_parameterPrime_le_two_div_correction h.1
    (by linarith [h.2.1]) h.2.2.1
  have htwice : 2 * Real.log (parameterPrime N) ≤
      4 / exponentCorrection N := by
    have := mul_le_mul_of_nonneg_left hpLog (by norm_num : (0 : ℝ) ≤ 2)
    calc
      2 * Real.log (parameterPrime N) ≤
          2 * (2 / exponentCorrection N) := this
      _ = 4 / exponentCorrection N := by ring
  exact (log_parameterProduct_le_two_logPrime h).trans htwice

/-- The strong design size is at most an explicit multiple of
`log N * exponentCorrection N`. -/
theorem chosenDesign_coordCard_le
    {N : ℕ} (h : ParameterRegular N)
    (C : ShortLinearCode (parameterPrime N) (2 * parameterDimension N)
      (trevisanEta (parameterPrime N) (parameterDimension N))) :
    (((SuffixDesign.build C.ell (parameterDimension N)).coordCard : ℕ) : ℝ) ≤
      100000000 * Real.log (N : ℝ) * exponentCorrection N := by
  let L := Real.log (N : ℝ)
  let q := Real.log L
  let δ := exponentCorrection N
  let r := parameterDimension N
  let u := Real.log ((parameterPrime N * r : ℕ) : ℝ)
  have hL : 0 < L := h.1
  have hq : 2 ≤ q := h.2.1
  have hδ : 0 < δ := parameterRegular_correction_pos h
  have hδ1 : δ ≤ 1 := parameterRegular_correction_le_one h
  have hr : (r : ℝ) ≤ L * δ := by
    simpa [L, δ, r] using parameterDimension_le_log_mul_correction h
  have hr0Nat : 0 < r := by
    apply parameterDimension_pos
    have hnR : (1 : ℝ) < N :=
      (Real.log_pos_iff (by positivity : (0 : ℝ) ≤ N)).mp h.1
    exact_mod_cast hnR
  have hu : u ≤ 4 / δ := by
    simpa [u, δ, r] using log_parameterProduct_le_four_div_correction h
  have hu1 : 1 ≤ u := by
    have hp3 : 3 ≤ parameterPrime N := by
      exact_mod_cast (two_lt_parameterPrime N)
    have hprod : 3 ≤ parameterPrime N * r := by
      simpa using Nat.mul_le_mul hp3 (show 1 ≤ r by omega)
    dsimp [u]
    exact ((Real.lt_log_iff_exp_lt (by positivity)).2
      (Real.exp_one_lt_three.trans_le (by exact_mod_cast hprod))).le
  have hlogu : Real.log u ≤ q + Real.log 4 := by
    have hinvδL : δ⁻¹ ≤ L := by
      have hA := parameterRegular_log_mul_correction h
      have hone : (1 : ℝ) ≤ Real.log (N : ℝ) * exponentCorrection N :=
        (by norm_num : (1 : ℝ) ≤ 2).trans hA
      have hdiv : 1 / δ ≤ L := (div_le_iff₀ hδ).2 (by
        simpa [L, δ, mul_comm] using hone)
      simpa [one_div] using hdiv
    have hu4L : u ≤ 4 * L := by
      rw [div_eq_mul_inv] at hu
      nlinarith
    have hlog := Real.log_le_log (zero_lt_one.trans_le hu1) hu4L
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (ne_of_gt hL)] at hlog
    simpa [q, add_comm] using hlog
  have hcube : δ ^ 3 = q / L := by
    simpa [L, q, δ] using
      exponentCorrection_pow_three h.1 (by linarith [h.2.1])
  have hrel : L * δ ^ 3 = q := by
    rw [hcube]
    field_simp
  let A := L * δ
  have hA0 : 0 < A := mul_pos hL hδ
  have hqAδ : q = A * δ ^ 2 := by
    dsimp [A]
    rw [hrel.symm]
    ring
  have hsqrtA : Real.sqrt A ≤ A * δ := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · calc
        A ≤ A * q :=
          by simpa using
            (mul_le_mul_of_nonneg_left
              (by linarith : (1 : ℝ) ≤ q) hA0.le)
        _ = (A * δ) ^ 2 := by rw [hqAδ]; ring
  have hinvSqrt : δ⁻¹ * Real.sqrt A ≤ A := by
    calc
      δ⁻¹ * Real.sqrt A ≤ δ⁻¹ * (A * δ) :=
        mul_le_mul_of_nonneg_left hsqrtA (inv_nonneg.mpr hδ.le)
      _ = A := by field_simp
  have hsqrtr : Real.sqrt (r : ℝ) ≤ Real.sqrt A :=
    Real.sqrt_le_sqrt (by simpa [A] using hr)
  have hfirst : 1000 * u * Real.sqrt (r : ℝ) ≤ 4000 * A := by
    have hu' : u ≤ 4 * δ⁻¹ := by simpa [div_eq_mul_inv] using hu
    calc
      1000 * u * Real.sqrt (r : ℝ) ≤
          1000 * (4 * δ⁻¹) * Real.sqrt A := by gcongr
      _ = 4000 * (δ⁻¹ * Real.sqrt A) := by ring
      _ ≤ 4000 * A := by gcongr
  have hlog4 : Real.log 4 ≤ 2 := by
    have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
      have hraw :=
        Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at hraw
      exact hraw
    calc
      Real.log (4 : ℝ) = 2 * Real.log (2 : ℝ) := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        norm_num
      _ ≤ 2 * 1 := mul_le_mul_of_nonneg_left hlog2 (by norm_num)
      _ = 2 := by norm_num
  have hfactor : 1 + Real.log u ≤ (5 / 2 : ℝ) * q := by
    nlinarith
  have hinvSqFactor : δ⁻¹ ^ 2 * (1 + Real.log u) ≤
      (5 / 2 : ℝ) * A := by
    have hidentity : δ⁻¹ ^ 2 * q = A := by
      rw [hqAδ]
      field_simp
    calc
      δ⁻¹ ^ 2 * (1 + Real.log u) ≤
          δ⁻¹ ^ 2 * ((5 / 2 : ℝ) * q) :=
        mul_le_mul_of_nonneg_left hfactor (sq_nonneg _)
      _ = (5 / 2 : ℝ) * A := by rw [← hidentity]; ring
  have hsecond : 2000000 * u ^ 2 * (1 + Real.log u) ≤
      80000000 * A := by
    have huSq : u ^ 2 ≤ (4 * δ⁻¹) ^ 2 := by
      gcongr
      simpa [div_eq_mul_inv] using hu
    have hfactor0 : 0 ≤ 1 + Real.log u := by
      have := Real.log_nonneg hu1
      linarith
    calc
      2000000 * u ^ 2 * (1 + Real.log u) ≤
          2000000 * (4 * δ⁻¹) ^ 2 * (1 + Real.log u) := by
        gcongr
      _ = 32000000 * (δ⁻¹ ^ 2 * (1 + Real.log u)) := by ring
      _ ≤ 32000000 * ((5 / 2 : ℝ) * A) := by gcongr
      _ = 80000000 * A := by ring
  have hdesign := builtDesign_coordCard_le_log_bound
    (two_lt_parameterPrime N) hr0Nat C
  have hdesign' : (((SuffixDesign.build C.ell r).coordCard : ℕ) : ℝ) ≤
      1000 * u * Real.sqrt (r : ℝ) +
        2000000 * u ^ 2 * (1 + Real.log u) := by
    simpa [u, r] using hdesign
  calc
    (((SuffixDesign.build C.ell (parameterDimension N)).coordCard : ℕ) : ℝ) ≤
        1000 * u * Real.sqrt (r : ℝ) +
          2000000 * u ^ 2 * (1 + Real.log u) := by
      simpa [r] using hdesign'
    _ ≤ 100000000 * A := by linarith
    _ = 100000000 * Real.log (N : ℝ) * exponentCorrection N := by
      simp [A, L, δ]
      ring

end Erdos788


/-! Flattened from Erdos788.SlackCondition. -/


/-!
# A logarithmic sufficient condition for the entropy slack
-/

namespace Erdos788

theorem slackThreshold_le_monomial {p r D : ℕ} (hp : 0 < p) (hr : 0 < r) :
    trevisanSlackThreshold p r D ≤
      128040 * 2 ^ D * p ^ 2 * r ^ 3 := by
  have hpr0 : 0 < p ^ 2 * r ^ 2 := by positivity
  have hpr : 1 ≤ p ^ 2 * r ^ 2 := by omega
  have hinner : 3200 * p ^ 2 * r ^ 2 + 1 ≤
      3201 * p ^ 2 * r ^ 2 := by nlinarith
  rw [trevisanSlackThreshold]
  calc
    40 * r * 2 ^ D * (3200 * p ^ 2 * r ^ 2 + 1) ≤
        40 * r * 2 ^ D * (3201 * p ^ 2 * r ^ 2) :=
      Nat.mul_le_mul_left (40 * r * 2 ^ D) hinner
    _ = 128040 * 2 ^ D * p ^ 2 * r ^ 3 := by ring

/-- The displayed logarithmic inequality implies that all reconstruction
descriptions fit below min-entropy `r+s` with `s ≤ r`. -/
theorem slackThreshold_le_pow_of_log_bound {p r D : ℕ}
    (hp : 0 < p) (hr : 0 < r)
    (hlog : Real.log 128040 + (D : ℝ) * Real.log 2 +
        2 * Real.log p + 3 * Real.log r ≤
      (r : ℝ) * Real.log p) :
    trevisanSlackThreshold p r D ≤ p ^ r := by
  have hmonoNat := slackThreshold_le_monomial (D := D) hp hr
  have hKpos : (0 : ℝ) < trevisanSlackThreshold p r D := by
    exact_mod_cast slackThreshold_pos hr
  have hmonopos : (0 : ℝ) <
      (128040 * 2 ^ D * p ^ 2 * r ^ 3 : ℕ) := by
    positivity
  have hpowpos : (0 : ℝ) < (p ^ r : ℕ) := by positivity
  have hKmonoR : ((trevisanSlackThreshold p r D : ℕ) : ℝ) ≤
      (128040 * 2 ^ D * p ^ 2 * r ^ 3 : ℕ) := by
    exact_mod_cast hmonoNat
  have hlogKmono := Real.log_le_log hKpos hKmonoR
  have hmonoExpand :
      Real.log ((128040 * 2 ^ D * p ^ 2 * r ^ 3 : ℕ) : ℝ) =
        Real.log 128040 + (D : ℝ) * Real.log 2 +
          2 * Real.log p + 3 * Real.log r := by
    push_cast
    calc
      Real.log ((((128040 : ℝ) * 2 ^ D) * p ^ 2) * r ^ 3) =
          Real.log (((128040 : ℝ) * 2 ^ D) * p ^ 2) +
            Real.log (r ^ 3) := by rw [Real.log_mul (by positivity) (by positivity)]
      _ = (Real.log ((128040 : ℝ) * 2 ^ D) + Real.log (p ^ 2)) +
            Real.log (r ^ 3) := by rw [Real.log_mul (by positivity) (by positivity)]
      _ = ((Real.log 128040 + Real.log (2 ^ D)) + Real.log (p ^ 2)) +
            Real.log (r ^ 3) := by rw [Real.log_mul (by positivity) (by positivity)]
      _ = Real.log 128040 + (D : ℝ) * Real.log 2 +
          2 * Real.log p + 3 * Real.log r := by
            rw [Real.log_pow, Real.log_pow, Real.log_pow]
            ring
  have hpowExpand : Real.log ((p ^ r : ℕ) : ℝ) =
      (r : ℝ) * Real.log p := by
    push_cast
    rw [Real.log_pow]
  have hlogs : Real.log (trevisanSlackThreshold p r D : ℕ) ≤
      Real.log (p ^ r : ℕ) := by
    calc
      Real.log (trevisanSlackThreshold p r D : ℕ) ≤
          Real.log (128040 * 2 ^ D * p ^ 2 * r ^ 3 : ℕ) := hlogKmono
      _ = Real.log 128040 + (D : ℝ) * Real.log 2 +
          2 * Real.log p + 3 * Real.log r := hmonoExpand
      _ ≤ (r : ℝ) * Real.log p := hlog
      _ = Real.log (p ^ r : ℕ) := hpowExpand.symm
  have hreal := (Real.log_le_log_iff hKpos hpowpos).mp hlogs
  exact_mod_cast hreal

theorem slackExponent_le_of_log_bound {p r D : ℕ}
    (hp : 1 < p) (hr : 0 < r)
    (hlog : Real.log 128040 + (D : ℝ) * Real.log 2 +
        2 * Real.log p + 3 * Real.log r ≤
      (r : ℝ) * Real.log p) :
    trevisanSlackExponent p r D ≤ r := by
  rw [slackExponent_le_iff hp]
  exact slackThreshold_le_pow_of_log_bound (by omega) hr hlog

end Erdos788


/-! Flattened from Erdos788.FiniteDistribution. -/


/-!
# Elementary probability distributions on finite types

The extractor reconstruction is entirely finite.  Keeping distributions as
nonnegative real mass functions avoids measure-theoretic conditional
probability and, in particular, all zero-denominator cases.
-/

namespace Erdos788

open scoped BigOperators

/-- A probability distribution on a finite type, represented by its mass
function. -/
@[ext]
structure FinDist (α : Type*) [Fintype α] where
  mass : α → ℝ
  nonneg : ∀ a, 0 ≤ mass a
  sum_mass : ∑ a, mass a = 1

namespace FinDist

variable {α β γ : Type*}

/-- The uniform distribution on a nonempty finite type. -/
noncomputable def uniform (α : Type*) [Fintype α] [Nonempty α] :
    FinDist α where
  mass := fun _ ↦ (Fintype.card α : ℝ)⁻¹
  nonneg := fun _ ↦ inv_nonneg.mpr (Nat.cast_nonneg _)
  sum_mass := by simp

@[simp]
theorem uniform_mass [Fintype α] [Nonempty α] (a : α) :
    (uniform α).mass a = (Fintype.card α : ℝ)⁻¹ :=
  rfl

/-- The uniform distribution on a specified nonempty finset, extended by
zero outside that finset. -/
noncomputable def uniformOn [Fintype α] [DecidableEq α]
    (A : Finset α) (hA : A.Nonempty) : FinDist α where
  mass := fun a ↦ if a ∈ A then (A.card : ℝ)⁻¹ else 0
  nonneg := by
    intro a
    split_ifs
    · exact inv_nonneg.mpr (Nat.cast_nonneg _)
    · exact le_rfl
  sum_mass := by
    classical
    simp [hA.card_ne_zero]

@[simp]
theorem uniformOn_mass [Fintype α] [DecidableEq α]
    (A : Finset α) (hA : A.Nonempty) (a : α) :
    (uniformOn A hA).mass a =
      if a ∈ A then (A.card : ℝ)⁻¹ else 0 :=
  rfl

/-- Push a finite distribution forward along a function. -/
noncomputable def map [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (P : FinDist α) : FinDist β where
  mass := fun b ↦ ∑ a with f a = b, P.mass a
  nonneg := by
    intro b
    exact Finset.sum_nonneg fun _ _ ↦ P.nonneg _
  sum_mass := by
    simpa [Finset.sum_fiberwise_eq_sum_filter Finset.univ Finset.univ f P.mass]
      using P.sum_mass

@[simp]
theorem map_mass [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (P : FinDist α) (b : β) :
    (P.map f).mass b = ∑ a with f a = b, P.mass a :=
  rfl

/-- Total variation distance, written as half the finite `L¹` distance. -/
noncomputable def tv [Fintype α] (P Q : FinDist α) : ℝ :=
  (1 / 2 : ℝ) * ∑ a, |P.mass a - Q.mass a|

theorem tv_nonneg [Fintype α] (P Q : FinDist α) :
    0 ≤ P.tv Q := by
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)

@[simp]
theorem tv_self [Fintype α] (P : FinDist α) : P.tv P = 0 := by
  simp [tv]

theorem tv_symm [Fintype α] (P Q : FinDist α) : P.tv Q = Q.tv P := by
  unfold tv
  congr 1
  apply Finset.sum_congr rfl
  intro a _ha
  exact abs_sub_comm _ _

theorem tv_triangle [Fintype α] (P Q R : FinDist α) :
    P.tv R ≤ P.tv Q + Q.tv R := by
  have hpoint : ∀ a : α,
      |P.mass a - R.mass a| ≤
        |P.mass a - Q.mass a| + |Q.mass a - R.mass a| := by
    intro a
    exact abs_sub_le _ _ _
  have hsum := Finset.sum_le_sum fun a (_ha : a ∈ (Finset.univ : Finset α)) ↦
    hpoint a
  rw [Finset.sum_add_distrib] at hsum
  unfold tv
  nlinarith

/-- An event-probability discrepancy is bounded by total variation. -/
theorem event_gap_le_tv [Fintype α] [DecidableEq α]
    (P Q : FinDist α) (T : Finset α) :
    |(∑ x ∈ T, P.mass x) - ∑ x ∈ T, Q.mass x| ≤ P.tv Q := by
  let d : α → ℝ := fun x ↦ P.mass x - Q.mass x
  have htotal : ∑ x, d x = 0 := by
    simp only [d, Finset.sum_sub_distrib, P.sum_mass, Q.sum_mass, sub_self]
  have hcomp : ∑ x ∈ (Finset.univ \ T), d x = -(∑ x ∈ T, d x) := by
    rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ T), htotal, zero_sub]
  have hsplitAbs :
      (∑ x, |d x|) =
        (∑ x ∈ (Finset.univ \ T), |d x|) + ∑ x ∈ T, |d x| := by
    rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ T)]
    ring
  have hT : |∑ x ∈ T, d x| ≤ ∑ x ∈ T, |d x| :=
    Finset.abs_sum_le_sum_abs _ _
  have hTc : |∑ x ∈ (Finset.univ \ T), d x| ≤
      ∑ x ∈ (Finset.univ \ T), |d x| :=
    Finset.abs_sum_le_sum_abs _ _
  have habs : |∑ x ∈ (Finset.univ \ T), d x| = |∑ x ∈ T, d x| := by
    rw [hcomp, abs_neg]
  have hrewrite :
      (∑ x ∈ T, P.mass x) - ∑ x ∈ T, Q.mass x =
        ∑ x ∈ T, d x := by
    simp [d, Finset.sum_sub_distrib]
  rw [tv, hrewrite]
  rw [habs] at hTc
  nlinarith

/-- A distribution supported on `T` is at least `1 - |T|/|α|` away
from uniform. -/
theorem tv_uniform_ge_one_sub_support [Fintype α] [DecidableEq α]
    [Nonempty α] (P : FinDist α) (T : Finset α)
    (hsupport : ∀ x, x ∉ T → P.mass x = 0) :
    1 - (T.card : ℝ) / Fintype.card α ≤ P.tv (uniform α) := by
  have hout : ∑ x ∈ (Finset.univ \ T), P.mass x = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    exact hsupport x (Finset.mem_sdiff.mp hx).2
  have hPT : ∑ x ∈ T, P.mass x = 1 := by
    have hsplit := Finset.sum_sdiff_eq_sub
      (f := P.mass) (Finset.subset_univ T)
    rw [hout, P.sum_mass] at hsplit
    linarith
  have hcard : (T.card : ℝ) ≤ Fintype.card α := by
    exact_mod_cast Finset.card_le_univ T
  have hcardpos : (0 : ℝ) < Fintype.card α := by
    exact_mod_cast Fintype.card_pos
  have hnonneg : 0 ≤ 1 - (T.card : ℝ) / Fintype.card α := by
    rw [sub_nonneg, div_le_one hcardpos]
    exact hcard
  have hevent := event_gap_le_tv P (uniform α) T
  have hsumU : ∑ x ∈ T, (uniform α).mass x =
      (T.card : ℝ) / Fintype.card α := by
    simp [div_eq_mul_inv]
  rw [hPT, hsumU, abs_of_nonneg hnonneg] at hevent
  exact hevent

/-- A denominator-free form of a min-entropy lower bound. -/
def PointBound [Fintype α] (P : FinDist α) (K : ℕ) : Prop :=
  ∀ a, P.mass a ≤ (K : ℝ)⁻¹

theorem uniform_pointBound [Fintype α] [Nonempty α] :
    (uniform α).PointBound (Fintype.card α) := by
  intro a
  exact le_rfl

theorem uniformOn_pointBound [Fintype α] [DecidableEq α]
    (A : Finset α) (hA : A.Nonempty) :
    (uniformOn A hA).PointBound A.card := by
  intro a
  by_cases ha : a ∈ A
  · simp [uniformOn, ha]
  · simp [uniformOn, ha, inv_nonneg]

/-- A pushed-forward uniform-on-`A` distribution is supported on `f '' A`. -/
theorem map_uniformOn_mass_eq_zero_of_notMem_image
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (A : Finset α) (hA : A.Nonempty) (f : α → β) {b : β}
    (hb : b ∉ A.image f) :
    ((uniformOn A hA).map f).mass b = 0 := by
  rw [map_mass]
  apply Finset.sum_eq_zero
  intro a ha
  have hfa : f a = b := (Finset.mem_filter.mp ha).2
  have haA : a ∉ A := by
    intro haA
    exact hb (Finset.mem_image.mpr ⟨a, haA, hfa⟩)
  simp [uniformOn, haA]

theorem pointBound_mono [Fintype α] {P : FinDist α} {K L : ℕ}
    (hLpos : 0 < L) (hLK : L ≤ K) (hK : P.PointBound K) :
    P.PointBound L := by
  intro a
  refine (hK a).trans ?_
  exact inv_anti₀ (by exact_mod_cast hLpos) (by exact_mod_cast hLK)

end FinDist

end Erdos788


/-! Flattened from Erdos788.UpperGraph. -/


/-!
# Finite-field sum graphs and kernel palettes

This file isolates the exact graph-theoretic consequence needed from the
extractor construction.  The extractor will provide `SetImageExpanding`: a
large source set has a seed for which its linear image contains more than one
representative per antipodal pair.  The union of the seed kernels then has
small cardinality and forces a small independence number.
-/

namespace Erdos788

open Finset

/-- The `k`-dimensional vector space over `ZMod p`. -/
abbrev FFVec (p k : ℕ) := Fin k → ZMod p

/-- The simple sum graph generated by a finite palette in an additive group. -/
def groupSumGraph {V : Type*} [AddCommGroup V] (S : Finset V) :
    SimpleGraph V :=
  SimpleGraph.fromRel fun x y ↦ x + y ∈ S

@[simp]
theorem groupSumGraph_adj {V : Type*} [AddCommGroup V]
    {S : Finset V} {x y : V} :
    (groupSumGraph S).Adj x y ↔ x ≠ y ∧ x + y ∈ S := by
  simp [groupSumGraph, add_comm]

/-- The union of the kernels of an indexed finite family of linear maps. -/
def kernelPalette (p r : ℕ) [Fact p.Prime] {ι : Type*} [DecidableEq ι]
    (Y : Finset ι)
    (F : ι → FFVec p (2 * r) →ₗ[ZMod p] FFVec p r) :
    Finset (FFVec p (2 * r)) :=
  Y.biUnion (kernelFinset p r ∘ F)

/-- The exact set-expansion property used by the kernel-palette argument.

It is enough to prove this property for uniform distributions on source
finsets; the stronger seeded-extractor inequality in the paper implies it.
-/
def SetImageExpanding (p r s : ℕ) {ι : Type*} [DecidableEq ι]
    (Y : Finset ι)
    (F : ι → FFVec p (2 * r) →ₗ[ZMod p] FFVec p r) : Prop :=
  ∀ A : Finset (FFVec p (2 * r)), p ^ (r + s) ≤ A.card →
    ∃ y ∈ Y, p ^ r + 1 < 2 * (A.image (F y)).card

/-- In odd characteristic, the only vector equal to its negative is zero. -/
theorem eq_zero_of_eq_neg_ffVec {p r : ℕ} [Fact p.Prime] (hp : 2 < p)
    (z : FFVec p r) (hz : z = -z) : z = 0 := by
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hdiv : p ∣ 2 :=
      (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using hzero)
    have hle : p ≤ 2 := Nat.le_of_dvd (by omega) hdiv
    omega
  funext i
  change z i = (0 : ZMod p)
  have hzi : z i = -(z i) := congrFun hz i
  have hadd : z i + z i = 0 := (eq_neg_iff_add_eq_zero).mp hzi
  have hmul : (2 : ZMod p) * z i = 0 := by
    simpa [two_mul] using hadd
  exact (mul_eq_zero.mp hmul).resolve_left htwo

/-- A finite set containing no nonzero antipodal pair occupies at most one
point from each antipodal pair, plus possibly zero. -/
theorem antipodal_support_bound_twice {V : Type*}
    [AddCommGroup V] [Fintype V] [DecidableEq V]
    (T : Finset V)
    (hanti : ∀ z, z ∈ T → -z ∈ T → z = 0) :
    2 * T.card ≤ Fintype.card V + 1 := by
  let Tneg : Finset V := T.image (-·)
  have hnegcard : Tneg.card = T.card := by
    exact Finset.card_image_of_injective T neg_injective
  have hinter : (T ∩ Tneg).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    have hx' := Finset.mem_inter.mp hx
    have hy' := Finset.mem_inter.mp hy
    have hxneg : -x ∈ T := by
      rcases Finset.mem_image.mp hx'.2 with ⟨z, hz, hzx⟩
      have hzx' : z = -x := by
        calc
          z = -(-z) := by simp
          _ = -x := congrArg Neg.neg hzx
      simpa [hzx'] using hz
    have hyneg : -y ∈ T := by
      rcases Finset.mem_image.mp hy'.2 with ⟨z, hz, hzy⟩
      have hzy' : z = -y := by
        calc
          z = -(-z) := by simp
          _ = -y := congrArg Neg.neg hzy
      simpa [hzy'] using hz
    exact (hanti x hx'.1 hxneg).trans (hanti y hy'.1 hyneg).symm
  have hunion : (T ∪ Tneg).card ≤ Fintype.card V :=
    Finset.card_le_univ _
  have hinclusion := Finset.card_union_add_card_inter T Tneg
  omega

section KernelPalette

variable (p r : ℕ) [Fact p.Prime]

/-- An independent set in a union-of-kernels sum graph has no nonzero
antipodal pair in its image under any selected map. -/
theorem image_antipodal_bound {ι : Type*} [DecidableEq ι]
    (hp : 2 < p) (Y : Finset ι)
    (F : ι → FFVec p (2 * r) →ₗ[ZMod p] FFVec p r)
    (A : Finset (FFVec p (2 * r)))
    (hA : (groupSumGraph (kernelPalette p r Y F)).IsIndepSet
      (A : Set (FFVec p (2 * r))))
    {y : ι} (hy : y ∈ Y) :
    2 * (A.image (F y)).card ≤ p ^ r + 1 := by
  classical
  have hanti : ∀ z, z ∈ A.image (F y) → -z ∈ A.image (F y) → z = 0 := by
    intro z hz hzneg
    rcases Finset.mem_image.mp hz with ⟨a, ha, hFa⟩
    rcases Finset.mem_image.mp hzneg with ⟨a', ha', hFa'⟩
    by_cases hzero : z = 0
    · exact hzero
    · have hneq : a ≠ a' := by
        intro haa'
        subst a'
        have hzneg' : z = -z := hFa.symm.trans hFa'
        exact hzero (eq_zero_of_eq_neg_ffVec hp z hzneg')
      have hker : a + a' ∈ kernelFinset p r (F y) := by
        rw [kernelFinset, Set.mem_toFinset, Set.mem_ofPred_eq]
        change F y (a + a') = 0
        rw [LinearMap.map_add, hFa, hFa', add_neg_cancel]
      have hpal : a + a' ∈ kernelPalette p r Y F := by
        refine Finset.mem_biUnion.mpr ⟨y, hy, ?_⟩
        simpa only [Function.comp_apply] using hker
      exact (hA ha ha' hneq (groupSumGraph_adj.mpr ⟨hneq, hpal⟩)).elim
  have hbound := antipodal_support_bound_twice (A.image (F y)) hanti
  simpa [FFVec, Fintype.card_fun, ZMod.card] using hbound

/-- The group-palette proposition in a denominator-free form: a finite
surjective family with the required set-image expansion produces a palette of
size at most `p^(r+d)` and independence number below `p^(r+s)`. -/
theorem exists_kernelPalette_of_setImageExpanding
    {d s : ℕ} {ι : Type*} [DecidableEq ι]
    (hp : 2 < p) (Y : Finset ι)
    (F : ι → FFVec p (2 * r) →ₗ[ZMod p] FFVec p r)
    (hY : Y.card ≤ p ^ d)
    (hF : ∀ y ∈ Y, Function.Surjective (F y))
    (hexpand : SetImageExpanding p r s Y F) :
    ∃ S : Finset (FFVec p (2 * r)),
      S.card ≤ p ^ (r + d) ∧
        (groupSumGraph S).indepNum < p ^ (r + s) := by
  classical
  let S := kernelPalette p r Y F
  refine ⟨S, ?_, ?_⟩
  · calc
      S.card ≤ Y.card * p ^ r := by
        simpa [S, kernelPalette] using kernel_palette_card_le p r Y F hF
      _ ≤ p ^ d * p ^ r := Nat.mul_le_mul_right (p ^ r) hY
      _ = p ^ (r + d) := by rw [Nat.pow_add]; ac_rfl
  · obtain ⟨A, hA⟩ := (groupSumGraph S).exists_isNIndepSet_indepNum
    by_contra hnot
    have hlarge : p ^ (r + s) ≤ A.card := by
      rw [hA.card_eq]
      omega
    obtain ⟨y, hy, himage⟩ := hexpand A hlarge
    have hsmall : 2 * (A.image (F y)).card ≤ p ^ r + 1 := by
      apply image_antipodal_bound p r hp Y F A
      · simpa [S] using hA.isIndepSet
      · exact hy
    omega

end KernelPalette

end Erdos788


/-! Flattened from Erdos788.ExtractorInterface. -/


/-!
# The checked extractor-to-palette interface

The reconstruction module will construct `LinearExtractorFamily`.  This file
proves, without any asymptotics, that its total-variation guarantee implies
the exact set-image expansion required by `UpperGraph` and hence the
union-of-kernels palette theorem.
-/

namespace Erdos788

open scoped BigOperators

@[simp]
theorem fintypeCard_ffVec (p k : ℕ) [NeZero p] :
    Fintype.card (FFVec p k) = p ^ k := by
  simp [FFVec, ZMod.card]

/-- A finite indexed family of surjective linear maps satisfying the strong
average total-variation guarantee used in the paper. -/
structure LinearExtractorFamily (p r d s : ℕ) [Fact p.Prime] where
  Seed : Type
  [seedFintype : Fintype Seed]
  [seedDecidableEq : DecidableEq Seed]
  [seedNonempty : Nonempty Seed]
  card_seed_le : Fintype.card Seed ≤ p ^ d
  map : Seed → FFVec p (2 * r) →ₗ[ZMod p] FFVec p r
  surjective : ∀ y, Function.Surjective (map y)
  extracts : ∀ P : FinDist (FFVec p (2 * r)),
    P.PointBound (p ^ (r + s)) →
      (Fintype.card Seed : ℝ)⁻¹ *
          ∑ y : Seed, (P.map (map y)).tv (FinDist.uniform (FFVec p r)) <
        1 / 3

attribute [instance] LinearExtractorFamily.seedFintype
  LinearExtractorFamily.seedDecidableEq LinearExtractorFamily.seedNonempty

theorem one_third_le_one_sub_card_div_of_antipodal_bound
    {p r t : ℕ} (hp : 2 < p) (hr : 0 < r)
    (hanti : 2 * t ≤ p ^ r + 1) :
    (1 / 3 : ℝ) ≤ 1 - (t : ℝ) / (p ^ r : ℕ) := by
  have hp0 : 0 < p := by omega
  have hr1 : 1 ≤ r := hr
  have hp_le_pow : p ≤ p ^ r := by
    simpa only [pow_one] using Nat.pow_le_pow_right hp0 hr1
  have hpow3 : 3 ≤ p ^ r := (by omega : 3 ≤ p).trans hp_le_pow
  have hthree : 3 * t ≤ 2 * p ^ r := by omega
  have hpowR : (0 : ℝ) < (p ^ r : ℕ) := by
    exact_mod_cast pow_pos hp0 r
  have hthreeR : (3 : ℝ) * t ≤ 2 * (p ^ r : ℕ) := by
    exact_mod_cast hthree
  have hratio : (t : ℝ) / (p ^ r : ℕ) ≤ 2 / 3 := by
    apply (div_le_iff₀ hpowR).2
    nlinarith
  nlinarith

/-- The strong average extractor guarantee forces the denominator-free image
expansion property used by the group palette argument. -/
theorem extractorFamily_setImageExpanding
    {p r d s : ℕ} [Fact p.Prime] (hp : 2 < p) (hr : 0 < r)
    (E : LinearExtractorFamily p r d s) :
    SetImageExpanding p r s (Finset.univ : Finset E.Seed) E.map := by
  intro A hlarge
  have hp0 : 0 < p := by omega
  have hthreshold : 0 < p ^ (r + s) := pow_pos hp0 _
  have hAcard : 0 < A.card := hthreshold.trans_le hlarge
  have hA : A.Nonempty := Finset.card_pos.mp hAcard
  by_cases hex : ∃ y ∈ (Finset.univ : Finset E.Seed),
      p ^ r + 1 < 2 * (A.image (E.map y)).card
  · exact hex
  · have hsmall : ∀ y : E.Seed,
        2 * (A.image (E.map y)).card ≤ p ^ r + 1 := by
      intro y
      exact Nat.le_of_not_gt fun h ↦ hex ⟨y, Finset.mem_univ y, h⟩
    let P : FinDist (FFVec p (2 * r)) := FinDist.uniformOn A hA
    have hpoint : P.PointBound (p ^ (r + s)) := by
      apply FinDist.pointBound_mono hthreshold hlarge
      exact FinDist.uniformOn_pointBound A hA
    have hseed : ∀ y : E.Seed, (1 / 3 : ℝ) ≤
        (P.map (E.map y)).tv (FinDist.uniform (FFVec p r)) := by
      intro y
      let T : Finset (FFVec p r) := A.image (E.map y)
      have hsupport : ∀ z, z ∉ T → (P.map (E.map y)).mass z = 0 := by
        intro z hz
        exact FinDist.map_uniformOn_mass_eq_zero_of_notMem_image
          A hA (E.map y) hz
      have htv := FinDist.tv_uniform_ge_one_sub_support
        (P.map (E.map y)) T hsupport
      have hthird : (1 / 3 : ℝ) ≤
          1 - (T.card : ℝ) / (p ^ r : ℕ) :=
        one_third_le_one_sub_card_div_of_antipodal_bound hp hr (hsmall y)
      have hcard : Fintype.card (FFVec p r) = p ^ r :=
        fintypeCard_ffVec p r
      rw [hcard] at htv
      exact hthird.trans htv
    have hsum : (Fintype.card E.Seed : ℝ) * (1 / 3 : ℝ) ≤
        ∑ y : E.Seed, (P.map (E.map y)).tv
          (FinDist.uniform (FFVec p r)) := by
      simpa using Finset.sum_le_sum fun y (_hy : y ∈
        (Finset.univ : Finset E.Seed)) ↦ hseed y
    have hcardpos : (0 : ℝ) < Fintype.card E.Seed := by
      exact_mod_cast Fintype.card_pos
    have havg : (1 / 3 : ℝ) ≤
        (Fintype.card E.Seed : ℝ)⁻¹ *
          ∑ y : E.Seed, (P.map (E.map y)).tv
            (FinDist.uniform (FFVec p r)) := by
      calc
        (1 / 3 : ℝ) = (Fintype.card E.Seed : ℝ)⁻¹ *
            ((Fintype.card E.Seed : ℝ) * (1 / 3 : ℝ)) := by
              field_simp
        _ ≤ (Fintype.card E.Seed : ℝ)⁻¹ *
            ∑ y : E.Seed, (P.map (E.map y)).tv
              (FinDist.uniform (FFVec p r)) :=
          mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hcardpos.le)
    exact (not_lt_of_ge havg (E.extracts P hpoint)).elim

/-- Proposition 5.1 of the paper, obtained directly from a checked linear
extractor family. -/
theorem kernelPalette_of_linearExtractorFamily
    {p r d s : ℕ} [Fact p.Prime] (hp : 2 < p) (hr : 0 < r)
    (E : LinearExtractorFamily p r d s) :
    ∃ S : Finset (FFVec p (2 * r)),
      S.card ≤ p ^ (r + d) ∧
        (groupSumGraph S).indepNum < p ^ (r + s) := by
  apply exists_kernelPalette_of_setImageExpanding p r hp
    (Finset.univ : Finset E.Seed) E.map
  · simpa using E.card_seed_le
  · intro y _hy
    exact E.surjective y
  · exact extractorFamily_setImageExpanding hp hr E

end Erdos788


/-! Flattened from Erdos788.RankPruning. -/


/-!
# Pruning rank-deficient extractor seeds

The raw Trevisan construction gives one linear map for every binary seed but
does not make each map surjective.  Applying the raw extractor to the uniform
source shows that only a small fraction of seeds can be rank deficient.  This
file formalizes that finite argument and renormalizes the retained family.
-/

namespace Erdos788

open scoped BigOperators

/-- The range of a finite linear map, represented as a finset of its
codomain. -/
noncomputable def linearRangeFinset {p m r : ℕ} [Fact p.Prime]
    (F : FFVec p m →ₗ[ZMod p] FFVec p r) : Finset (FFVec p r) :=
  by
    classical
    exact Finset.univ.image (fun z : F.range ↦ z.val)

@[simp]
theorem mem_linearRangeFinset {p m r : ℕ} [Fact p.Prime]
    (F : FFVec p m →ₗ[ZMod p] FFVec p r) (z : FFVec p r) :
    z ∈ linearRangeFinset F ↔ z ∈ F.range := by
  classical
  constructor
  · intro hz
    rw [linearRangeFinset, Finset.mem_image] at hz
    obtain ⟨w, _hw, rfl⟩ := hz
    exact w.property
  · intro hz
    rw [linearRangeFinset, Finset.mem_image]
    exact ⟨⟨z, hz⟩, Finset.mem_univ _, rfl⟩

theorem card_linearRangeFinset {p m r : ℕ} [Fact p.Prime]
    (F : FFVec p m →ₗ[ZMod p] FFVec p r) :
    (linearRangeFinset F).card =
      p ^ Module.finrank (ZMod p) F.range := by
  classical
  calc
    (linearRangeFinset F).card = Fintype.card F.range := by
      rw [linearRangeFinset, Finset.card_image_of_injective]
      · exact Finset.card_univ
      · exact Subtype.val_injective
    _ = Nat.card F.range := Nat.card_eq_fintype_card.symm
    _ = p ^ Module.finrank (ZMod p) F.range := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := F.range),
        Nat.card_zmod]

/-- A non-surjective map to `ᵓ_p^r` has image of size at most
`p^(r-1)`. -/
theorem card_linearRangeFinset_le_of_not_surjective
    {p m r : ℕ} [Fact p.Prime] (hp : 0 < p)
    (F : FFVec p m →ₗ[ZMod p] FFVec p r)
    (hF : ¬Function.Surjective F) :
    (linearRangeFinset F).card ≤ p ^ (r - 1) := by
  have hrange_ne : F.range ≠ ⊤ := by
    intro hrange
    exact hF (LinearMap.range_eq_top.mp hrange)
  have hrange_lt : F.range < ⊤ := lt_top_iff_ne_top.mpr hrange_ne
  have hfinrank := Submodule.finrank_lt_finrank_of_lt hrange_lt
  have htop : Module.finrank (ZMod p)
      (⊤ : Submodule (ZMod p) (FFVec p r)) = r := by
    rw [finrank_top, Module.finrank_fintype_fun_eq_card]
    simp
  rw [htop] at hfinrank
  rw [card_linearRangeFinset]
  exact Nat.pow_le_pow_right hp (by omega)

/-- The pushforward of the uniform source is supported on the linear range. -/
theorem map_uniform_mass_eq_zero_of_notMem_linearRange
    {p m r : ℕ} [Fact p.Prime]
    (F : FFVec p m →ₗ[ZMod p] FFVec p r) {z : FFVec p r}
    (hz : z ∉ linearRangeFinset F) :
    ((FinDist.uniform (FFVec p m)).map F).mass z = 0 := by
  rw [FinDist.map_mass]
  apply Finset.sum_eq_zero
  intro x hx
  have hFx : F x = z := (Finset.mem_filter.mp hx).2
  have hzrange : z ∈ linearRangeFinset F := by
    rw [mem_linearRangeFinset]
    exact ⟨x, hFx⟩
  exact (hz hzrange).elim

/-- In odd prime characteristic, every rank-deficient fixed-seed map sends
the uniform source to a distribution at total variation at least `2/3` from
uniform. -/
theorem two_thirds_le_tv_map_uniform_of_not_surjective
    {p m r : ℕ} [Fact p.Prime] (hp : 2 < p) (hr : 0 < r)
    (F : FFVec p m →ₗ[ZMod p] FFVec p r)
    (hF : ¬Function.Surjective F) :
    (2 / 3 : ℝ) ≤
      ((FinDist.uniform (FFVec p m)).map F).tv
        (FinDist.uniform (FFVec p r)) := by
  have hp0 : 0 < p := by omega
  let T := linearRangeFinset F
  have hTcard : T.card ≤ p ^ (r - 1) :=
    card_linearRangeFinset_le_of_not_surjective hp0 F hF
  have hpow : p ^ (r - 1) * p = p ^ r := by
    rw [← pow_succ]
    congr 1
    omega
  have hthree : 3 * T.card ≤ p ^ r := by
    calc
      3 * T.card ≤ p * p ^ (r - 1) :=
        Nat.mul_le_mul (by omega) hTcard
      _ = p ^ r := by rw [Nat.mul_comm, hpow]
  have hpowR : (0 : ℝ) < (p ^ r : ℕ) := by
    exact_mod_cast pow_pos hp0 r
  have hthreeR : (3 : ℝ) * T.card ≤ (p ^ r : ℕ) := by
    exact_mod_cast hthree
  have hratio : (T.card : ℝ) / (p ^ r : ℕ) ≤ 1 / 3 := by
    apply (div_le_iff₀ hpowR).2
    nlinarith
  have hsupport : ∀ z, z ∉ T →
      ((FinDist.uniform (FFVec p m)).map F).mass z = 0 := by
    intro z hz
    exact map_uniform_mass_eq_zero_of_notMem_linearRange F hz
  have htv := FinDist.tv_uniform_ge_one_sub_support
    ((FinDist.uniform (FFVec p m)).map F) T hsupport
  rw [fintypeCard_ffVec p r] at htv
  nlinarith

/-- A raw family before rank pruning. -/
structure RawLinearExtractorFamily (p r d s : ℕ) [Fact p.Prime] where
  Seed : Type
  [seedFintype : Fintype Seed]
  [seedDecidableEq : DecidableEq Seed]
  [seedNonempty : Nonempty Seed]
  card_seed_le : Fintype.card Seed ≤ p ^ d
  map : Seed → FFVec p (2 * r) →ₗ[ZMod p] FFVec p r
  extracts : ∀ P : FinDist (FFVec p (2 * r)),
    P.PointBound (p ^ (r + s)) →
      (Fintype.card Seed : ℝ)⁻¹ *
          ∑ y : Seed, (P.map (map y)).tv (FinDist.uniform (FFVec p r)) ≤
        1 / 20

attribute [instance] RawLinearExtractorFamily.seedFintype
  RawLinearExtractorFamily.seedDecidableEq
  RawLinearExtractorFamily.seedNonempty

/-- Seeds whose fixed-seed map has full rank. -/
noncomputable def surjectiveSeeds {p r d s : ℕ} [Fact p.Prime]
    (E : RawLinearExtractorFamily p r d s) : Finset E.Seed := by
  classical
  exact Finset.univ.filter fun y ↦ Function.Surjective (E.map y)

/-- Seeds whose fixed-seed map is rank deficient. -/
noncomputable def nonsurjectiveSeeds {p r d s : ℕ} [Fact p.Prime]
    (E : RawLinearExtractorFamily p r d s) : Finset E.Seed := by
  classical
  exact Finset.univ.filter fun y ↦ ¬Function.Surjective (E.map y)

@[simp]
theorem mem_surjectiveSeeds {p r d s : ℕ} [Fact p.Prime]
    (E : RawLinearExtractorFamily p r d s) (y : E.Seed) :
    y ∈ surjectiveSeeds E ↔ Function.Surjective (E.map y) := by
  classical
  simp [surjectiveSeeds]

@[simp]
theorem mem_nonsurjectiveSeeds {p r d s : ℕ} [Fact p.Prime]
    (E : RawLinearExtractorFamily p r d s) (y : E.Seed) :
    y ∈ nonsurjectiveSeeds E ↔ ¬Function.Surjective (E.map y) := by
  classical
  simp [nonsurjectiveSeeds]

theorem card_surjectiveSeeds_add_card_nonsurjectiveSeeds
    {p r d s : ℕ} [Fact p.Prime]
    (E : RawLinearExtractorFamily p r d s) :
    (surjectiveSeeds E).card + (nonsurjectiveSeeds E).card =
      Fintype.card E.Seed := by
  classical
  simpa [surjectiveSeeds, nonsurjectiveSeeds] using
    (Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset E.Seed))
      (fun y ↦ Function.Surjective (E.map y)))

/-- The retained seed type. -/
def SurjectiveSeed {p r d s : ℕ} [Fact p.Prime]
    (E : RawLinearExtractorFamily p r d s) :=
  {y : E.Seed // Function.Surjective (E.map y)}

noncomputable instance surjectiveSeedFintype
    {p r d s : ℕ} [Fact p.Prime]
    (E : RawLinearExtractorFamily p r d s) : Fintype (SurjectiveSeed E) := by
  classical
  exact Subtype.fintype fun y : E.Seed ↦ Function.Surjective (E.map y)

theorem card_surjectiveSeed {p r d s : ℕ} [Fact p.Prime]
    (E : RawLinearExtractorFamily p r d s) :
    Fintype.card (SurjectiveSeed E) = (surjectiveSeeds E).card := by
  classical
  simpa [SurjectiveSeed, surjectiveSeeds] using
    (Fintype.card_subtype fun y : E.Seed ↦ Function.Surjective (E.map y))

/-- Remove the averaging denominator from the raw extractor guarantee. -/
theorem RawLinearExtractorFamily.total_error_le_card_div_twenty
    {p r d s : ℕ} [Fact p.Prime]
    (E : RawLinearExtractorFamily p r d s)
    (P : FinDist (FFVec p (2 * r)))
    (hP : P.PointBound (p ^ (r + s))) :
    ∑ y : E.Seed, (P.map (E.map y)).tv (FinDist.uniform (FFVec p r)) ≤
      (Fintype.card E.Seed : ℝ) / 20 := by
  have hraw := E.extracts P hP
  have hcardpos : (0 : ℝ) < Fintype.card E.Seed := by
    exact_mod_cast Fintype.card_pos
  have hcardne : (Fintype.card E.Seed : ℝ) ≠ 0 := ne_of_gt hcardpos
  calc
    ∑ y : E.Seed, (P.map (E.map y)).tv (FinDist.uniform (FFVec p r)) =
        (Fintype.card E.Seed : ℝ) *
          ((Fintype.card E.Seed : ℝ)⁻¹ *
            ∑ y : E.Seed,
              (P.map (E.map y)).tv (FinDist.uniform (FFVec p r))) := by
          rw [← mul_assoc, mul_inv_cancel₀ hcardne, one_mul]
    _ ≤ (Fintype.card E.Seed : ℝ) * (1 / 20 : ℝ) :=
      mul_le_mul_of_nonneg_left hraw hcardpos.le
    _ = (Fintype.card E.Seed : ℝ) / 20 := by ring

/-- The uniform source has enough min-entropy for the raw guarantee whenever
`r+s ≤ 2r`. -/
theorem uniform_source_pointBound_of_add_le_two_mul
    {p r s : ℕ} [Fact p.Prime] (hp : 2 < p) (hrs : r + s ≤ 2 * r) :
    (FinDist.uniform (FFVec p (2 * r))).PointBound (p ^ (r + s)) := by
  have hp0 : 0 < p := by omega
  have hfull : (FinDist.uniform (FFVec p (2 * r))).PointBound (p ^ (2 * r)) := by
    simpa only [fintypeCard_ffVec] using
      (FinDist.uniform_pointBound (α := FFVec p (2 * r)))
  exact FinDist.pointBound_mono (pow_pos hp0 _) (Nat.pow_le_pow_right hp0 hrs) hfull

/-- At most a `3/40` fraction of raw seeds are rank deficient. -/
theorem forty_mul_card_nonsurjectiveSeeds_le_three_mul_card
    {p r d s : ℕ} [Fact p.Prime]
    (hp : 2 < p) (hr : 0 < r) (hrs : r + s ≤ 2 * r)
    (E : RawLinearExtractorFamily p r d s) :
    40 * (nonsurjectiveSeeds E).card ≤ 3 * Fintype.card E.Seed := by
  classical
  let P : FinDist (FFVec p (2 * r)) := FinDist.uniform (FFVec p (2 * r))
  have hpoint : P.PointBound (p ^ (r + s)) := by
    exact uniform_source_pointBound_of_add_le_two_mul hp hrs
  have hbadPoint : ∀ y ∈ nonsurjectiveSeeds E, (2 / 3 : ℝ) ≤
      (P.map (E.map y)).tv (FinDist.uniform (FFVec p r)) := by
    intro y hy
    exact two_thirds_le_tv_map_uniform_of_not_surjective hp hr (E.map y)
      ((mem_nonsurjectiveSeeds E y).mp hy)
  have hbadLower : ((nonsurjectiveSeeds E).card : ℝ) * (2 / 3 : ℝ) ≤
      ∑ y ∈ nonsurjectiveSeeds E,
        (P.map (E.map y)).tv (FinDist.uniform (FFVec p r)) := by
    calc
      ((nonsurjectiveSeeds E).card : ℝ) * (2 / 3 : ℝ) =
          ∑ y ∈ nonsurjectiveSeeds E, (2 / 3 : ℝ) := by simp
      _ ≤ ∑ y ∈ nonsurjectiveSeeds E,
          (P.map (E.map y)).tv (FinDist.uniform (FFVec p r)) :=
        Finset.sum_le_sum hbadPoint
  have hbadLeTotal :
      (∑ y ∈ nonsurjectiveSeeds E,
          (P.map (E.map y)).tv (FinDist.uniform (FFVec p r))) ≤
        ∑ y : E.Seed,
          (P.map (E.map y)).tv (FinDist.uniform (FFVec p r)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro y _hy _hbad
    exact FinDist.tv_nonneg _ _
  have htotal :
      (∑ y : E.Seed,
          (P.map (E.map y)).tv (FinDist.uniform (FFVec p r))) ≤
        (Fintype.card E.Seed : ℝ) / 20 :=
    E.total_error_le_card_div_twenty P hpoint
  have hbadReal : (40 : ℝ) * (nonsurjectiveSeeds E).card ≤
      3 * Fintype.card E.Seed := by
    nlinarith [hbadLower.trans hbadLeTotal]
  exact_mod_cast hbadReal

/-- Consequently at least a `37/40` fraction of raw seeds are retained. -/
theorem thirty_seven_mul_card_le_forty_mul_card_surjectiveSeeds
    {p r d s : ℕ} [Fact p.Prime]
    (hp : 2 < p) (hr : 0 < r) (hrs : r + s ≤ 2 * r)
    (E : RawLinearExtractorFamily p r d s) :
    37 * Fintype.card E.Seed ≤ 40 * (surjectiveSeeds E).card := by
  have hbad := forty_mul_card_nonsurjectiveSeeds_le_three_mul_card hp hr hrs E
  have hpartition := card_surjectiveSeeds_add_card_nonsurjectiveSeeds E
  omega

theorem nonempty_surjectiveSeed
    {p r d s : ℕ} [Fact p.Prime]
    (hp : 2 < p) (hr : 0 < r) (hrs : r + s ≤ 2 * r)
    (E : RawLinearExtractorFamily p r d s) :
    Nonempty (SurjectiveSeed E) := by
  have hgood := thirty_seven_mul_card_le_forty_mul_card_surjectiveSeeds hp hr hrs E
  have hall : 0 < Fintype.card E.Seed := Fintype.card_pos
  have hcard : 0 < Fintype.card (SurjectiveSeed E) := by
    rw [card_surjectiveSeed]
    omega
  exact Fintype.card_pos_iff.mp hcard

/-- Prune every rank-deficient seed and renormalize the extractor average.
The retained average is at most `2/37`, hence strictly below `1/3`. -/
theorem prune_rank_deficient_seeds
    {p r d s : ℕ} [Fact p.Prime]
    (hp : 2 < p) (hr : 0 < r) (hrs : r + s ≤ 2 * r)
    (E : RawLinearExtractorFamily p r d s) :
    Nonempty (LinearExtractorFamily p r d s) := by
  classical
  let _ : Nonempty (SurjectiveSeed E) := nonempty_surjectiveSeed hp hr hrs E
  refine ⟨{
    Seed := SurjectiveSeed E
    seedFintype := inferInstance
    seedDecidableEq := inferInstance
    seedNonempty := inferInstance
    card_seed_le := ?_
    map := fun y ↦ E.map y.val
    surjective := fun y ↦ y.property
    extracts := ?_ }⟩
  · exact (Fintype.card_subtype_le fun y : E.Seed ↦
      Function.Surjective (E.map y)).trans E.card_seed_le
  · intro P hP
    let loss : E.Seed → ℝ := fun y ↦
      (P.map (E.map y)).tv (FinDist.uniform (FFVec p r))
    have htotal : ∑ y : E.Seed, loss y ≤
        (Fintype.card E.Seed : ℝ) / 20 := by
      exact E.total_error_le_card_div_twenty P hP
    have hsumEq : (∑ y : SurjectiveSeed E, loss y.val) =
        ∑ y ∈ (Finset.univ : Finset E.Seed) with
          Function.Surjective (E.map y), loss y := by
      simpa [SurjectiveSeed] using
        (Finset.sum_subtype_eq_sum_filter
          (s := (Finset.univ : Finset E.Seed)) loss
          (p := fun y ↦ Function.Surjective (E.map y)))
    have hretainedLeAll : (∑ y : SurjectiveSeed E, loss y.val) ≤
        ∑ y : E.Seed, loss y := by
      rw [hsumEq]
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro y _hy _hgood
      exact FinDist.tv_nonneg _ _
    have hretained : (∑ y : SurjectiveSeed E, loss y.val) ≤
        (Fintype.card E.Seed : ℝ) / 20 :=
      hretainedLeAll.trans htotal
    have hgoodNat :=
      thirty_seven_mul_card_le_forty_mul_card_surjectiveSeeds hp hr hrs E
    have hgoodNat' : 37 * Fintype.card E.Seed ≤
        40 * Fintype.card (SurjectiveSeed E) := by
      simpa [card_surjectiveSeed] using hgoodNat
    have hgoodReal : (37 : ℝ) * Fintype.card E.Seed ≤
        40 * Fintype.card (SurjectiveSeed E) := by
      exact_mod_cast hgoodNat'
    have hcardpos : (0 : ℝ) < Fintype.card (SurjectiveSeed E) := by
      exact_mod_cast Fintype.card_pos
    have hscaled : (Fintype.card (SurjectiveSeed E) : ℝ)⁻¹ *
        (∑ y : SurjectiveSeed E, loss y.val) ≤ 2 / 37 := by
      rw [inv_mul_eq_div]
      apply (div_le_iff₀ hcardpos).2
      have hratio : (Fintype.card E.Seed : ℝ) / 20 ≤
          (2 / 37 : ℝ) * Fintype.card (SurjectiveSeed E) := by
        nlinarith
      exact hretained.trans hratio
    exact hscaled.trans_lt (by norm_num)

end Erdos788


/-! Flattened from Erdos788.FinitePrediction. -/


/-!
# Finite product distributions and prediction from total variation

These lemmas isolate the probability bookkeeping used by the reconstruction
argument.  In particular, the predictor theorem is stated with unnormalised
context masses, so no conditional-probability denominator or zero-mass case
is needed.
-/

namespace Erdos788

open scoped BigOperators

namespace FinDist

variable {α β γ : Type*}

/-- Product of two finite distributions. -/
noncomputable def prod [Fintype α] [Fintype β]
    (P : FinDist α) (Q : FinDist β) : FinDist (α × β) where
  mass := fun z ↦ P.mass z.1 * Q.mass z.2
  nonneg := fun z ↦ mul_nonneg (P.nonneg z.1) (Q.nonneg z.2)
  sum_mass := by
    rw [Fintype.sum_prod_type]
    calc
      (∑ a, ∑ b, P.mass a * Q.mass b) =
          ∑ a, P.mass a * ∑ b, Q.mass b := by
        apply Finset.sum_congr rfl
        intro a _ha
        rw [Finset.mul_sum]
      _ = 1 := by rw [Q.sum_mass]; simp [P.sum_mass]

@[simp]
theorem prod_mass [Fintype α] [Fintype β]
    (P : FinDist α) (Q : FinDist β) (z : α × β) :
    (P.prod Q).mass z = P.mass z.1 * Q.mass z.2 :=
  rfl

/-- Total variation is unchanged after adjoining the same independent right
factor. -/
theorem tv_prod_right [Fintype α] [Fintype β]
    (P Q : FinDist α) (R : FinDist β) :
    (P.prod R).tv (Q.prod R) = P.tv Q := by
  rw [tv, tv, Fintype.sum_prod_type]
  simp only [prod_mass]
  have hpoint : ∀ a : α, ∀ b : β,
      |P.mass a * R.mass b - Q.mass a * R.mass b| =
        |P.mass a - Q.mass a| * R.mass b := by
    intro a b
    rw [← sub_mul, abs_mul, abs_of_nonneg (R.nonneg b)]
  simp_rw [hpoint]
  calc
    (1 / 2 : ℝ) * ∑ a, ∑ b, |P.mass a - Q.mass a| * R.mass b =
        (1 / 2 : ℝ) * ∑ a, |P.mass a - Q.mass a| * ∑ b, R.mass b := by
      congr 1
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Finset.mul_sum]
    _ = (1 / 2 : ℝ) * ∑ a, |P.mass a - Q.mass a| := by
      rw [R.sum_mass]
      simp

/-- Total variation is unchanged after adjoining the same independent left
factor. -/
theorem tv_prod_left [Fintype α] [Fintype β]
    (R : FinDist α) (P Q : FinDist β) :
    (R.prod P).tv (R.prod Q) = P.tv Q := by
  rw [tv, tv, Fintype.sum_prod_type]
  simp only [prod_mass]
  have hpoint : ∀ a : α, ∀ b : β,
      |R.mass a * P.mass b - R.mass a * Q.mass b| =
        R.mass a * |P.mass b - Q.mass b| := by
    intro a b
    rw [← mul_sub, abs_mul, abs_of_nonneg (R.nonneg a)]
  simp_rw [hpoint]
  calc
    (1 / 2 : ℝ) * ∑ a, ∑ b, R.mass a * |P.mass b - Q.mass b| =
        (1 / 2 : ℝ) * ∑ a, R.mass a * ∑ b, |P.mass b - Q.mass b| := by
      congr 1
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Finset.mul_sum]
    _ = (1 / 2 : ℝ) * ∑ b, |P.mass b - Q.mass b| := by
      rw [← Finset.sum_mul, R.sum_mass, one_mul]

/-- Pushing forward cannot increase finite total variation. -/
theorem tv_map_le [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (P Q : FinDist α) :
    (P.map f).tv (Q.map f) ≤ P.tv Q := by
  rw [tv, tv]
  have hfiber : ∀ b : β,
      |∑ a with f a = b, P.mass a - ∑ a with f a = b, Q.mass a| ≤
        ∑ a with f a = b, |P.mass a - Q.mass a| := by
    intro b
    rw [← Finset.sum_sub_distrib]
    exact Finset.abs_sum_le_sum_abs _ _
  have hsum := Finset.sum_le_sum fun b
      (_hb : b ∈ (Finset.univ : Finset β)) ↦ hfiber b
  have hpartition :
      (∑ b, ∑ a with f a = b, |P.mass a - Q.mass a|) =
        ∑ a, |P.mass a - Q.mass a| := by
    simp [Finset.sum_fiberwise_eq_sum_filter Finset.univ Finset.univ f
      (fun a ↦ |P.mass a - Q.mass a|)]
  rw [hpartition] at hsum
  exact mul_le_mul_of_nonneg_left hsum (by norm_num)

@[simp]
theorem map_equiv_mass [Fintype α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (P : FinDist α) (a : α) :
    (P.map e).mass (e a) = P.mass a := by
  rw [map_mass]
  have hfiber :
      (Finset.univ.filter fun x : α ↦ e x = e a) = {a} := by
    ext x
    simp
  rw [hfiber]
  simp

/-- A uniform finite distribution remains uniform under a reindexing
equivalence. -/
theorem map_uniform_equiv [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] [DecidableEq β]
    (e : α ≃ β) :
    (FinDist.uniform α).map e = FinDist.uniform β := by
  classical
  ext b
  let a : α := e.symm b
  have hab : e a = b := e.apply_symm_apply b
  rw [← hab, map_equiv_mass]
  simp only [uniform_mass]
  rw [Fintype.card_congr e]

/-- Total variation is invariant under a reindexing equivalence. -/
theorem tv_map_equiv [Fintype α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (P Q : FinDist α) :
    (P.map e).tv (Q.map e) = P.tv Q := by
  rw [tv, tv]
  congr 1
  calc
    (∑ b : β, |(P.map e).mass b - (Q.map e).mass b|) =
        ∑ a : α, |(P.map e).mass (e a) - (Q.map e).mass (e a)| :=
      (e.sum_comp fun b ↦ |(P.map e).mass b - (Q.map e).mass b|).symm
    _ = ∑ a : α, |P.mass a - Q.mass a| := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [map_equiv_mass e P a, map_equiv_mass e Q a]

/-- Functoriality of finite pushforward. -/
theorem map_map [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ]
    (P : FinDist α) (f : α → β) (g : β → γ) :
    (P.map f).map g = P.map (g ∘ f) := by
  ext c
  rw [map_mass, map_mass]
  simp only [map_mass]
  let T : Finset β := Finset.univ.filter fun b ↦ g b = c
  have h := Finset.sum_fiberwise_eq_sum_filter
    (Finset.univ : Finset α) T f P.mass
  simpa only [T, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.comp_apply] using h

/-- A deterministic maximizer on a nonempty finite type. -/
noncomputable def finiteArgmax (α : Type*) [Fintype α] [Nonempty α]
    (f : α → ℝ) : α :=
  Classical.choose
    (Finset.exists_max_image (Finset.univ : Finset α) f Finset.univ_nonempty)

theorem le_finiteArgmax (α : Type*) [Fintype α] [Nonempty α]
    (f : α → ℝ) (a : α) : f a ≤ f (finiteArgmax α f) := by
  exact (Classical.choose_spec
    (Finset.exists_max_image (Finset.univ : Finset α) f
      Finset.univ_nonempty)).2 a (Finset.mem_univ a)

/-- Marginal distribution on the first coordinate. -/
noncomputable def fst [Fintype α] [Fintype β] [DecidableEq α]
    (P : FinDist (α × β)) : FinDist α :=
  P.map Prod.fst

@[simp]
theorem fst_mass [Fintype α] [Fintype β] [DecidableEq α]
    (P : FinDist (α × β)) (a : α) :
    P.fst.mass a = ∑ b, P.mass (a, b) := by
  rw [fst, map_mass]
  apply Finset.sum_bij (fun z _hz ↦ z.2)
  · intro z _hz
    exact Finset.mem_univ z.2
  · intro z₁ hz₁ z₂ hz₂ hsnd
    apply Prod.ext
    · exact ((Finset.mem_filter.mp hz₁).2).trans
        ((Finset.mem_filter.mp hz₂).2).symm
    · exact hsnd
  · intro b _hb
    exact ⟨(a, b), by simp, rfl⟩
  · intro z hz
    congr 1
    exact Prod.ext (Finset.mem_filter.mp hz).2 rfl

/-- The first marginal of an independent product is its first factor. -/
@[simp]
theorem fst_prod [Fintype α] [Fintype β] [DecidableEq α]
    (P : FinDist α) (Q : FinDist β) :
    (P.prod Q).fst = P := by
  ext a
  rw [fst_mass]
  simp only [prod_mass]
  rw [← Finset.mul_sum, Q.sum_mass, mul_one]

/-- The uniform law on a product is the product of the uniform laws. -/
theorem uniform_prod [Fintype α] [Fintype β] [Nonempty α] [Nonempty β] :
    FinDist.uniform (α × β) =
      (FinDist.uniform α).prod (FinDist.uniform β) := by
  classical
  ext z
  simp only [uniform_mass, prod_mass, Fintype.card_prod]
  have ha : (Fintype.card α : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos : 0 < Fintype.card α))
  have hb : (Fintype.card β : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos : 0 < Fintype.card β))
  push_cast
  field_simp

/-- Associativity of independent finite products, after the canonical
reindexing of the underlying product type. -/
theorem map_prodAssoc
    {δ : Type*} [Fintype α] [Fintype β] [Fintype δ]
    [DecidableEq α] [DecidableEq β] [DecidableEq δ]
    (P : FinDist α) (Q : FinDist β) (R : FinDist δ) :
    ((P.prod Q).prod R).map (Equiv.prodAssoc α β δ) =
      P.prod (Q.prod R) := by
  classical
  ext z
  let w : (α × β) × δ := ((z.1, z.2.1), z.2.2)
  have hw : Equiv.prodAssoc α β δ w = z := by
    exact Prod.ext rfl (Prod.ext rfl rfl)
  rw [← hw, map_equiv_mass]
  simp only [prod_mass]
  rw [hw]
  dsimp [w]
  ring

/-- The point selected by `finiteArgmax` has at least the average mass. -/
theorem average_le_argmax_mass [Fintype β] [Nonempty β]
    (μ : β → ℝ) :
    (∑ b, μ b) / Fintype.card β ≤ μ (finiteArgmax β μ) := by
  have hsum : ∑ b, μ b ≤
      ∑ _b : β, μ (finiteArgmax β μ) :=
    Finset.sum_le_sum fun b _hb ↦ le_finiteArgmax β μ b
  rw [Finset.sum_const] at hsum
  simp only [nsmul_eq_mul] at hsum
  have hcard : (0 : ℝ) < Fintype.card β := by
    exact_mod_cast Fintype.card_pos
  exact (div_le_iff₀ hcard).2 (by simpa [mul_comm] using hsum)

/-- Pointwise `L¹` deviation from the uniform split of a total mass is at
most twice the alphabet size times the best prediction advantage. -/
theorem sum_abs_sub_average_le
    [Fintype β] [Nonempty β]
    (μ : β → ℝ) :
    ∑ b, |μ b - (∑ c, μ c) / Fintype.card β| ≤
      2 * Fintype.card β *
        (μ (finiteArgmax β μ) - (∑ c, μ c) / Fintype.card β) := by
  let t : ℝ := (∑ c, μ c) / Fintype.card β
  let M : ℝ := μ (finiteArgmax β μ) - t
  have hM : 0 ≤ M := by
    dsimp [M, t]
    exact sub_nonneg.mpr (average_le_argmax_mass μ)
  have hle : ∀ b : β, μ b - t ≤ M := by
    intro b
    dsimp [M]
    linarith [le_finiteArgmax β μ b]
  have hpoint : ∀ b : β, |μ b - t| ≤ 2 * M - (μ b - t) := by
    intro b
    by_cases hb : 0 ≤ μ b - t
    · rw [abs_of_nonneg hb]
      linarith [hle b]
    · rw [abs_of_neg (lt_of_not_ge hb)]
      linarith
  calc
    ∑ b, |μ b - (∑ c, μ c) / Fintype.card β| =
        ∑ b, |μ b - t| := by rfl
    _ ≤ ∑ b, (2 * M - (μ b - t)) := Finset.sum_le_sum fun b _ ↦ hpoint b
    _ = 2 * Fintype.card β * M := by
      simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      dsimp [t]
      have hcard : (Fintype.card β : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos : 0 < Fintype.card β))
      field_simp
      ring
    _ = 2 * Fintype.card β *
        (μ (finiteArgmax β μ) -
          (∑ c, μ c) / Fintype.card β) := by rfl

/-- If a joint law is far from its context marginal times a uniform
alphabet symbol, a deterministic context predictor has a corresponding
unconditional success advantage.  The denominator `p` is slightly weaker
than the optimal `p-1`, but is fully sufficient for the extractor
parameters and avoids all conditional-probability cases. -/
theorem exists_predictor_of_tv_gt
    {p : ℕ} [NeZero p]
    {Context : Type*} [Fintype Context] [DecidableEq Context]
    (Q : FinDist (Context × ZMod p)) (δ : ℝ)
    (hδ : δ < Q.tv (Q.fst.prod (FinDist.uniform (ZMod p)))) :
    ∃ predictor : Context → ZMod p,
      1 / (p : ℝ) + δ / p <
        ∑ c, Q.mass (c, predictor c) := by
  classical
  let predictor : Context → ZMod p := fun c ↦
    finiteArgmax (ZMod p) (fun a ↦ Q.mass (c, a))
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  have hcontext (c : Context) :
      ∑ a, |Q.mass (c, a) - Q.fst.mass c * (p : ℝ)⁻¹| ≤
        2 * p * (Q.mass (c, predictor c) - Q.fst.mass c / p) := by
    have h := sum_abs_sub_average_le (fun a : ZMod p ↦ Q.mass (c, a))
    rw [hcard] at h
    rw [Q.fst_mass c]
    simpa [predictor, div_eq_mul_inv] using h
  have htvUpper : Q.tv (Q.fst.prod (FinDist.uniform (ZMod p))) ≤
      (p : ℝ) *
        ((∑ c, Q.mass (c, predictor c)) - 1 / (p : ℝ)) := by
    rw [tv, Fintype.sum_prod_type]
    simp only [prod_mass, uniform_mass]
    rw [hcard]
    have hsum := Finset.sum_le_sum fun c
        (_hc : c ∈ (Finset.univ : Finset Context)) ↦ hcontext c
    calc
      (1 / 2 : ℝ) *
          ∑ c, ∑ a, |Q.mass (c, a) - Q.fst.mass c * (p : ℝ)⁻¹| ≤
          (1 / 2 : ℝ) *
            ∑ c, 2 * p *
              (Q.mass (c, predictor c) - Q.fst.mass c / p) :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ = (p : ℝ) *
          ((∑ c, Q.mass (c, predictor c)) - 1 / (p : ℝ)) := by
        rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_div,
          Q.fst.sum_mass]
        field_simp [NeZero.ne p]
  refine ⟨predictor, ?_⟩
  have hpNat : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hp : (0 : ℝ) < p := by exact_mod_cast hpNat
  have hmain : δ < (p : ℝ) *
      ((∑ c, Q.mass (c, predictor c)) - 1 / (p : ℝ)) :=
    hδ.trans_le htvUpper
  have hdiv : δ / (p : ℝ) <
      (∑ c, Q.mass (c, predictor c)) - 1 / (p : ℝ) := by
    apply (div_lt_iff₀ hp).2
    simpa [mul_comm] using hmain
  linarith

/-- Repeated triangle inequality along a finite chain. -/
theorem tv_le_sum_range_chain [Fintype α]
    (H : ℕ → FinDist α) (r : ℕ) :
    (H 0).tv (H r) ≤
      ∑ i ∈ Finset.range r, (H i).tv (H (i + 1)) := by
  induction r with
  | zero => simp
  | succ r ih =>
      calc
        (H 0).tv (H (r + 1)) ≤
            (H 0).tv (H r) + (H r).tv (H (r + 1)) :=
          tv_triangle (H 0) (H r) (H (r + 1))
        _ ≤ (∑ i ∈ Finset.range r, (H i).tv (H (i + 1))) +
            (H r).tv (H (r + 1)) := add_le_add ih le_rfl
        _ = ∑ i ∈ Finset.range (r + 1),
            (H i).tv (H (i + 1)) := by
          rw [Finset.sum_range_succ]

/-- If the endpoints of a chain are more than `ε` apart, one of its `r`
steps is more than `ε/r` apart. -/
theorem exists_step_tv_gt [Fintype α]
    (H : ℕ → FinDist α) {r : ℕ} (hr : 0 < r) (ε : ℝ)
    (hend : ε < (H 0).tv (H r)) :
    ∃ i < r, ε / r < (H i).tv (H (i + 1)) := by
  by_contra hnone
  push Not at hnone
  have hsum :
      (∑ i ∈ Finset.range r, (H i).tv (H (i + 1))) ≤ ε := by
    calc
      (∑ i ∈ Finset.range r, (H i).tv (H (i + 1))) ≤
          ∑ _i ∈ Finset.range r, ε / r :=
        Finset.sum_le_sum fun i hi ↦ hnone i (Finset.mem_range.mp hi)
      _ = ε := by
        rw [Finset.sum_const, Finset.card_range]
        simp only [nsmul_eq_mul]
        have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
        field_simp
  exact (not_lt_of_ge ((tv_le_sum_range_chain H r).trans hsum)) hend

end FinDist

end Erdos788


/-! Flattened from Erdos788.Reconstruction. -/


/-!
# Finite Trevisan reconstruction

This module carries out the strong-extractor reconstruction entirely with
`FinDist`.  Code coordinates and seed coordinates are binary, while all
symbols and all fixed-seed maps are over `ZMod p`.
-/

set_option linter.style.haveILetI false

namespace Erdos788

open scoped BigOperators

namespace Reconstruction

local instance reconstructionFintypeCoord {ell r : ℕ}
    {D : SuffixDesign ell r} : Fintype D.Coord :=
  D.instFintypeCoord

local instance reconstructionDecidableEqCoord {ell r : ℕ}
    {D : SuffixDesign ell r} : DecidableEq D.Coord :=
  D.instDecidableEqCoord

/-- Assignments to the coordinates in one design row. -/
abbrev RowAssignment {ell r : ℕ} (D : SuffixDesign ell r) (i : Fin r) :=
  D.row i → Bool

/-- The cardinality equality used to identify a design-row assignment with
a binary code coordinate. -/
theorem card_binaryCoord_eq_rowAssignment {ell r : ℕ}
    (D : SuffixDesign ell r) (i : Fin r) :
    Fintype.card (BinaryCoord ell) = Fintype.card (RowAssignment D i) := by
  letI := D.instFintypeCoord
  letI := D.instDecidableEqCoord
  simp [BinaryCoord, RowAssignment, D.row_card i]

/-- A fixed identification between code coordinates and assignments on row
`i`. -/
noncomputable def rowAssignmentEquiv {ell r : ℕ}
    (D : SuffixDesign ell r) (i : Fin r) :
    BinaryCoord ell ≃ RowAssignment D i := by
  letI := D.instFintypeCoord
  letI := D.instDecidableEqCoord
  exact Fintype.equivOfCardEq (card_binaryCoord_eq_rowAssignment D i)

/-- Restrict a full binary seed to a row and regard it as a code
coordinate. -/
noncomputable def seedCodeCoord {ell r : ℕ}
    (D : SuffixDesign ell r) (i : Fin r)
    (y : D.Coord → Bool) : BinaryCoord ell := by
  letI := D.instFintypeCoord
  letI := D.instDecidableEqCoord
  exact (rowAssignmentEquiv D i).symm (fun c ↦ y c.1)

theorem seedCodeCoord_apply_equiv {ell r : ℕ}
    (D : SuffixDesign ell r) (i : Fin r)
    (y : D.Coord → Bool) (c : D.row i) :
    rowAssignmentEquiv D i (seedCodeCoord D i y) c = y c.1 := by
  letI := D.instFintypeCoord
  letI := D.instDecidableEqCoord
  simp [seedCodeCoord]

/-- Assignments outside one distinguished design row. -/
abbrev OutsideAssignment {ell r : ℕ}
    (D : SuffixDesign ell r) (i : Fin r) :=
  {c : D.Coord // c ∉ D.row i} → Bool

/-- Combine an outside assignment and a row assignment into a full seed. -/
def combineSeed {ell r : ℕ} (D : SuffixDesign ell r) (i : Fin r)
    (a : OutsideAssignment D i) (z : RowAssignment D i) :
    D.Coord → Bool := fun c ↦
  if hc : c ∈ D.row i then z ⟨c, hc⟩ else a ⟨c, hc⟩

@[simp]
theorem combineSeed_apply_mem {ell r : ℕ}
    (D : SuffixDesign ell r) (i : Fin r)
    (a : OutsideAssignment D i) (z : RowAssignment D i)
    {c : D.Coord} (hc : c ∈ D.row i) :
    combineSeed D i a z c = z ⟨c, hc⟩ := by
  simp [combineSeed, hc]

@[simp]
theorem combineSeed_apply_notMem {ell r : ℕ}
    (D : SuffixDesign ell r) (i : Fin r)
    (a : OutsideAssignment D i) (z : RowAssignment D i)
    {c : D.Coord} (hc : c ∉ D.row i) :
    combineSeed D i a z c = a ⟨c, hc⟩ := by
  simp [combineSeed, hc]

/-- Full seeds split exactly into their outside and inside restrictions. -/
def seedSplitEquiv {ell r : ℕ} (D : SuffixDesign ell r) (i : Fin r) :
    (D.Coord → Bool) ≃ OutsideAssignment D i × RowAssignment D i where
  toFun y := (fun c ↦ y c.1, fun c ↦ y c.1)
  invFun q := combineSeed D i q.1 q.2
  left_inv y := by
    funext c
    by_cases hc : c ∈ D.row i <;> simp [combineSeed, hc]
  right_inv q := by
    apply Prod.ext <;> funext c
    · simp [combineSeed, c.2]
    · simp [combineSeed, c.2]

/-- Assignments on the overlap of row `i` with its `j`th predecessor. -/
abbrev OverlapAssignment {ell r : ℕ}
    (D : SuffixDesign ell r) (i : Fin r) (j : Fin i.val) :=
  {c : D.Coord //
    c ∈ D.row i ∩ D.row (priorIndex i j.val)} → Bool

/-- A reconstruction description: the seed outside row `i`, together with
one table for every earlier output coordinate. -/
abbrev Description {p ell r : ℕ} [NeZero p]
    (D : SuffixDesign ell r) (i : Fin r) :=
  OutsideAssignment D i ×
    ((j : Fin i.val) → OverlapAssignment D i j → ZMod p)

theorem sum_overlap_powers_le {ell r : ℕ}
    (D : SuffixDesign ell r) (i : Fin r) :
    (∑ j : Fin i.val,
      2 ^ (D.row i ∩ D.row (priorIndex i j.val)).card) ≤ r - 1 := by
  letI := D.instFintypeCoord
  letI := D.instDecidableEqCoord
  have hterm (j : ℕ) :
      2 ^ (D.row i ∩ D.row (priorIndex i j)).card =
        overlapCost (D.row i) (D.row (priorIndex i j)) + 1 := by
    rw [overlapCost]
    have hpos : 0 < 2 ^ (D.row i ∩ D.row (priorIndex i j)).card := by positivity
    omega
  have hsum :
      (∑ j ∈ Finset.range i.val,
          2 ^ (D.row i ∩ D.row (priorIndex i j)).card) =
        (∑ j ∈ Finset.range i.val,
          overlapCost (D.row i) (D.row (priorIndex i j))) + i.val := by
    simp_rw [hterm, Finset.sum_add_distrib]
    simp
  have hsumFin :
      (∑ j : Fin i.val,
        2 ^ (D.row i ∩ D.row (priorIndex i j.val)).card) =
        (∑ j ∈ Finset.range i.val,
          overlapCost (D.row i) (D.row (priorIndex i j))) + i.val := by
    simpa only [← Fin.sum_univ_eq_sum_range] using hsum
  rw [hsumFin]
  have hs := D.suffix_slack i
  omega

theorem card_outsideAssignment_le {ell r : ℕ}
    (D : SuffixDesign ell r) (i : Fin r) :
    Fintype.card (OutsideAssignment D i) ≤ 2 ^ D.coordCard := by
  letI := D.instFintypeCoord
  letI := D.instDecidableEqCoord
  simp only [OutsideAssignment, Fintype.card_fun, Fintype.card_bool]
  apply Nat.pow_le_pow_right (by omega)
  exact Fintype.card_subtype_le _

theorem card_description_le {p ell r : ℕ} [Fact p.Prime]
    (D : SuffixDesign ell r) (i : Fin r) :
    Fintype.card (Description (p := p) D i) ≤
      2 ^ D.coordCard * p ^ (r - 1) := by
  letI := D.instFintypeCoord
  letI := D.instDecidableEqCoord
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hovercard (j : Fin i.val) :
      Fintype.card (OverlapAssignment D i j) =
        2 ^ (D.row i ∩ D.row (priorIndex i j.val)).card := by
    simp only [OverlapAssignment, Fintype.card_fun, Fintype.card_bool]
    congr 1
    rw [Fintype.card_subtype]
    congr 1
    ext c
    simp
  have hinner (j : Fin i.val) :
      Fintype.card (OverlapAssignment D i j → ZMod p) =
        p ^ (2 ^ (D.row i ∩ D.row (priorIndex i j.val)).card) := by
    rw [Fintype.card_fun, ZMod.card, hovercard]
  have htable :
      Fintype.card ((j : Fin i.val) →
        OverlapAssignment D i j → ZMod p) =
        p ^ (∑ j : Fin i.val,
          2 ^ (D.row i ∩ D.row (priorIndex i j.val)).card) := by
    rw [Fintype.card_pi]
    simp_rw [hinner]
    simpa using Finset.prod_pow_eq_pow_sum
      (Finset.univ : Finset (Fin i.val))
      (fun j ↦ 2 ^ (D.row i ∩ D.row (priorIndex i j.val)).card) p
  rw [Fintype.card_prod, htable]
  exact Nat.mul_le_mul (card_outsideAssignment_le D i)
    (Nat.pow_le_pow_right hp (sum_overlap_powers_le D i))

/-- Restrict a row assignment to one of its predecessor overlaps. -/
def overlapRestriction {ell r : ℕ} (D : SuffixDesign ell r)
    (i : Fin r) (j : Fin i.val) (z : RowAssignment D i) :
    OverlapAssignment D i j := fun c ↦ z ⟨c.1, (Finset.mem_inter.mp c.2).1⟩

/-- Extend overlap bits to the distinguished row, using `false` away from
the predecessor row.  Values away from the overlap will not affect that
predecessor's code coordinate. -/
def extendOverlap {ell r : ℕ} (D : SuffixDesign ell r)
    (i : Fin r) (j : Fin i.val) (w : OverlapAssignment D i j) :
    RowAssignment D i := fun c ↦
  if hc : c.1 ∈ D.row (priorIndex i j.val) then
    w ⟨c.1, Finset.mem_inter.mpr ⟨c.2, hc⟩⟩
  else false

@[simp]
theorem extendOverlap_overlapRestriction_apply
    {ell r : ℕ} (D : SuffixDesign ell r)
    (i : Fin r) (j : Fin i.val) (z : RowAssignment D i)
    (c : D.row i) (hc : c.1 ∈ D.row (priorIndex i j.val)) :
    extendOverlap D i j (overlapRestriction D i j z) c = z c := by
  simp [extendOverlap, overlapRestriction, hc]

theorem seedCodeCoord_eq_of_eq_on_row {ell r : ℕ}
    (D : SuffixDesign ell r) (i : Fin r)
    {y y' : D.Coord → Bool}
    (h : ∀ c ∈ D.row i, y c = y' c) :
    seedCodeCoord D i y = seedCodeCoord D i y' := by
  letI := D.instFintypeCoord
  letI := D.instDecidableEqCoord
  apply (rowAssignmentEquiv D i).injective
  funext c
  simp only [seedCodeCoord_apply_equiv]
  exact h c.1 c.2

/-- The genuine earlier-output table associated with `x` and a fixed
outside assignment. -/
noncomputable def actualPriorTable
    {p r : ℕ} [Fact p.Prime] {η : ℝ}
    (C : ShortLinearCode p (2 * r) η)
    (D : SuffixDesign C.ell r) (i : Fin r)
    (x : FFVec p (2 * r)) (a : OutsideAssignment D i)
    (j : Fin i.val) : OverlapAssignment D i j → ZMod p :=
  fun w ↦ C.encoder x
    (seedCodeCoord D (priorIndex i j.val)
      (combineSeed D i a (extendOverlap D i j w)))

theorem actualPriorTable_correct
    {p r : ℕ} [Fact p.Prime] {η : ℝ}
    (C : ShortLinearCode p (2 * r) η)
    (D : SuffixDesign C.ell r) (i : Fin r)
    (x : FFVec p (2 * r)) (a : OutsideAssignment D i)
    (j : Fin i.val) (z : RowAssignment D i) :
    actualPriorTable C D i x a j (overlapRestriction D i j z) =
      C.encoder x
        (seedCodeCoord D (priorIndex i j.val) (combineSeed D i a z)) := by
  apply congrArg (fun q ↦ C.encoder x q)
  apply seedCodeCoord_eq_of_eq_on_row
  intro c hcPrior
  by_cases hcI : c ∈ D.row i
  · rw [combineSeed_apply_mem D i a _ hcI,
      combineSeed_apply_mem D i a z hcI]
    exact extendOverlap_overlapRestriction_apply D i j z ⟨c, hcI⟩ hcPrior
  · rw [combineSeed_apply_notMem D i a _ hcI,
      combineSeed_apply_notMem D i a z hcI]

/-- Earlier Trevisan outputs, represented as a prefix tuple. -/
noncomputable def outputPrefix
    {p r : ℕ} [Fact p.Prime] {η : ℝ}
    (C : ShortLinearCode p (2 * r) η)
    (D : SuffixDesign C.ell r) (i : Fin r)
    (x : FFVec p (2 * r)) (y : D.Coord → Bool) :
    Fin i.val → ZMod p := fun j ↦
  C.encoder x (seedCodeCoord D (priorIndex i j.val) y)

/-- The received word decoded from one reconstruction description. -/
noncomputable def descriptionWord
    {p r : ℕ} [Fact p.Prime] {η : ℝ}
    (C : ShortLinearCode p (2 * r) η)
    (D : SuffixDesign C.ell r) (i : Fin r)
    (predictor : (D.Coord → Bool) →
      (Fin i.val → ZMod p) → ZMod p)
    (desc : Description (p := p) D i) :
    BinaryCoord C.ell → ZMod p := fun q ↦
  let z := rowAssignmentEquiv D i q
  let y := combineSeed D i desc.1 z
  predictor y (fun j ↦ desc.2 j (overlapRestriction D i j z))

theorem descriptionWord_actual
    {p r : ℕ} [Fact p.Prime] {η : ℝ}
    (C : ShortLinearCode p (2 * r) η)
    (D : SuffixDesign C.ell r) (i : Fin r)
    (predictor : (D.Coord → Bool) →
      (Fin i.val → ZMod p) → ZMod p)
    (x : FFVec p (2 * r)) (a : OutsideAssignment D i)
    (q : BinaryCoord C.ell) :
    descriptionWord C D i predictor
        (a, actualPriorTable C D i x a) q =
      predictor
        (combineSeed D i a (rowAssignmentEquiv D i q))
        (outputPrefix C D i x
          (combineSeed D i a (rowAssignmentEquiv D i q))) := by
  let z := rowAssignmentEquiv D i q
  let y := combineSeed D i a z
  change predictor y
      (fun j ↦ actualPriorTable C D i x a j
        (overlapRestriction D i j z)) =
    predictor y (fun j ↦
      C.encoder x (seedCodeCoord D (priorIndex i j.val) y))
  apply congrArg (predictor y)
  funext j
  exact actualPriorTable_correct C D i x a j z

/-- The fixed-seed Trevisan output map. -/
noncomputable def fixedSeedMap
    {p r : ℕ} [Fact p.Prime] {η : ℝ}
    (C : ShortLinearCode p (2 * r) η)
    (D : SuffixDesign C.ell r)
    (y : D.Coord → Bool) :
    FFVec p (2 * r) →ₗ[ZMod p] FFVec p r where
  toFun x i := C.encoder x (seedCodeCoord D i y)
  map_add' x x' := by
    funext i
    exact congrFun (C.encoder.map_add x x')
      (seedCodeCoord D i y)
  map_smul' a x := by
    funext i
    exact congrFun (C.encoder.map_smul a x)
      (seedCodeCoord D i y)

end Reconstruction

end Erdos788


/-! Flattened from Erdos788.SequentialPrediction. -/


/-!
# Sequential prediction from total variation

This file packages the finite hybrid argument for a tuple over `ZMod p`.
A context is retained throughout the chain, so it can later carry the
Trevisan seed.
-/

namespace Erdos788

open scoped BigOperators

namespace FinDist

/-- The first `i` entries of a finite tuple. -/
def tuplePrefix {p r : ℕ} (i : Fin r) (z : FFVec p r) :
    FFVec p i.val := fun j ↦
  z (Fin.castLE (Nat.le_of_lt i.isLt) j)

/-- Split a tuple at its last entry while retaining an external context. -/
def lastSplitEquiv (Context : Type*) (p n : ℕ) :
    Context × FFVec p (n + 1) ≃
      (Context × FFVec p n) × ZMod p :=
  (Equiv.prodCongr (Equiv.refl Context)
    (Fin.succFunEquiv (ZMod p) n)).trans
      (Equiv.prodAssoc Context (FFVec p n) (ZMod p)).symm

@[simp]
theorem lastSplitEquiv_apply
    {Context : Type*} {p n : ℕ}
    (w : Context × FFVec p (n + 1)) :
    lastSplitEquiv Context p n w =
      ((w.1, fun j ↦ w.2 j.castSucc), w.2 (Fin.last n)) := by
  rfl

/-- Pushforward expectation identity for a finite distribution. -/
theorem sum_map_mass_mul'
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (P : FinDist A) (f : A → B) (g : B → ℝ) :
    ∑ b, (P.map f).mass b * g b = ∑ a, P.mass a * g (f a) := by
  simp only [map_mass, Finset.sum_mul]
  calc
    (∑ b, ∑ a with f a = b, P.mass a * g b) =
        ∑ b, ∑ a with f a = b, P.mass a * g (f a) := by
      apply Finset.sum_congr rfl
      intro b _hb
      apply Finset.sum_congr rfl
      intro a ha
      rw [(Finset.mem_filter.mp ha).2]
    _ = ∑ a, P.mass a * g (f a) := by
      simpa using (Finset.sum_fiberwise_eq_sum_filter
        (Finset.univ : Finset A) (Finset.univ : Finset B) f
        (fun a ↦ P.mass a * g (f a)))

/-- Splitting the last entry sends a context times a uniform tuple to the
corresponding three-factor product. -/
theorem map_context_uniform_lastSplit
    {Context : Type*} [Fintype Context] [DecidableEq Context]
    {p n : ℕ} [Fact p.Prime]
    (C : FinDist Context) :
    (C.prod (FinDist.uniform (FFVec p (n + 1)))).map
        (lastSplitEquiv Context p n) =
      (C.prod (FinDist.uniform (FFVec p n))).prod
        (FinDist.uniform (ZMod p)) := by
  ext q
  let e := lastSplitEquiv Context p n
  let w := e.symm q
  have hw : e w = q := e.apply_symm_apply q
  rw [← hw, map_equiv_mass]
  simp only [prod_mass, uniform_mass, fintypeCard_ffVec, ZMod.card,
    e, lastSplitEquiv_apply]
  rw [pow_succ]
  push_cast
  field_simp [NeZero.ne p]

/-- The prefix marginal obtained after the last-coordinate split is the
pushforward by the literal prefix map. -/
theorem fst_map_lastSplit
    {Context : Type*} [Fintype Context] [DecidableEq Context]
    {p n : ℕ} [Fact p.Prime]
    (P : FinDist (Context × FFVec p (n + 1))) :
    (P.map (lastSplitEquiv Context p n)).fst =
      P.map (fun w ↦ (w.1, fun j ↦ w.2 j.castSucc)) := by
  rw [fst, map_map]
  apply congrArg (fun f ↦ P.map f)
  funext w
  rfl

/-- Splitting off tuple entries does not alter the original context
marginal. -/
theorem fst_fst_map_lastSplit
    {Context : Type*} [Fintype Context] [DecidableEq Context]
    {p n : ℕ} [Fact p.Prime]
    (P : FinDist (Context × FFVec p (n + 1))) :
    ((P.map (lastSplitEquiv Context p n)).fst).fst = P.fst := by
  rw [fst_map_lastSplit, fst, map_map]
  apply congrArg (fun f ↦ P.map f)
  funext w
  rfl

@[simp]
theorem tuplePrefix_castSucc {p n : ℕ}
    (i : Fin n) (z : FFVec p (n + 1)) :
    tuplePrefix i.castSucc z =
      tuplePrefix i (fun j ↦ z j.castSucc) := by
  funext j
  rfl

@[simp]
theorem tuplePrefix_last {p n : ℕ} (z : FFVec p (n + 1)) :
    tuplePrefix (Fin.last n) z = fun j ↦ z j.castSucc := by
  funext j
  rfl

/-- A law on `Context × (Fin 0 → A)` is completely determined by its
context marginal. -/
theorem eq_fst_prod_uniform_finZero
    {Context A : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype A] [Nonempty A]
    (P : FinDist (Context × (Fin 0 → A))) :
    P = P.fst.prod (FinDist.uniform (Fin 0 → A)) := by
  ext w
  have hmass := P.fst_mass w.1
  have hcard : Fintype.card (Fin 0 → A) = 1 := by simp
  have hsum : (∑ u : Fin 0 → A, P.mass (w.1, u)) =
      P.mass w := by
    classical
    simp [Subsingleton.elim (α := Fin 0 → A) _ w.2]
  simp only [prod_mass, uniform_mass, hcard, Nat.cast_one, inv_one, mul_one]
  exact (hmass.trans hsum).symm

/-- Selecting one symbol in every context is the same as summing the
corresponding indicator over the whole joint law. -/
theorem sum_selected_eq_sum_indicator
    {Context : Type*} [Fintype Context]
    {p : ℕ} [NeZero p]
    (Q : FinDist (Context × ZMod p))
    (predictor : Context → ZMod p) :
    (∑ c, Q.mass (c, predictor c)) =
      ∑ q, Q.mass q *
        (if predictor q.1 = q.2 then (1 : ℝ) else 0) := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro c _hc
  classical
  simp

/-- The selected-mass expression after a last-coordinate split, pulled
back to the original tuple. -/
theorem sum_selected_map_lastSplit
    {Context : Type*} [Fintype Context] [DecidableEq Context]
    {p n : ℕ} [Fact p.Prime]
    (P : FinDist (Context × FFVec p (n + 1)))
    (predictor : Context × FFVec p n → ZMod p) :
    (∑ c, (P.map (lastSplitEquiv Context p n)).mass
        (c, predictor c)) =
      ∑ w, P.mass w *
        (if predictor (w.1, fun j ↦ w.2 j.castSucc) =
            w.2 (Fin.last n) then (1 : ℝ) else 0) := by
  rw [sum_selected_eq_sum_indicator]
  exact sum_map_mass_mul' P (lastSplitEquiv Context p n)
    (fun q ↦ if predictor q.1 = q.2 then (1 : ℝ) else 0)

/-- Pull a success event on a prefix marginal back to the original
tuple. -/
theorem sum_prefixEvent_map_lastSplit
    {Context : Type*} [Fintype Context] [DecidableEq Context]
    {p n : ℕ} [Fact p.Prime]
    (P : FinDist (Context × FFVec p (n + 1)))
    (i : Fin n) (predictor : Context × FFVec p i.val → ZMod p) :
    (∑ u, (P.map (lastSplitEquiv Context p n)).fst.mass u *
        (if predictor (u.1, tuplePrefix i u.2) = u.2 i
          then (1 : ℝ) else 0)) =
      ∑ w, P.mass w *
        (if predictor (w.1, tuplePrefix i.castSucc w.2) =
            w.2 i.castSucc then (1 : ℝ) else 0) := by
  rw [fst_map_lastSplit]
  have h := sum_map_mass_mul' P
    (fun w ↦ (w.1, fun j ↦ w.2 j.castSucc))
    (fun u ↦ if predictor (u.1, tuplePrefix i u.2) = u.2 i
      then (1 : ℝ) else 0)
  simpa only [tuplePrefix_castSucc] using h

/-- A finite chain-rule form of the hybrid argument.  If a tuple remains
far from uniform after conditioning on an arbitrary context, then one
coordinate is predictably biased from the context and all preceding
coordinates. -/
theorem exists_sequential_predictor_of_tv_gt
    {Context : Type*} [Fintype Context] [DecidableEq Context]
    {p r : ℕ} [Fact p.Prime]
    (P : FinDist (Context × FFVec p r))
    (δ : ℝ) (hr : 0 < r) (hδ : 0 < δ)
    (hfar : δ < P.tv (P.fst.prod (FinDist.uniform (FFVec p r)))) :
    ∃ i : Fin r,
      ∃ predictor : Context × FFVec p i.val → ZMod p,
        1 / (p : ℝ) + δ / ((r : ℝ) * p) <
          ∑ w, P.mass w *
            (if predictor (w.1, tuplePrefix i w.2) = w.2 i
              then (1 : ℝ) else 0) := by
  induction r generalizing δ with
  | zero => omega
  | succ n ih =>
      let e := lastSplitEquiv Context p n
      let Q : FinDist ((Context × FFVec p n) × ZMod p) := P.map e
      let U := FinDist.uniform (ZMod p)
      let prefixUniform := P.fst.prod (FinDist.uniform (FFVec p n))
      have hfarQ : δ < Q.tv (prefixUniform.prod U) := by
        dsimp only [Q, e, prefixUniform, U]
        rw [← map_context_uniform_lastSplit P.fst]
        rw [tv_map_equiv]
        exact hfar
      have htriangle : Q.tv (prefixUniform.prod U) ≤
          Q.tv (Q.fst.prod U) + Q.fst.tv prefixUniform := by
        have h := tv_triangle Q (Q.fst.prod U) (prefixUniform.prod U)
        rwa [tv_prod_right] at h
      by_cases hn : n = 0
      · subst n
        have hprefixZero : Q.fst.tv prefixUniform = 0 := by
          have hQ := eq_fst_prod_uniform_finZero Q.fst
          have hff := fst_fst_map_lastSplit P
          change Q.fst.fst = P.fst at hff
          dsimp only [prefixUniform]
          rw [hQ, hff, tv_self]
        have hlast : δ < Q.tv (Q.fst.prod U) := by
          linarith
        obtain ⟨predictor, hpredictor⟩ :=
          exists_predictor_of_tv_gt Q δ hlast
        refine ⟨Fin.last 0, predictor, ?_⟩
        rw [show ((0 + 1 : ℕ) : ℝ) = 1 by norm_num]
        simp only [one_mul]
        calc
          1 / (p : ℝ) + δ / p <
              ∑ c, (P.map (lastSplitEquiv Context p 0)).mass
                (c, predictor c) := by
            simpa only [Q, e] using hpredictor
          _ = ∑ w, P.mass w *
              (if predictor (w.1, tuplePrefix (Fin.last 0) w.2) =
                w.2 (Fin.last 0) then (1 : ℝ) else 0) := by
            rw [sum_selected_map_lastSplit]
            simp only [tuplePrefix_last]
            rfl
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        by_cases hlast : δ / (n + 1 : ℝ) < Q.tv (Q.fst.prod U)
        · obtain ⟨predictor, hpredictor⟩ :=
            exists_predictor_of_tv_gt Q (δ / (n + 1 : ℝ)) hlast
          refine ⟨Fin.last n, predictor, ?_⟩
          simp only [Nat.cast_add, Nat.cast_one]
          have hconst :
              1 / (p : ℝ) + δ / ((n + 1 : ℝ) * p) =
                1 / (p : ℝ) + (δ / (n + 1 : ℝ)) / p := by
            field_simp [NeZero.ne p]
          calc
            1 / (p : ℝ) + δ / ((n + 1 : ℝ) * p) =
                1 / (p : ℝ) + (δ / (n + 1 : ℝ)) / p := hconst
            _ < ∑ c, (P.map (lastSplitEquiv Context p n)).mass
                  (c, predictor c) := by
              simpa only [Q, e] using hpredictor
            _ = ∑ w, P.mass w *
                (if predictor (w.1, tuplePrefix (Fin.last n) w.2) =
                  w.2 (Fin.last n) then (1 : ℝ) else 0) := by
              rw [sum_selected_map_lastSplit]
              simp only [tuplePrefix_last]
              rfl
        · have hlastLe : Q.tv (Q.fst.prod U) ≤
              δ / (n + 1 : ℝ) := le_of_not_gt hlast
          have hsplit : δ / (n + 1 : ℝ) +
              δ * n / (n + 1 : ℝ) = δ := by
            have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
            field_simp
            ring
          have hprefix : δ * n / (n + 1 : ℝ) <
              Q.fst.tv prefixUniform := by
            nlinarith
          have hδprefix : 0 < δ * n / (n + 1 : ℝ) := by positivity
          have hQfst : Q.fst.fst = P.fst := by
            exact fst_fst_map_lastSplit P
          have hprefix' : δ * n / (n + 1 : ℝ) <
              Q.fst.tv (Q.fst.fst.prod
                (FinDist.uniform (FFVec p n))) := by
            rwa [hQfst]
          obtain ⟨i, predictor, hpredictor⟩ :=
            ih Q.fst (δ * n / (n + 1 : ℝ)) hnpos hδprefix hprefix'
          refine ⟨i.castSucc, predictor, ?_⟩
          simp only [Nat.cast_add, Nat.cast_one]
          have hadv :
              (δ * n / (n + 1 : ℝ)) / ((n : ℝ) * p) =
                δ / ((n + 1 : ℝ) * p) := by
            field_simp [NeZero.ne p, Nat.ne_of_gt hnpos]
          calc
            1 / (p : ℝ) + δ / ((n + 1 : ℝ) * p) =
                1 / (p : ℝ) +
                  (δ * n / (n + 1 : ℝ)) / ((n : ℝ) * p) := by
              rw [hadv]
            _ < ∑ u, Q.fst.mass u *
                (if predictor (u.1, tuplePrefix i u.2) = u.2 i
                  then (1 : ℝ) else 0) := hpredictor
            _ = ∑ w, P.mass w *
                (if predictor (w.1, tuplePrefix i.castSucc w.2) =
                  w.2 i.castSucc then (1 : ℝ) else 0) := by
              simpa only [Q, e] using
                (sum_prefixEvent_map_lastSplit P i predictor)

end FinDist

end Erdos788


/-! Flattened from Erdos788.TrevisanRaw. -/


/-!
# The raw Trevisan extractor family

This file combines the finite hybrid/prediction argument with the
reconstruction data from `Reconstruction.lean`.
-/

namespace Erdos788

open scoped BigOperators

namespace Reconstruction

local instance rawFintypeCoord {ell r : ℕ}
    {D : SuffixDesign ell r} : Fintype D.Coord :=
  D.instFintypeCoord

local instance rawDecidableEqCoord {ell r : ℕ}
    {D : SuffixDesign ell r} : DecidableEq D.Coord :=
  D.instDecidableEqCoord

/-- Summing a test function against a pushforward is the same as summing
its pullback against the original finite distribution. -/
theorem sum_map_mass_mul
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (P : FinDist A) (f : A → B) (g : B → ℝ) :
    ∑ b, (P.map f).mass b * g b = ∑ a, P.mass a * g (f a) := by
  simp only [FinDist.map_mass, Finset.sum_mul]
  calc
    (∑ b, ∑ a with f a = b, P.mass a * g b) =
        ∑ b, ∑ a with f a = b, P.mass a * g (f a) := by
      apply Finset.sum_congr rfl
      intro b _hb
      apply Finset.sum_congr rfl
      intro a ha
      rw [(Finset.mem_filter.mp ha).2]
    _ = ∑ a, P.mass a * g (f a) := by
      simpa using (Finset.sum_fiberwise_eq_sum_filter
        (Finset.univ : Finset A) (Finset.univ : Finset B) f
        (fun a ↦ P.mass a * g (f a)))

/-- The joint law of a uniform seed and the extractor output on source
`P`. -/
noncomputable def seedOutputDist
    {p r : ℕ} [Fact p.Prime] {η : ℝ}
    (C : ShortLinearCode p (2 * r) η)
    (D : SuffixDesign C.ell r)
    (P : FinDist (FFVec p (2 * r))) :
    FinDist ((D.Coord → Bool) × FFVec p r) where
  mass := fun yz ↦
    (FinDist.uniform (D.Coord → Bool)).mass yz.1 *
      (P.map (fixedSeedMap C D yz.1)).mass yz.2
  nonneg := fun yz ↦ mul_nonneg
    ((FinDist.uniform (D.Coord → Bool)).nonneg yz.1)
    ((P.map (fixedSeedMap C D yz.1)).nonneg yz.2)
  sum_mass := by
    rw [Fintype.sum_prod_type]
    calc
      (∑ y, ∑ z,
          (FinDist.uniform (D.Coord → Bool)).mass y *
            (P.map (fixedSeedMap C D y)).mass z) =
          ∑ y, (FinDist.uniform (D.Coord → Bool)).mass y *
            ∑ z, (P.map (fixedSeedMap C D y)).mass z := by
        apply Finset.sum_congr rfl
        intro y _hy
        rw [Finset.mul_sum]
      _ = 1 := by
        simp only [FinDist.sum_mass, mul_one]

@[simp]
theorem seedOutputDist_mass
    {p r : ℕ} [Fact p.Prime] {η : ℝ}
    (C : ShortLinearCode p (2 * r) η)
    (D : SuffixDesign C.ell r)
    (P : FinDist (FFVec p (2 * r)))
    (yz : (D.Coord → Bool) × FFVec p r) :
    (seedOutputDist C D P).mass yz =
      (FinDist.uniform (D.Coord → Bool)).mass yz.1 *
        (P.map (fixedSeedMap C D yz.1)).mass yz.2 :=
  rfl

/-- The seed marginal of the joint seed/output law is uniform. -/
theorem seedOutputDist_fst
    {p r : ℕ} [Fact p.Prime] {η : ℝ}
    (C : ShortLinearCode p (2 * r) η)
    (D : SuffixDesign C.ell r)
    (P : FinDist (FFVec p (2 * r))) :
    (seedOutputDist C D P).fst =
      FinDist.uniform (D.Coord → Bool) := by
  ext y
  rw [FinDist.fst_mass]
  simp only [seedOutputDist_mass]
  rw [← Finset.mul_sum, FinDist.sum_mass, mul_one]

/-- Averaging the fixed-seed total variations is exactly the total
variation of the joint seed/output law. -/
theorem average_tv_eq_seedOutputDist_tv
    {p r : ℕ} [Fact p.Prime] {η : ℝ}
    (C : ShortLinearCode p (2 * r) η)
    (D : SuffixDesign C.ell r)
    (P : FinDist (FFVec p (2 * r))) :
    (Fintype.card (D.Coord → Bool) : ℝ)⁻¹ *
        ∑ y : D.Coord → Bool,
          (P.map (fixedSeedMap C D y)).tv
            (FinDist.uniform (FFVec p r)) =
      (seedOutputDist C D P).tv
        ((FinDist.uniform (D.Coord → Bool)).prod
          (FinDist.uniform (FFVec p r))) := by
  simp only [FinDist.tv]
  rw [Fintype.sum_prod_type]
  simp only [seedOutputDist_mass, FinDist.prod_mass, FinDist.uniform_mass]
  have hseed : 0 ≤
      (Fintype.card (D.Coord → Bool) : ℝ)⁻¹ := by positivity
  simp_rw [← mul_sub, abs_mul, abs_of_nonneg hseed]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _hy
  apply Finset.sum_congr rfl
  intro z _hz
  ring

@[simp]
theorem tuplePrefix_fixedSeedMap
    {p r : ℕ} [Fact p.Prime] {η : ℝ}
    (C : ShortLinearCode p (2 * r) η)
    (D : SuffixDesign C.ell r)
    (i : Fin r) (x : FFVec p (2 * r))
    (y : D.Coord → Bool) :
    FinDist.tuplePrefix i (fixedSeedMap C D y x) =
      outputPrefix C D i x y := by
  funext j
  unfold FinDist.tuplePrefix fixedSeedMap outputPrefix
  apply congrArg (fun k : Fin r ↦
    C.encoder x (seedCodeCoord D k y))
  apply Fin.ext
  rw [priorIndex_val_of_lt i j.isLt]
  rfl

/-- The success indicator of a sequential predictor on input `x` and seed
`y`. -/
noncomputable def predictorSuccess
    {p r : ℕ} [Fact p.Prime] {η : ℝ}
    (C : ShortLinearCode p (2 * r) η)
    (D : SuffixDesign C.ell r) (i : Fin r)
    (predictor : (D.Coord → Bool) × FFVec p i.val → ZMod p)
    (x : FFVec p (2 * r)) (y : D.Coord → Bool) : ℝ :=
  if predictor (y, outputPrefix C D i x y) =
      C.encoder x (seedCodeCoord D i y) then 1 else 0

/-- Success probability of a predictor over the uniform design seed. -/
noncomputable def predictorSuccessRate
    {p r : ℕ} [Fact p.Prime] {η : ℝ}
    (C : ShortLinearCode p (2 * r) η)
    (D : SuffixDesign C.ell r) (i : Fin r)
    (predictor : (D.Coord → Bool) × FFVec p i.val → ZMod p)
    (x : FFVec p (2 * r)) : ℝ :=
  (Fintype.card (D.Coord → Bool) : ℝ)⁻¹ *
    ∑ y, predictorSuccess C D i predictor x y

/-- The sequential success expression for the joint seed/output law is the
source average of the per-input seed success rates. -/
theorem sequential_sum_eq_weighted_successRate
    {p r : ℕ} [Fact p.Prime] {η : ℝ}
    (C : ShortLinearCode p (2 * r) η)
    (D : SuffixDesign C.ell r) (i : Fin r)
    (predictor : (D.Coord → Bool) × FFVec p i.val → ZMod p)
    (P : FinDist (FFVec p (2 * r))) :
    (∑ w, (seedOutputDist C D P).mass w *
        (if predictor (w.1, FinDist.tuplePrefix i w.2) = w.2 i
          then (1 : ℝ) else 0)) =
      ∑ x, P.mass x * predictorSuccessRate C D i predictor x := by
  rw [Fintype.sum_prod_type]
  simp only [seedOutputDist_mass, FinDist.uniform_mass]
  have hy' (y : D.Coord → Bool) :
      (∑ z, (P.map (fixedSeedMap C D y)).mass z *
          (if predictor (y, FinDist.tuplePrefix i z) = z i
            then (1 : ℝ) else 0)) =
        ∑ x, P.mass x * predictorSuccess C D i predictor x y := by
    rw [sum_map_mass_mul]
    apply Finset.sum_congr rfl
    intro x _hx
    simp only [tuplePrefix_fixedSeedMap]
    rfl
  unfold predictorSuccessRate
  calc
    (∑ y, ∑ z,
        ((Fintype.card (D.Coord → Bool) : ℝ)⁻¹ *
          (P.map (fixedSeedMap C D y)).mass z) *
          (if predictor (y, FinDist.tuplePrefix i z) = z i
            then (1 : ℝ) else 0)) =
      ∑ y, (Fintype.card (D.Coord → Bool) : ℝ)⁻¹ *
        ∑ z, (P.map (fixedSeedMap C D y)).mass z *
          (if predictor (y, FinDist.tuplePrefix i z) = z i
            then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro y _hy
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _hz
      ring
    _ = ∑ y, (Fintype.card (D.Coord → Bool) : ℝ)⁻¹ *
        ∑ x, P.mass x * predictorSuccess C D i predictor x y := by
      apply Finset.sum_congr rfl
      intro y _hy
      rw [hy']
    _ = ∑ x, P.mass x *
        ((Fintype.card (D.Coord → Bool) : ℝ)⁻¹ *
          ∑ y, predictorSuccess C D i predictor x y) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _hx
      apply Finset.sum_congr rfl
      intro y _hy
      ring

theorem predictorSuccessRate_nonneg
    {p r : ℕ} [Fact p.Prime] {η : ℝ}
    (C : ShortLinearCode p (2 * r) η)
    (D : SuffixDesign C.ell r) (i : Fin r)
    (predictor : (D.Coord → Bool) × FFVec p i.val → ZMod p)
    (x : FFVec p (2 * r)) :
    0 ≤ predictorSuccessRate C D i predictor x := by
  unfold predictorSuccessRate
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro y _hy
  unfold predictorSuccess
  split <;> norm_num

theorem predictorSuccessRate_le_one
    {p r : ℕ} [Fact p.Prime] {η : ℝ}
    (C : ShortLinearCode p (2 * r) η)
    (D : SuffixDesign C.ell r) (i : Fin r)
    (predictor : (D.Coord → Bool) × FFVec p i.val → ZMod p)
    (x : FFVec p (2 * r)) :
    predictorSuccessRate C D i predictor x ≤ 1 := by
  have hpoint : ∀ y : D.Coord → Bool,
      predictorSuccess C D i predictor x y ≤ 1 := by
    intro y
    unfold predictorSuccess
    split <;> norm_num
  have hsum : (∑ y, predictorSuccess C D i predictor x y) ≤
      ∑ _y : D.Coord → Bool, (1 : ℝ) :=
    Finset.sum_le_sum fun y _hy ↦ hpoint y
  unfold predictorSuccessRate
  have hcard : (0 : ℝ) < Fintype.card (D.Coord → Bool) := by
    exact_mod_cast Fintype.card_pos
  calc
    (Fintype.card (D.Coord → Bool) : ℝ)⁻¹ *
        ∑ y, predictorSuccess C D i predictor x y ≤
      (Fintype.card (D.Coord → Bool) : ℝ)⁻¹ *
        ∑ _y : D.Coord → Bool, (1 : ℝ) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 1 := by simp

/-- Inputs whose predictor succeeds with advantage more than `η`. -/
noncomputable def badInputs
    {p r : ℕ} [Fact p.Prime] {η : ℝ}
    (C : ShortLinearCode p (2 * r) η)
    (D : SuffixDesign C.ell r) (i : Fin r)
    (predictor : (D.Coord → Bool) × FFVec p i.val → ZMod p) :
    Finset (FFVec p (2 * r)) := by
  classical
  exact Finset.univ.filter fun x ↦
    1 / (p : ℝ) + η < predictorSuccessRate C D i predictor x

/-- If the source-average success advantage is more than `2η`, the bad
inputs carry mass more than `η`. -/
theorem eta_lt_mass_badInputs
    {p r : ℕ} [Fact p.Prime] {η : ℝ} (hη : 0 < η)
    (C : ShortLinearCode p (2 * r) η)
    (D : SuffixDesign C.ell r) (i : Fin r)
    (predictor : (D.Coord → Bool) × FFVec p i.val → ZMod p)
    (P : FinDist (FFVec p (2 * r)))
    (havg : 1 / (p : ℝ) + 2 * η <
      ∑ x, P.mass x * predictorSuccessRate C D i predictor x) :
    η < ∑ x ∈ badInputs C D i predictor, P.mass x := by
  classical
  have hp0 : (0 : ℝ) < p := by
    exact_mod_cast (Fact.out : p.Prime).pos
  have hpoint (x : FFVec p (2 * r)) :
      predictorSuccessRate C D i predictor x ≤
        1 / (p : ℝ) + η +
          (if x ∈ badInputs C D i predictor then (1 : ℝ) else 0) := by
    by_cases hx : x ∈ badInputs C D i predictor
    · rw [if_pos hx]
      have hrate := predictorSuccessRate_le_one C D i predictor x
      have hbase : 0 ≤ 1 / (p : ℝ) + η := by positivity
      linarith
    · rw [if_neg hx]
      have hnot : ¬(1 / (p : ℝ) + η <
          predictorSuccessRate C D i predictor x) := by
        simpa [badInputs] using hx
      linarith
  have hweighted :
      (∑ x, P.mass x * predictorSuccessRate C D i predictor x) ≤
        1 / (p : ℝ) + η +
          ∑ x ∈ badInputs C D i predictor, P.mass x := by
    calc
      (∑ x, P.mass x * predictorSuccessRate C D i predictor x) ≤
          ∑ x, P.mass x *
            (1 / (p : ℝ) + η +
              (if x ∈ badInputs C D i predictor then (1 : ℝ) else 0)) :=
        Finset.sum_le_sum fun x _hx ↦
          mul_le_mul_of_nonneg_left (hpoint x) (P.nonneg x)
      _ = 1 / (p : ℝ) + η +
          ∑ x ∈ badInputs C D i predictor, P.mass x := by
        simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
          P.sum_mass, one_mul]
        simp
  linarith

/-- An average extractor failure produces a sequential predictor with
advantage `2 * trevisanEta`. -/
theorem exists_predictor_of_average_tv_gt
    {p r : ℕ} [Fact p.Prime] (hr : 0 < r)
    (C : ShortLinearCode p (2 * r) (trevisanEta p r))
    (D : SuffixDesign C.ell r)
    (P : FinDist (FFVec p (2 * r)))
    (havg : (1 / 20 : ℝ) <
      (Fintype.card (D.Coord → Bool) : ℝ)⁻¹ *
        ∑ y : D.Coord → Bool,
          (P.map (fixedSeedMap C D y)).tv
            (FinDist.uniform (FFVec p r))) :
    ∃ i : Fin r,
      ∃ predictor : (D.Coord → Bool) × FFVec p i.val → ZMod p,
        1 / (p : ℝ) + 2 * trevisanEta p r <
          ∑ x, P.mass x * predictorSuccessRate C D i predictor x := by
  let J := seedOutputDist C D P
  have hfar : (1 / 20 : ℝ) <
      J.tv (J.fst.prod (FinDist.uniform (FFVec p r))) := by
    rw [seedOutputDist_fst]
    rw [← average_tv_eq_seedOutputDist_tv]
    exact havg
  obtain ⟨i, predictor, hpredictor⟩ :=
    FinDist.exists_sequential_predictor_of_tv_gt J (1 / 20 : ℝ)
      hr (by norm_num) hfar
  refine ⟨i, predictor, ?_⟩
  have hp0 : (0 : ℝ) < p := by
    exact_mod_cast (Fact.out : p.Prime).pos
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hconst :
      2 * trevisanEta p r = (1 / 20 : ℝ) / ((r : ℝ) * p) := by
    rw [trevisanEta]
    field_simp
    ring
  calc
    1 / (p : ℝ) + 2 * trevisanEta p r =
        1 / (p : ℝ) + (1 / 20 : ℝ) / ((r : ℝ) * p) := by
      rw [hconst]
    _ < ∑ w, J.mass w *
        (if predictor (w.1, FinDist.tuplePrefix i w.2) = w.2 i
          then (1 : ℝ) else 0) := hpredictor
    _ = ∑ x, P.mass x * predictorSuccessRate C D i predictor x := by
      exact sequential_sum_eq_weighted_successRate C D i predictor P

@[simp]
theorem seedCodeCoord_combineSeed
    {ell r : ℕ} (D : SuffixDesign ell r) (i : Fin r)
    (a : OutsideAssignment D i) (z : RowAssignment D i) :
    seedCodeCoord D i (combineSeed D i a z) =
      (rowAssignmentEquiv D i).symm z := by
  apply (rowAssignmentEquiv D i).injective
  funext c
  rw [seedCodeCoord_apply_equiv, Equiv.apply_symm_apply]
  exact combineSeed_apply_mem D i a z c.2

/-- Predictor success after fixing all seed bits outside the distinguished
design row. -/
noncomputable def insideSuccessRate
    {p r : ℕ} [Fact p.Prime] {η : ℝ}
    (C : ShortLinearCode p (2 * r) η)
    (D : SuffixDesign C.ell r) (i : Fin r)
    (predictor : (D.Coord → Bool) × FFVec p i.val → ZMod p)
    (x : FFVec p (2 * r)) (a : OutsideAssignment D i) : ℝ :=
  (Fintype.card (RowAssignment D i) : ℝ)⁻¹ *
    ∑ z, predictorSuccess C D i predictor x (combineSeed D i a z)

/-- Averaging first over the outside seed bits and then over the row bits
is the same as averaging over the full seed. -/
theorem predictorSuccessRate_eq_average_inside
    {p r : ℕ} [Fact p.Prime] {η : ℝ}
    (C : ShortLinearCode p (2 * r) η)
    (D : SuffixDesign C.ell r) (i : Fin r)
    (predictor : (D.Coord → Bool) × FFVec p i.val → ZMod p)
    (x : FFVec p (2 * r)) :
    predictorSuccessRate C D i predictor x =
      (Fintype.card (OutsideAssignment D i) : ℝ)⁻¹ *
        ∑ a, insideSuccessRate C D i predictor x a := by
  have hcard : Fintype.card (D.Coord → Bool) =
      Fintype.card (OutsideAssignment D i) *
        Fintype.card (RowAssignment D i) := by
    rw [Fintype.card_congr (seedSplitEquiv D i), Fintype.card_prod]
  have hsum :
      (∑ y : D.Coord → Bool, predictorSuccess C D i predictor x y) =
        ∑ q : OutsideAssignment D i × RowAssignment D i,
          predictorSuccess C D i predictor x
            (combineSeed D i q.1 q.2) := by
    symm
    exact Fintype.sum_equiv (seedSplitEquiv D i).symm _ _
      (fun q ↦ rfl)
  unfold predictorSuccessRate insideSuccessRate
  rw [hsum, Fintype.sum_prod_type, hcard]
  push_cast
  have hA : (0 : ℝ) < Fintype.card (OutsideAssignment D i) := by
    exact_mod_cast Fintype.card_pos
  have hB : (0 : ℝ) < Fintype.card (RowAssignment D i) := by
    exact_mod_cast Fintype.card_pos
  field_simp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  field_simp

/-- A globally successful input has an outside-row fixing on which the
inside-row agreement remains above the same threshold. -/
theorem exists_outside_of_successRate_gt
    {p r : ℕ} [Fact p.Prime] {η t : ℝ}
    (C : ShortLinearCode p (2 * r) η)
    (D : SuffixDesign C.ell r) (i : Fin r)
    (predictor : (D.Coord → Bool) × FFVec p i.val → ZMod p)
    (x : FFVec p (2 * r))
    (hx : t < predictorSuccessRate C D i predictor x) :
    ∃ a : OutsideAssignment D i,
      t < insideSuccessRate C D i predictor x a := by
  let μ : OutsideAssignment D i → ℝ :=
    fun a ↦ insideSuccessRate C D i predictor x a
  let a₀ := FinDist.finiteArgmax (OutsideAssignment D i) μ
  have havg := FinDist.average_le_argmax_mass μ
  have heq := predictorSuccessRate_eq_average_inside C D i predictor x
  refine ⟨a₀, ?_⟩
  rw [heq] at hx
  have hrewrite :
      (Fintype.card (OutsideAssignment D i) : ℝ)⁻¹ * ∑ a, μ a =
        (∑ a, μ a) / Fintype.card (OutsideAssignment D i) := by
    rw [div_eq_mul_inv, mul_comm]
  rw [hrewrite] at hx
  exact hx.trans_le havg

/-- Agreement is the uniform average of its equality indicators. -/
theorem agreement_eq_average_indicator
    {p ell : ℕ} (u v : BinaryCoord ell → ZMod p) :
    agreement u v =
      (Fintype.card (BinaryCoord ell) : ℝ)⁻¹ *
        ∑ q, if u q = v q then (1 : ℝ) else 0 := by
  have hsum :
      (∑ q, if u q = v q then (1 : ℝ) else 0) =
        (agreementCount u v : ℝ) := by
    classical
    unfold agreementCount
    simp [Finset.sum_boole]
  rw [hsum, agreement, div_eq_mul_inv, mul_comm]

/-- For the genuine reconstruction description, inside-row predictor
success is exactly codeword agreement with the reconstructed received
word. -/
theorem insideSuccessRate_eq_agreement_description
    {p r : ℕ} [Fact p.Prime] {η : ℝ}
    (C : ShortLinearCode p (2 * r) η)
    (D : SuffixDesign C.ell r) (i : Fin r)
    (predictor : (D.Coord → Bool) × FFVec p i.val → ZMod p)
    (x : FFVec p (2 * r)) (a : OutsideAssignment D i) :
    insideSuccessRate C D i predictor x a =
      agreement (C.encoder x)
        (descriptionWord C D i (fun y z ↦ predictor (y, z))
          (a, actualPriorTable C D i x a)) := by
  unfold insideSuccessRate
  rw [agreement_eq_average_indicator]
  rw [card_binaryCoord_eq_rowAssignment D i]
  congr 1
  exact Fintype.sum_equiv (rowAssignmentEquiv D i).symm _ _ (fun z ↦ by
    simp only [predictorSuccess, seedCodeCoord_combineSeed]
    rw [descriptionWord_actual]
    simp only [Equiv.apply_symm_apply]
    by_cases h : C.encoder x ((rowAssignmentEquiv D i).symm z) =
        predictor (combineSeed D i a z,
          outputPrefix C D i x (combineSeed D i a z))
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (by simpa [eq_comm] using h)])

/-- Every bad input belongs to one list indexed by a reconstruction
description. -/
theorem exists_description_of_mem_badInputs
    {p r : ℕ} [Fact p.Prime] {η : ℝ}
    (C : ShortLinearCode p (2 * r) η)
    (D : SuffixDesign C.ell r) (i : Fin r)
    (predictor : (D.Coord → Bool) × FFVec p i.val → ZMod p)
    {x : FFVec p (2 * r)}
    (hx : x ∈ badInputs C D i predictor) :
    ∃ desc : Description (p := p) D i,
      x ∈ codeAgreementList C.encoder
        (descriptionWord C D i (fun y z ↦ predictor (y, z)) desc) η := by
  have hbad : 1 / (p : ℝ) + η <
      predictorSuccessRate C D i predictor x := by
    simpa [badInputs] using (Finset.mem_filter.mp hx).2
  obtain ⟨a, ha⟩ := exists_outside_of_successRate_gt
    C D i predictor x hbad
  refine ⟨(a, actualPriorTable C D i x a), ?_⟩
  simp only [codeAgreementList, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← insideSuccessRate_eq_agreement_description C D i predictor x a]
  exact ha

/-- The bad inputs are covered by one short code list for every possible
reconstruction description. -/
theorem card_badInputs_lt_description_count
    {p r : ℕ} [Fact p.Prime] {η : ℝ}
    (C : ShortLinearCode p (2 * r) η)
    (D : SuffixDesign C.ell r) (i : Fin r)
    (predictor : (D.Coord → Bool) × FFVec p i.val → ZMod p) :
    ((badInputs C D i predictor).card : ℝ) <
      ((2 ^ D.coordCard * p ^ (r - 1) : ℕ) : ℝ) *
        (2 / η ^ 2 + 1) := by
  classical
  let Bad := {x : FFVec p (2 * r) // x ∈ badInputs C D i predictor}
  let descOf : Bad → Description (p := p) D i := fun bx ↦
    Classical.choose (exists_description_of_mem_badInputs
      C D i predictor bx.2)
  have descOf_mem (bx : Bad) :
      bx.1 ∈ codeAgreementList C.encoder
        (descriptionWord C D i (fun y z ↦ predictor (y, z))
          (descOf bx)) η :=
    Classical.choose_spec (exists_description_of_mem_badInputs
      C D i predictor bx.2)
  let Candidate := Σ desc : Description (p := p) D i,
    {x : FFVec p (2 * r) //
      x ∈ codeAgreementList C.encoder
        (descriptionWord C D i (fun y z ↦ predictor (y, z)) desc) η}
  let f : Bad → Candidate := fun bx ↦
    ⟨descOf bx, ⟨bx.1, descOf_mem bx⟩⟩
  have hf : Function.Injective f := by
    intro bx bx' hxy
    apply Subtype.ext
    exact congrArg (fun q : Candidate ↦ q.2.1) hxy
  have hcardNat : Fintype.card Bad ≤ Fintype.card Candidate :=
    Fintype.card_le_of_injective f hf
  have hcard : ((badInputs C D i predictor).card : ℝ) ≤
      (Fintype.card Candidate : ℝ) := by
    have hcardNat' : (badInputs C D i predictor).card ≤
        Fintype.card Candidate := by
      simpa only [Bad, Fintype.card_coe] using hcardNat
    exact_mod_cast hcardNat'
  have hcandidate : (Fintype.card Candidate : ℝ) =
      ∑ desc : Description (p := p) D i,
        ((codeAgreementList C.encoder
          (descriptionWord C D i (fun y z ↦ predictor (y, z)) desc) η).card : ℝ) := by
    dsimp only [Candidate]
    rw [Fintype.card_sigma]
    push_cast
    apply Finset.sum_congr rfl
    intro desc _hdesc
    simp
  let J : ℝ := 2 / η ^ 2 + 1
  let desc₀ : Description (p := p) D i :=
    (fun _ ↦ false, fun _ _ ↦ 0)
  have hnonempty : (Finset.univ : Finset (Description (p := p) D i)).Nonempty :=
    ⟨desc₀, Finset.mem_univ _⟩
  have hsumlt :
      (∑ desc : Description (p := p) D i,
        ((codeAgreementList C.encoder
          (descriptionWord C D i (fun y z ↦ predictor (y, z)) desc) η).card : ℝ)) <
        ∑ _desc : Description (p := p) D i, J := by
    apply Finset.sum_lt_sum_of_nonempty hnonempty
    intro desc _hdesc
    exact C.listBound _
  have hsumconst :
      (∑ _desc : Description (p := p) D i, J) =
        (Fintype.card (Description (p := p) D i) : ℝ) * J := by
    simp
  have hdescNat := card_description_le (p := p) D i
  have hdesc : (Fintype.card (Description (p := p) D i) : ℝ) ≤
      ((2 ^ D.coordCard * p ^ (r - 1) : ℕ) : ℝ) := by
    exact_mod_cast hdescNat
  have hJ : 0 ≤ J := by
    dsimp [J]
    positivity
  calc
    ((badInputs C D i predictor).card : ℝ) ≤
        (Fintype.card Candidate : ℝ) := hcard
    _ = ∑ desc : Description (p := p) D i,
        ((codeAgreementList C.encoder
          (descriptionWord C D i (fun y z ↦ predictor (y, z)) desc) η).card : ℝ) :=
      hcandidate
    _ < ∑ _desc : Description (p := p) D i, J := hsumlt
    _ = (Fintype.card (Description (p := p) D i) : ℝ) * J := hsumconst
    _ ≤ ((2 ^ D.coordCard * p ^ (r - 1) : ℕ) : ℝ) * J :=
      mul_le_mul_of_nonneg_right hdesc hJ
    _ = ((2 ^ D.coordCard * p ^ (r - 1) : ℕ) : ℝ) *
        (2 / η ^ 2 + 1) := rfl

/-- The raw Trevisan family associated with a short code and a suffix-slack
design. -/
noncomputable def rawTrevisanFamily
    {p r d s : ℕ} [Fact p.Prime] (hr : 0 < r)
    (C : ShortLinearCode p (2 * r) (trevisanEta p r))
    (D : SuffixDesign C.ell r)
    (hseed : 2 ^ D.coordCard ≤ p ^ d)
    (hcount :
      (((2 ^ D.coordCard * p ^ (r - 1) : ℕ) : ℝ) *
          (2 / trevisanEta p r ^ 2 + 1)) ≤
        trevisanEta p r * (p ^ (r + s) : ℕ)) :
    RawLinearExtractorFamily p r d s where
  Seed := D.Coord → Bool
  seedFintype := inferInstance
  seedDecidableEq := inferInstance
  seedNonempty := inferInstance
  card_seed_le := by
    simpa [SuffixDesign.coordCard] using hseed
  map := fixedSeedMap C D
  extracts := by
    intro P hpoint
    by_contra hfail
    have havg : (1 / 20 : ℝ) <
        (Fintype.card (D.Coord → Bool) : ℝ)⁻¹ *
          ∑ y : D.Coord → Bool,
            (P.map (fixedSeedMap C D y)).tv
              (FinDist.uniform (FFVec p r)) := lt_of_not_ge hfail
    obtain ⟨i, predictor, hpredictor⟩ :=
      exists_predictor_of_average_tv_gt hr C D P havg
    have hpNat : 0 < p := (Fact.out : p.Prime).pos
    have hη : 0 < trevisanEta p r := trevisanEta_pos hpNat hr
    have hmass : trevisanEta p r <
        ∑ x ∈ badInputs C D i predictor, P.mass x :=
      eta_lt_mass_badInputs hη C D i predictor P hpredictor
    have hbadCard := card_badInputs_lt_description_count C D i predictor
    have hbadCount : ((badInputs C D i predictor).card : ℝ) <
        trevisanEta p r * (p ^ (r + s) : ℕ) :=
      hbadCard.trans_le hcount
    let K : ℕ := p ^ (r + s)
    have hKnat : 0 < K := by
      dsimp [K]
      positivity
    have hK : (0 : ℝ) < K := by exact_mod_cast hKnat
    have hmassUpper :
        (∑ x ∈ badInputs C D i predictor, P.mass x) ≤
          ((badInputs C D i predictor).card : ℝ) * (K : ℝ)⁻¹ := by
      calc
        (∑ x ∈ badInputs C D i predictor, P.mass x) ≤
            ∑ _x ∈ badInputs C D i predictor, (K : ℝ)⁻¹ :=
          Finset.sum_le_sum fun x _hx ↦ hpoint x
        _ = ((badInputs C D i predictor).card : ℝ) * (K : ℝ)⁻¹ := by
          simp
    have hratio :
        ((badInputs C D i predictor).card : ℝ) * (K : ℝ)⁻¹ <
          trevisanEta p r := by
      rw [← div_eq_mul_inv]
      calc
        ((badInputs C D i predictor).card : ℝ) / K <
            (trevisanEta p r * K) / K :=
          (div_lt_div_iff_of_pos_right hK).2 (by simpa [K] using hbadCount)
        _ = trevisanEta p r := by field_simp
    linarith

/-- The canonical seed and entropy-slack exponents satisfy the two
counting hypotheses of `rawTrevisanFamily`. -/
noncomputable def canonicalRawTrevisanFamily
    {p r : ℕ} [Fact p.Prime] (hp : 2 < p) (hr : 0 < r)
    (C : ShortLinearCode p (2 * r) (trevisanEta p r))
    (D : SuffixDesign C.ell r) :
    RawLinearExtractorFamily p r
      (trevisanSeedExponent p D.coordCard)
      (trevisanSlackExponent p r D.coordCard) :=
  rawTrevisanFamily hr C D
    (seedThreshold_le_pow_seedExponent (by omega))
    (trevisan_reconstruction_count hp hr)

/-- Existence of the complete raw Trevisan family with the canonical
integer parameters. -/
theorem exists_canonicalRawTrevisanFamily
    (p r : ℕ) [Fact p.Prime] (hp : 2 < p) (hr : 0 < r) :
    ∃ C : ShortLinearCode p (2 * r) (trevisanEta p r),
      ∃ D : SuffixDesign C.ell r,
        Nonempty (RawLinearExtractorFamily p r
          (trevisanSeedExponent p D.coordCard)
          (trevisanSlackExponent p r D.coordCard)) := by
  have hm : 1 ≤ 2 * r := by omega
  obtain ⟨C⟩ := exists_shortLinearCode p (2 * r) hm
    (trevisanEta p r)
    (trevisanEta_pos (by omega) hr)
    (trevisanEta_lt_half hp hr)
  let D := SuffixDesign.build C.ell r
  exact ⟨C, D, ⟨canonicalRawTrevisanFamily hp hr C D⟩⟩

end Reconstruction

end Erdos788


/-! Flattened from Erdos788.CanonicalTrevisan. -/


/-!
# The canonical Trevisan extractor at the chosen parameters

This file discharges the pointwise numerical hypotheses of reconstruction
and rank pruning.  The eventual analytic estimates are isolated in
`ParameterRegular`; everything below is a finite construction at one `N`.
-/

namespace Erdos788

/-- The chosen dimension is nonzero at every regular parameter. -/
theorem parameterDimension_pos_of_regular {N : ℕ} (h : ParameterRegular N) :
    0 < parameterDimension N := by
  apply parameterDimension_pos
  have hN : (1 : ℝ) < N :=
    (Real.log_pos_iff (by positivity : (0 : ℝ) ≤ N)).mp h.1
  exact_mod_cast hN

/-- At the chosen parameters, the dimension logarithm is no larger than the
field-size logarithm. -/
theorem log_parameterDimension_le_log_parameterPrime
    {N : ℕ} (h : ParameterRegular N) :
    Real.log (parameterDimension N : ℝ) ≤
      Real.log (parameterPrime N : ℝ) := by
  have hr := parameterDimension_pos_of_regular h
  have hrR : (0 : ℝ) < parameterDimension N := by exact_mod_cast hr
  have hlogr : Real.log (parameterDimension N : ℝ) ≤
      Real.log (Real.log (N : ℝ)) := by
    apply Real.log_le_log hrR
    exact parameterDimension_le_log h
  exact hlogr.trans (loglog_le_log_parameterPrime N)

/-- The explicit design bound and the regularity inequalities leave at least
half of `log N` for reconstruction descriptions. -/
theorem chosenDesign_entropy_log_bound
    {N : ℕ} (h : ParameterRegular N)
    (C : ShortLinearCode (parameterPrime N) (2 * parameterDimension N)
      (trevisanEta (parameterPrime N) (parameterDimension N))) :
    Real.log 128040 +
          (((SuffixDesign.build C.ell (parameterDimension N)).coordCard : ℕ) : ℝ) *
            Real.log 2 +
          2 * Real.log (parameterPrime N : ℝ) +
          3 * Real.log (parameterDimension N : ℝ) ≤
      (parameterDimension N : ℝ) * Real.log (parameterPrime N : ℝ) := by
  let L := Real.log (N : ℝ)
  let q := Real.log L
  let δ := exponentCorrection N
  let r := parameterDimension N
  let p := parameterPrime N
  let D := (SuffixDesign.build C.ell r).coordCard
  let A := L * δ
  have hL : 0 < L := h.1
  have hq : 2 ≤ q := h.2.1
  have hδ : 0 < δ := by
    simpa [δ] using parameterRegular_correction_pos h
  have hδ1 : δ ≤ 1 := by
    simpa [δ] using parameterRegular_correction_le_one h
  have hA : 2 ≤ A := by
    simpa [A, L, δ] using parameterRegular_log_mul_correction h
  have hA0 : 0 ≤ A := (by linarith : (0 : ℝ) ≤ A)
  have hcube : δ ^ 3 = q / L := by
    simpa [L, q, δ] using
      exponentCorrection_pow_three h.1 (by linarith [h.2.1])
  have hrel : L * δ ^ 3 = q := by
    rw [hcube]
    field_simp
  have hpow : δ ^ 3 ≤ δ ^ 2 := by
    nlinarith [sq_nonneg δ]
  have hone_le_delta_mul_A : 1 ≤ δ * A := by
    have hmul := mul_le_mul_of_nonneg_left hpow hL.le
    have hq_le : q ≤ L * δ ^ 2 := by
      calc
        q = L * δ ^ 3 := hrel.symm
        _ ≤ L * δ ^ 2 := hmul
    dsimp [A]
    nlinarith
  have hinv_le_A : δ⁻¹ ≤ A := by
    rw [inv_le_iff_one_le_mul₀' hδ]
    simpa [mul_comm] using hone_le_delta_mul_A
  have hpLog : Real.log (p : ℝ) ≤ 2 * δ⁻¹ := by
    have hpLog' := log_parameterPrime_le_two_div_correction h.1
      (by linarith [h.2.1]) h.2.2.1
    simpa [p, δ, div_eq_mul_inv] using hpLog'
  have hrLog : Real.log (r : ℝ) ≤ Real.log (p : ℝ) := by
    simpa [r, p] using log_parameterDimension_le_log_parameterPrime h
  have hlogs :
      2 * Real.log (p : ℝ) + 3 * Real.log (r : ℝ) ≤ 10 * A := by
    calc
      2 * Real.log (p : ℝ) + 3 * Real.log (r : ℝ) ≤
          5 * Real.log (p : ℝ) := by linarith
      _ ≤ 10 * δ⁻¹ := by linarith
      _ ≤ 10 * A := by gcongr
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    convert Real.log_le_sub_one_of_pos
      (by norm_num : (0 : ℝ) < 2) using 1
    norm_num
  have hlog2nonneg : 0 ≤ Real.log (2 : ℝ) :=
    Real.log_nonneg (by norm_num)
  have hD : (D : ℝ) ≤ 100000000 * A := by
    simpa [D, A, L, δ, r, mul_assoc] using
      chosenDesign_coordCard_le h C
  have hD0 : (0 : ℝ) ≤ D := by positivity
  have hDterm : (D : ℝ) * Real.log 2 ≤ 100000000 * A := by
    calc
      (D : ℝ) * Real.log 2 ≤ (100000000 * A) * 1 :=
        mul_le_mul hD hlog2 hlog2nonneg (by positivity)
      _ = 100000000 * A := by ring
  have hconstRaw : Real.log (128040 : ℝ) ≤ 128039 := by
    convert Real.log_le_sub_one_of_pos
      (by norm_num : (0 : ℝ) < 128040) using 1
    norm_num
  have hconst : Real.log (128040 : ℝ) ≤ 64020 * A := by
    calc
      Real.log (128040 : ℝ) ≤ 128039 := hconstRaw
      _ ≤ 64020 * A := by nlinarith
  have hleft : Real.log 128040 + (D : ℝ) * Real.log 2 +
        2 * Real.log (p : ℝ) + 3 * Real.log (r : ℝ) ≤
      200000000 * A := by
    calc
      Real.log 128040 + (D : ℝ) * Real.log 2 +
            2 * Real.log (p : ℝ) + 3 * Real.log (r : ℝ) ≤
          64020 * A + 100000000 * A + 10 * A := by linarith
      _ ≤ 200000000 * A := by nlinarith
  have hsmall : 200000000 * δ ≤ 1 / 2 := by
    have := h.2.2.2
    dsimp [δ]
    linarith
  have hhalf : 200000000 * A ≤ L / 2 := by
    have hmul := mul_le_mul_of_nonneg_left hsmall hL.le
    dsimp [A]
    nlinarith
  have hrpos : 0 < r := by
    simpa [r] using parameterDimension_pos_of_regular h
  have hlogp : 0 < Real.log (p : ℝ) := by
    apply Real.log_pos
    have hp2 : 2 < p := by simpa [p] using two_lt_parameterPrime N
    exact_mod_cast (show 1 < p by omega)
  have hdiv : L / (2 * Real.log (p : ℝ)) ≤ (r : ℝ) := by
    simpa [L, p, r] using
      log_div_le_cast_parameterDimension (N := N) (by
        have hN : (1 : ℝ) < N :=
          (Real.log_pos_iff (by positivity : (0 : ℝ) ≤ N)).mp h.1
        exact_mod_cast (show (0 : ℝ) < N from zero_lt_one.trans hN))
  have hrhs : L / 2 ≤ (r : ℝ) * Real.log (p : ℝ) := by
    have hden : 0 < 2 * Real.log (p : ℝ) := by positivity
    have hcross := (div_le_iff₀ hden).mp hdiv
    nlinarith
  change Real.log 128040 + (D : ℝ) * Real.log 2 +
      2 * Real.log (p : ℝ) + 3 * Real.log (r : ℝ) ≤
    (r : ℝ) * Real.log (p : ℝ)
  exact hleft.trans (hhalf.trans hrhs)

/-- The canonical entropy-slack exponent is at most the chosen dimension. -/
theorem chosenSlackExponent_le_dimension
    {N : ℕ} (h : ParameterRegular N)
    (C : ShortLinearCode (parameterPrime N) (2 * parameterDimension N)
      (trevisanEta (parameterPrime N) (parameterDimension N))) :
    trevisanSlackExponent (parameterPrime N) (parameterDimension N)
        (SuffixDesign.build C.ell (parameterDimension N)).coordCard ≤
      parameterDimension N := by
  apply slackExponent_le_of_log_bound
  · exact Nat.lt_trans (by norm_num) (two_lt_parameterPrime N)
  · exact parameterDimension_pos_of_regular h
  · exact chosenDesign_entropy_log_bound h C

/-- The canonical slack is small enough for the uniform-source rank-pruning
argument. -/
theorem chosen_dimension_add_slack_le_two_mul
    {N : ℕ} (h : ParameterRegular N)
    (C : ShortLinearCode (parameterPrime N) (2 * parameterDimension N)
      (trevisanEta (parameterPrime N) (parameterDimension N))) :
    parameterDimension N +
        trevisanSlackExponent (parameterPrime N) (parameterDimension N)
          (SuffixDesign.build C.ell (parameterDimension N)).coordCard ≤
      2 * parameterDimension N := by
  have hs := chosenSlackExponent_le_dimension h C
  omega

/-- At each regular `N`, the canonical raw Trevisan family can be rank
pruned to a surjective linear extractor family with the same integer seed
and entropy exponents. -/
theorem exists_chosenLinearExtractorFamily
    {N : ℕ} (h : ParameterRegular N) :
    ∃ C : ShortLinearCode (parameterPrime N) (2 * parameterDimension N)
        (trevisanEta (parameterPrime N) (parameterDimension N)),
      Nonempty (LinearExtractorFamily (parameterPrime N) (parameterDimension N)
        (trevisanSeedExponent (parameterPrime N)
          (SuffixDesign.build C.ell (parameterDimension N)).coordCard)
        (trevisanSlackExponent (parameterPrime N) (parameterDimension N)
          (SuffixDesign.build C.ell (parameterDimension N)).coordCard)) := by
  let p := parameterPrime N
  let r := parameterDimension N
  have hp : 2 < p := by simpa [p] using two_lt_parameterPrime N
  have hr : 0 < r := by simpa [r] using parameterDimension_pos_of_regular h
  have hm : 1 ≤ 2 * r := by omega
  obtain ⟨C⟩ := exists_shortLinearCode p (2 * r) hm (trevisanEta p r)
    (trevisanEta_pos (by omega) hr) (trevisanEta_lt_half hp hr)
  let D := SuffixDesign.build C.ell r
  let E := Reconstruction.canonicalRawTrevisanFamily hp hr C D
  have hs : trevisanSlackExponent p r D.coordCard ≤ r := by
    simpa [p, r, D] using chosenSlackExponent_le_dimension h C
  have hrs : r + trevisanSlackExponent p r D.coordCard ≤ 2 * r := by omega
  refine ⟨C, ?_⟩
  simpa [p, r, D, E] using
    (prune_rank_deficient_seeds hp hr hrs E)

end Erdos788


/-! Flattened from Erdos788.AsymptoticRegularity. -/


/-!
# Eventual regularity of the chosen parameters

This file discharges the elementary asymptotic hypotheses isolated in
`ParameterRegular`.  Keeping this argument separate means that all finite
construction modules remain pointwise and threshold-free.
-/

namespace Erdos788

private theorem log_nat_tendsto_atTop :
    Filter.Tendsto (fun N : ℕ => Real.log (N : ℝ))
      Filter.atTop Filter.atTop :=
  Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop :
      Filter.Tendsto (fun N : ℕ => (N : ℝ)) Filter.atTop Filter.atTop)

private theorem loglog_nat_tendsto_atTop :
    Filter.Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ)))
      Filter.atTop Filter.atTop :=
  Real.tendsto_log_atTop.comp log_nat_tendsto_atTop

/-- The explicit exponent correction tends to zero. -/
theorem exponentCorrection_tendsto_zero :
    Filter.Tendsto exponentCorrection Filter.atTop (nhds 0) := by
  have hratioReal :
      Filter.Tendsto (fun x : ℝ => Real.log x / x)
        Filter.atTop (nhds 0) := by
    simpa [Function.id_def] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hratioNat := hratioReal.comp log_nat_tendsto_atTop
  have hrpow := hratioNat.rpow_const
    (Or.inr (by norm_num : (0 : ℝ) ≤ 1 / 3))
  change Filter.Tendsto
    (fun N : ℕ =>
      (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ)) ^ (1 / 3 : ℝ))
    Filter.atTop (nhds 0)
  simpa only [Function.comp_apply, one_div,
    Real.zero_rpow (by norm_num : (3 : ℝ)⁻¹ ≠ 0)] using hrpow

/-- The correction still tends to zero after multiplication by `log log N`. -/
theorem correction_mul_loglog_tendsto_zero :
    Filter.Tendsto
      (fun N : ℕ => exponentCorrection N *
        Real.log (Real.log (N : ℝ)))
      Filter.atTop (nhds 0) := by
  have hpowerReal :
      Filter.Tendsto
        (fun x : ℝ => Real.log x ^ (4 / 3 : ℝ) / x ^ (1 / 3 : ℝ))
        Filter.atTop (nhds 0) := by
    simpa using
      (isLittleO_log_rpow_rpow_atTop (4 / 3 : ℝ)
        (by norm_num : (0 : ℝ) < 1 / 3)).tendsto_div_nhds_zero
  have hpowerNat := hpowerReal.comp log_nat_tendsto_atTop
  have heq :
      (fun N : ℕ => exponentCorrection N *
          Real.log (Real.log (N : ℝ))) =ᶠ[Filter.atTop]
        (fun N : ℕ =>
          Real.log (Real.log (N : ℝ)) ^ (4 / 3 : ℝ) /
            Real.log (N : ℝ) ^ (1 / 3 : ℝ)) := by
    filter_upwards [log_nat_tendsto_atTop.eventually_gt_atTop 0,
      loglog_nat_tendsto_atTop.eventually_gt_atTop 0] with N hL hq
    rw [exponentCorrection, Real.div_rpow hq.le hL.le]
    rw [div_mul_eq_mul_div, ← Real.rpow_add_one hq.ne']
    norm_num
  exact hpowerNat.congr' heq.symm

/-- The bundled pointwise hypotheses used by the parameter calculation hold
for every sufficiently large integer. -/
theorem eventually_parameterRegular :
    ∀ᶠ N : ℕ in Filter.atTop, ParameterRegular N := by
  have hproduct :
      Filter.Tendsto
        (fun N : ℕ => exponentCorrection N *
          (Real.log (Real.log (N : ℝ)) + Real.log 4))
        Filter.atTop (nhds 0) := by
    have hconst := exponentCorrection_tendsto_zero.mul_const (Real.log 4)
    have hadd := correction_mul_loglog_tendsto_zero.add hconst
    simpa [mul_add] using hadd
  have hscaled :
      Filter.Tendsto
        (fun N : ℕ => 400000000 * exponentCorrection N)
        Filter.atTop (nhds 0) := by
    simpa [mul_comm] using
      exponentCorrection_tendsto_zero.mul_const (400000000 : ℝ)
  filter_upwards [log_nat_tendsto_atTop.eventually_gt_atTop 0,
    loglog_nat_tendsto_atTop.eventually_ge_atTop 2,
    (tendsto_order.1 hproduct).2 1 (by norm_num),
    (tendsto_order.1 hscaled).2 1 (by norm_num)] with N hL hq hproductN hscaledN
  exact ⟨hL, hq, hproductN.le, hscaledN.le⟩

/-- A concrete natural threshold exists for `ParameterRegular`. -/
theorem exists_parameterRegular_threshold :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ParameterRegular N := by
  simpa only [Filter.eventually_atTop] using eventually_parameterRegular

end Erdos788


/-! Flattened from Erdos788.CarryFactorization. -/


/-!
# The base-`p` carry lift

This file transfers a finite-field sum palette to an ordinary integer sum
palette.  We use little-endian, fixed-length base-`p` words.  Once the
coordinatewise residue of a raw digit sum is fixed, its ordinary value is
determined by one overflow bit in each coordinate.
-/

namespace Erdos788

open Finset

/-- The ordinary sum graph on the interval `[0, N)`. -/
def intSumGraph (N : ℕ) (B : Finset ℕ) : SimpleGraph (Fin N) :=
  SimpleGraph.fromRel fun x y ↦ x.val + y.val ∈ B

@[simp]
theorem intSumGraph_adj {N : ℕ} {B : Finset ℕ} {x y : Fin N} :
    (intSumGraph N B).Adj x y ↔ x ≠ y ∧ x.val + y.val ∈ B := by
  simp [intSumGraph, add_comm]

/-- A fixed-length word of base-`p` digits. -/
abbrev DigitWord (p k : ℕ) := Fin k → Fin p

/-- Interpret an arbitrary length-`k` natural word in base `p`. -/
def rawWordValue (p : ℕ) {k : ℕ} (d : Fin k → ℕ) : ℕ :=
  Nat.ofDigits p (List.ofFn d)

/-- Interpret a bounded digit word in base `p`. -/
def digitWordValue (p k : ℕ) (w : DigitWord p k) : ℕ :=
  rawWordValue p fun i ↦ (w i).val

theorem digitWordValue_lt_pow {p k : ℕ} (hp : 1 < p) (w : DigitWord p k) :
    digitWordValue p k w < p ^ k := by
  have h := Nat.ofDigits_lt_base_pow_length hp (l := List.ofFn fun i ↦ (w i).val)
    (by
      intro d hd
      simp only [List.mem_ofFn] at hd
      obtain ⟨i, rfl⟩ := hd
      exact (w i).isLt)
  simpa [digitWordValue, rawWordValue] using h

/-- The value map, with its range proof bundled into `Fin (p^k)`. -/
def digitWordToFin {p k : ℕ} (hp : 1 < p) : DigitWord p k → Fin (p ^ k) :=
  fun w ↦ ⟨digitWordValue p k w, digitWordValue_lt_pow hp w⟩

theorem digitWordToFin_injective {p k : ℕ} (hp : 1 < p) :
    Function.Injective (digitWordToFin (k := k) hp) := by
  intro a b hab
  have hvalue : digitWordValue p k a = digitWordValue p k b :=
    congrArg Fin.val hab
  have hlists : List.ofFn (fun i ↦ (a i).val) =
      List.ofFn (fun i ↦ (b i).val) := by
    apply Nat.ofDigits_inj_of_len_eq hp (by simp)
    · intro d hd
      simp only [List.mem_ofFn] at hd
      obtain ⟨i, rfl⟩ := hd
      exact (a i).isLt
    · intro d hd
      simp only [List.mem_ofFn] at hd
      obtain ⟨i, rfl⟩ := hd
      exact (b i).isLt
    · exact hvalue
  have hfun : (fun i ↦ (a i).val) = fun i ↦ (b i).val :=
    List.ofFn_injective hlists
  funext i
  exact Fin.ext (congrFun hfun i)

theorem digitWordToFin_bijective {p k : ℕ} (hp : 1 < p) :
    Function.Bijective (digitWordToFin (k := k) hp) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨digitWordToFin_injective hp, ?_⟩
  simp [DigitWord]

/-- Fixed-length base-`p` expansion as an equivalence. -/
noncomputable def digitWordEquiv {p k : ℕ} (hp : 1 < p) :
    DigitWord p k ≃ Fin (p ^ k) :=
  Equiv.ofBijective (digitWordToFin (k := k) hp) (digitWordToFin_bijective hp)

@[simp]
theorem digitWordEquiv_apply_val {p k : ℕ} (hp : 1 < p) (w : DigitWord p k) :
    (digitWordEquiv hp w).val = digitWordValue p k w :=
  rfl

@[simp]
theorem digitWordEquiv_symm_value {p k : ℕ} (hp : 1 < p) (x : Fin (p ^ k)) :
    digitWordValue p k ((digitWordEquiv hp).symm x) = x.val := by
  change (digitWordEquiv hp ((digitWordEquiv hp).symm x)).val = x.val
  exact congrArg Fin.val ((digitWordEquiv hp).apply_symm_apply x)

/-- Send a bounded natural digit to its residue class, coordinatewise. -/
def wordResidue (p k : ℕ) (w : DigitWord p k) : FFVec p k :=
  fun i ↦ ((w i).val : ZMod p)

theorem wordResidue_injective {p k : ℕ} :
    Function.Injective (wordResidue p k) := by
  intro a b hab
  funext i
  apply Fin.ext
  have hi := congrFun hab i
  have hval := congrArg ZMod.val hi
  simpa [wordResidue, ZMod.val_natCast_of_lt (a i).isLt,
    ZMod.val_natCast_of_lt (b i).isLt] using hval

/-- The residue-vector labeling of the integer interval `[0,p^k)`. -/
noncomputable def integerResidue {p k : ℕ} (hp : 1 < p) :
    Fin (p ^ k) → FFVec p k :=
  fun x ↦ wordResidue p k ((digitWordEquiv hp).symm x)

theorem integerResidue_injective {p k : ℕ} (hp : 1 < p) :
    Function.Injective (integerResidue (k := k) hp) :=
  (wordResidue_injective (p := p) (k := k)).comp (digitWordEquiv hp).symm.injective

/-- Pairs of digit words having a prescribed coordinatewise residue sum. -/
def ResiduePair (p k : ℕ) (s : FFVec p k) :=
  {q : DigitWord p k × DigitWord p k //
    wordResidue p k q.1 + wordResidue p k q.2 = s}

noncomputable instance residuePairFintype (p k : ℕ) (s : FFVec p k) :
    Fintype (ResiduePair p k s) :=
  Fintype.ofInjective (fun q : ResiduePair p k s ↦ q.val) Subtype.val_injective

/-- The ordinary value of a pair of digit words. -/
def residuePairValue {p k : ℕ} {s : FFVec p k} (q : ResiduePair p k s) : ℕ :=
  digitWordValue p k q.val.1 + digitWordValue p k q.val.2

/-- All ordinary sums arising above one fixed residue vector. -/
noncomputable def residueSumFibre (p k : ℕ) (s : FFVec p k) : Finset ℕ :=
  Finset.univ.image (residuePairValue : ResiduePair p k s → ℕ)

/-- The raw overflow bit at one coordinate. -/
def rawOverflow {p k : ℕ} {s : FFVec p k} (q : ResiduePair p k s)
    (i : Fin k) : Bool :=
  Bool.ofNat (((q.val.1 i).val + (q.val.2 i).val) / p)

/-- Recover an ordinary raw digit word from a residue vector and overflow bits. -/
def decodeRawSum (p : ℕ) {k : ℕ} (s : FFVec p k) (c : Fin k → Bool) : ℕ :=
  rawWordValue p fun i ↦ (s i).val + p * (c i).toNat

theorem digitWordValue_add {p k : ℕ} (a b : DigitWord p k) :
    digitWordValue p k a + digitWordValue p k b =
      rawWordValue p (fun i ↦ (a i).val + (b i).val) := by
  unfold digitWordValue rawWordValue
  rw [Nat.ofDigits_add_ofDigits_eq_ofDigits_zipWith_of_length_eq (by simp)]
  congr 1
  apply List.ext_get (by simp)
  intro n h₁ h₂
  simp

theorem rawOverflow_toNat {p k : ℕ} (hp : 1 < p) {s : FFVec p k}
    (q : ResiduePair p k s) (i : Fin k) :
    (rawOverflow q i).toNat = ((q.val.1 i).val + (q.val.2 i).val) / p := by
  have hq : ((q.val.1 i).val + (q.val.2 i).val) / p ≤ 1 :=
    one_bit_raw_carry (p := p) (Nat.zero_lt_of_lt hp)
    (q.val.1 i).isLt (q.val.2 i).isLt
  have hcases : ((q.val.1 i).val + (q.val.2 i).val) / p = 0 ∨
      ((q.val.1 i).val + (q.val.2 i).val) / p = 1 :=
    Nat.le_one_iff_eq_zero_or_eq_one.mp hq
  rcases hcases with hzero | hone
  · simp [rawOverflow, hzero]
  · simp [rawOverflow, hone]

theorem residuePair_raw_digit {p k : ℕ} (hp : 1 < p) {s : FFVec p k}
    (q : ResiduePair p k s) (i : Fin k) :
    (q.val.1 i).val + (q.val.2 i).val =
      (s i).val + p * (rawOverflow q i).toNat := by
  have hres : (((q.val.1 i).val + (q.val.2 i).val : ℕ) : ZMod p) = s i := by
    rw [Nat.cast_add]
    simpa [wordResidue, Pi.add_apply] using congrFun q.property i
  have hmod : ((q.val.1 i).val + (q.val.2 i).val) % p = (s i).val := by
    calc
      ((q.val.1 i).val + (q.val.2 i).val) % p =
          ((((q.val.1 i).val + (q.val.2 i).val : ℕ) : ZMod p)).val := by
            rw [ZMod.val_natCast]
      _ = (s i).val := congrArg ZMod.val hres
  rw [← Nat.mod_add_div ((q.val.1 i).val + (q.val.2 i).val) p,
    hmod, rawOverflow_toNat hp q i]

theorem residuePairValue_factor {p k : ℕ} (hp : 1 < p) {s : FFVec p k}
    (q : ResiduePair p k s) :
    residuePairValue q = decodeRawSum p s (rawOverflow q) := by
  rw [residuePairValue, digitWordValue_add]
  unfold decodeRawSum
  congr 2
  funext i
  exact residuePair_raw_digit hp q i

theorem residueSumFibre_card_le {p k : ℕ} (hp : 1 < p) (s : FFVec p k) :
    (residueSumFibre p k s).card ≤ 2 ^ k := by
  classical
  exact carry_description_bound k
    (residuePairValue : ResiduePair p k s → ℕ)
    (rawOverflow : ResiduePair p k s → Fin k → Bool)
    (decodeRawSum p s) (residuePairValue_factor hp)

/-- The integer palette obtained by taking every ordinary sum above `S`. -/
noncomputable def carryPalette (p k : ℕ) (S : Finset (FFVec p k)) : Finset ℕ :=
  S.biUnion (residueSumFibre p k)

theorem carryPalette_card_le {p k : ℕ} (hp : 1 < p) (S : Finset (FFVec p k)) :
    (carryPalette p k S).card ≤ 2 ^ k * S.card := by
  classical
  calc
    (carryPalette p k S).card ≤ S.card * 2 ^ k :=
      Finset.card_biUnion_le_card_mul S (residueSumFibre p k) (2 ^ k)
        (fun s _ ↦ residueSumFibre_card_le hp s)
    _ = 2 ^ k * S.card := Nat.mul_comm _ _

theorem carryPalette_subset_range {p k : ℕ} (hp : 1 < p)
    (S : Finset (FFVec p k)) :
    carryPalette p k S ⊆ Finset.range (2 * p ^ k - 1) := by
  classical
  intro z hz
  rcases Finset.mem_biUnion.mp hz with ⟨s, hs, hzs⟩
  rw [residueSumFibre] at hzs
  rcases Finset.mem_image.mp hzs with ⟨q, _hq, rfl⟩
  rw [Finset.mem_range]
  change digitWordValue p k q.val.1 + digitWordValue p k q.val.2 < 2 * p ^ k - 1
  have ha := digitWordValue_lt_pow hp q.val.1
  have hb := digitWordValue_lt_pow hp q.val.2
  have hpow : 0 < p ^ k := Nat.pow_pos (by omega)
  omega

theorem digitWord_sum_mem_carryPalette {p k : ℕ} (S : Finset (FFVec p k))
    (a b : DigitWord p k)
    (hab : wordResidue p k a + wordResidue p k b ∈ S) :
    digitWordValue p k a + digitWordValue p k b ∈ carryPalette p k S := by
  classical
  apply Finset.mem_biUnion.mpr
  refine ⟨wordResidue p k a + wordResidue p k b, hab, ?_⟩
  rw [residueSumFibre]
  apply Finset.mem_image.mpr
  let q : ResiduePair p k (wordResidue p k a + wordResidue p k b) :=
    ⟨(a, b), rfl⟩
  exact ⟨q, Finset.mem_univ q, rfl⟩

theorem integer_sum_mem_carryPalette {p k : ℕ} (hp : 1 < p)
    (S : Finset (FFVec p k)) (x y : Fin (p ^ k))
    (hxy : integerResidue hp x + integerResidue hp y ∈ S) :
    x.val + y.val ∈ carryPalette p k S := by
  have hmem := digitWord_sum_mem_carryPalette S
    ((digitWordEquiv hp).symm x) ((digitWordEquiv hp).symm y) hxy
  simpa [integerResidue] using hmem

/-- Exact carry lift from a group sum palette to an integer sum palette. -/
theorem carry_lift (p k : ℕ) (hp : 1 < p) (S : Finset (FFVec p k)) :
    ∃ B : Finset ℕ,
      B ⊆ Finset.range (2 * p ^ k - 1) ∧
      B.card ≤ 2 ^ k * S.card ∧
      (intSumGraph (p ^ k) B).indepNum ≤ (groupSumGraph S).indepNum := by
  classical
  let _ : NeZero p := ⟨by omega⟩
  refine ⟨carryPalette p k S, carryPalette_subset_range hp S,
    carryPalette_card_le hp S, ?_⟩
  obtain ⟨A, hA⟩ :=
    (intSumGraph (p ^ k) (carryPalette p k S)).exists_isNIndepSet_indepNum
  let C : Finset (FFVec p k) := A.image (integerResidue hp)
  have hCind : (groupSumGraph S).IsIndepSet (C : Set (FFVec p k)) := by
    intro u hu v hv huv hadj
    change u ∈ C at hu
    change v ∈ C at hv
    rcases Finset.mem_image.mp hu with ⟨x, hx, rfl⟩
    rcases Finset.mem_image.mp hv with ⟨y, hy, rfl⟩
    have hxy : x ≠ y := by
      intro h
      exact huv (congrArg (integerResidue hp) h)
    have hsum : integerResidue hp x + integerResidue hp y ∈ S :=
      (groupSumGraph_adj.mp hadj).2
    have hB := integer_sum_mem_carryPalette hp S x y hsum
    exact hA.isIndepSet hx hy hxy (intSumGraph_adj.mpr ⟨hxy, hB⟩)
  calc
    (intSumGraph (p ^ k) (carryPalette p k S)).indepNum = A.card :=
      hA.card_eq.symm
    _ = C.card := by
      symm
      exact Finset.card_image_of_injective A (integerResidue_injective hp)
    _ ≤ (groupSumGraph S).indepNum := hCind.card_le_indepNum

end Erdos788


/-! Flattened from Erdos788.EveryNFinite. -/


/-!
# Restricting the finite-field construction to every interval length

This file contains the exact finite part of the "every `N`" step.  It is
independent of the later analytic choice of `p` and `r`.
-/

namespace Erdos788

open Finset

/-- The ordinary and normalized sum-graph definitions coincide. -/
theorem intSumGraph_eq_sumGraph (N : ℕ) (B : Finset ℕ) :
    intSumGraph N B = sumGraph N B := by
  ext x y
  simp only [intSumGraph_adj, sumGraph_adj]

/-- Inclusion of a shorter initial interval into a longer one. -/
def finInitialEmbedding {N M : ℕ} (hNM : N ≤ M) : Fin N ↪ Fin M where
  toFun := Fin.castLE hNM
  inj' := Fin.castLE_injective hNM

/-- Restricting a sum graph to an initial interval cannot increase its
independence number. -/
theorem indepNum_sumGraph_mono_vertices
    {N M : ℕ} (hNM : N ≤ M) (B : Finset ℕ) :
    (sumGraph N B).indepNum ≤ (sumGraph M B).indepNum := by
  classical
  obtain ⟨A, hA⟩ := (sumGraph N B).exists_isNIndepSet_indepNum
  let C : Finset (Fin M) := A.map (finInitialEmbedding hNM)
  have hC : (sumGraph M B).IsIndepSet (C : Set (Fin M)) := by
    intro u hu v hv huv hadj
    change u ∈ C at hu
    change v ∈ C at hv
    rcases Finset.mem_map.mp hu with ⟨x, hx, rfl⟩
    rcases Finset.mem_map.mp hv with ⟨y, hy, rfl⟩
    have hxy : x ≠ y := by
      intro h
      exact huv (congrArg (finInitialEmbedding hNM) h)
    have hsum : x.val + y.val ∈ B := (sumGraph_adj.mp hadj).2
    exact hA.isIndepSet hx hy hxy (sumGraph_adj.mpr ⟨hxy, hsum⟩)
  calc
    (sumGraph N B).indepNum = A.card := hA.card_eq.symm
    _ = C.card := by simp [C]
    _ ≤ (sumGraph M B).indepNum := hC.card_le_indepNum

/-- Delete all colors that cannot be a sum of two distinct vertices of the
first `N` integers. -/
def restrictToAttainable (N : ℕ) (B : Finset ℕ) : Finset ℕ :=
  B.filter fun s ↦ s ∈ attainableNormalizedSums N

theorem restrictToAttainable_subset (N : ℕ) (B : Finset ℕ) :
    restrictToAttainable N B ⊆ attainableNormalizedSums N := by
  intro s hs
  exact (Finset.mem_filter.mp hs).2

theorem card_restrictToAttainable_le (N : ℕ) (B : Finset ℕ) :
    (restrictToAttainable N B).card ≤ B.card :=
  Finset.card_filter_le _ _

/-- Removing unattainable sums does not alter the graph. -/
theorem sumGraph_restrictToAttainable (N : ℕ) (B : Finset ℕ) :
    sumGraph N (restrictToAttainable N B) = sumGraph N B := by
  ext x y
  simp only [sumGraph_adj]
  constructor
  · rintro ⟨hxy, hmem⟩
    exact ⟨hxy, (Finset.mem_filter.mp hmem).1⟩
  · rintro ⟨hxy, hmem⟩
    refine ⟨hxy, Finset.mem_filter.mpr ⟨hmem, ?_⟩⟩
    exact (isAttainableNormalizedSum_iff_mem N (x.val + y.val)).mp
      ⟨x, y, hxy, rfl⟩

/-- Carry lifting followed by restriction to any shorter initial interval. -/
theorem carry_lift_restrict
    (p k N : ℕ) (hp : 1 < p) (hNM : N ≤ p ^ k)
    (S : Finset (FFVec p k)) :
    ∃ B : Finset ℕ,
      B ⊆ attainableNormalizedSums N ∧
      B.card ≤ 2 ^ k * S.card ∧
      (sumGraph N B).indepNum ≤ (groupSumGraph S).indepNum := by
  obtain ⟨B, _hBrange, hBcard, hBind⟩ := carry_lift p k hp S
  refine ⟨restrictToAttainable N B, restrictToAttainable_subset N B,
    (card_restrictToAttainable_le N B).trans hBcard, ?_⟩
  rw [sumGraph_restrictToAttainable]
  calc
    (sumGraph N B).indepNum ≤ (sumGraph (p ^ k) B).indepNum :=
      indepNum_sumGraph_mono_vertices hNM B
    _ = (intSumGraph (p ^ k) B).indepNum := by
      rw [intSumGraph_eq_sumGraph]
    _ ≤ (groupSumGraph S).indepNum := hBind

/-- A normalized palette supported on attainable sums gives an exact upper
bound for the original Erdős function. -/
theorem fNat_le_of_normalized_palette
    (n : ℕ) (A : Finset ℕ)
    (hA : A ⊆ attainableNormalizedSums (n - 1)) :
    fNat n ≤ A.card + (sumGraph (n - 1) A).indepNum := by
  classical
  let B := denormalizePalette n A
  have hB : B ⊆ J n := by
    intro b hb
    rw [show B = denormalizePalette n A from rfl, mem_denormalizePalette] at hb
    obtain ⟨s, hsA, hsatt, rfl⟩ := hb
    rw [J, Finset.mem_Ioo]
    rw [attainableNormalizedSums, Finset.mem_Icc] at hsatt
    simp only [sumOffset]
    omega
  have hfilter : A.filter (fun s ↦ s ∈ attainableNormalizedSums (n - 1)) = A :=
    Finset.filter_eq_self.mpr hA
  have hnorm : normalizePalette n B = A := by
    rw [show B = denormalizePalette n A from rfl,
      normalizePalette_denormalizePalette, hfilter]
  have hcard : B.card = A.card := by
    rw [show B = denormalizePalette n A from rfl,
      card_denormalizePalette, hfilter]
  have hscore : graphScore n B =
      A.card + (sumGraph (n - 1) A).indepNum := by
    rw [graphScore, hcard, indepNum_paletteGraph_eq_sumGraph, hnorm]
  rw [fNat_eq_minGraphScore, ← hscore]
  exact minGraphScore_le hB

/-- Exact finite upper bridge from a group palette to `f(N+1)`. -/
theorem fNat_succ_le_of_group_palette
    (p k N : ℕ) (hp : 1 < p) (hNM : N ≤ p ^ k)
    (S : Finset (FFVec p k)) :
    fNat (N + 1) ≤ 2 ^ k * S.card + (groupSumGraph S).indepNum := by
  obtain ⟨B, hBatt, hBcard, hBind⟩ := carry_lift_restrict p k N hp hNM S
  have hf := fNat_le_of_normalized_palette (N + 1) B (by
    simpa using hBatt)
  exact hf.trans (Nat.add_le_add hBcard hBind)

end Erdos788


/-! Flattened from Erdos788.UpperAssembly. -/


/-!
# Exact finite assembly of the upper-bound construction

This file composes the checked extractor, kernel-palette, carry, and
normalization interfaces.  No asymptotic parameter choices are made here.
-/

namespace Erdos788

/-- The exact two-term upper bound before removing the ceiling logarithms. -/
def trevisanFiniteUpperBound (p r D : ℕ) : ℕ :=
  2 ^ (2 * r) * p ^ (r + trevisanSeedExponent p D) +
    p ^ (r + trevisanSlackExponent p r D)

/-- Both ceiling logarithms cost at most one factor of `p`; after factoring,
all remaining losses are displayed explicitly. -/
theorem trevisanFiniteUpperBound_le {p r D : ℕ}
    (hp : 1 < p) (hr : 0 < r) :
    trevisanFiniteUpperBound p r D ≤
      p ^ r * p * 2 ^ D *
        (2 ^ (2 * r) + 40 * r * (3200 * p ^ 2 * r ^ 2 + 1)) := by
  have hd := pow_seedExponent_le (p := p) (D := D) hp
  have hs := pow_slackExponent_le (p := p) (r := r) (D := D) hp hr
  rw [trevisanFiniteUpperBound, Nat.pow_add, Nat.pow_add]
  calc
    2 ^ (2 * r) * (p ^ r * p ^ trevisanSeedExponent p D) +
        p ^ r * p ^ trevisanSlackExponent p r D ≤
      2 ^ (2 * r) * (p ^ r * (p * 2 ^ D)) +
        p ^ r * (p * trevisanSlackThreshold p r D) := by
          exact Nat.add_le_add
            (Nat.mul_le_mul_left (2 ^ (2 * r))
              (Nat.mul_le_mul_left (p ^ r) hd))
            (Nat.mul_le_mul_left (p ^ r) hs)
    _ = p ^ r * p * 2 ^ D *
        (2 ^ (2 * r) + 40 * r * (3200 * p ^ 2 * r ^ 2 + 1)) := by
          rw [trevisanSlackThreshold]
          ring

/-- A simpler multiplicative majorant, convenient for taking logarithms. -/
theorem trevisanFiniteUpperBound_le_monomial {p r D : ℕ}
    (hp : 2 < p) (hr : 0 < r) :
    trevisanFiniteUpperBound p r D ≤
      130000 * p ^ (r + 3) * 2 ^ (D + 2 * r) * r ^ 3 := by
  have hbase := trevisanFiniteUpperBound_le (p := p) (r := r) (D := D)
    (by omega) hr
  have hpr0 : 0 < p ^ 2 * r ^ 2 := by positivity
  have hpr : 1 ≤ p ^ 2 * r ^ 2 := by omega
  have hinner : 3200 * p ^ 2 * r ^ 2 + 1 ≤
      3201 * p ^ 2 * r ^ 2 := by
    nlinarith
  have hpoly : 40 * r * (3200 * p ^ 2 * r ^ 2 + 1) ≤
      128040 * p ^ 2 * r ^ 3 := by
    calc
      40 * r * (3200 * p ^ 2 * r ^ 2 + 1) ≤
          40 * r * (3201 * p ^ 2 * r ^ 2) :=
        Nat.mul_le_mul_left (40 * r) hinner
      _ = 128040 * p ^ 2 * r ^ 3 := by ring
  have hunit0 : 0 < p ^ 2 * r ^ 3 := by positivity
  have hunit : 1 ≤ p ^ 2 * r ^ 3 := by omega
  have htwo : 2 ^ (2 * r) ≤
      2 ^ (2 * r) * p ^ 2 * r ^ 3 := by
    simpa [mul_assoc] using Nat.mul_le_mul_left (2 ^ (2 * r)) hunit
  have hbracket :
      2 ^ (2 * r) + 40 * r * (3200 * p ^ 2 * r ^ 2 + 1) ≤
        130000 * 2 ^ (2 * r) * p ^ 2 * r ^ 3 := by
    calc
      2 ^ (2 * r) + 40 * r * (3200 * p ^ 2 * r ^ 2 + 1) ≤
          2 ^ (2 * r) * p ^ 2 * r ^ 3 +
            128040 * p ^ 2 * r ^ 3 := Nat.add_le_add htwo hpoly
      _ ≤ 130000 * 2 ^ (2 * r) * p ^ 2 * r ^ 3 := by
        have hpow0 : 0 < 2 ^ (2 * r) := by positivity
        have hpow : 1 ≤ 2 ^ (2 * r) := by omega
        nlinarith
  calc
    trevisanFiniteUpperBound p r D ≤
        p ^ r * p * 2 ^ D *
          (2 ^ (2 * r) + 40 * r * (3200 * p ^ 2 * r ^ 2 + 1)) := hbase
    _ ≤ p ^ r * p * 2 ^ D *
          (130000 * 2 ^ (2 * r) * p ^ 2 * r ^ 3) :=
      Nat.mul_le_mul_left (p ^ r * p * 2 ^ D) hbracket
    _ = 130000 * p ^ (r + 3) * 2 ^ (D + 2 * r) * r ^ 3 := by
      rw [Nat.pow_add, Nat.pow_add]
      ring

/-- A linear extractor family gives an ordinary normalized palette on every
shorter initial interval, with the exact carry and kernel bounds exposed. -/
theorem exists_normalizedPalette_of_linearExtractorFamily
    {p r d s N : ℕ} [Fact p.Prime]
    (hp : 2 < p) (hr : 0 < r) (hN : N ≤ p ^ (2 * r))
    (E : LinearExtractorFamily p r d s) :
    ∃ B : Finset ℕ,
      B ⊆ attainableNormalizedSums N ∧
      B.card ≤ 2 ^ (2 * r) * p ^ (r + d) ∧
      (sumGraph N B).indepNum ≤ p ^ (r + s) := by
  obtain ⟨S, hScard, hSind⟩ :=
    kernelPalette_of_linearExtractorFamily hp hr E
  obtain ⟨B, hBatt, hBcard, hBind⟩ :=
    carry_lift_restrict p (2 * r) N (by omega) hN S
  refine ⟨B, hBatt, hBcard.trans ?_, hBind.trans ?_⟩
  · exact Nat.mul_le_mul_left (2 ^ (2 * r)) hScard
  · exact Nat.le_of_lt hSind

/-- Exact finite upper bound for the original Erdős min--max function,
before choosing the asymptotic parameters. -/
theorem fNat_succ_le_of_linearExtractorFamily
    {p r d s N : ℕ} [Fact p.Prime]
    (hp : 2 < p) (hr : 0 < r) (hN : N ≤ p ^ (2 * r))
    (E : LinearExtractorFamily p r d s) :
    fNat (N + 1) ≤
      2 ^ (2 * r) * p ^ (r + d) + p ^ (r + s) := by
  obtain ⟨B, hBatt, hBcard, hBind⟩ :=
    exists_normalizedPalette_of_linearExtractorFamily hp hr hN E
  have hf := fNat_le_of_normalized_palette (N + 1) B (by
    simpa using hBatt)
  exact hf.trans (Nat.add_le_add hBcard hBind)

/-- Specialized form for the canonical integral Trevisan exponents. -/
theorem fNat_succ_le_of_trevisanFamily
    {p r D N : ℕ} [Fact p.Prime]
    (hp : 2 < p) (hr : 0 < r) (hN : N ≤ p ^ (2 * r))
    (E : LinearExtractorFamily p r
      (trevisanSeedExponent p D) (trevisanSlackExponent p r D)) :
    fNat (N + 1) ≤ trevisanFiniteUpperBound p r D := by
  exact fNat_succ_le_of_linearExtractorFamily hp hr hN E

end Erdos788


/-! Flattened from Erdos788.UpperExponentBounds. -/


/-!
# Converting the finite upper bound to an exponent bound

The finite construction produces a product of powers of `p`, `2`, and `r`.
This file performs the pointwise logarithmic calculation for the canonical
prime, dimension, and design choices.
-/

namespace Erdos788

/-- A deliberately rounded absolute constant for the upper exponent. -/
def upperExponentConstant : ℝ := 101000000

theorem upperExponentConstant_pos : 0 < upperExponentConstant := by
  norm_num [upperExponentConstant]

private theorem log_trevisanMonomial
    {p r D : ℕ} (hp : 0 < p) (hr : 0 < r) :
    Real.log (((130000 * p ^ (r + 3) * 2 ^ (D + 2 * r) * r ^ 3 : ℕ) : ℝ)) =
      Real.log 130000 + (r + 3 : ℕ) * Real.log p +
        (D + 2 * r : ℕ) * Real.log 2 + 3 * Real.log r := by
  push_cast
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow]
  push_cast
  ring

/-- The logarithm of the monomial finite majorant has the desired
`1/2 + O(exponentCorrection N)` exponent. -/
theorem log_trevisanMonomial_le_chosen
    {N : ℕ} (h : ParameterRegular N)
    (C : ShortLinearCode (parameterPrime N) (2 * parameterDimension N)
      (trevisanEta (parameterPrime N) (parameterDimension N))) :
    Real.log
        (((130000 * parameterPrime N ^ (parameterDimension N + 3) *
          2 ^ ((SuffixDesign.build C.ell (parameterDimension N)).coordCard +
            2 * parameterDimension N) * parameterDimension N ^ 3 : ℕ) : ℝ)) ≤
      ((1 / 2 : ℝ) + upperExponentConstant * exponentCorrection N) *
        Real.log (N : ℝ) := by
  let L := Real.log (N : ℝ)
  let q := Real.log L
  let δ := exponentCorrection N
  let p := parameterPrime N
  let r := parameterDimension N
  let D := (SuffixDesign.build C.ell r).coordCard
  let A := L * δ
  have hL : 0 < L := h.1
  have hq : 2 ≤ q := h.2.1
  have hδ : 0 < δ := parameterRegular_correction_pos h
  have hδ1 : δ ≤ 1 := parameterRegular_correction_le_one h
  have hp2 : 2 < p := by simpa [p] using two_lt_parameterPrime N
  have hpR : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hlp : 0 < Real.log (p : ℝ) := Real.log_pos hpR
  have hrNat : 0 < r := by
    apply parameterDimension_pos
    have hnR : (1 : ℝ) < N :=
      (Real.log_pos_iff (by positivity : (0 : ℝ) ≤ N)).mp h.1
    exact_mod_cast hnR
  have hrR : (0 : ℝ) < r := by exact_mod_cast hrNat
  have hA0 : 0 < A := mul_pos hL hδ
  have hA2 : 2 ≤ A := by
    simpa [A, L, δ] using parameterRegular_log_mul_correction h
  have hr : (r : ℝ) ≤ A := by
    simpa [r, A, L, δ] using parameterDimension_le_log_mul_correction h
  have hD : (D : ℝ) ≤ 100000000 * A := by
    simpa [D, r, A, L, δ, mul_assoc] using chosenDesign_coordCard_le h C
  have hpLog : Real.log (p : ℝ) ≤ 2 / δ := by
    simpa [p, δ] using log_parameterPrime_le_two_div_correction h.1
      (by linarith [h.2.1]) h.2.2.1
  have hpLogInv : Real.log (p : ℝ) ≤ 2 * δ⁻¹ := by
    simpa [div_eq_mul_inv] using hpLog
  have hlogr : Real.log (r : ℝ) ≤ Real.log (p : ℝ) := by
    have hrL : (r : ℝ) ≤ L := by
      simpa [r, L] using parameterDimension_le_log h
    have hlogrQ : Real.log (r : ℝ) ≤ q := by
      apply Real.log_le_log hrR
      simpa [q, L] using hrL
    have hqP : q ≤ Real.log (p : ℝ) := by
      simpa [q, L, p] using loglog_le_log_parameterPrime N
    exact hlogrQ.trans hqP
  have hrlp : (r : ℝ) * Real.log (p : ℝ) ≤
      L / 2 + Real.log (p : ℝ) := by
    have hnR : (1 : ℝ) < N :=
      (Real.log_pos_iff (by positivity : (0 : ℝ) ≤ N)).mp h.1
    have hn : 1 ≤ N := by exact_mod_cast hnR.le
    have hceil : (r : ℝ) <
        L / (2 * Real.log (p : ℝ)) + 1 := by
      simpa [r, L, p] using cast_parameterDimension_lt_log_div_add_one hn
    exact (calc
      (r : ℝ) * Real.log (p : ℝ) <
          (L / (2 * Real.log (p : ℝ)) + 1) *
            Real.log (p : ℝ) := mul_lt_mul_of_pos_right hceil hlp
      _ = L / 2 + Real.log (p : ℝ) := by
        field_simp
      ).le
  have hcube : δ ^ 3 = q / L := by
    simpa [δ, q, L] using
      exponentCorrection_pow_three h.1 (by linarith [h.2.1])
  have hqAδ : q = A * δ ^ 2 := by
    have hrel : L * δ ^ 3 = q := by
      rw [hcube]
      field_simp
    dsimp [A]
    rw [hrel.symm]
    ring
  have hinvA : δ⁻¹ ≤ A := by
    have hδsq : δ ^ 2 ≤ δ := by nlinarith [sq_nonneg δ]
    have hAδsq : 2 ≤ A * δ ^ 2 := by simpa [← hqAδ] using hq
    have hAδ : 1 ≤ A * δ := by
      have := mul_le_mul_of_nonneg_left hδsq hA0.le
      nlinarith
    have hdiv : 1 / δ ≤ A := (div_le_iff₀ hδ).2 hAδ
    simpa [one_div] using hdiv
  have hpA : Real.log (p : ℝ) ≤ 2 * A :=
    hpLogInv.trans (mul_le_mul_of_nonneg_left hinvA (by norm_num))
  have hlog2nonneg : 0 ≤ Real.log (2 : ℝ) :=
    Real.log_nonneg (by norm_num)
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have hraw :=
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hraw
    exact hraw
  have hconst : Real.log (130000 : ℝ) ≤ 65000 * A := by
    have hraw :=
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 130000)
    nlinarith
  have hpPower : ((r + 3 : ℕ) : ℝ) * Real.log (p : ℝ) ≤
      L / 2 + 8 * A := by
    push_cast
    nlinarith
  have htwoPower : ((D + 2 * r : ℕ) : ℝ) * Real.log (2 : ℝ) ≤
      100000002 * A := by
    push_cast
    have hDlog : (D : ℝ) * Real.log (2 : ℝ) ≤ D := by
      simpa using mul_le_mul_of_nonneg_left hlog2
        (by positivity : (0 : ℝ) ≤ (D : ℝ))
    have hrlog : (r : ℝ) * Real.log (2 : ℝ) ≤ r := by
      simpa using mul_le_mul_of_nonneg_left hlog2
        (by positivity : (0 : ℝ) ≤ (r : ℝ))
    nlinarith
  have hrPower : 3 * Real.log (r : ℝ) ≤ 6 * A := by
    nlinarith
  rw [log_trevisanMonomial (by omega : 0 < p) hrNat]
  have hsum :
      Real.log (130000 : ℝ) + ((r + 3 : ℕ) : ℝ) * Real.log (p : ℝ) +
          ((D + 2 * r : ℕ) : ℝ) * Real.log (2 : ℝ) +
            3 * Real.log (r : ℝ) ≤
        L / 2 + upperExponentConstant * A := by
    calc
      Real.log (130000 : ℝ) + ((r + 3 : ℕ) : ℝ) * Real.log (p : ℝ) +
            ((D + 2 * r : ℕ) : ℝ) * Real.log (2 : ℝ) +
              3 * Real.log (r : ℝ) ≤
          (65000 * A + (L / 2 + 8 * A)) + 100000002 * A + 6 * A :=
        add_le_add (add_le_add (add_le_add hconst hpPower) htwoPower) hrPower
      _ = L / 2 + 100065016 * A := by ring
      _ ≤ L / 2 + 101000000 * A := by
        gcongr
        norm_num
      _ = L / 2 + upperExponentConstant * A := by
        rfl
  calc
    Real.log (130000 : ℝ) + ((r + 3 : ℕ) : ℝ) * Real.log (p : ℝ) +
          ((D + 2 * r : ℕ) : ℝ) * Real.log (2 : ℝ) +
            3 * Real.log (r : ℝ) ≤
        L / 2 + upperExponentConstant * A := hsum
    _ = ((1 / 2 : ℝ) + upperExponentConstant * δ) * L := by
      dsimp [A]
      ring

/-- The canonical finite bound is dominated by the advertised real power. -/
theorem cast_trevisanFiniteUpperBound_le_rpow_chosen
    {N : ℕ} (h : ParameterRegular N)
    (C : ShortLinearCode (parameterPrime N) (2 * parameterDimension N)
      (trevisanEta (parameterPrime N) (parameterDimension N))) :
    ((trevisanFiniteUpperBound (parameterPrime N) (parameterDimension N)
        (SuffixDesign.build C.ell (parameterDimension N)).coordCard : ℕ) : ℝ) ≤
      (N : ℝ) ^
        ((1 / 2 : ℝ) + upperExponentConstant * exponentCorrection N) := by
  have hr : 0 < parameterDimension N := by
    apply parameterDimension_pos
    have hnR : (1 : ℝ) < N :=
      (Real.log_pos_iff (by positivity : (0 : ℝ) ≤ N)).mp h.1
    exact_mod_cast hnR
  have hmonoNat := trevisanFiniteUpperBound_le_monomial
    (two_lt_parameterPrime N) hr
    (D := (SuffixDesign.build C.ell (parameterDimension N)).coordCard)
  have hmonoReal :
      ((trevisanFiniteUpperBound (parameterPrime N) (parameterDimension N)
          (SuffixDesign.build C.ell (parameterDimension N)).coordCard : ℕ) : ℝ) ≤
        ((130000 * parameterPrime N ^ (parameterDimension N + 3) *
          2 ^ ((SuffixDesign.build C.ell (parameterDimension N)).coordCard +
            2 * parameterDimension N) * parameterDimension N ^ 3 : ℕ) : ℝ) := by
    exact_mod_cast hmonoNat
  have hnPos : (0 : ℝ) < N := by
    have hnR : (1 : ℝ) < N :=
      (Real.log_pos_iff (by positivity : (0 : ℝ) ≤ N)).mp h.1
    positivity
  have hlog := log_trevisanMonomial_le_chosen h C
  exact hmonoReal.trans (Real.le_rpow_of_log_le hnPos hlog)

end Erdos788


/-! Flattened from Erdos788.UpperFinal. -/


/-!
# Final upper bound

This module joins the canonical extractor, the finite palette construction,
and the pointwise exponent calculation for every sufficiently large integer.
-/

namespace Erdos788

/-- Pointwise upper bound at every regular parameter value. -/
theorem cast_fNat_le_rpow_of_parameterRegular
    {N : ℕ} (h : ParameterRegular N) :
    (fNat N : ℝ) ≤
      (N : ℝ) ^
        ((1 / 2 : ℝ) + upperExponentConstant * exponentCorrection N) := by
  obtain ⟨C, ⟨E⟩⟩ := exists_chosenLinearExtractorFamily h
  have hp : 2 < parameterPrime N := two_lt_parameterPrime N
  have hr : 0 < parameterDimension N := parameterDimension_pos_of_regular h
  have hnR : (1 : ℝ) < N :=
    (Real.log_pos_iff (by positivity : (0 : ℝ) ≤ N)).mp h.1
  have hn : 1 ≤ N := by exact_mod_cast hnR.le
  have hcover : N - 1 ≤ parameterPrime N ^ (2 * parameterDimension N) :=
    (Nat.sub_le N 1).trans (parameterDimension_cover N)
  have hfinite := fNat_succ_le_of_trevisanFamily hp hr hcover E
  rw [Nat.sub_add_cancel hn] at hfinite
  have hfiniteReal :
      (fNat N : ℝ) ≤
        (trevisanFiniteUpperBound (parameterPrime N) (parameterDimension N)
          (SuffixDesign.build C.ell (parameterDimension N)).coordCard : ℝ) := by
    exact_mod_cast hfinite
  exact hfiniteReal.trans (cast_trevisanFiniteUpperBound_le_rpow_chosen h C)

/-- The same bound for the integer-valued function in the problem statement. -/
theorem cast_f_le_rpow_of_parameterRegular
    {N : ℕ} (h : ParameterRegular N) :
    (f N : ℝ) ≤
      (N : ℝ) ^
        ((1 / 2 : ℝ) + upperExponentConstant * exponentCorrection N) := by
  simpa [f] using cast_fNat_le_rpow_of_parameterRegular h

/-- Eventual quantified form of the strong upper bound. -/
theorem exists_upperBound_threshold :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      (f N : ℝ) ≤
        (N : ℝ) ^
          ((1 / 2 : ℝ) + upperExponentConstant * exponentCorrection N) := by
  have hevent : ∀ᶠ N : ℕ in Filter.atTop,
      (f N : ℝ) ≤
        (N : ℝ) ^
          ((1 / 2 : ℝ) + upperExponentConstant * exponentCorrection N) :=
    eventually_parameterRegular.mono fun _N hN ↦
      cast_f_le_rpow_of_parameterRegular hN
  obtain ⟨m, hm⟩ := Filter.eventually_atTop.1 hevent
  refine ⟨max 1 m, le_max_left _ _, ?_⟩
  intro N hN
  exact hm N ((le_max_right 1 m).trans hN)

end Erdos788


/-! Flattened from Erdos788.ExponentConsequences. -/


/-!
# From the quantitative estimate to exponent one half

The explicit two-sided estimate immediately implies the usual
`n^(1/2+o(1))` formulation.  This file records that implication once, so the
final theorem only needs to establish the quantitative statement.
-/

namespace Erdos788

/-- The quantitative theorem implies the full epsilon formulation. -/
theorem quantitativeMainTheorem_implies_hasExponentOneHalf
    (hmain : QuantitativeMainTheorem) : HasExponentOneHalf := by
  rcases hmain with ⟨c, C, hc, hC, n₀, hn₀, hbound⟩
  intro ε hε
  have hNat : Filter.Tendsto (fun n : ℕ => (n : ℝ))
      Filter.atTop Filter.atTop := tendsto_natCast_atTop_atTop
  have hLog : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ))
      Filter.atTop Filter.atTop := Real.tendsto_log_atTop.comp hNat
  have hPow : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ ε)
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hε).comp hNat
  have hCorrection : ∀ᶠ n : ℕ in Filter.atTop,
      exponentCorrection n < ε / C :=
    (tendsto_order.1 exponentCorrection_tendsto_zero).2
      (ε / C) (div_pos hε hC)
  have hevent : ∀ᶠ n : ℕ in Filter.atTop,
      (n : ℝ) ^ ((1 / 2 : ℝ) - ε) ≤ (f n : ℝ) ∧
        (f n : ℝ) ≤ (n : ℝ) ^ ((1 / 2 : ℝ) + ε) := by
    filter_upwards [Filter.eventually_ge_atTop n₀,
      Filter.eventually_ge_atTop 1,
      hLog.eventually_ge_atTop 1,
      hPow.eventually_ge_atTop (1 / c), hCorrection] with
      n hnLarge hnOne hlogOne hpowLarge hcorr
    have hxpos : (0 : ℝ) < n := by
      exact_mod_cast (Nat.zero_lt_one.trans_le hnOne)
    have hxOne : (1 : ℝ) ≤ n := by exact_mod_cast hnOne
    have hcPow : (1 : ℝ) ≤ c * (n : ℝ) ^ ε := by
      calc
        (1 : ℝ) = c * (1 / c) := by field_simp
        _ ≤ c * (n : ℝ) ^ ε :=
          mul_le_mul_of_nonneg_left hpowLarge hc.le
    have hsplit :
        (n : ℝ) ^ ((1 / 2 : ℝ) - ε) * (n : ℝ) ^ ε =
          (n : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add hxpos]
      congr 1
      ring
    have hsqrt : Real.sqrt (n : ℝ) ≤
        Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
      apply Real.sqrt_le_sqrt
      have := mul_le_mul_of_nonneg_left hlogOne hxpos.le
      simpa using this
    have hlowerPower :
        (n : ℝ) ^ ((1 / 2 : ℝ) - ε) ≤
          c * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
      calc
        (n : ℝ) ^ ((1 / 2 : ℝ) - ε) =
            (n : ℝ) ^ ((1 / 2 : ℝ) - ε) * 1 := by ring
        _ ≤ (n : ℝ) ^ ((1 / 2 : ℝ) - ε) *
            (c * (n : ℝ) ^ ε) :=
          mul_le_mul_of_nonneg_left hcPow (Real.rpow_nonneg hxpos.le _)
        _ = c * ((n : ℝ) ^ ((1 / 2 : ℝ) - ε) *
            (n : ℝ) ^ ε) := by ring
        _ = c * (n : ℝ) ^ (1 / 2 : ℝ) := by rw [hsplit]
        _ = c * Real.sqrt (n : ℝ) := by rw [Real.sqrt_eq_rpow]
        _ ≤ c * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hsqrt hc.le
    have hCcorr : C * exponentCorrection n ≤ ε := by
      have hmul := mul_lt_mul_of_pos_left hcorr hC
      have heq : C * (ε / C) = ε := by field_simp
      linarith
    obtain ⟨hlower, hupper⟩ := hbound n hnLarge
    refine ⟨hlowerPower.trans hlower, hupper.trans ?_⟩
    exact Real.rpow_le_rpow_of_exponent_le hxOne (by linarith)
  obtain ⟨m, hm⟩ := Filter.eventually_atTop.1 hevent
  refine ⟨max 1 m, le_max_left _ _, ?_⟩
  intro n hn
  exact hm n ((le_max_right 1 m).trans hn)

end Erdos788


/-! Flattened from Erdos788.FinalTheorem. -/


/-!
# Final theorem for Erdős Problem 788

This module combines the explicit lower and upper estimates and then invokes
the already proved exponent-consequence theorem.
-/

namespace Erdos788

theorem finalLowerBoundConstant_pos : 0 < finalLowerBoundConstant := by
  norm_num [finalLowerBoundConstant]

/-- The complete quantitative two-sided estimate. -/
theorem quantitativeMainTheorem : QuantitativeMainTheorem := by
  obtain ⟨nLower, hnLower, hLower⟩ := exists_lowerBound_threshold
  obtain ⟨nUpper, hnUpper, hUpper⟩ := exists_upperBound_threshold
  refine ⟨finalLowerBoundConstant, upperExponentConstant,
    finalLowerBoundConstant_pos, upperExponentConstant_pos,
    max nLower nUpper, ?_, ?_⟩
  · exact hnLower.trans (le_max_left _ _)
  · intro n hn
    constructor
    · simpa only [finalLowerBoundConstant] using
        hLower n ((le_max_left nLower nUpper).trans hn)
    · exact hUpper n ((le_max_right nLower nUpper).trans hn)

/-- The explicit epsilon formulation of the exponent-one-half conclusion. -/
theorem hasExponentOneHalf : HasExponentOneHalf :=
  quantitativeMainTheorem_implies_hasExponentOneHalf quantitativeMainTheorem

/-- The strong paper's statement, including its fixed lower constant and the
fact that the lower estimate holds for every `n ≥ 3`. -/
theorem paperMainTheorem : PaperMainTheorem := by
  refine ⟨?_, ?_, hasExponentOneHalf⟩
  · intro n hn
    simpa only [finalLowerBoundConstant] using cast_f_lower hn
  · obtain ⟨nUpper, hnUpper, hUpper⟩ := exists_upperBound_threshold
    refine ⟨upperExponentConstant, upperExponentConstant_pos,
      max 3 nUpper, by omega, ?_⟩
    intro n hn
    constructor
    · simpa only [finalLowerBoundConstant] using
        cast_f_lower ((le_max_left 3 nUpper).trans hn)
    · exact hUpper n ((le_max_right 3 nUpper).trans hn)

/-- The original website's question `f(n) ≤ n^(1/2+o(1))`, with all
epsilon and eventual quantifiers made explicit. -/
theorem answersOriginalUpperQuestion : AnswersOriginalUpperQuestion := by
  intro ε hε
  obtain ⟨n₀, hn₀, hbound⟩ := hasExponentOneHalf ε hε
  exact ⟨n₀, hn₀, fun n hn ↦ (hbound n hn).2⟩

/-- Erdős Problem 788, preserving both the strong paper statement and the
exact quantifier form of the original upper-bound question. -/
theorem erdos788 : MainTheorem :=
  ⟨paperMainTheorem, answersOriginalUpperQuestion⟩

end Erdos788


/-! Exact local copy and canonical bridge. -/


namespace Erdos788.CanonicalPort

open Filter

def InUpperInterval (n : ℕ) (B : Finset ℕ) : Prop :=
  ∀ b ∈ B, 2 * n < b ∧ b < 4 * n

def InLowerInterval (n : ℕ) (C : Finset ℕ) : Prop :=
  ∀ c ∈ C, n < c ∧ c < 2 * n

def AvoidsDistinctSums (B C : Finset ℕ) : Prop :=
  ∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ ≠ c₂ → c₁ + c₂ ∉ B

noncomputable def bestForUpperSet (n : ℕ) (B : Finset ℕ) : ℕ :=
  sSup {m : ℕ | ∃ C : Finset ℕ,
    InLowerInterval n C ∧ AvoidsDistinctSums B C ∧
      m = C.card + B.card}

noncomputable def choiFunction (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ B : Finset ℕ,
    InUpperInterval n B ∧ bestForUpperSet n B = m}

abbrev statement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ n : ℕ in atTop,
      (choiFunction n : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 2 + ε)

theorem upper_subset {n : ℕ} {B : Finset ℕ}
    (hB : InUpperInterval n B) : B ⊆ J n := by
  intro b hb
  exact Finset.mem_Ioo.mpr (hB b hb)

theorem lower_subset {n : ℕ} {C : Finset ℕ}
    (hC : InLowerInterval n C) : C ⊆ I n := by
  intro c hc
  exact Finset.mem_Ioo.mpr (hC c hc)

theorem upper_of_subset {n : ℕ} {B : Finset ℕ}
    (hB : B ⊆ J n) : InUpperInterval n B := by
  intro b hb
  exact Finset.mem_Ioo.mp (hB hb)

theorem lower_of_subset {n : ℕ} {C : Finset ℕ}
    (hC : C ⊆ I n) : InLowerInterval n C := by
  intro c hc
  exact Finset.mem_Ioo.mp (hC hc)

theorem scoreSet_nonempty (n : ℕ) (B : Finset ℕ) :
    Set.Nonempty {m : ℕ | ∃ C : Finset ℕ,
      InLowerInterval n C ∧ AvoidsDistinctSums B C ∧
        m = C.card + B.card} := by
  refine ⟨B.card, ∅, ?_, ?_, by simp⟩
  · simp [InLowerInterval]
  · simp [AvoidsDistinctSums]

theorem scoreSet_bddAbove (n : ℕ) (B : Finset ℕ) :
    BddAbove {m : ℕ | ∃ C : Finset ℕ,
      InLowerInterval n C ∧ AvoidsDistinctSums B C ∧
        m = C.card + B.card} := by
  refine ⟨(I n).card + B.card, ?_⟩
  intro m hm
  obtain ⟨C, hC, _havoid, rfl⟩ := hm
  exact Nat.add_le_add_right (Finset.card_le_card (lower_subset hC)) B.card

theorem bestForUpperSet_spec (n : ℕ) (B : Finset ℕ) :
    ∃ C : Finset ℕ,
      InLowerInterval n C ∧ AvoidsDistinctSums B C ∧
        bestForUpperSet n B = C.card + B.card := by
  exact Nat.sSup_mem (scoreSet_nonempty n B) (scoreSet_bddAbove n B)

theorem score_le_bestForUpperSet {n : ℕ} {B C : Finset ℕ}
    (hC : InLowerInterval n C) (havoid : AvoidsDistinctSums B C) :
    C.card + B.card ≤ bestForUpperSet n B := by
  exact le_csSup (scoreSet_bddAbove n B) ⟨C, hC, havoid, rfl⟩

theorem outerSet_nonempty (n : ℕ) :
    Set.Nonempty {m : ℕ | ∃ B : Finset ℕ,
      InUpperInterval n B ∧ bestForUpperSet n B = m} := by
  refine ⟨bestForUpperSet n ∅, ∅, ?_, rfl⟩
  simp [InUpperInterval]

theorem choiFunction_eq_fNat (n : ℕ) :
    choiFunction n = fNat n := by
  apply Nat.le_antisymm
  · apply le_fNat
    intro B hB
    obtain ⟨C, hC, havoid, hbest⟩ := bestForUpperSet_spec n B
    refine ⟨C, ⟨lower_subset hC, havoid⟩, ?_⟩
    have hmin : choiFunction n ≤ bestForUpperSet n B :=
      Nat.sInf_le ⟨B, upper_of_subset hB, rfl⟩
    rw [hbest] at hmin
    simpa [Nat.add_comm] using hmin
  · obtain ⟨B, hB, hbest⟩ :=
      Nat.sInf_mem (outerSet_nonempty n)
    have hguarantee := fNat_guarantees n
    obtain ⟨C, hC, hscore⟩ := hguarantee B (upper_subset hB)
    have hmax : C.card + B.card ≤ bestForUpperSet n B :=
      score_le_bestForUpperSet
        (lower_of_subset hC.1) hC.2
    change bestForUpperSet n B = choiFunction n at hbest
    rw [hbest] at hmax
    omega

theorem proof : statement := by
  intro ε hε
  obtain ⟨n₀, _hn₀, hbound⟩ :=
    answersOriginalUpperQuestion ε hε
  filter_upwards [Filter.eventually_atTop.2 ⟨n₀, hbound⟩] with n hn
  simpa only [choiFunction_eq_fNat, f, Int.cast_natCast] using hn

end Erdos788.CanonicalPort

namespace Submissions.Erdos788ChoiSumAvoidance.KnownSolutionPorter2

theorem proof : Erdos788.CanonicalPort.statement :=
  Erdos788.CanonicalPort.proof

#print axioms proof

end Submissions.Erdos788ChoiSumAvoidance.KnownSolutionPorter2
