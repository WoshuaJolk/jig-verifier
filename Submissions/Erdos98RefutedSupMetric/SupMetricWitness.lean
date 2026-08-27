import Mathlib.Data.Finset.Prod
import Mathlib.Geometry.Euclidean.Sphere.Basic
import Mathlib.Topology.Instances.Nat
import Mathlib.Tactic

/-!
# Jig #35 (Erdős 98) is false as formalised: the plane is L∞, not Euclidean

`abbrev Plane := Fin 2 → ℝ` carries Mathlib's Pi metric, so `dist p q =
max |p₀-q₀| |p₁-q₁|`, and `EuclideanGeometry.Cospherical` (which needs only
`[MetricSpace P]`) means "on a common axis-parallel square".

Witness: `p_i = (4n²i, i²)` for `i = 1..n`.

* every distance is `max(4n²|i-j|, |i²-j²|) = 4n²|i-j|`, so at most `n` values;
* no three are collinear: the determinant is `4n²(j-i)(k-i)(k-j) ≠ 0`;
* no four are cospherical: an L∞ sphere has two vertical and two horizontal
  sides; the x-coordinates are distinct so at most two points sit on vertical
  sides, the y-coordinates are distinct so at most two sit on horizontal sides,
  and four points force both, giving `2r = 4n²|i-j| ≥ 4n²` and `2r = |k²-l²| ≤ n²`.

Hence `minDistinctDistances n ≤ n` and `h(n)/n ≤ 1`, so it cannot tend to `atTop`.
-/

namespace Submissions.Erdos98RefutedSupMetric.SupMetricWitness

open Filter Finset EuclideanGeometry
open scoped Topology
open Classical

abbrev Plane := Fin 2 → ℝ

def nonTrilinear (X : Set Plane) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, ∀ z ∈ X,
    x ≠ y → x ≠ z → y ≠ z → ¬Collinear ℝ {x, y, z}

def inGeneralPosition (X : Set Plane) : Prop :=
  nonTrilinear X ∧ ∀ T ⊆ X, T.ncard = 4 → ¬Cospherical T

noncomputable def distanceSet (points : Finset Plane) : Finset ℝ :=
  points.offDiag.image (fun pair => dist pair.1 pair.2)

noncomputable def distinctDistances (points : Finset Plane) : ℕ :=
  (distanceSet points).card

noncomputable def minDistinctDistances (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ points : Finset Plane,
    points.card = n ∧ inGeneralPosition points ∧ k = distinctDistances points}

/-- the witness point set -/
noncomputable def g (n i : ℕ) : Plane := ![4*(n:ℝ)^2*(i:ℝ), (i:ℝ)^2]

lemma g0 (n i : ℕ) : g n i 0 = 4*(n:ℝ)^2*(i:ℝ) := rfl
lemma g1 (n i : ℕ) : g n i 1 = (i:ℝ)^2 := rfl

noncomputable def P (n : ℕ) : Finset Plane := (Finset.Icc 1 n).image (g n)

lemma ginj {n : ℕ} (hn : 1 ≤ n) : Function.Injective (g n) := by
  intro i j h
  have := congrFun h 0
  rw [g0, g0] at this
  have hn' : (0:ℝ) < 4*(n:ℝ)^2 := by
    have : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    positivity
  have hij : (i:ℝ) = (j:ℝ) := by
    have := mul_left_cancel₀ (ne_of_gt hn') this
    exact this
  exact_mod_cast hij

lemma cardP {n : ℕ} (hn : 1 ≤ n) : (P n).card = n := by
  rw [P, Finset.card_image_of_injective _ (ginj hn), Nat.card_Icc]
  omega


lemma distg {n : ℕ} (hn : 1 ≤ n) {i j : ℕ} (hi : i ≤ n) (hj : j ≤ n) :
    dist (g n i) (g n j) = 4*(n:ℝ)^2 * |(i:ℝ) - (j:ℝ)| := by
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hc : (0:ℝ) ≤ 4*(n:ℝ)^2 * |(i:ℝ) - (j:ℝ)| := by positivity
  refine le_antisymm ?_ ?_
  · rw [dist_pi_le_iff hc]
    intro b
    fin_cases b
    · show dist (g n i 0) (g n j 0) ≤ _
      rw [g0, g0, Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 4*(n:ℝ)^2)]
    · show dist (g n i 1) (g n j 1) ≤ _
      rw [g1, g1, Real.dist_eq]
      have hfac : (i:ℝ)^2 - (j:ℝ)^2 = ((i:ℝ) - (j:ℝ)) * ((i:ℝ) + (j:ℝ)) := by ring
      rw [hfac, abs_mul]
      have h1 : |(i:ℝ) + (j:ℝ)| ≤ 2*(n:ℝ) := by
        have hi' : (i:ℝ) ≤ (n:ℝ) := by exact_mod_cast hi
        have hj' : (j:ℝ) ≤ (n:ℝ) := by exact_mod_cast hj
        have hi0 : (0:ℝ) ≤ (i:ℝ) := Nat.cast_nonneg i
        have hj0 : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
        rw [abs_le]; constructor <;> linarith
      have h2 : (2:ℝ)*(n:ℝ) ≤ 4*(n:ℝ)^2 := by
        have h1n : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
        nlinarith
      have := abs_nonneg ((i:ℝ) - (j:ℝ))
      nlinarith [h1, h2, abs_nonneg ((i:ℝ) - (j:ℝ))]
  · have h0 := dist_le_pi_dist (g n i) (g n j) 0
    rw [g0, g0, Real.dist_eq, ← mul_sub, abs_mul,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 4*(n:ℝ)^2)] at h0
    exact h0

lemma distSubset {n : ℕ} (hn : 1 ≤ n) :
    distanceSet (P n) ⊆ (Finset.range n).image (fun k : ℕ => 4*(n:ℝ)^2*(k:ℝ)) := by
  intro d hd
  rw [distanceSet, Finset.mem_image] at hd
  obtain ⟨pair, hpair, rfl⟩ := hd
  rw [Finset.mem_offDiag] at hpair
  obtain ⟨h1, h2, _⟩ := hpair
  rw [P, Finset.mem_image] at h1 h2
  obtain ⟨i, hi, hgi⟩ := h1
  obtain ⟨j, hj, hgj⟩ := h2
  simp only [Finset.mem_Icc] at hi hj
  rw [← hgi, ← hgj, distg hn hi.2 hj.2]
  rcases le_total i j with h | h
  · refine Finset.mem_image.2 ⟨j - i, ?_, ?_⟩
    · rw [Finset.mem_range]; omega
    · have hc : ((j - i : ℕ) : ℝ) = (j:ℝ) - (i:ℝ) := by
        have : (i:ℝ) ≤ (j:ℝ) := by exact_mod_cast h
        push_cast [Nat.cast_sub h]; ring
      rw [hc, abs_of_nonpos (by
        have : (i:ℝ) ≤ (j:ℝ) := by exact_mod_cast h
        linarith)]
      ring
  · refine Finset.mem_image.2 ⟨i - j, ?_, ?_⟩
    · rw [Finset.mem_range]; omega
    · have hc : ((i - j : ℕ) : ℝ) = (i:ℝ) - (j:ℝ) := by
        push_cast [Nat.cast_sub h]; ring
      rw [hc, abs_of_nonneg (by
        have : (j:ℝ) ≤ (i:ℝ) := by exact_mod_cast h
        linarith)]

lemma distCount {n : ℕ} (hn : 1 ≤ n) : distinctDistances (P n) ≤ n := by
  rw [distinctDistances]
  calc (distanceSet (P n)).card
      ≤ ((Finset.range n).image (fun k : ℕ => 4*(n:ℝ)^2*(k:ℝ))).card :=
        Finset.card_le_card (distSubset hn)
    _ ≤ (Finset.range n).card := Finset.card_image_le
    _ = n := Finset.card_range n

lemma det_of_collinear {x y z : Plane} (h : Collinear ℝ ({x, y, z} : Set Plane)) :
    (y 0 - x 0) * (z 1 - x 1) - (y 1 - x 1) * (z 0 - x 0) = 0 := by
  rw [collinear_iff_of_mem (Set.mem_insert x {y, z})] at h
  obtain ⟨v, hv⟩ := h
  obtain ⟨ry, hry⟩ := hv y (by simp)
  obtain ⟨rz, hrz⟩ := hv z (by simp)
  have hy0 : y 0 - x 0 = ry * v 0 := by rw [hry]; simp [Pi.add_apply]
  have hy1 : y 1 - x 1 = ry * v 1 := by rw [hry]; simp [Pi.add_apply]
  have hz0 : z 0 - x 0 = rz * v 0 := by rw [hrz]; simp [Pi.add_apply]
  have hz1 : z 1 - x 1 = rz * v 1 := by rw [hrz]; simp [Pi.add_apply]
  rw [hy0, hy1, hz0, hz1]; ring

lemma noncol {n : ℕ} (hn : 1 ≤ n) : nonTrilinear ↑(P n) := by
  rintro x hx y hy z hz hxy hxz hyz hcol
  simp only [P, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_Icc] at hx hy hz
  obtain ⟨i, hi, hix⟩ := hx
  obtain ⟨j, hj, hjy⟩ := hy
  obtain ⟨k, hk, hkz⟩ := hz
  have hij : i ≠ j := by rintro rfl; exact hxy (hix.symm.trans hjy)
  have hik : i ≠ k := by rintro rfl; exact hxz (hix.symm.trans hkz)
  have hjk : j ≠ k := by rintro rfl; exact hyz (hjy.symm.trans hkz)
  have hdet := det_of_collinear hcol
  rw [← hix, ← hjy, ← hkz] at hdet
  simp only [g0, g1] at hdet
  have hexp : (4*(n:ℝ)^2*(j:ℝ) - 4*(n:ℝ)^2*(i:ℝ)) * ((k:ℝ)^2 - (i:ℝ)^2)
      - ((j:ℝ)^2 - (i:ℝ)^2) * (4*(n:ℝ)^2*(k:ℝ) - 4*(n:ℝ)^2*(i:ℝ))
      = 4*(n:ℝ)^2 * (((j:ℝ)-(i:ℝ)) * (((k:ℝ)-(i:ℝ)) * ((k:ℝ)-(j:ℝ)))) := by ring
  rw [hexp] at hdet
  have hn0 : (4:ℝ)*(n:ℝ)^2 ≠ 0 := by
    have : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    positivity
  have h1 : ((j:ℝ)-(i:ℝ)) ≠ 0 := by
    intro h; exact hij (by exact_mod_cast (sub_eq_zero.1 h).symm)
  have h2 : ((k:ℝ)-(i:ℝ)) ≠ 0 := by
    intro h; exact hik (by exact_mod_cast (sub_eq_zero.1 h).symm)
  have h3 : ((k:ℝ)-(j:ℝ)) ≠ 0 := by
    intro h; exact hjk (by exact_mod_cast (sub_eq_zero.1 h).symm)
  exact (mul_ne_zero hn0 (mul_ne_zero h1 (mul_ne_zero h2 h3))) hdet

lemma inj0 {n : ℕ} (hn : 1 ≤ n) {p q : Plane} (hp : p ∈ P n) (hq : q ∈ P n)
    (h : p 0 = q 0) : p = q := by
  rw [P, Finset.mem_image] at hp hq
  obtain ⟨i, _, hip⟩ := hp
  obtain ⟨j, _, hjq⟩ := hq
  rw [← hip, ← hjq] at h ⊢
  rw [g0, g0] at h
  have hn' : (0:ℝ) < 4*(n:ℝ)^2 := by
    have : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    positivity
  have : (i:ℝ) = (j:ℝ) := mul_left_cancel₀ (ne_of_gt hn') h
  have : i = j := by exact_mod_cast this
  rw [this]

lemma inj1 {n : ℕ} {p q : Plane} (hp : p ∈ P n) (hq : q ∈ P n)
    (h : p 1 = q 1) : p = q := by
  rw [P, Finset.mem_image] at hp hq
  obtain ⟨i, hi, hip⟩ := hp
  obtain ⟨j, hj, hjq⟩ := hq
  simp only [Finset.mem_Icc] at hi hj
  rw [← hip, ← hjq] at h ⊢
  rw [g1, g1] at h
  have hij : i = j := by
    have h0i : (0:ℝ) ≤ (i:ℝ) := Nat.cast_nonneg i
    have h0j : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
    have : (i:ℝ) = (j:ℝ) := by nlinarith [h]
    exact_mod_cast this
  rw [hij]

lemma coord_le {p c : Plane} {r : ℝ} (h : dist p c = r) (b : Fin 2) :
    |p b - c b| ≤ r := by
  have := dist_le_pi_dist p c b
  rw [h, Real.dist_eq] at this
  exact this

lemma coord_eq {p c : Plane} {r : ℝ} (h : dist p c = r) :
    |p 0 - c 0| = r ∨ |p 1 - c 1| = r := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h0, h1⟩ := hcon
  have l0 : |p 0 - c 0| < r := lt_of_le_of_ne (coord_le h 0) h0
  have l1 : |p 1 - c 1| < r := lt_of_le_of_ne (coord_le h 1) h1
  set m := max (|p 0 - c 0|) (|p 1 - c 1|) with hm
  have hmr : m < r := max_lt l0 l1
  have : dist p c ≤ m := by
    rw [dist_pi_le_iff (le_trans (abs_nonneg _) (le_max_left _ _))]
    intro b
    fin_cases b
    · rw [Real.dist_eq]; exact le_max_left _ _
    · rw [Real.dist_eq]; exact le_max_right _ _
  rw [h] at this
  linarith

lemma memP {n : ℕ} {p : Plane} (hp : p ∈ P n) : ∃ i, 1 ≤ i ∧ i ≤ n ∧ p = g n i := by
  rw [P, Finset.mem_image] at hp
  obtain ⟨i, hi, hip⟩ := hp
  simp only [Finset.mem_Icc] at hi
  exact ⟨i, hi.1, hi.2, hip.symm⟩

lemma nocosph {n : ℕ} (hn : 1 ≤ n) :
    ∀ T ⊆ (P n : Set Plane), T.ncard = 4 → ¬Cospherical T := by
  rintro T hT hcard ⟨c, r, hc⟩
  have hfin : T.Finite := Set.Finite.subset (P n).finite_toSet hT
  set S : Finset Plane := hfin.toFinset with hS
  have hmem : ∀ p, p ∈ S ↔ p ∈ T := by intro p; rw [hS]; exact Set.Finite.mem_toFinset hfin
  have hScard : S.card = 4 := by
    rw [hS, ← Set.ncard_eq_toFinset_card T hfin]; exact hcard
  have hSP : ∀ p ∈ S, p ∈ P n := by
    intro p hp; exact hT ((hmem p).1 hp)
  have hr0 : 0 ≤ r := by
    have : S.Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨p, hp⟩ := this
    exact le_trans (abs_nonneg _) (coord_le (hc p ((hmem p).1 hp)) 0)
  classical
  set V : Finset Plane := S.filter (fun p => |p 0 - c 0| = r) with hV
  set H : Finset Plane := S.filter (fun p => |p 1 - c 1| = r) with hH
  have hcover : ∀ p ∈ S, p ∈ V ∨ p ∈ H := by
    intro p hp
    rcases coord_eq (hc p ((hmem p).1 hp)) with h | h
    · exact Or.inl (Finset.mem_filter.2 ⟨hp, h⟩)
    · exact Or.inr (Finset.mem_filter.2 ⟨hp, h⟩)
  have hcard2 : ∀ a b : ℝ, ({a, b} : Finset ℝ).card ≤ 2 := by
    intro a b; exact (Finset.card_insert_le _ _).trans (by simp)
  have hVle : V.card ≤ 2 := by
    have h1 : V.card ≤ ({c 0 - r, c 0 + r} : Finset ℝ).card := by
      refine Finset.card_le_card_of_injOn (fun p : Plane => p 0) ?_ ?_
      · intro a ha
        simp only [Finset.mem_coe, hV, Finset.mem_filter] at ha
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff]
        rcases (abs_eq hr0).1 ha.2 with h | h
        · exact Or.inr (by linarith)
        · exact Or.inl (by linarith)
      · intro a ha b hb hab
        simp only [Finset.mem_coe, hV, Finset.mem_filter] at ha hb
        exact inj0 hn (hSP a ha.1) (hSP b hb.1) hab
    have := hcard2 (c 0 - r) (c 0 + r); omega
  have hHle : H.card ≤ 2 := by
    have h1 : H.card ≤ ({c 1 - r, c 1 + r} : Finset ℝ).card := by
      refine Finset.card_le_card_of_injOn (fun p : Plane => p 1) ?_ ?_
      · intro a ha
        simp only [Finset.mem_coe, hH, Finset.mem_filter] at ha
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff]
        rcases (abs_eq hr0).1 ha.2 with h | h
        · exact Or.inr (by linarith)
        · exact Or.inl (by linarith)
      · intro a ha b hb hab
        simp only [Finset.mem_coe, hH, Finset.mem_filter] at ha hb
        exact inj1 (hSP a ha.1) (hSP b hb.1) hab
    have := hcard2 (c 1 - r) (c 1 + r); omega
  have hVge : 2 ≤ V.card := by
    have hsub : S \ H ⊆ V := by
      intro p hp
      rw [Finset.mem_sdiff] at hp
      rcases hcover p hp.1 with h | h
      · exact h
      · exact absurd h hp.2
    have : 2 ≤ (S \ H).card := by
      have hsc := Finset.card_sdiff_add_card_eq_card (s := H) (t := S) (Finset.filter_subset _ S)
      omega
    exact le_trans this (Finset.card_le_card hsub)
  have hHge : 2 ≤ H.card := by
    have hsub : S \ V ⊆ H := by
      intro p hp
      rw [Finset.mem_sdiff] at hp
      rcases hcover p hp.1 with h | h
      · exact absurd h hp.2
      · exact h
    have : 2 ≤ (S \ V).card := by
      have hsc := Finset.card_sdiff_add_card_eq_card (s := V) (t := S) (Finset.filter_subset _ S)
      omega
    exact le_trans this (Finset.card_le_card hsub)
  -- two distinct points on the vertical sides
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.1 (show 1 < V.card by omega)
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.1 (show 1 < H.card by omega)
  simp only [hV, Finset.mem_filter] at hp hq
  simp only [hH, Finset.mem_filter] at hu hv
  obtain ⟨i, hi1, hi2, hpi⟩ := memP (hSP p hp.1)
  obtain ⟨j, hj1, hj2, hqj⟩ := memP (hSP q hq.1)
  obtain ⟨k, hk1, hk2, huk⟩ := memP (hSP u hu.1)
  obtain ⟨l, hl1, hl2, hvl⟩ := memP (hSP v hv.1)
  have hij : i ≠ j := by rintro rfl; exact hpq (hpi.trans hqj.symm)
  have hkl : k ≠ l := by rintro rfl; exact huv (huk.trans hvl.symm)
  have hp0 : p 0 = 4*(n:ℝ)^2*(i:ℝ) := by rw [hpi, g0]
  have hq0 : q 0 = 4*(n:ℝ)^2*(j:ℝ) := by rw [hqj, g0]
  have hu1 : u 1 = (k:ℝ)^2 := by rw [huk, g1]
  have hv1 : v 1 = (l:ℝ)^2 := by rw [hvl, g1]
  have hne0 : p 0 ≠ q 0 := fun h => hpq (inj0 hn (hSP p hp.1) (hSP q hq.1) h)
  have hne1 : u 1 ≠ v 1 := fun h => huv (inj1 (hSP u hu.1) (hSP v hv.1) h)
  -- 2r equals the coordinate gaps
  have hVgap : |p 0 - q 0| = 2*r := by
    rcases (abs_eq hr0).1 hp.2 with h1 | h1 <;> rcases (abs_eq hr0).1 hq.2 with h2 | h2
    · exact absurd (by linarith : p 0 = q 0) hne0
    · rw [abs_of_nonneg (by linarith)]; linarith
    · rw [abs_of_nonpos (by linarith)]; linarith
    · exact absurd (by linarith : p 0 = q 0) hne0
  have hHgap : |u 1 - v 1| = 2*r := by
    rcases (abs_eq hr0).1 hu.2 with h1 | h1 <;> rcases (abs_eq hr0).1 hv.2 with h2 | h2
    · exact absurd (by linarith : u 1 = v 1) hne1
    · rw [abs_of_nonneg (by linarith)]; linarith
    · rw [abs_of_nonpos (by linarith)]; linarith
    · exact absurd (by linarith : u 1 = v 1) hne1
  have hnR : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  -- lower bound from the vertical sides
  have hlow : 4*(n:ℝ)^2 ≤ 2*r := by
    have hd : (1:ℝ) ≤ |(i:ℝ) - (j:ℝ)| := by
      rcases lt_or_gt_of_ne hij with h | h
      · have hij' : (i:ℝ) + 1 ≤ (j:ℝ) := by exact_mod_cast h
        rw [abs_of_nonpos (by linarith)]
        linarith
      · have hij' : (j:ℝ) + 1 ≤ (i:ℝ) := by exact_mod_cast h
        rw [abs_of_nonneg (by linarith)]
        linarith
    have : |p 0 - q 0| = 4*(n:ℝ)^2 * |(i:ℝ) - (j:ℝ)| := by
      rw [hp0, hq0, ← mul_sub, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 4*(n:ℝ)^2)]
    rw [this] at hVgap
    nlinarith [hVgap, hd]
  -- upper bound from the horizontal sides
  have hhigh : 2*r ≤ (n:ℝ)^2 := by
    have hk : (1:ℝ) ≤ (k:ℝ) ∧ (k:ℝ) ≤ (n:ℝ) := ⟨by exact_mod_cast hk1, by exact_mod_cast hk2⟩
    have hl : (1:ℝ) ≤ (l:ℝ) ∧ (l:ℝ) ≤ (n:ℝ) := ⟨by exact_mod_cast hl1, by exact_mod_cast hl2⟩
    rw [hu1, hv1] at hHgap
    rcases abs_cases ((k:ℝ)^2 - (l:ℝ)^2) with ⟨he, _⟩ | ⟨he, _⟩
    · rw [he] at hHgap; nlinarith [hk.1, hk.2, hl.1, hl.2]
    · rw [he] at hHgap; nlinarith [hk.1, hk.2, hl.1, hl.2]
  nlinarith [hlow, hhigh, hnR]

lemma genpos {n : ℕ} (hn : 1 ≤ n) : inGeneralPosition (P n : Set Plane) :=
  ⟨noncol hn, nocosph hn⟩

lemma hle {n : ℕ} (hn : 1 ≤ n) : minDistinctDistances n ≤ n := by
  have hmem : distinctDistances (P n) ∈
      {k : ℕ | ∃ points : Finset Plane,
        points.card = n ∧ inGeneralPosition points ∧ k = distinctDistances points} :=
    ⟨P n, cardP hn, genpos hn, rfl⟩
  exact le_trans (Nat.sInf_le hmem) (distCount hn)

theorem refutation :
    ¬ Tendsto (fun n : ℕ => (minDistinctDistances n : ℝ) / (n : ℝ)) atTop atTop := by
  intro h
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (tendsto_atTop.1 h 2)
  set m := max N 1 with hm
  have hm1 : 1 ≤ m := le_max_right _ _
  have hNn := hN m (le_max_left _ _)
  have hb : (minDistinctDistances m : ℝ) ≤ (m:ℝ) := by exact_mod_cast hle hm1
  have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm1
  rw [le_div_iff₀ hmpos] at hNn
  linarith


theorem proof :
    ¬ Tendsto (fun n : ℕ => (minDistinctDistances n : ℝ) / (n : ℝ)) atTop atTop :=
  refutation

end Submissions.Erdos98RefutedSupMetric.SupMetricWitness
