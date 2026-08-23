import Mathlib

/-!
# `h(L_d(2)) ≥ d!`: the permutohedron of `(2⁰, 2¹, …, 2^(d-1))` is an empty polytope

Proof of `ExpLatticeFactorialLB`, in every dimension `d` at once.

`V` is the set of `d!` points obtained by permuting the coordinates of `(2⁰, …, 2^(d-1))`.

*Convex position* is the norm argument, which is dimension-free and needs no rearrangement
inequality.  Every `v ∈ V` has the same squared norm `Q = Σ_{j<d} 4^j`, so for `w ≠ v`
`⟪v,w⟫ = Q - |v-w|²/2 < Q`; and `⟪v,w⟫` is a natural number, so in fact `⟪v,w⟫ ≤ Q - 1`,
which is the uniform threshold a single separating functional needs.  The functional
`x ↦ ⟪v,x⟫` therefore separates `v` from the hull of the others.

*Emptiness* is the arithmetic half.  Every `v ∈ V` has coordinate sum `2^d - 1`, so the two
functionals `±(1,…,1)` confine `conv V` to that hyperplane, and a lattice point of `L_d(2)`
in the hull is a `d`-tuple of powers of two summing to `2^d - 1`.  A multiset of exponents
whose powers of two sum to `n` has at least `n.bitIndices.length` elements — merging a
repeat, `2^a + 2^a = 2^(a+1)`, keeps the sum and drops the count — and
`(2^d - 1).bitIndices = range d` has length `d`, so a `d`-element multiset meeting the bound
has no repeat and is the binary representation.  The tuple is then a permutation of
`(2⁰, …, 2^(d-1))`, i.e. a point of `V`.

The arithmetic half is the statement filed on this board as `TwoPowerBinaryUniqueness`
(green).  A submission may not import another submission, so the argument is re-derived here
in the two forms this proof needs; the transfer from `Fin d → ℕ` to a multiset, which that
statement does not carry, is `perm_of_sum_eq` below.
-/

set_option maxHeartbeats 1000000

namespace Submissions.ExpLatticeFactorialLB.Permutohedron

open Finset

/-! ### The arithmetic half: the binary representation is the unique `d`-term one -/

/-- The sum of `2 ^ i` over a multiset of exponents. -/
def S (s : Multiset ℕ) : ℕ := (s.map (fun i => 2 ^ i)).sum

@[simp] theorem S_cons (a : ℕ) (t : Multiset ℕ) : S (a ::ₘ t) = 2 ^ a + S t := by simp [S]

theorem S_coe (L : List ℕ) : S (↑L) = (L.map (fun i => 2 ^ i)).sum := by simp [S]

theorem sum_range_two_pow (d : ℕ) : ((List.range d).map (fun i => 2 ^ i)).sum = 2 ^ d - 1 := by
  induction d with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [pow_succ]
    omega

theorem bitIndices_pred (d : ℕ) : (2 ^ d - 1).bitIndices = List.range d := by
  have h := Nat.bitIndices_sum_map_two_pow (L := List.range d) (List.sortedLT_range d)
  rwa [sum_range_two_pow] at h

theorem sorted_lt_of_nodup (s : Multiset ℕ) (h : s.Nodup) : (s.sort (· ≤ ·)).SortedLT := by
  rw [List.sortedLT_iff_pairwise]
  have hnd : (s.sort (· ≤ ·)).Nodup := by
    rw [← Multiset.coe_nodup, Multiset.sort_eq]; exact h
  have hle := Multiset.pairwise_sort s (· ≤ ·)
  exact List.Pairwise.imp₂ (fun _ _ hab hne => lt_of_le_of_ne hab hne) hle hnd

/-- A multiset of exponents whose powers of two sum to `n` has at least as many elements as
`n` has binary digits: merging a repeat keeps the sum and drops the count. -/
theorem bitIndices_length_le :
    ∀ (n : ℕ) (s : Multiset ℕ), Multiset.card s = n → (S s).bitIndices.length ≤ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hcard
    by_cases hnd : s.Nodup
    · have hL := sorted_lt_of_nodup s hnd
      have hs : S s = ((s.sort (· ≤ ·)).map (fun i => 2 ^ i)).sum := by
        rw [← S_coe, Multiset.sort_eq]
      rw [hs, Nat.bitIndices_sum_map_two_pow hL]
      rw [← hcard, ← Multiset.coe_card, Multiset.sort_eq]
    · rw [Multiset.nodup_iff_count_le_one] at hnd
      push_neg at hnd
      obtain ⟨a, ha⟩ := hnd
      have hmem : a ∈ s := Multiset.count_pos.mp (by omega)
      obtain ⟨s', rfl⟩ := Multiset.exists_cons_of_mem hmem
      have hmem' : a ∈ s' := by
        rw [Multiset.count_cons_self] at ha
        exact Multiset.count_pos.mp (by omega)
      obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem hmem'
      have hct : Multiset.card ((a + 1) ::ₘ t) = n - 1 := by
        simp only [Multiset.card_cons] at hcard ⊢
        omega
      have hlt : n - 1 < n := by
        simp only [Multiset.card_cons] at hcard
        omega
      have hSt : S (a ::ₘ a ::ₘ t) = S ((a + 1) ::ₘ t) := by
        simp only [S_cons, pow_succ]
        ring
      have hle := ih (n - 1) hlt ((a + 1) ::ₘ t) hct
      rw [hSt]
      omega

theorem nodup_of_card_le (s : Multiset ℕ)
    (h : Multiset.card s ≤ (S s).bitIndices.length) : s.Nodup := by
  by_contra hnd
  rw [Multiset.nodup_iff_count_le_one] at hnd
  push_neg at hnd
  obtain ⟨a, ha⟩ := hnd
  have hmem : a ∈ s := Multiset.count_pos.mp (by omega)
  obtain ⟨s', rfl⟩ := Multiset.exists_cons_of_mem hmem
  have hmem' : a ∈ s' := by
    rw [Multiset.count_cons_self] at ha
    exact Multiset.count_pos.mp (by omega)
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem hmem'
  have hSt : S (a ::ₘ a ::ₘ t) = S ((a + 1) ::ₘ t) := by
    simp only [S_cons, pow_succ]; ring
  have hle := bitIndices_length_le (Multiset.card ((a + 1) ::ₘ t)) _ rfl
  rw [← hSt] at hle
  simp only [Multiset.card_cons] at h hle
  omega

/-- **Uniqueness of the binary representation.**  A multiset of exactly `d` exponents whose
powers of two sum to `2 ^ d - 1` is `{0, 1, …, d-1}`. -/
theorem eq_range (d : ℕ) (s : Multiset ℕ) (hc : Multiset.card s = d)
    (hS : S s = 2 ^ d - 1) : s = Multiset.range d := by
  have hbi : (S s).bitIndices = List.range d := by rw [hS, bitIndices_pred]
  have hlen : (S s).bitIndices.length = d := by rw [hbi, List.length_range]
  have hnd : s.Nodup := nodup_of_card_le s (by omega)
  have hsum : S s = ((s.sort (· ≤ ·)).map (fun i => 2 ^ i)).sum := by
    rw [← S_coe, Multiset.sort_eq]
  have hsort : s.sort (· ≤ ·) = List.range d := by
    rw [← hbi, hsum, Nat.bitIndices_sum_map_two_pow (sorted_lt_of_nodup s hnd)]
  calc s = ↑(s.sort (· ≤ ·)) := (Multiset.sort_eq s _).symm
    _ = ↑(List.range d) := by rw [hsort]
    _ = Multiset.range d := rfl

/-! ### The transfer: a `d`-tuple of exponents summing correctly is a permutation -/

/-- If `n : Fin d → ℕ` has `Σ 2^(n i) = 2^d - 1` then `n` is a permutation of `0, …, d-1`:
there is `σ : Equiv.Perm (Fin d)` with `(σ i : ℕ) = n i` for every `i`. -/
theorem perm_of_sum_eq {d : ℕ} (n : Fin d → ℕ)
    (hsum : ∑ i : Fin d, 2 ^ (n i) = 2 ^ d - 1) :
    ∃ σ : Equiv.Perm (Fin d), ∀ i, (σ i : ℕ) = n i := by
  classical
  set s : Multiset ℕ := Multiset.map n Finset.univ.val with hs
  have hcard : Multiset.card s = d := by
    simp [hs, Finset.card_univ]
  have hSs : S s = 2 ^ d - 1 := by
    rw [← hsum]
    simp only [S, hs, Finset.sum, Multiset.map_map]
    rfl
  have hrange : s = Multiset.range d := eq_range d s hcard hSs
  -- every value is `< d`
  have hlt : ∀ i, n i < d := by
    intro i
    have : n i ∈ s := by
      simp only [hs]
      exact Multiset.mem_map_of_mem n (Finset.mem_univ i)
    rw [hrange, Multiset.mem_range] at this
    exact this
  -- `n` is injective, since `range d` has no duplicate
  have hnd : s.Nodup := by rw [hrange]; exact Multiset.nodup_range d
  have hinj : Function.Injective n := by
    intro i j hij
    exact Multiset.inj_on_of_nodup_map (s := Finset.univ.val) (by rw [← hs]; exact hnd)
      i (Finset.mem_univ i) j (Finset.mem_univ j) hij
  -- package as a permutation of `Fin d`
  let m : Fin d → Fin d := fun i => ⟨n i, hlt i⟩
  have hminj : Function.Injective m := by
    intro i j hij
    exact hinj (congrArg Fin.val hij)
  exact ⟨Equiv.ofBijective m (Finite.injective_iff_bijective.mp hminj), fun i => rfl⟩

/-! ### Geometry -/

variable {d : ℕ}

/-- The lattice point of `L_d(2)` attached to a permutation `σ`: its `i`-th coordinate is
`2 ^ σ(i)`. -/
def rp (σ : Equiv.Perm (Fin d)) : Fin d → ℝ := fun i => (2 : ℝ) ^ ((σ i : ℕ))

/-- The vertex set: the `d!` permutations of `(2⁰, …, 2^(d-1))`. -/
def VS (d : ℕ) : Set (Fin d → ℝ) := Set.range (rp (d := d))

/-- The exponential lattice `L_d(2) = {2ⁿ : n ∈ ℕ₀}^d`. -/
def LAT (d : ℕ) : Set (Fin d → ℝ) := {x : Fin d → ℝ | ∀ i, ∃ n : ℕ, x i = (2 : ℝ) ^ n}

/-- The linear functional with real coefficient vector `a`. -/
def LF (a x : Fin d → ℝ) : ℝ := ∑ i, a i * x i

theorem isLinearMap_LF (a : Fin d → ℝ) : IsLinearMap ℝ (LF a) := by
  constructor
  · intro x y
    simp only [LF, Pi.add_apply, mul_add]
    exact Finset.sum_add_distrib
  · intro c x
    simp only [LF, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

theorem hull_le {a : Fin d → ℝ} {r : ℝ} {T : Set (Fin d → ℝ)}
    (hT : ∀ x ∈ T, LF a x ≤ r) {p : Fin d → ℝ} (hp : p ∈ convexHull ℝ T) : LF a p ≤ r :=
  convexHull_min hT (convex_halfSpace_le (isLinearMap_LF a) r) hp

theorem not_mem_hull {a : Fin d → ℝ} {r : ℝ} {T : Set (Fin d → ℝ)}
    (hT : ∀ x ∈ T, LF a x ≤ r) {p : Fin d → ℝ} (hp : r < LF a p) :
    p ∉ convexHull ℝ T := fun h => absurd (hull_le hT h) (not_le.mpr hp)

theorem two_pow_inj {a b : ℕ} (h : (2 : ℝ) ^ a = 2 ^ b) : a = b := by
  have h' : ((2 ^ a : ℕ) : ℝ) = ((2 ^ b : ℕ) : ℝ) := by push_cast; exact h
  exact Nat.pow_right_injective (le_refl 2) (Nat.cast_injective h')

theorem rp_inj : Function.Injective (rp (d := d)) := by
  intro σ τ h
  ext i
  exact two_pow_inj (congrFun h i)

/-! #### Coordinate sums: every vertex lies on `Σ xᵢ = 2^d - 1` -/

/-- In `ℕ`, avoiding truncated subtraction. -/
theorem nat_sum_perm (σ : Equiv.Perm (Fin d)) :
    (∑ i : Fin d, 2 ^ ((σ i : ℕ))) + 1 = 2 ^ d := by
  have h : ∑ i : Fin d, 2 ^ ((σ i : ℕ)) = ∑ i : Fin d, 2 ^ ((i : ℕ)) :=
    Equiv.sum_comp σ (fun j : Fin d => 2 ^ ((j : ℕ)))
  rw [h]
  clear h σ
  induction d with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    have : (∑ i : Fin k, 2 ^ ((i : ℕ))) + 1 = 2 ^ k := ih
    rw [pow_succ]
    omega

theorem sum_coords_rp (σ : Equiv.Perm (Fin d)) :
    LF (fun _ => 1) (rp σ) = ((2 ^ d - 1 : ℕ) : ℝ) := by
  have hnat := nat_sum_perm σ
  have : ((∑ i : Fin d, 2 ^ ((σ i : ℕ)) : ℕ) : ℝ) = ((2 ^ d - 1 : ℕ) : ℝ) := by
    congr 1
    omega
  rw [← this]
  simp only [LF, rp, one_mul, Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat]

/-! #### Convex position via the common squared norm -/

/-- The common squared norm `Q = Σ_{j<d} 4^j`, as a natural number. -/
def Q (d : ℕ) : ℕ := ∑ i : Fin d, 2 ^ ((i : ℕ)) * 2 ^ ((i : ℕ))

/-- The integer pairing of two vertices. -/
def dot (σ τ : Equiv.Perm (Fin d)) : ℕ := ∑ i : Fin d, 2 ^ ((σ i : ℕ)) * 2 ^ ((τ i : ℕ))

theorem dot_self (σ : Equiv.Perm (Fin d)) : dot σ σ = Q d :=
  Equiv.sum_comp σ (fun j : Fin d => 2 ^ ((j : ℕ)) * 2 ^ ((j : ℕ)))

/-- **The norm argument.**  Distinct vertices pair strictly below the common squared norm:
`2(Q - ⟪v,w⟫) = |v - w|² > 0`.  Everything is an integer, so the gap is at least one. -/
theorem dot_lt (σ τ : Equiv.Perm (Fin d)) (hne : σ ≠ τ) : dot σ τ < Q d := by
  have key : ∀ i : Fin d,
      (2 : ℤ) * (2 ^ ((σ i : ℕ)) * 2 ^ ((τ i : ℕ)))
        ≤ 2 ^ ((σ i : ℕ)) * 2 ^ ((σ i : ℕ)) + 2 ^ ((τ i : ℕ)) * 2 ^ ((τ i : ℕ)) := by
    intro i
    nlinarith [sq_nonneg ((2 : ℤ) ^ ((σ i : ℕ)) - 2 ^ ((τ i : ℕ)))]
  obtain ⟨i₀, hi₀⟩ : ∃ i, σ i ≠ τ i := by
    by_contra hc
    push_neg at hc
    exact hne (Equiv.ext hc)
  have hstrict :
      (2 : ℤ) * (2 ^ ((σ i₀ : ℕ)) * 2 ^ ((τ i₀ : ℕ)))
        < 2 ^ ((σ i₀ : ℕ)) * 2 ^ ((σ i₀ : ℕ)) + 2 ^ ((τ i₀ : ℕ)) * 2 ^ ((τ i₀ : ℕ)) := by
    have hne' : ((2 : ℤ) ^ ((σ i₀ : ℕ)) - 2 ^ ((τ i₀ : ℕ))) ≠ 0 := by
      intro h
      have : (2 : ℤ) ^ ((σ i₀ : ℕ)) = 2 ^ ((τ i₀ : ℕ)) := by linarith
      have hnat : ((σ i₀ : ℕ)) = ((τ i₀ : ℕ)) := by
        have h2 : (2 : ℝ) ^ ((σ i₀ : ℕ)) = 2 ^ ((τ i₀ : ℕ)) := by exact_mod_cast this
        exact two_pow_inj h2
      exact hi₀ (Fin.ext hnat)
    have hsq : 0 < ((2 : ℤ) ^ ((σ i₀ : ℕ)) - 2 ^ ((τ i₀ : ℕ))) ^ 2 := by positivity
    nlinarith [hsq]
  have hsum : (2 : ℤ) * (dot σ τ : ℤ) < (dot σ σ : ℤ) + (dot τ τ : ℤ) := by
    have h1 : (2 : ℤ) * (dot σ τ : ℤ)
        = ∑ i : Fin d, (2 : ℤ) * (2 ^ ((σ i : ℕ)) * 2 ^ ((τ i : ℕ))) := by
      simp only [dot, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
        Finset.mul_sum]
    have h2 : (dot σ σ : ℤ) + (dot τ τ : ℤ)
        = ∑ i : Fin d, ((2 : ℤ) ^ ((σ i : ℕ)) * 2 ^ ((σ i : ℕ))
            + 2 ^ ((τ i : ℕ)) * 2 ^ ((τ i : ℕ))) := by
      simp only [dot, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
        Finset.sum_add_distrib]
    rw [h1, h2]
    exact Finset.sum_lt_sum (fun i _ => key i) ⟨i₀, Finset.mem_univ i₀, hstrict⟩
  rw [dot_self, dot_self] at hsum
  have : (dot σ τ : ℤ) < (Q d : ℤ) := by linarith
  exact_mod_cast this

theorem LF_rp_rp (σ τ : Equiv.Perm (Fin d)) : LF (rp σ) (rp τ) = ((dot σ τ : ℕ) : ℝ) := by
  simp only [LF, rp, dot, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

/-! #### The four defining properties -/

theorem VS_finite : (VS d).Finite := Set.finite_range _

theorem VS_ncard : (VS d).ncard = Nat.factorial d := by
  rw [VS, Set.ncard_range_of_injective rp_inj]
  simp [Nat.card_eq_fintype_card, Fintype.card_perm]

theorem VS_subset : VS d ⊆ LAT d := by
  rintro x ⟨σ, rfl⟩ i
  exact ⟨(σ i : ℕ), rfl⟩

theorem VS_convexPosition : ∀ v ∈ VS d, v ∉ convexHull ℝ ((VS d) \ {v}) := by
  rintro v ⟨σ, rfl⟩
  -- the threshold is real, not truncated in `ℕ`, so `d = 0` needs no separate case
  refine not_mem_hull (a := rp σ) (r := ((Q d : ℝ) - 1)) ?_ ?_
  · rintro x ⟨⟨τ, rfl⟩, hne⟩
    have hστ : σ ≠ τ := fun h => hne (by rw [h]; rfl)
    have hlt : (dot σ τ : ℝ) < (Q d : ℝ) := by exact_mod_cast dot_lt σ τ hστ
    have hint : (dot σ τ : ℝ) ≤ (Q d : ℝ) - 1 := by
      have : dot σ τ + 1 ≤ Q d := dot_lt σ τ hστ
      have : ((dot σ τ + 1 : ℕ) : ℝ) ≤ ((Q d : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at this
      linarith
    rw [LF_rp_rp]
    exact hint
  · rw [LF_rp_rp, dot_self]
    linarith

theorem VS_empty : convexHull ℝ (VS d) ∩ LAT d ⊆ VS d := by
  classical
  rintro p ⟨hp, hpS⟩
  choose n hn using hpS
  -- `Σ pᵢ = 2^d - 1`, from the two functionals `±(1, …, 1)`
  have hle : LF (fun _ => 1) p ≤ ((2 ^ d - 1 : ℕ) : ℝ) := by
    refine hull_le ?_ hp
    rintro x ⟨σ, rfl⟩
    exact le_of_eq (sum_coords_rp σ)
  have hge : LF (fun _ => -1) p ≤ -((2 ^ d - 1 : ℕ) : ℝ) := by
    refine hull_le ?_ hp
    rintro x ⟨σ, rfl⟩
    have := sum_coords_rp σ
    simp only [LF, neg_mul, one_mul, Finset.sum_neg_distrib] at this ⊢
    linarith [this]
  have heq : LF (fun _ => 1) p = ((2 ^ d - 1 : ℕ) : ℝ) := by
    have : LF (fun _ => -1) p = - LF (fun _ => 1) p := by
      simp only [LF, neg_mul, one_mul, Finset.sum_neg_distrib]
    linarith [hle, hge, this]
  -- turn it into an equation in `ℕ`
  have hnat : ∑ i : Fin d, 2 ^ (n i) = 2 ^ d - 1 := by
    have hcast : ((∑ i : Fin d, 2 ^ (n i) : ℕ) : ℝ) = ((2 ^ d - 1 : ℕ) : ℝ) := by
      rw [← heq]
      simp only [LF, one_mul, Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat]
      exact Finset.sum_congr rfl fun i _ => (hn i).symm
    exact_mod_cast hcast
  obtain ⟨σ, hσ⟩ := perm_of_sum_eq n hnat
  refine ⟨σ, ?_⟩
  funext i
  rw [rp, hσ i, ← hn i]

/-- **`h(L_d(2)) ≥ d!` in every dimension.**  The `d!` permutations of `(2⁰, …, 2^(d-1))`
form an empty polytope of the exponential lattice `{2ⁿ : n ∈ ℕ₀}^d`. -/
theorem proof :
    ∀ d : ℕ, ∃ V : Set (Fin d → ℝ),
      (V.Finite ∧
        V ⊆ {x : Fin d → ℝ | ∀ i, ∃ n : ℕ, x i = (2 : ℝ) ^ n} ∧
        (∀ v ∈ V, v ∉ convexHull ℝ (V \ {v})) ∧
        convexHull ℝ V ∩ {x : Fin d → ℝ | ∀ i, ∃ n : ℕ, x i = (2 : ℝ) ^ n} ⊆ V) ∧
      V.ncard = Nat.factorial d :=
  fun d => ⟨VS d, ⟨VS_finite, VS_subset, VS_convexPosition, VS_empty⟩, VS_ncard⟩

end Submissions.ExpLatticeFactorialLB.Permutohedron
