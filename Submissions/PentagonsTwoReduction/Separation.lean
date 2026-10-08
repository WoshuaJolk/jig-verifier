import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

namespace Submissions.PentagonsTwoReduction.Separation

open Real

/-- Circumradius of a regular pentagon with unit side length. -/
noncomputable def circumradius : ℝ := 1 / (2 * Real.sin (Real.pi / 5))

/-- The closed regular pentagon with unit side, centre `(a, b)`, rotated by `θ`. -/
noncomputable def pentagon (a b θ : ℝ) : Set (ℝ × ℝ) :=
  convexHull ℝ (Set.range fun k : Fin 5 =>
    (a + circumradius * Real.cos (θ + 2 * Real.pi * (k : ℕ) / 5),
     b + circumradius * Real.sin (θ + 2 * Real.pi * (k : ℕ) / 5)))

/-- `n` unit regular pentagons, each with arbitrary position and rotation, fit inside the
axis-parallel square `[0, s] × [0, s]` with pairwise disjoint interiors. -/
def PacksInSquare (n : ℕ) (s : ℝ) : Prop :=
  ∃ a b θ : Fin n → ℝ,
    (∀ i, pentagon (a i) (b i) (θ i) ⊆ Set.Icc 0 s ×ˢ Set.Icc 0 s) ∧
    (∀ i j, i ≠ j →
      Disjoint (interior (pentagon (a i) (b i) (θ i)))
        (interior (pentagon (a j) (b j) (θ j))))

/-- Side of the smallest known square for two unit pentagons:
`C (3 + C - 2 C²) / (S (S + C))` with `C = cos (π/5)`, `S = sin (π/5)` (≈ 2.46345). -/
noncomputable def sStar : ℝ :=
  Real.cos (Real.pi / 5) * (3 + Real.cos (Real.pi / 5) - 2 * Real.cos (Real.pi / 5) ^ 2) /
    (Real.sin (Real.pi / 5) * (Real.sin (Real.pi / 5) + Real.cos (Real.pi / 5)))

lemma collinear_det {p₁ p₂ p₃ : ℝ × ℝ} (h : Collinear ℝ ({p₁, p₂, p₃} : Set (ℝ × ℝ))) :
    (p₂.1 - p₁.1) * (p₃.2 - p₁.2) - (p₃.1 - p₁.1) * (p₂.2 - p₁.2) = 0 := by
  rw [collinear_iff_of_mem (p₀ := p₁) (by simp)] at h
  obtain ⟨v, hv⟩ := h
  obtain ⟨r₂, h₂⟩ := hv p₂ (by simp)
  obtain ⟨r₃, h₃⟩ := hv p₃ (by simp)
  subst h₂ h₃
  simp; ring

theorem pentagon_interior_nonempty (a b θ : ℝ) : (interior (pentagon a b θ)).Nonempty := by
  have hR : 0 < circumradius := by
    unfold circumradius
    have : 0 < Real.sin (Real.pi / 5) :=
      Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
    positivity
  set v : Fin 5 → ℝ × ℝ := fun k =>
    (a + circumradius * Real.cos (θ + 2 * Real.pi * ((k : ℕ) : ℝ) / 5),
     b + circumradius * Real.sin (θ + 2 * Real.pi * ((k : ℕ) : ℝ) / 5)) with hv
  have hpent : pentagon a b θ = convexHull ℝ (Set.range v) := rfl
  rw [hpent, interior_convexHull_nonempty_iff_affineSpan_eq_top]
  -- three vertices are not collinear
  have hS : 0 < Real.sin (Real.pi / 5) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  have hC : Real.cos (Real.pi / 5) = (1 + Real.sqrt 5) / 4 := Real.cos_pi_div_five
  have h5 : (2 : ℝ) < Real.sqrt 5 := by
    rw [show (2:ℝ) = Real.sqrt 4 by rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hnc : ¬ Collinear ℝ ({v 0, v 1, v 2} : Set (ℝ × ℝ)) := by
    intro h
    have hd := collinear_det h
    simp only [hv] at hd
    have e1 : θ + 2 * Real.pi * ((((1 : Fin 5)) : ℕ) : ℝ) / 5 = θ + 2 * (Real.pi / 5) := by
      simp; ring
    have e2 : θ + 2 * Real.pi * ((((2 : Fin 5)) : ℕ) : ℝ) / 5 = θ + (Real.pi - Real.pi / 5) := by
      simp; ring
    have e0 : θ + 2 * Real.pi * ((((0 : Fin 5)) : ℕ) : ℝ) / 5 = θ := by simp
    rw [e0, e1, e2] at hd
    simp only [Real.cos_add, Real.sin_add, Real.cos_two_mul, Real.sin_two_mul,
      Real.cos_pi_sub, Real.sin_pi_sub, hC] at hd
    have key : circumradius ^ 2 * (2 * Real.sin (Real.pi / 5) *
        (2 * ((1 + Real.sqrt 5) / 4) - 1) * ((1 + Real.sqrt 5) / 4 + 1)) = 0 := by
      rw [← hd]
      have hs5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
      have hsc : Real.sin (Real.pi/5) ^ 2 = 1 - ((1 + Real.sqrt 5) / 4) ^ 2 := by
        rw [← hC, ← Real.cos_sq_add_sin_sq (Real.pi/5)]; ring
      linear_combination (circumradius ^ 2 * (2 * Real.sin (Real.pi / 5) *
        (2 * ((1 + Real.sqrt 5) / 4) - 1) * ((1 + Real.sqrt 5) / 4 + 1))
        - 2 * Real.sqrt 5 * circumradius ^ 2 * Real.sin (Real.pi / 5)) * (Real.sin_sq_add_cos_sq θ)
        + (circumradius ^ 2 * Real.sin (Real.pi / 5) *
            (1 / 2 - (Real.cos θ ^ 2 + Real.sin θ ^ 2) / 2)) * hs5
    have : 0 < circumradius ^ 2 * (2 * Real.sin (Real.pi / 5) *
        (2 * ((1 + Real.sqrt 5) / 4) - 1) * ((1 + Real.sqrt 5) / 4 + 1)) := by
      apply mul_pos (by positivity)
      apply mul_pos (mul_pos (by positivity) (by linarith)) (by positivity)
    linarith
  have hai : AffineIndependent ℝ ![v 0, v 1, v 2] := by
    rw [affineIndependent_iff_not_collinear_set]; exact hnc
  have htop : affineSpan ℝ (Set.range ![v 0, v 1, v 2]) = ⊤ := by
    rw [hai.affineSpan_eq_top_iff_card_eq_finrank_add_one]
    simp [Module.finrank_prod]
  apply eq_top_iff.mpr
  rw [← htop]
  apply affineSpan_mono
  rintro _ ⟨i, rfl⟩
  fin_cases i <;> simp


/-! ### Basic vertex facts -/

lemma vert_mem (a b θ : ℝ) (m : ℤ) :
    (a + circumradius * cos (θ + 2 * π * (m : ℝ) / 5),
      b + circumradius * sin (θ + 2 * π * (m : ℝ) / 5)) ∈ pentagon a b θ := by
  have hk : (m % 5).toNat < 5 := by omega
  apply subset_convexHull
  refine ⟨⟨(m % 5).toNat, hk⟩, ?_⟩
  have h1 : (((m % 5).toNat : ℕ) : ℤ) = m % 5 := Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
  have h2 : (m : ℝ) = 5 * ((m / 5 : ℤ) : ℝ) + (((m % 5).toNat : ℕ) : ℝ) := by
    have h3 : ((((m % 5).toNat : ℕ)) : ℝ) = ((m % 5 : ℤ) : ℝ) := by exact_mod_cast h1
    rw [h3]
    have h4 : m = m % 5 + 5 * (m / 5) := by omega
    have h5 : (m : ℝ) = ((m % 5 : ℤ) : ℝ) + 5 * ((m / 5 : ℤ) : ℝ) := by exact_mod_cast h4
    linarith
  have e : θ + 2 * π * (m : ℝ) / 5
      = θ + 2 * π * (((m % 5).toNat : ℕ) : ℝ) / 5 + ((m / 5 : ℤ) : ℝ) * (2 * π) := by
    rw [h2]; ring
  simp only
  rw [e, cos_add_int_mul_two_pi, sin_add_int_mul_two_pi]

/-- An affine map of the form `x ↦ (e₁ x₁ + c₁, e₂ x₂ + c₂)`. -/
def σ (e1 c1 e2 c2 : ℝ) (x : ℝ × ℝ) : ℝ × ℝ := (e1 * x.1 + c1, e2 * x.2 + c2)

lemma convex_preimage {K : Set (ℝ × ℝ)} (hK : Convex ℝ K) (e1 c1 e2 c2 : ℝ) :
    Convex ℝ {x | σ e1 c1 e2 c2 x ∈ K} := by
  intro x hx y hy t u ht hu htu
  simp only [Set.mem_setOf_eq] at *
  have := hK hx hy ht hu htu
  convert this using 1
  simp only [σ, Prod.smul_mk, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul, Prod.mk.injEq]
  constructor
  · linear_combination (-c1) * htu
  · linear_combination (-c2) * htu

/-- Transport along `σ`: if every vertex of `N` is mapped by `σ` to a vertex of `P`, then
`σ` maps `N` into `P`. -/
lemma image_sub {a b θ a' b' θ' e1 c1 e2 c2 : ℝ}
    (hv : ∀ m : ℤ, ∃ m' : ℤ,
      σ e1 c1 e2 c2 (a' + circumradius * cos (θ' + 2 * π * (m : ℝ) / 5),
        b' + circumradius * sin (θ' + 2 * π * (m : ℝ) / 5)) =
      (a + circumradius * cos (θ + 2 * π * (m' : ℝ) / 5),
        b + circumradius * sin (θ + 2 * π * (m' : ℝ) / 5)))
    {p : ℝ × ℝ} (hp : p ∈ pentagon a' b' θ') : σ e1 c1 e2 c2 p ∈ pentagon a b θ := by
  have hsub : pentagon a' b' θ' ⊆ {x | σ e1 c1 e2 c2 x ∈ pentagon a b θ} := by
    apply convexHull_min _ (convex_preimage (convex_convexHull ℝ _) _ _ _ _)
    rintro _ ⟨k, rfl⟩
    obtain ⟨m', hm'⟩ := hv (k : ℕ)
    simp only [Set.mem_setOf_eq]
    have := vert_mem a b θ m'
    rw [← hm'] at this
    push_cast at this
    exact this
  exact hsub hp

/-- Vertices of `N` lie in the quadrant if they are `σ`-images of vertices of a pentagon in a box. -/
lemma quad_of_box {a b θ a' b' θ' s : ℝ} (e1 c1 e2 c2 : ℝ)
    (hbox : pentagon a b θ ⊆ Set.Icc 0 s ×ˢ Set.Icc 0 s)
    (hq : ∀ x : ℝ × ℝ, x ∈ Set.Icc 0 s ×ˢ Set.Icc 0 s → σ e1 c1 e2 c2 x ∈ Set.Ici 0 ×ˢ Set.Ici 0)
    (hv : ∀ m : ℤ, ∃ m' : ℤ,
      (a' + circumradius * cos (θ' + 2 * π * (m : ℝ) / 5),
        b' + circumradius * sin (θ' + 2 * π * (m : ℝ) / 5)) =
      σ e1 c1 e2 c2 (a + circumradius * cos (θ + 2 * π * (m' : ℝ) / 5),
        b + circumradius * sin (θ + 2 * π * (m' : ℝ) / 5))) :
    pentagon a' b' θ' ⊆ Set.Ici 0 ×ˢ Set.Ici 0 := by
  apply convexHull_min _ ((convex_Ici _).prod (convex_Ici _))
  rintro _ ⟨k, rfl⟩
  obtain ⟨m', hm'⟩ := hv (k : ℕ)
  have := hq _ (hbox (vert_mem a b θ m'))
  rw [← hm'] at this
  push_cast at this
  exact this

/-- The corner lemma at all four corners of the square `[0,s]²`. -/
lemma corners (H : ∀ a b θ : ℝ, pentagon a b θ ⊆ Set.Ici 0 ×ˢ Set.Ici 0 →
      ∃ p ∈ pentagon a b θ, sStar / 2 ≤ p.1 ∧ sStar / 2 ≤ p.2)
    {a b θ s : ℝ} (hbox : pentagon a b θ ⊆ Set.Icc 0 s ×ˢ Set.Icc 0 s) :
    (∃ p ∈ pentagon a b θ, sStar / 2 ≤ p.1 ∧ sStar / 2 ≤ p.2) ∧
    (∃ p ∈ pentagon a b θ, p.1 ≤ s - sStar / 2 ∧ sStar / 2 ≤ p.2) ∧
    (∃ p ∈ pentagon a b θ, sStar / 2 ≤ p.1 ∧ p.2 ≤ s - sStar / 2) ∧
    (∃ p ∈ pentagon a b θ, p.1 ≤ s - sStar / 2 ∧ p.2 ≤ s - sStar / 2) := by
  have hq0 : pentagon a b θ ⊆ Set.Ici 0 ×ˢ Set.Ici 0 := fun x hx => by
    obtain ⟨⟨h1, -⟩, ⟨h2, -⟩⟩ := hbox hx; exact ⟨h1, h2⟩
  refine ⟨H a b θ hq0, ?_, ?_, ?_⟩
  · -- reflect x ↦ s - x
    have hN := quad_of_box (a' := s - a) (b' := b) (θ' := π - θ) (-1) s 1 0 hbox
      (fun x ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ => ⟨by simp [σ]; linarith, by simp [σ]; linarith⟩)
      (fun m => ⟨-m, by
        simp only [σ, Prod.mk.injEq]; push_cast
        rw [show π - θ + 2 * π * (m : ℝ) / 5 = π - (θ + 2 * π * (-(m : ℝ)) / 5) by ring,
          cos_pi_sub, sin_pi_sub]
        constructor <;> ring⟩)
    obtain ⟨p, hp, h1, h2⟩ := H _ _ _ hN
    refine ⟨σ (-1) s 1 0 p, image_sub (fun m => ⟨-m, ?_⟩) hp, ?_, ?_⟩
    · simp only [σ, Prod.mk.injEq]; push_cast
      rw [show π - θ + 2 * π * (m : ℝ) / 5 = π - (θ + 2 * π * (-(m : ℝ)) / 5) by ring,
        cos_pi_sub, sin_pi_sub]
      constructor <;> ring
    · simp only [σ]; linarith
    · simp only [σ]; linarith
  · -- reflect y ↦ s - y
    have hN := quad_of_box (a' := a) (b' := s - b) (θ' := -θ) 1 0 (-1) s hbox
      (fun x ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ => ⟨by simp [σ]; linarith, by simp [σ]; linarith⟩)
      (fun m => ⟨-m, by
        simp only [σ, Prod.mk.injEq]; push_cast
        rw [show -θ + 2 * π * (m : ℝ) / 5 = -(θ + 2 * π * (-(m : ℝ)) / 5) by ring,
          cos_neg, sin_neg]
        constructor <;> ring⟩)
    obtain ⟨p, hp, h1, h2⟩ := H _ _ _ hN
    refine ⟨σ 1 0 (-1) s p, image_sub (fun m => ⟨-m, ?_⟩) hp, ?_, ?_⟩
    · simp only [σ, Prod.mk.injEq]; push_cast
      rw [show -θ + 2 * π * (m : ℝ) / 5 = -(θ + 2 * π * (-(m : ℝ)) / 5) by ring,
        cos_neg, sin_neg]
      constructor <;> ring
    · simp only [σ]; linarith
    · simp only [σ]; linarith
  · -- point reflection
    have hN := quad_of_box (a' := s - a) (b' := s - b) (θ' := θ + π) (-1) s (-1) s hbox
      (fun x ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ => ⟨by simp [σ]; linarith, by simp [σ]; linarith⟩)
      (fun m => ⟨m, by
        simp only [σ, Prod.mk.injEq]
        rw [show θ + π + 2 * π * (m : ℝ) / 5 = (θ + 2 * π * (m : ℝ) / 5) + π by ring,
          cos_add_pi, sin_add_pi]
        constructor <;> ring⟩)
    obtain ⟨p, hp, h1, h2⟩ := H _ _ _ hN
    refine ⟨σ (-1) s (-1) s p, image_sub (fun m => ⟨m, ?_⟩) hp, ?_, ?_⟩
    · simp only [σ, Prod.mk.injEq]
      rw [show θ + π + 2 * π * (m : ℝ) / 5 = (θ + 2 * π * (m : ℝ) / 5) + π by ring,
        cos_add_pi, sin_add_pi]
      constructor <;> ring
    · simp only [σ]; linarith
    · simp only [σ]; linarith

/-! ### Separation of two pentagons with disjoint interiors -/

lemma pentagon_closed (a b θ : ℝ) : IsClosed (pentagon a b θ) :=
  (Set.finite_range _).isClosed_convexHull ℝ

lemma separate {a b θ a' b' θ' : ℝ}
    (hd : Disjoint (interior (pentagon a b θ)) (interior (pentagon a' b' θ'))) :
    ∃ u1 u2 u : ℝ, (u1 ≠ 0 ∨ u2 ≠ 0) ∧
      (∀ x ∈ pentagon a b θ, u1 * x.1 + u2 * x.2 ≤ u) ∧
      (∀ x ∈ pentagon a' b' θ', u ≤ u1 * x.1 + u2 * x.2) := by
  have hP := pentagon_interior_nonempty a b θ
  have hQ := pentagon_interior_nonempty a' b' θ'
  have cP : Convex ℝ (pentagon a b θ) := convex_convexHull ℝ _
  have cQ : Convex ℝ (pentagon a' b' θ') := convex_convexHull ℝ _
  obtain ⟨f, u, hf1, hf2⟩ := geometric_hahn_banach_open_open cP.interior isOpen_interior
    cQ.interior isOpen_interior hd
  have hlin : ∀ x : ℝ × ℝ, f x = f (1, 0) * x.1 + f (0, 1) * x.2 := by
    intro x
    have : x = x.1 • ((1:ℝ), (0:ℝ)) + x.2 • ((0:ℝ), (1:ℝ)) := by ext <;> simp
    conv_lhs => rw [this]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]; ring
  refine ⟨f (1, 0), f (0, 1), u, ?_, ?_, ?_⟩
  · by_contra h
    push_neg at h
    obtain ⟨x, hx⟩ := hP; obtain ⟨y, hy⟩ := hQ
    have h1 := hf1 x hx; have h2 := hf2 y hy
    rw [hlin, h.1, h.2] at h1 h2
    linarith
  · intro x hx
    have hcl : pentagon a b θ ⊆ closure (interior (pentagon a b θ)) := by
      rw [cP.closure_interior_eq_closure_of_nonempty_interior hP, (pentagon_closed a b θ).closure_eq]
    have hsub : closure (interior (pentagon a b θ)) ⊆ {x | f x ≤ u} :=
      closure_minimal (fun y hy => (hf1 y hy).le) (isClosed_le f.continuous continuous_const)
    have := hsub (hcl hx)
    simp only [Set.mem_setOf_eq] at this
    rwa [hlin] at this
  · intro x hx
    have hcl : pentagon a' b' θ' ⊆ closure (interior (pentagon a' b' θ')) := by
      rw [cQ.closure_interior_eq_closure_of_nonempty_interior hQ, (pentagon_closed a' b' θ').closure_eq]
    have hsub : closure (interior (pentagon a' b' θ')) ⊆ {x | u ≤ f x} :=
      closure_minimal (fun y hy => (hf2 y hy).le) (isClosed_le continuous_const f.continuous)
    have := hsub (hcl hx)
    simp only [Set.mem_setOf_eq] at this
    rwa [hlin] at this

theorem proof : (∀ a b θ : ℝ, pentagon a b θ ⊆ Set.Ici 0 ×ˢ Set.Ici 0 →
      ∃ p ∈ pentagon a b θ, sStar / 2 ≤ p.1 ∧ sStar / 2 ≤ p.2) →
    ∀ s : ℝ, PacksInSquare 2 s → sStar ≤ s := by
  intro H s ⟨a, b, θ, hbox, hdisj⟩
  obtain ⟨u1, u2, u, hu, hP, hQ⟩ := separate (hdisj 0 1 (by decide))
  obtain ⟨P1, P2, P3, P4⟩ := corners H (hbox 0)
  obtain ⟨Q1, Q2, Q3, Q4⟩ := corners H (hbox 1)
  rcases le_total 0 u1 with h1 | h1 <;> rcases le_total 0 u2 with h2 | h2
  · obtain ⟨p, hp, hp1, hp2⟩ := P1; obtain ⟨q, hq, hq1, hq2⟩ := Q4
    have := hP p hp; have := hQ q hq
    have hpos : 0 < u1 + u2 := by
      rcases hu with hu | hu
      · exact add_pos_of_pos_of_nonneg (lt_of_le_of_ne h1 (Ne.symm hu)) h2
      · exact add_pos_of_nonneg_of_pos h1 (lt_of_le_of_ne h2 (Ne.symm hu))
    nlinarith [mul_le_mul_of_nonneg_left (show q.1 - p.1 ≤ s - sStar by linarith) h1,
      mul_le_mul_of_nonneg_left (show q.2 - p.2 ≤ s - sStar by linarith) h2]
  · obtain ⟨p, hp, hp1, hp2⟩ := P3; obtain ⟨q, hq, hq1, hq2⟩ := Q2
    have := hP p hp; have := hQ q hq
    have hpos : 0 < u1 - u2 := by
      rcases hu with hu | hu
      · have := lt_of_le_of_ne h1 (Ne.symm hu); linarith
      · have := lt_of_le_of_ne h2 hu; linarith
    nlinarith [mul_le_mul_of_nonneg_left (show q.1 - p.1 ≤ s - sStar by linarith) h1,
      mul_le_mul_of_nonneg_left (show p.2 - q.2 ≤ s - sStar by linarith) (neg_nonneg.mpr h2)]
  · obtain ⟨p, hp, hp1, hp2⟩ := P2; obtain ⟨q, hq, hq1, hq2⟩ := Q3
    have := hP p hp; have := hQ q hq
    have hpos : 0 < u2 - u1 := by
      rcases hu with hu | hu
      · have := lt_of_le_of_ne h1 hu; linarith
      · have := lt_of_le_of_ne h2 (Ne.symm hu); linarith
    nlinarith [mul_le_mul_of_nonneg_left (show p.1 - q.1 ≤ s - sStar by linarith) (neg_nonneg.mpr h1),
      mul_le_mul_of_nonneg_left (show q.2 - p.2 ≤ s - sStar by linarith) h2]
  · obtain ⟨p, hp, hp1, hp2⟩ := P4; obtain ⟨q, hq, hq1, hq2⟩ := Q1
    have := hP p hp; have := hQ q hq
    have hpos : 0 < -u1 - u2 := by
      rcases hu with hu | hu
      · have := lt_of_le_of_ne h1 hu; linarith
      · have := lt_of_le_of_ne h2 hu; linarith
    nlinarith [mul_le_mul_of_nonneg_left (show p.1 - q.1 ≤ s - sStar by linarith) (neg_nonneg.mpr h1),
      mul_le_mul_of_nonneg_left (show p.2 - q.2 ≤ s - sStar by linarith) (neg_nonneg.mpr h2)]

end Submissions.PentagonsTwoReduction.Separation
