import Mathlib.Geometry.Euclidean.Sphere.Basic
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Data.Set.Card
import Mathlib.Tactic

open EuclideanGeometry

namespace Submissions.Erdos213UpToSeven.KreiselKurz

abbrev Point := EuclideanSpace ℝ (Fin 2)

def IsGeneralPosition (S : Set Point) : Prop :=
  (∀ Q : Set Point, Q ⊆ S → Q.ncard = 3 → ¬ Collinear ℝ Q) ∧
  (∀ Q : Set Point, Q ⊆ S → Q.ncard = 4 → ¬ Cospherical Q)

def HasIntegralDistances (S : Set Point) : Prop :=
  S.Pairwise fun p q => dist p q ∈ Set.range Int.cast

def ExistsConfiguration (n : ℕ) : Prop :=
  ∃ S : Set Point,
    S.Finite ∧ S.ncard = n ∧
    IsGeneralPosition S ∧ HasIntegralDistances S

/-! Kreisel–Kurz (2008): seven points with characteristic 2002, scaled by `L = 37859`.
Point `i` is `(X i / L, Y i * √2002 / L)`. -/

def X : Fin 7 → ℤ := ![0, 843119930, 444159306, 546423401, 299471456, 124863436, 324343748]
def Y : Fin 7 → ℤ := ![0, 0, 15845088, 7001688, 4053888, 7001688, -920856]
def Dm : Fin 7 → Fin 7 → ℕ := ![
  ![0, 22270, 22098, 16637, 9248, 8908, 8636],
  ![22270, 0, 21488, 11397, 15138, 20698, 13746],
  ![22098, 21488, 0, 10795, 14450, 13430, 20066],
  ![16637, 11397, 10795, 0, 7395, 11135, 11049],
  ![9248, 15138, 14450, 7395, 0, 5780, 5916],
  ![8908, 20698, 13430, 11135, 5780, 0, 10744],
  ![8636, 13746, 20066, 11049, 5916, 10744, 0]]

def det3 (i j k : Fin 7) : ℤ :=
  (X j - X i) * (Y k - Y i) - (X k - X i) * (Y j - Y i)

def W (i : Fin 7) : ℤ := X i ^ 2 + 2002 * Y i ^ 2

def det4 (i j k l : Fin 7) : ℤ :=
  (W j - W i) * ((X k - X i) * (Y l - Y i) - (X l - X i) * (Y k - Y i))
  - (W k - W i) * ((X j - X i) * (Y l - Y i) - (X l - X i) * (Y j - Y i))
  + (W l - W i) * ((X j - X i) * (Y k - Y i) - (X k - X i) * (Y j - Y i))

lemma int_dist : ∀ i j : Fin 7,
    (X i - X j) ^ 2 + 2002 * (Y i - Y j) ^ 2 = 37859 ^ 2 * ((Dm i j : ℤ)) ^ 2 := by
  decide

lemma int_inj : ∀ i j : Fin 7, X i = X j → Y i = Y j → i = j := by decide

lemma int_det3 : ∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k → det3 i j k ≠ 0 := by decide

lemma int_det4 : ∀ i j k l : Fin 7, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
    det4 i j k l ≠ 0 := by decide


noncomputable def s : ℝ := Real.sqrt 2002

lemma hs : s ^ 2 = 2002 := Real.sq_sqrt (by norm_num)
lemma hs0 : 0 < s := Real.sqrt_pos.mpr (by norm_num)

noncomputable def P (i : Fin 7) : Point :=
  !₂[(X i : ℝ) / 37859, (Y i : ℝ) * s / 37859]

lemma P_zero (i : Fin 7) : (P i) 0 = (X i : ℝ) / 37859 := by simp [P]
lemma P_one (i : Fin 7) : (P i) 1 = (Y i : ℝ) * s / 37859 := by simp [P]

lemma dist_P (i j : Fin 7) : dist (P i) (P j) = (Dm i j : ℝ) := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  simp only [Real.dist_eq, sq_abs]
  have h := int_dist i j
  have hR : ((X i : ℝ) - X j) ^ 2 + 2002 * ((Y i : ℝ) - Y j) ^ 2
      = 37859 ^ 2 * ((Dm i j : ℝ)) ^ 2 := by exact_mod_cast h
  have : ((P i) 0 - (P j) 0) ^ 2 + ((P i) 1 - (P j) 1) ^ 2 = ((Dm i j : ℝ)) ^ 2 := by
    rw [P_zero, P_zero, P_one, P_one]
    linear_combination (1 / 37859 ^ 2 : ℝ) * hR + ((Y i : ℝ) - Y j) ^ 2 / 37859 ^ 2 * hs
  rw [show ((P i).ofLp 0 - (P j).ofLp 0) ^ 2 + ((P i).ofLp 1 - (P j).ofLp 1) ^ 2
      = ((P i) 0 - (P j) 0) ^ 2 + ((P i) 1 - (P j) 1) ^ 2 from rfl, this]
  exact Real.sqrt_sq (by positivity)

lemma P_inj : Function.Injective P := by
  intro i j h
  have h0 := congrArg (fun p : Point => p 0) h
  have h1 := congrArg (fun p : Point => p 1) h
  simp only [P_zero, P_one] at h0 h1
  apply int_inj
  · have : (X i : ℝ) = X j := by linarith
    exact_mod_cast this
  · have : (Y i : ℝ) * s = Y j * s := by linarith
    have := mul_right_cancel₀ hs0.ne' this
    exact_mod_cast this

lemma collinear_det {p₁ p₂ p₃ : Point} (h : Collinear ℝ ({p₁, p₂, p₃} : Set Point)) :
    (p₂ 0 - p₁ 0) * (p₃ 1 - p₁ 1) - (p₃ 0 - p₁ 0) * (p₂ 1 - p₁ 1) = 0 := by
  rw [collinear_iff_of_mem (p₀ := p₁) (by simp)] at h
  obtain ⟨v, hv⟩ := h
  obtain ⟨r₂, h₂⟩ := hv p₂ (by simp)
  obtain ⟨r₃, h₃⟩ := hv p₃ (by simp)
  have e20 : p₂ 0 = r₂ * v 0 + p₁ 0 := by rw [h₂]; simp
  have e21 : p₂ 1 = r₂ * v 1 + p₁ 1 := by rw [h₂]; simp
  have e30 : p₃ 0 = r₃ * v 0 + p₁ 0 := by rw [h₃]; simp
  have e31 : p₃ 1 = r₃ * v 1 + p₁ 1 := by rw [h₃]; simp
  rw [e20, e21, e30, e31]; ring

lemma not_collinear (i j k : Fin 7) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ¬ Collinear ℝ ({P i, P j, P k} : Set Point) := by
  intro h
  have h1 := collinear_det h
  rw [P_zero, P_zero, P_zero, P_one, P_one, P_one] at h1
  have h2 : (s / 37859 ^ 2) * (det3 i j k : ℝ) = 0 := by
    rw [← h1]; simp only [det3]; push_cast; ring
  have h3 := int_det3 i j k hij hik hjk
  rcases mul_eq_zero.mp h2 with h4 | h4
  · have : 0 < s / 37859 ^ 2 := div_pos hs0 (by norm_num)
    linarith [hs0]
  · exact h3 (by exact_mod_cast h4)

lemma cospherical_det {p₁ p₂ p₃ p₄ : Point}
    (h : Cospherical ({p₁, p₂, p₃, p₄} : Set Point)) :
    let u := fun p : Point => (p 0 ^ 2 + p 1 ^ 2) - (p₁ 0 ^ 2 + p₁ 1 ^ 2)
    let v := fun p : Point => p 0 - p₁ 0
    let t := fun p : Point => p 1 - p₁ 1
    u p₂ * (v p₃ * t p₄ - v p₄ * t p₃) - u p₃ * (v p₂ * t p₄ - v p₄ * t p₂)
      + u p₄ * (v p₂ * t p₃ - v p₃ * t p₂) = 0 := by
  obtain ⟨c, r, hc⟩ := h
  have key : ∀ p ∈ ({p₁, p₂, p₃, p₄} : Set Point),
      (p 0 - c 0) ^ 2 + (p 1 - c 1) ^ 2 = r ^ 2 := by
    intro p hp
    have := hc p hp
    rw [EuclideanSpace.dist_eq, Fin.sum_univ_two] at this
    simp only [Real.dist_eq, sq_abs] at this
    rw [← this, Real.sq_sqrt (by positivity)]
  have h1 := key p₁ (by simp)
  have h2 := key p₂ (by simp)
  have h3 := key p₃ (by simp)
  have h4 := key p₄ (by simp)
  intro u v t
  simp only [u, v, t]
  linear_combination
    ((p₃ 0 - p₁ 0) * (p₄ 1 - p₁ 1) - (p₄ 0 - p₁ 0) * (p₃ 1 - p₁ 1)) * (h2 - h1)
    - ((p₂ 0 - p₁ 0) * (p₄ 1 - p₁ 1) - (p₄ 0 - p₁ 0) * (p₂ 1 - p₁ 1)) * (h3 - h1)
    + ((p₂ 0 - p₁ 0) * (p₃ 1 - p₁ 1) - (p₃ 0 - p₁ 0) * (p₂ 1 - p₁ 1)) * (h4 - h1)

lemma not_cospherical (i j k l : Fin 7) (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    ¬ Cospherical ({P i, P j, P k, P l} : Set Point) := by
  intro h
  have h1 := cospherical_det h
  simp only [P_zero, P_one] at h1
  have h2 : (s / 37859 ^ 4) * (det4 i j k l : ℝ) = 0 := by
    rw [← h1]; simp only [det4, W]; push_cast
    linear_combination (-(s * ((X i:ℝ) * (Y j:ℝ)^2 * (Y k:ℝ) - (X i:ℝ) * (Y j:ℝ)^2 * (Y l:ℝ) - (X i:ℝ) * (Y j:ℝ) * (Y k:ℝ)^2 + (X i:ℝ) * (Y j:ℝ) * (Y l:ℝ)^2 + (X i:ℝ) * (Y k:ℝ)^2 * (Y l:ℝ) - (X i:ℝ) * (Y k:ℝ) * (Y l:ℝ)^2 - (X j:ℝ) * (Y i:ℝ)^2 * (Y k:ℝ) + (X j:ℝ) * (Y i:ℝ)^2 * (Y l:ℝ) + (X j:ℝ) * (Y i:ℝ) * (Y k:ℝ)^2 - (X j:ℝ) * (Y i:ℝ) * (Y l:ℝ)^2 - (X j:ℝ) * (Y k:ℝ)^2 * (Y l:ℝ) + (X j:ℝ) * (Y k:ℝ) * (Y l:ℝ)^2 + (X k:ℝ) * (Y i:ℝ)^2 * (Y j:ℝ) - (X k:ℝ) * (Y i:ℝ)^2 * (Y l:ℝ) - (X k:ℝ) * (Y i:ℝ) * (Y j:ℝ)^2 + (X k:ℝ) * (Y i:ℝ) * (Y l:ℝ)^2 + (X k:ℝ) * (Y j:ℝ)^2 * (Y l:ℝ) - (X k:ℝ) * (Y j:ℝ) * (Y l:ℝ)^2 - (X l:ℝ) * (Y i:ℝ)^2 * (Y j:ℝ) + (X l:ℝ) * (Y i:ℝ)^2 * (Y k:ℝ) + (X l:ℝ) * (Y i:ℝ) * (Y j:ℝ)^2 - (X l:ℝ) * (Y i:ℝ) * (Y k:ℝ)^2 - (X l:ℝ) * (Y j:ℝ)^2 * (Y k:ℝ) + (X l:ℝ) * (Y j:ℝ) * (Y k:ℝ)^2) / 37859 ^ 4)) * hs
  have h3 := int_det4 i j k l hij hik hil hjk hjl hkl
  rcases mul_eq_zero.mp h2 with h4 | h4
  · have : 0 < s / 37859 ^ 4 := div_pos hs0 (by norm_num)
    linarith [hs0]
  · exact h3 (by exact_mod_cast h4)

theorem seven : ExistsConfiguration 7 := by
  refine ⟨Set.range P, Set.finite_range P, ?_, ⟨?_, ?_⟩, ?_⟩
  · rw [← Set.image_univ, Set.ncard_image_of_injective _ P_inj, Set.ncard_univ]
    simp
  · intro Q hQ hc
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Set.ncard_eq_three.mp hc
    obtain ⟨i, rfl⟩ := hQ (by simp : x ∈ ({x, y, z} : Set Point))
    obtain ⟨j, rfl⟩ := hQ (by simp : y ∈ ({P i, y, z} : Set Point))
    obtain ⟨k, rfl⟩ := hQ (by simp : z ∈ ({P i, P j, z} : Set Point))
    exact not_collinear i j k (fun h => hxy (h ▸ rfl)) (fun h => hxz (h ▸ rfl))
      (fun h => hyz (h ▸ rfl))
  · intro Q hQ hc
    have hfin : Q.Finite := (Set.finite_range P).subset hQ
    obtain ⟨a, T, haT, rfl, hT⟩ := (Set.ncard_eq_succ hfin).mp hc
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Set.ncard_eq_three.mp hT
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at haT
    obtain ⟨hax, hay, haz⟩ := haT
    obtain ⟨l, rfl⟩ := hQ (by simp : a ∈ insert a ({x, y, z} : Set Point))
    obtain ⟨i, rfl⟩ := hQ (by simp : x ∈ insert (P l) ({x, y, z} : Set Point))
    obtain ⟨j, rfl⟩ := hQ (by simp : y ∈ insert (P l) ({P i, y, z} : Set Point))
    obtain ⟨k, rfl⟩ := hQ (by simp : z ∈ insert (P l) ({P i, P j, z} : Set Point))
    exact not_cospherical l i j k (fun h => hax (h ▸ rfl)) (fun h => hay (h ▸ rfl))
      (fun h => haz (h ▸ rfl)) (fun h => hxy (h ▸ rfl)) (fun h => hxz (h ▸ rfl))
      (fun h => hyz (h ▸ rfl))
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
    exact ⟨Dm i j, by rw [dist_P]; norm_cast⟩

lemma hereditary : ∀ m n : ℕ, m ≤ n → ExistsConfiguration n → ExistsConfiguration m := by
  intro m n hmn ⟨S, hfin, hcard, ⟨h3, h4⟩, hint⟩
  obtain ⟨T, hTS, hT⟩ := Set.exists_subset_card_eq (s := S) (n := m) (by omega)
  exact ⟨T, hfin.subset hTS, hT,
    ⟨fun Q hQ hc => h3 Q (hQ.trans hTS) hc, fun Q hQ hc => h4 Q (hQ.trans hTS) hc⟩,
    hint.mono hTS⟩

theorem proof : ∀ n : ℕ, 4 ≤ n → n ≤ 7 → ExistsConfiguration n :=
  fun n _ h7 => hereditary n 7 h7 seven

end Submissions.Erdos213UpToSeven.KreiselKurz
