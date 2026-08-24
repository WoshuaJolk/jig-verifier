import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

namespace Submissions.Length4NestedFiberNonvanishing.Nested

open scoped BigOperators

noncomputable section

set_option linter.unusedSimpArgs false

def pair {k : ℕ} (x y : Fin k → ℂ) : ℂ := ∑ r, star (x r) * y r

def bilinCof (u v w : Fin 4 → ℂ) : Fin 4 → ℂ := fun i =>
  (-1 : ℂ) ^ (i : ℕ) *
    Matrix.det (fun a b : Fin 3 => (![u, v, w] b) (i.succAbove a))

def hermCof (u v w : Fin 4 → ℂ) : Fin 4 → ℂ :=
  star (bilinCof u v w)

def rVec : Fin 4 → ℂ := ![1, 0, 0, 0]
def nVec : Fin 4 → ℂ := ![0, 1, 0, 0]
def e2 : Fin 4 → ℂ := ![0, 0, 1, 0]
def e3 : Fin 4 → ℂ := ![0, 0, 0, 1]
def e2I : Fin 4 → ℂ := ![0, 0, 1, Complex.I]

def nestedLead (b p q tau : Fin 4 → ℂ) : ℂ :=
  pair (hermCof b (hermCof b p q) tau) rVec

def plucker (x y : Fin 4 → ℂ) (i j : Fin 4) : ℂ :=
  x i * y j - x j * y i

@[simp] lemma fin3_zero {α : Type*} (a b c : α) : (![a, b, c] : Fin 3 → α) 0 = a := rfl
@[simp] lemma fin3_one {α : Type*} (a b c : α) : (![a, b, c] : Fin 3 → α) 1 = b := rfl
@[simp] lemma fin3_two {α : Type*} (a b c : α) : (![a, b, c] : Fin 3 → α) 2 = c := rfl

lemma sa00 : (0 : Fin 4).succAbove 0 = 1 := rfl
lemma sa01 : (0 : Fin 4).succAbove 1 = 2 := rfl
lemma sa02 : (0 : Fin 4).succAbove 2 = 3 := rfl
lemma sa10 : (1 : Fin 4).succAbove 0 = 0 := rfl
lemma sa11 : (1 : Fin 4).succAbove 1 = 2 := rfl
lemma sa12 : (1 : Fin 4).succAbove 2 = 3 := rfl
lemma sa20 : (2 : Fin 4).succAbove 0 = 0 := rfl
lemma sa21 : (2 : Fin 4).succAbove 1 = 1 := rfl
lemma sa22 : (2 : Fin 4).succAbove 2 = 3 := rfl
lemma sa30 : (3 : Fin 4).succAbove 0 = 0 := rfl
lemma sa31 : (3 : Fin 4).succAbove 1 = 1 := rfl
lemma sa32 : (3 : Fin 4).succAbove 2 = 2 := rfl

lemma bilinCof_expand (u v w : Fin 4 → ℂ) (i : Fin 4) :
    bilinCof u v w i =
      (-1 : ℂ) ^ (i : ℕ) *
        (u (i.succAbove 0) * v (i.succAbove 1) * w (i.succAbove 2) -
          u (i.succAbove 0) * w (i.succAbove 1) * v (i.succAbove 2) -
          v (i.succAbove 0) * u (i.succAbove 1) * w (i.succAbove 2) +
          v (i.succAbove 0) * w (i.succAbove 1) * u (i.succAbove 2) +
          w (i.succAbove 0) * u (i.succAbove 1) * v (i.succAbove 2) -
          w (i.succAbove 0) * v (i.succAbove 1) * u (i.succAbove 2)) := by
  unfold bilinCof
  rw [Matrix.det_fin_three (A := fun a b : Fin 3 => (![u, v, w] b) (i.succAbove a))]
  simp
  try ring

lemma pair_rVec (y : Fin 4 → ℂ) : pair rVec y = y 0 := by
  simp [pair, rVec, Fin.sum_univ_four]

lemma pair_rVec_left (y : Fin 4 → ℂ) : pair y rVec = star (y 0) := by
  simp [pair, rVec, Fin.sum_univ_four]

lemma pair_nVec (y : Fin 4 → ℂ) : pair nVec y = y 1 := by
  simp [pair, nVec, Fin.sum_univ_four]

lemma pair_e2 : pair rVec e2 = 0 ∧ pair nVec e2 = 0 := by
  simp [pair_rVec, pair_nVec, e2]

lemma pair_e3 : pair rVec e3 = 0 ∧ pair nVec e3 = 0 := by
  simp [pair_rVec, pair_nVec, e3]

lemma pair_e2e3 : pair rVec (e2 + e3) = 0 ∧ pair nVec (e2 + e3) = 0 := by
  simp [pair_rVec, pair_nVec, e2, e3]

lemma pair_e2I : pair rVec e2I = 0 ∧ pair nVec e2I = 0 := by
  simp [pair_rVec, pair_nVec, e2I]

lemma nestedLead_as_bilin (b p q tau : Fin 4 → ℂ) :
    nestedLead b p q tau = bilinCof b (hermCof b p q) tau 0 := by
  unfold nestedLead hermCof
  rw [pair_rVec_left]
  simp [Pi.star_apply]

lemma bilinCof_e2 (p q : Fin 4 → ℂ) :
    bilinCof e2 p q 0 = -p 1 * q 3 + p 3 * q 1 ∧
    bilinCof e2 p q 1 = p 0 * q 3 - p 3 * q 0 ∧
    bilinCof e2 p q 2 = 0 ∧
    bilinCof e2 p q 3 = -p 0 * q 1 + p 1 * q 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [bilinCof_expand, sa00, sa01, sa02]; simp [e2]; try ring
  · rw [bilinCof_expand, sa10, sa11, sa12]; simp [e2]; try ring
  · rw [bilinCof_expand, sa20, sa21, sa22]; simp [e2]; try ring
  · rw [bilinCof_expand, sa30, sa31, sa32]; simp [e2]; try ring

lemma bilinCof_e3 (p q : Fin 4 → ℂ) :
    bilinCof e3 p q 0 = p 1 * q 2 - p 2 * q 1 ∧
    bilinCof e3 p q 1 = -p 0 * q 2 + p 2 * q 0 ∧
    bilinCof e3 p q 2 = p 0 * q 1 - p 1 * q 0 ∧
    bilinCof e3 p q 3 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [bilinCof_expand, sa00, sa01, sa02]; simp [e3]; try ring
  · rw [bilinCof_expand, sa10, sa11, sa12]; simp [e3]; try ring
  · rw [bilinCof_expand, sa20, sa21, sa22]; simp [e3]; try ring
  · rw [bilinCof_expand, sa30, sa31, sa32]; simp [e3]; try ring

lemma bilinCof_e2_mid (C tau : Fin 4 → ℂ) :
    bilinCof e2 C tau 0 = -C 1 * tau 3 + tau 1 * C 3 := by
  rw [bilinCof_expand, sa00, sa01, sa02]; simp [e2]; try ring

lemma bilinCof_e3_mid (C tau : Fin 4 → ℂ) :
    bilinCof e3 C tau 0 = C 1 * tau 2 - tau 1 * C 2 := by
  rw [bilinCof_expand, sa00, sa01, sa02]; simp [e3]; try ring

lemma bilinCof_e2e3_mid (C tau : Fin 4 → ℂ) :
    bilinCof (e2 + e3) C tau 0 =
      C 1 * tau 2 - C 1 * tau 3 - C 2 * tau 1 + C 3 * tau 1 := by
  rw [bilinCof_expand, sa00, sa01, sa02]
  simp [e2, e3, Pi.add_apply]; try ring

lemma bilinCof_e2I_mid (C tau : Fin 4 → ℂ) :
    bilinCof e2I C tau 0 =
      Complex.I * C 1 * tau 2 - C 1 * tau 3 - Complex.I * C 2 * tau 1 + C 3 * tau 1 := by
  rw [bilinCof_expand, sa00, sa01, sa02]; simp [e2I]; try ring

lemma bilinCof_e2e3_sides (p q : Fin 4 → ℂ) :
    bilinCof (e2 + e3) p q 1 = -p 0 * q 2 + p 0 * q 3 + p 2 * q 0 - p 3 * q 0 ∧
    bilinCof (e2 + e3) p q 2 = p 0 * q 1 - p 1 * q 0 ∧
    bilinCof (e2 + e3) p q 3 = -p 0 * q 1 + p 1 * q 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [bilinCof_expand, sa10, sa11, sa12]; simp [e2, e3, Pi.add_apply]; try ring
  · rw [bilinCof_expand, sa20, sa21, sa22]; simp [e2, e3, Pi.add_apply]; try ring
  · rw [bilinCof_expand, sa30, sa31, sa32]; simp [e2, e3, Pi.add_apply]; try ring

lemma bilinCof_e2I_sides (p q : Fin 4 → ℂ) :
    bilinCof e2I p q 1 =
      -Complex.I * p 0 * q 2 + p 0 * q 3 + Complex.I * p 2 * q 0 - p 3 * q 0 ∧
    bilinCof e2I p q 2 = Complex.I * p 0 * q 1 - Complex.I * p 1 * q 0 ∧
    bilinCof e2I p q 3 = -p 0 * q 1 + p 1 * q 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [bilinCof_expand, sa10, sa11, sa12]; simp [e2I]; try ring
  · rw [bilinCof_expand, sa20, sa21, sa22]; simp [e2I]; try ring
  · rw [bilinCof_expand, sa30, sa31, sa32]; simp [e2I]; try ring

lemma nestedLead_e2 (p q tau : Fin 4 → ℂ) :
    nestedLead e2 p q tau =
      -tau 1 * star (plucker p q 0 1) - tau 3 * star (plucker p q 0 3) := by
  rw [nestedLead_as_bilin, bilinCof_e2_mid]
  unfold hermCof
  obtain ⟨_, h1, _, h3⟩ := bilinCof_e2 p q
  simp only [Pi.star_apply]
  rw [h1, h3]
  have hπ1 : -p 0 * q 1 + p 1 * q 0 = -plucker p q 0 1 := by
    simp [plucker]; ring
  have hπ3 : p 0 * q 3 - p 3 * q 0 = plucker p q 0 3 := rfl
  rw [hπ1, hπ3, star_neg]
  ring

lemma nestedLead_e3 (p q tau : Fin 4 → ℂ) :
    nestedLead e3 p q tau =
      -tau 1 * star (plucker p q 0 1) - tau 2 * star (plucker p q 0 2) := by
  rw [nestedLead_as_bilin, bilinCof_e3_mid]
  unfold hermCof
  obtain ⟨_, h1, h2, _⟩ := bilinCof_e3 p q
  simp only [Pi.star_apply]
  rw [h1, h2]
  have hπ1 : p 0 * q 1 - p 1 * q 0 = plucker p q 0 1 := rfl
  have hπ2 : -p 0 * q 2 + p 2 * q 0 = -plucker p q 0 2 := by
    simp [plucker]; ring
  rw [hπ1, hπ2, star_neg]
  ring

lemma nestedLead_e2e3 (p q tau : Fin 4 → ℂ) :
    nestedLead (e2 + e3) p q tau =
      -2 * tau 1 * star (plucker p q 0 1) +
        (tau 3 - tau 2) * star (plucker p q 0 2) +
        (tau 2 - tau 3) * star (plucker p q 0 3) := by
  rw [nestedLead_as_bilin, bilinCof_e2e3_mid]
  unfold hermCof
  obtain ⟨h1, h2, h3⟩ := bilinCof_e2e3_sides p q
  simp only [Pi.star_apply]
  rw [h1, h2, h3]
  have hπ1 : p 0 * q 1 - p 1 * q 0 = plucker p q 0 1 := rfl
  have hπ1' : -p 0 * q 1 + p 1 * q 0 = -plucker p q 0 1 := by
    simp [plucker]; ring
  have hπ23 :
      -p 0 * q 2 + p 0 * q 3 + p 2 * q 0 - p 3 * q 0 =
        -plucker p q 0 2 + plucker p q 0 3 := by
    simp [plucker]; ring
  rw [hπ1, hπ1', hπ23]
  simp [star_add, star_neg]
  ring

lemma nestedLead_e2I (p q tau : Fin 4 → ℂ) :
    nestedLead e2I p q tau =
      -2 * tau 1 * star (plucker p q 0 1) -
        tau 2 * star (plucker p q 0 2) +
        Complex.I * tau 2 * star (plucker p q 0 3) -
        Complex.I * tau 3 * star (plucker p q 0 2) -
        tau 3 * star (plucker p q 0 3) := by
  rw [nestedLead_as_bilin, bilinCof_e2I_mid]
  unfold hermCof
  obtain ⟨h1, h2, h3⟩ := bilinCof_e2I_sides p q
  simp only [Pi.star_apply]
  rw [h1, h2, h3]
  have hπ1 : -p 0 * q 1 + p 1 * q 0 = -plucker p q 0 1 := by
    simp [plucker]; ring
  have hπI :
      Complex.I * p 0 * q 1 - Complex.I * p 1 * q 0 = Complex.I * plucker p q 0 1 := by
    simp [plucker]; ring
  have hπ23 :
      -Complex.I * p 0 * q 2 + p 0 * q 3 + Complex.I * p 2 * q 0 - p 3 * q 0 =
        -Complex.I * plucker p q 0 2 + plucker p q 0 3 := by
    simp [plucker]; ring
  rw [hπ1, hπI, hπ23]
  simp [star_add, star_neg, star_mul, Complex.star_def, Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq]
  ring

lemma tau_not_in_link {tau : Fin 4 → ℂ}
    (hli : LinearIndependent ℂ ![rVec, nVec, tau]) :
    tau 2 ≠ 0 ∨ tau 3 ≠ 0 := by
  by_contra h
  push Not at h
  have hz : tau = tau 0 • rVec + tau 1 • nVec := by
    ext i
    fin_cases i
    · simp [rVec, nVec, Pi.add_apply]
    · simp [rVec, nVec, Pi.add_apply]
    · simp [rVec, nVec, Pi.add_apply, h.1]
    · simp [rVec, nVec, Pi.add_apply, h.2]
  rw [Fintype.linearIndependent_iff] at hli
  let a := tau 0
  let b := tau 1
  have hz' : tau = a • rVec + b • nVec := hz
  let g : Fin 3 → ℂ := ![a, b, -1]
  have hg : ∑ i : Fin 3, g i • (![rVec, nVec, tau] : Fin 3 → Fin 4 → ℂ) i = 0 := by
    simp only [g, Fin.sum_univ_three, fin3_zero, fin3_one, fin3_two]
    rw [hz', neg_one_smul]
    abel
  have := hli g hg 2
  simp [g] at this

lemma plucker_span_n (p q : Fin 4 → ℂ)
    (h02 : plucker p q 0 2 = 0) (h03 : plucker p q 0 3 = 0) :
    p 0 • q - q 0 • p = plucker p q 0 1 • nVec := by
  ext i
  fin_cases i
  · simp [plucker, nVec, Pi.sub_apply, Pi.smul_apply]; ring
  · simp [plucker, nVec, Pi.sub_apply, Pi.smul_apply]; ring
  · have : p 0 * q 2 - q 0 * p 2 = plucker p q 0 2 := by
      simp [plucker]; ring
    simp [nVec, Pi.sub_apply, Pi.smul_apply]
    rw [this, h02]
  · have : p 0 * q 3 - q 0 * p 3 = plucker p q 0 3 := by
      simp [plucker]; ring
    simp [nVec, Pi.sub_apply, Pi.smul_apply]
    rw [this, h03]

lemma pqn_of_plucker {p q : Fin 4 → ℂ}
    (h0 : p 0 ≠ 0 ∨ q 0 ≠ 0)
    (h02 : plucker p q 0 2 = 0) (h03 : plucker p q 0 3 = 0) :
    ¬ LinearIndependent ℂ ![p, q, nVec] := by
  intro hli
  rw [Fintype.linearIndependent_iff] at hli
  have hcomb := plucker_span_n p q h02 h03
  rcases h0 with hp | hq
  · let g : Fin 3 → ℂ := ![q 0, -p 0, plucker p q 0 1]
    have hg : ∑ i, g i • (![p, q, nVec] : Fin 3 → Fin 4 → ℂ) i = 0 := by
      simp only [g, Fin.sum_univ_three, fin3_zero, fin3_one, fin3_two]
      calc
        q 0 • p + (-p 0) • q + plucker p q 0 1 • nVec
            = -(p 0 • q - q 0 • p) + plucker p q 0 1 • nVec := by
              simp [neg_smul]; abel
        _ = -(plucker p q 0 1 • nVec) + plucker p q 0 1 • nVec := by rw [hcomb]
        _ = 0 := by abel
    have := hli g hg 1
    simp [g, hp] at this
  · let g : Fin 3 → ℂ := ![-q 0, p 0, -plucker p q 0 1]
    have hg : ∑ i, g i • (![p, q, nVec] : Fin 3 → Fin 4 → ℂ) i = 0 := by
      simp only [g, Fin.sum_univ_three, fin3_zero, fin3_one, fin3_two]
      calc
        (-q 0) • p + p 0 • q + (-plucker p q 0 1) • nVec
            = p 0 • q - q 0 • p - plucker p q 0 1 • nVec := by
              simp [neg_smul]; abel
        _ = plucker p q 0 1 • nVec - plucker p q 0 1 • nVec := by rw [hcomb]
        _ = 0 := by abel
    have := hli g hg 0
    simp [g, hq] at this

lemma iso_factor {u v : ℂ} (h : u * u + v * v = 0) :
    (v - Complex.I * u) * (v + Complex.I * u) = 0 := by
  have hsq := sq_sub_sq v (Complex.I * u)
  have hpow : v ^ 2 - (Complex.I * u) ^ 2 = u * u + v * v := by
    rw [mul_pow, Complex.I_sq]; ring
  rw [hpow, h, eq_comm] at hsq
  rw [mul_comm] at hsq
  exact hsq

lemma I_I_mul (z : ℂ) : Complex.I * (Complex.I * z) = -z := by
  rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]

lemma I_negI_mul (z : ℂ) : Complex.I * (-Complex.I * z) = z := by
  rw [← mul_assoc, mul_neg, Complex.I_mul_I, neg_neg, one_mul]

lemma not_all_zero (p q tau : Fin 4 → ℂ)
    (hpqn : LinearIndependent ℂ ![p, q, nVec])
    (hrnt : LinearIndependent ℂ ![rVec, nVec, tau])
    (hside : ¬ (p 0 = 0 ∧ q 0 = 0)) :
    nestedLead e2 p q tau ≠ 0 ∨
      nestedLead e3 p q tau ≠ 0 ∨
      nestedLead (e2 + e3) p q tau ≠ 0 ∨
      nestedLead e2I p q tau ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨he2, he3, he23, he2I⟩ := h
  rw [nestedLead_e2] at he2
  rw [nestedLead_e3] at he3
  rw [nestedLead_e2e3] at he23
  rw [nestedLead_e2I] at he2I
  set α := star (plucker p q 0 1)
  set β := star (plucker p q 0 2)
  set γ := star (plucker p q 0 3)
  have he2' : tau 1 * α + tau 3 * γ = 0 := by linear_combination -he2
  have he3' : tau 1 * α + tau 2 * β = 0 := by linear_combination -he3
  have htb : tau 2 * β = -tau 1 * α := by linear_combination he3'
  have htg : tau 3 * γ = -tau 1 * α := by linear_combination he2'
  have hlin1 : tau 2 * β - tau 3 * γ = 0 := by linear_combination htb - htg
  have h23' : tau 2 * β + tau 3 * β + tau 2 * γ - tau 3 * γ = 0 := by
    linear_combination he23 + 2 * htb
  have hmix : tau 2 * γ + tau 3 * β = 0 := by linear_combination h23' - hlin1
  have he2I' :
      tau 2 * β + Complex.I * tau 2 * γ - Complex.I * tau 3 * β - tau 3 * γ = 0 := by
    linear_combination he2I + 2 * htb
  have hdetβ : (tau 2 * tau 2 + tau 3 * tau 3) * β = 0 := by
    linear_combination tau 2 * hlin1 + tau 3 * hmix
  have hdetγ : (tau 2 * tau 2 + tau 3 * tau 3) * γ = 0 := by
    linear_combination tau 2 * hmix - tau 3 * hlin1
  have hβγ : β = 0 ∧ γ = 0 := by
    by_cases hdet : tau 2 * tau 2 + tau 3 * tau 3 = 0
    · have hτ2 : tau 2 ≠ 0 := by
        intro hz
        have hτ3 : tau 3 = 0 := by
          have : tau 3 * tau 3 = 0 := by simpa [hz] using hdet
          exact (mul_eq_zero.mp this).elim id id
        exact (tau_not_in_link hrnt).elim (fun h => h hz) (fun h => h hτ3)
      have hfac := iso_factor (u := tau 2) (v := tau 3) hdet
      rcases mul_eq_zero.mp hfac with hp | hm
      · have ht : tau 3 = Complex.I * tau 2 := sub_eq_zero.mp hp
        have h2β : (2 : ℂ) * tau 2 * β = 0 := by
          have := he2I'
          rw [ht] at this
          have hrewrite :
              tau 2 * β + Complex.I * tau 2 * γ - Complex.I * (Complex.I * tau 2) * β -
                  Complex.I * tau 2 * γ =
                (2 : ℂ) * tau 2 * β := by
            rw [I_I_mul]; ring
          rw [hrewrite] at this
          exact this
        have htwo : (2 : ℂ) ≠ 0 := by norm_num
        have hβ : β = 0 :=
          (mul_eq_zero.mp h2β).resolve_left (mul_ne_zero htwo hτ2)
        have hγ : γ = 0 := by
          have ht3 : tau 3 ≠ 0 := by
            rw [ht]
            exact mul_ne_zero Complex.I_ne_zero hτ2
          have : tau 3 * γ = 0 := by
            rw [hβ] at hlin1
            linear_combination -hlin1
          exact (mul_eq_zero.mp this).resolve_left ht3
        exact ⟨hβ, hγ⟩
      · have ht : tau 3 = -Complex.I * tau 2 := by linear_combination hm
        have h2γ : (2 : ℂ) * Complex.I * tau 2 * γ = 0 := by
          have := he2I'
          rw [ht] at this
          have hrewrite :
              tau 2 * β + Complex.I * tau 2 * γ - Complex.I * (-Complex.I * tau 2) * β -
                  (-Complex.I * tau 2) * γ =
                (2 : ℂ) * Complex.I * tau 2 * γ := by
            rw [I_negI_mul]; ring
          rw [hrewrite] at this
          exact this
        have htwo : (2 : ℂ) ≠ 0 := by norm_num
        have hγ : γ = 0 := by
          have hcoeff : (2 : ℂ) * Complex.I * tau 2 ≠ 0 :=
            mul_ne_zero (mul_ne_zero htwo Complex.I_ne_zero) hτ2
          exact (mul_eq_zero.mp h2γ).resolve_left hcoeff
        have hβ : β = 0 := by
          have ht3 : tau 3 ≠ 0 := by
            rw [ht]
            exact mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hτ2
          have : tau 3 * β = 0 := by
            rw [hγ] at hmix
            linear_combination hmix
          exact (mul_eq_zero.mp this).resolve_left ht3
        exact ⟨hβ, hγ⟩
    · have hβ : β = 0 := (mul_eq_zero.mp hdetβ).resolve_left hdet
      have hγ : γ = 0 := (mul_eq_zero.mp hdetγ).resolve_left hdet
      exact ⟨hβ, hγ⟩
  have hβ : plucker p q 0 2 = 0 := by
    simpa [β, star_eq_zero] using hβγ.1
  have hγ : plucker p q 0 3 = 0 := by
    simpa [γ, star_eq_zero] using hβγ.2
  have hside0 : p 0 ≠ 0 ∨ q 0 ≠ 0 := by
    rcases not_and_or.mp hside with h | h
    · exact Or.inl h
    · exact Or.inr h
  exact (pqn_of_plucker hside0 hβ hγ) hpqn

theorem proof :
    ∀ (p q tau : Fin 4 → ℂ),
      LinearIndependent ℂ ![p, q, nVec] →
      LinearIndependent ℂ ![rVec, nVec, tau] →
      ¬ (pair rVec p = 0 ∧ pair rVec q = 0) →
      ∃ b : Fin 4 → ℂ,
        pair rVec b = 0 ∧ pair nVec b = 0 ∧ nestedLead b p q tau ≠ 0 := by
  intro p q tau hpqn hrnt hside
  have hside' : ¬ (p 0 = 0 ∧ q 0 = 0) := by
    simpa [pair_rVec] using hside
  have hdisj := not_all_zero p q tau hpqn hrnt hside'
  rcases hdisj with h | h | h | h
  · exact ⟨e2, pair_e2.1, pair_e2.2, h⟩
  · exact ⟨e3, pair_e3.1, pair_e3.2, h⟩
  · exact ⟨e2 + e3, pair_e2e3.1, pair_e2e3.2, h⟩
  · exact ⟨e2I, pair_e2I.1, pair_e2I.2, h⟩

end

end Submissions.Length4NestedFiberNonvanishing.Nested
