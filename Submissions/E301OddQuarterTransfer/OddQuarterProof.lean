import Mathlib
namespace Submissions.E301OddQuarterTransfer.OddQuarterProof

def TripleFree (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a ≠ b → a ≠ c → b ≠ c →
    (a : ℚ)⁻¹ ≠ (b : ℚ)⁻¹ + (c : ℚ)⁻¹

def OddQuarter (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun n => Odd n ∧ 4 * n ≤ N)

theorem quarter_arithmetic {a b c : ℕ} (ha : 0 < a)
    (hb : 2 * a ≤ b) (hc : 2 * a ≤ c) (hne : b ≠ c) :
    b * c ≠ a * (b + c) := by
  intro heq
  have heq' : (b : ℤ) * c = (a : ℤ) * (b + c) := by exact_mod_cast heq
  have hp : (0 : ℤ) < a := by exact_mod_cast ha
  have hb' : (0 : ℤ) ≤ (b : ℤ) - 2 * a := by omega
  have hc' : (0 : ℤ) ≤ (c : ℤ) - 2 * a := by omega
  have hs : (0 : ℤ) < (b : ℤ) + c - 4 * a := by omega
  nlinarith [mul_nonneg hb' hc', mul_pos hp hs]

theorem proof : ∀ (N : ℕ) (A : Finset ℕ), A ⊆ Finset.Icc 1 N →
    (∀ n ∈ A, (N < 3 * n ∧ 2 * n < N ∧ Odd n) ∨ N ≤ 2 * n) →
    TripleFree A → TripleFree (A ∪ OddQuarter N) ∧
    (A ∪ OddQuarter N).card ≥ A.card + N / 8 := by
  classical
  intro N A hA hshape hfree
  have hoq : ∀ n ∈ OddQuarter N, 0 < n ∧ Odd n ∧ 4 * n ≤ N := by
    intro n hn
    have h := Finset.mem_filter.mp hn
    exact ⟨(Finset.mem_Icc.mp h.1).1, h.2⟩
  have hpos : ∀ n ∈ A ∪ OddQuarter N, 0 < n := by
    intro n hn
    rcases Finset.mem_union.mp hn with hn | hn
    · exact (Finset.mem_Icc.mp (hA hn)).1
    · exact (hoq n hn).1
  constructor
  · intro a ha b hb c hc hab hac hbc heq
    have pa := hpos a ha
    have pb := hpos b hb
    have pc := hpos c hc
    have za : (a : ℚ) ≠ 0 := by positivity
    have zb : (b : ℚ) ≠ 0 := by positivity
    have zc : (c : ℚ) ≠ 0 := by positivity
    have eqQ : (b : ℚ) * c = a * (b + c) := by
      field_simp at heq
      nlinarith [heq]
    have eqN : b*c = a*(b+c) := by exact_mod_cast eqQ
    have ab : a < b := by
      by_contra h
      have : b ≤ a := by omega
      nlinarith
    have ac : a < c := by
      by_contra h
      have : c ≤ a := by omega
      nlinarith
    have small : 4*a ≤ N := by
      by_contra h
      have allA : ∀ x ∈ A ∪ OddQuarter N, a ≤ x → x ∈ A := by
        intro x hx hax
        rcases Finset.mem_union.mp hx with hx | hx
        · exact hx
        · have := (hoq x hx).2.2; omega
      exact hfree a (allA a ha (by omega)) b (allA b hb (by omega))
        c (allA c hc (by omega)) hab hac hbc heq
    have oa : Odd a := by
      rcases Finset.mem_union.mp ha with ha | ha
      · rcases hshape a ha with h | h
        · exact h.2.2
        · omega
      · exact (hoq a ha).2.1
    have amod : a % 2 = 1 := Nat.odd_iff.mp oa
    have eqmod := congrArg (fun x : ℕ => x % 2) eqN
    rw [Nat.mul_mod b c, Nat.mul_mod a (b+c), Nat.add_mod b c, amod] at eqmod
    have mods : b % 2 = 0 ∧ c % 2 = 0 := by
      have bh := Nat.mod_lt b (by decide : 0 < 2)
      have ch := Nat.mod_lt c (by decide : 0 < 2)
      have hbmod : b % 2 = 0 ∨ b % 2 = 1 := by omega
      have hcmod : c % 2 = 0 ∨ c % 2 = 1 := by omega
      rcases hbmod with hbmod | hbmod <;> rcases hcmod with hcmod | hcmod <;>
        simp_all
    obtain ⟨bm, cm⟩ := mods
    have large : ∀ x ∈ A ∪ OddQuarter N, x % 2 = 0 → N ≤ 2*x := by
      intro x hx hm
      rcases Finset.mem_union.mp hx with hx | hx
      · rcases hshape x hx with h | h
        · have := Nat.odd_iff.mp h.2.2; omega
        · exact h
      · have := Nat.odd_iff.mp (hoq x hx).2.1; omega
    exact quarter_arithmetic pa (by have := large b hb bm; omega)
      (by have := large c hc cm; omega) hbc eqN
  · have hd : Disjoint A (OddQuarter N) := by
      apply Finset.disjoint_left.mpr
      intro n hn ho
      have hp := hoq n ho
      rcases hshape n hn with h | h <;> omega
    have hsub : (Finset.range (N/8)).image (fun k => 2*k+1) ⊆ OddQuarter N := by
      intro n hn
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hn
      have := Finset.mem_range.mp hk
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ⟨k, by omega⟩, by omega⟩
    have hcard : ((Finset.range (N/8)).image (fun k => 2*k+1)).card = N/8 := by
      rw [Finset.card_image_of_injective]
      · exact Finset.card_range _
      · intro a b h
        change 2*a+1 = 2*b+1 at h
        omega
    have := Finset.card_le_card hsub
    rw [hcard] at this
    rw [Finset.card_union_of_disjoint hd]
    omega
end Submissions.E301OddQuarterTransfer.OddQuarterProof
