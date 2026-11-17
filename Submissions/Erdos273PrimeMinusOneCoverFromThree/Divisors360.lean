import Mathlib

namespace Submissions.Erdos273PrimeMinusOneCoverFromThree.Divisors360

/-- Residue and modulus of each class; every modulus divides 360. -/
def L : List (ℕ × ℕ) :=
  [(0, 2), (1, 4), (1, 6), (1, 10), (3, 12), (5, 18), (5, 30), (11, 36), (3, 40),
   (47, 60), (71, 72), (179, 180)]

def toClass (c : ℕ × ℕ) : ℤ × ℕ := ((c.1 : ℤ), c.2)

set_option maxRecDepth 100000 in
theorem key : ∀ r : ℕ, r < 360 → ∃ c ∈ L, r % c.2 = c.1 ∧ c.2 ∣ 360 := by
  decide

theorem distinct : ∀ x ∈ L, ∀ y ∈ L, x.2 = y.2 → x = y := by
  decide

theorem primes : ∀ x ∈ L, (x.2 + 1).Prime ∧ 3 ≤ x.2 + 1 := by
  intro x hx
  simp [L] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (constructor <;> norm_num)

theorem proof :
    ∃ C : Finset (ℤ × ℕ),
      (∀ z : ℤ, ∃ c ∈ C, (c.2 : ℤ) ∣ z - c.1) ∧
      (∀ ⦃c₁⦄, c₁ ∈ C → ∀ ⦃c₂⦄, c₂ ∈ C → c₁.2 = c₂.2 → c₁ = c₂) ∧
      (∀ c ∈ C, ∃ p : ℕ, p.Prime ∧ 3 ≤ p ∧ c.2 = p - 1) := by
  refine ⟨(L.map toClass).toFinset, ?_, ?_, ?_⟩
  · intro z
    have hnn : 0 ≤ z % 360 := Int.emod_nonneg z (by norm_num)
    have hlt : z % 360 < 360 := Int.emod_lt_of_pos z (by norm_num)
    have hr : (((z % 360).toNat : ℕ) : ℤ) = z % 360 := Int.toNat_of_nonneg hnn
    have hrlt : (z % 360).toNat < 360 := by omega
    obtain ⟨c, hcL, hc1, hc2⟩ := key (z % 360).toNat hrlt
    refine ⟨toClass c, ?_, ?_⟩
    · rw [List.mem_toFinset]
      exact List.mem_map_of_mem hcL
    · have h1 : ((((z % 360).toNat % c.2 : ℕ)) : ℤ) = ((c.1 : ℕ) : ℤ) := by
        exact_mod_cast hc1
      have h2 : (((z % 360).toNat : ℕ) : ℤ)
          = ((c.2 : ℕ) : ℤ) * ((((z % 360).toNat / c.2 : ℕ)) : ℤ)
            + ((((z % 360).toNat % c.2 : ℕ)) : ℤ) := by
        exact_mod_cast (Nat.div_add_mod ((z % 360).toNat) c.2).symm
      obtain ⟨q, hq⟩ := hc2
      have h3 : (360 : ℤ) = ((c.2 : ℕ) : ℤ) * ((q : ℕ) : ℤ) := by
        exact_mod_cast hq
      have h4 : z = z % 360 + 360 * (z / 360) := by omega
      refine ⟨((((z % 360).toNat / c.2 : ℕ)) : ℤ) + ((q : ℕ) : ℤ) * (z / 360), ?_⟩
      show z - ((c.1 : ℕ) : ℤ)
          = ((c.2 : ℕ) : ℤ) * (((((z % 360).toNat / c.2 : ℕ)) : ℤ) + ((q : ℕ) : ℤ) * (z / 360))
      linear_combination h4 - hr + h2 + h1 + (z / 360) * h3
  · intro c₁ h₁ c₂ h₂ heq
    rw [List.mem_toFinset, List.mem_map] at h₁ h₂
    obtain ⟨x, hx, rfl⟩ := h₁
    obtain ⟨y, hy, rfl⟩ := h₂
    have hxy : x = y := distinct x hx y hy heq
    rw [hxy]
  · intro c hc
    rw [List.mem_toFinset, List.mem_map] at hc
    obtain ⟨x, hx, rfl⟩ := hc
    obtain ⟨hp, h3⟩ := primes x hx
    exact ⟨x.2 + 1, hp, h3, (Nat.add_sub_cancel).symm⟩

end Submissions.Erdos273PrimeMinusOneCoverFromThree.Divisors360
