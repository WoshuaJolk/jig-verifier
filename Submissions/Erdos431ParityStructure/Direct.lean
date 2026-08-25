import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.Interval.Set.Nat
import Mathlib.Tactic

namespace Submissions.Erdos431ParityStructure.Direct

def sumset (A B : Set ℕ) : Set ℕ :=
  {n | ∃ a ∈ A, ∃ b ∈ B, a + b = n}

/-- Any hypothetical asymptotic binary decomposition forces each summand
set to occupy just one parity class. -/
theorem left_parity_constant (A B : Set ℕ) (hB : B.Infinite)
    (hE : {n : ℕ | (n ∈ sumset A B) ≠ n.Prime}.Finite) :
    ∀ a₁ ∈ A, ∀ a₂ ∈ A, a₁ % 2 = a₂ % 2 := by
  obtain ⟨M, hM⟩ := hE.bddAbove
  have hex : ∃ b ∈ B, max M 2 < b := by
    by_contra! hbnd
    apply hB
    refine (Set.finite_Iic (max M 2)).subset ?_
    intro b hb
    exact hbnd b hb
  obtain ⟨b, hb, hbM⟩ := hex
  intro a₁ ha₁ a₂ ha₂
  have hsum₁ : a₁ + b ∈ sumset A B :=
    ⟨a₁, ha₁, b, hb, rfl⟩
  have hsum₂ : a₂ + b ∈ sumset A B :=
    ⟨a₂, ha₂, b, hb, rfl⟩
  have hout₁ :
      a₁ + b ∉ {n : ℕ | (n ∈ sumset A B) ≠ n.Prime} := by
    intro hmem
    exact (not_le_of_gt
      ((le_max_left M 2).trans_lt hbM |>.trans_le (Nat.le_add_left b a₁))) (hM hmem)
  have hout₂ :
      a₂ + b ∉ {n : ℕ | (n ∈ sumset A B) ≠ n.Prime} := by
    intro hmem
    exact (not_le_of_gt
      ((le_max_left M 2).trans_lt hbM |>.trans_le (Nat.le_add_left b a₂))) (hM hmem)
  have hp₁ : (a₁ + b).Prime := by
    change ¬((a₁ + b ∈ sumset A B) ≠ (a₁ + b).Prime) at hout₁
    exact (not_ne_iff.mp hout₁).mp hsum₁
  have hp₂ : (a₂ + b).Prime := by
    change ¬((a₂ + b ∈ sumset A B) ≠ (a₂ + b).Prime) at hout₂
    exact (not_ne_iff.mp hout₂).mp hsum₂
  have hodd₁ : (a₁ + b) % 2 = 1 :=
    hp₁.eq_two_or_odd.resolve_left (by omega)
  have hodd₂ : (a₂ + b) % 2 = 1 :=
    hp₂.eq_two_or_odd.resolve_left (by omega)
  omega

theorem proof (A B : Set ℕ)
    (hA : A.Infinite) (hB : B.Infinite)
    (hE : {n : ℕ | (n ∈ sumset A B) ≠ n.Prime}.Finite) :
    (∀ a₁ ∈ A, ∀ a₂ ∈ A, a₁ % 2 = a₂ % 2) ∧
      (∀ b₁ ∈ B, ∀ b₂ ∈ B, b₁ % 2 = b₂ % 2) := by
  constructor
  · exact left_parity_constant A B hB hE
  · apply left_parity_constant B A hA
    have hsum : sumset B A = sumset A B := by
      ext n
      constructor
      · rintro ⟨b, hb, a, ha, rfl⟩
        exact ⟨a, ha, b, hb, add_comm _ _⟩
      · rintro ⟨a, ha, b, hb, rfl⟩
        exact ⟨b, hb, a, ha, add_comm _ _⟩
    simpa [hsum] using hE

end Submissions.Erdos431ParityStructure.Direct
