import Init

namespace Submissions.Erdos3SeparatedBlocks.Basic

/-- Separated intervals cannot contain a three-term progression crossing blocks. -/
theorem triple_same_block
    (L U : Nat → Nat)
    (sep₁ : ∀ i j, i < j → 2 * U i < L j)
    (sep₂ : ∀ i j, i < j → U i + U j < 2 * L j)
    (x y z i j l : Nat)
    (hx : L i ≤ x ∧ x ≤ U i)
    (hy : L j ≤ y ∧ y ≤ U j)
    (hz : L l ≤ z ∧ z ≤ U l)
    (hxy : x < y) (hap : x + z = 2 * y) :
    i = j ∧ j = l := by
  have hij : i ≤ j := by
    by_cases h : i ≤ j
    · exact h
    · have hs := sep₁ j i (by omega)
      omega
  have hjl : j ≤ l := by
    by_cases h : j ≤ l
    · exact h
    · have hs := sep₁ l j (by omega)
      omega
  have heq : j = l := by
    by_cases h : j = l
    · exact h
    · have hs := sep₁ j l (by omega)
      omega
  subst l
  constructor
  · by_cases h : i = j
    · exact h
    · have hs := sep₂ i j (by omega)
      omega
  · rfl

/-- Local equality along all consecutive triples forces one block for every finite length. -/
theorem all_same_block
    (k : Nat) (hk : 3 ≤ k) (b : Nat → Nat)
    (h : ∀ n, n + 2 < k → b n = b (n + 1) ∧ b (n + 1) = b (n + 2)) :
    ∀ n, n < k → b n = b 0 := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    have hn' : n < k := by omega
    have hn0 := ih hn'
    cases n with
    | zero => exact (h 0 (by omega)).1.symm
    | succ m =>
      have hstep := (h m (by omega)).2
      exact hstep.symm.trans hn0

/-- Every progression of length at least three stays in one separated interval. -/
theorem progression_same_block
    (L U : Nat → Nat)
    (sep₁ : ∀ i j, i < j → 2 * U i < L j)
    (sep₂ : ∀ i j, i < j → U i + U j < 2 * L j)
    (k a d : Nat) (hk : 3 ≤ k) (hd : 0 < d) (b : Nat → Nat)
    (hb : ∀ n, n < k → L (b n) ≤ a + n * d ∧ a + n * d ≤ U (b n)) :
    ∀ n, n < k → b n = b 0 := by
  apply all_same_block k hk b
  intro n hn
  apply triple_same_block L U sep₁ sep₂
    (a + n * d) (a + (n + 1) * d) (a + (n + 2) * d)
    (b n) (b (n + 1)) (b (n + 2))
    (hb n (by omega)) (hb (n + 1) (by omega)) (hb (n + 2) hn)
  · simp only [Nat.add_mul, Nat.one_mul]
    omega
  · simp only [Nat.add_mul, Nat.one_mul]
    omega

/-- Gluing individually progression-free blocks preserves the forbidden length. -/
theorem proof
    (L U : Nat → Nat)
    (sep₁ : ∀ i j, i < j → 2 * U i < L j)
    (sep₂ : ∀ i j, i < j → U i + U j < 2 * L j)
    (k : Nat) (hk : 3 ≤ k) (B : Nat → Nat → Prop)
    (bounds : ∀ j x, B j x → L j ≤ x ∧ x ≤ U j)
    (free : ∀ j a d, 0 < d → ¬ (∀ n, n < k → B j (a + n * d))) :
    ∀ a d, 0 < d → ¬ (∀ n, n < k → ∃ j, B j (a + n * d)) := by
  intro a d hd h
  classical
  let b : Nat → Nat := fun n => if hn : n < k then Classical.choose (h n hn) else 0
  have hb : ∀ n, n < k → B (b n) (a + n * d) := by
    intro n hn
    simpa only [b, dif_pos hn] using Classical.choose_spec (h n hn)
  have hs := progression_same_block L U sep₁ sep₂ k a d hk hd b
    (fun n hn => bounds (b n) (a + n * d) (hb n hn))
  apply free (b 0) a d hd
  intro n hn
  have hm := hb n hn
  rw [hs n hn] at hm
  exact hm

/-- The base-four intervals used in the harmonic-mass reduction satisfy both gaps. -/
theorem base_four_separation (i j : Nat) (hij : i < j) :
    2 * (5 * 4 ^ i) < 4 * 4 ^ j + 1 ∧
    5 * 4 ^ i + 5 * 4 ^ j < 2 * (4 * 4 ^ j + 1) := by
  have hp := Nat.pow_le_pow_right (by decide : 0 < 4) (show i + 1 ≤ j by omega)
  simp only [Nat.pow_succ] at hp
  omega

/-- Every nonempty base-four block has at least one available natural number. -/
theorem base_four_nonempty (j : Nat) : 4 * 4 ^ j + 1 ≤ 5 * 4 ^ j := by
  have hp := Nat.one_le_pow j 4 (by decide)
  omega

/-- Base-four translated progression-free blocks remain progression-free together. -/
theorem base_four_union
    (k : Nat) (hk : 3 ≤ k) (B : Nat → Nat → Prop)
    (bounds : ∀ j x, B j x → 4 * 4 ^ j + 1 ≤ x ∧ x ≤ 5 * 4 ^ j)
    (free : ∀ j a d, 0 < d → ¬ (∀ n, n < k → B j (a + n * d))) :
    ∀ a d, 0 < d → ¬ (∀ n, n < k → ∃ j, B j (a + n * d)) :=
  proof (fun j => 4 * 4 ^ j + 1) (fun j => 5 * 4 ^ j)
    (fun i j hij => (base_four_separation i j hij).1)
    (fun i j hij => (base_four_separation i j hij).2) k hk B bounds free

/-- Translating arbitrary k-free sets in [1,4^j] gives a k-free union. -/
theorem translated_union
    (k : Nat) (hk : 3 ≤ k) (E : Nat → Nat → Prop)
    (bounds : ∀ j x, E j x → 1 ≤ x ∧ x ≤ 4 ^ j)
    (free : ∀ j a d, 0 < d → ¬ (∀ n, n < k → E j (a + n * d))) :
    ∀ a d, 0 < d → ¬ (∀ n, n < k →
      ∃ j x, E j x ∧ a + n * d = 4 * 4 ^ j + x) := by
  apply base_four_union k hk (fun j y => ∃ x, E j x ∧ y = 4 * 4 ^ j + x)
  · intro j y hy
    obtain ⟨x, hx, hxy⟩ := hy
    have hb := bounds j x hx
    omega
  · intro j a d hd h
    obtain ⟨x, hx, hax⟩ := h 0 (by omega)
    have ha : 4 * 4 ^ j ≤ a := by omega
    apply free j (a - 4 * 4 ^ j) d hd
    intro n hn
    obtain ⟨y, hy, hay⟩ := h n hn
    have heq : a - 4 * 4 ^ j + n * d = y := by omega
    rw [heq]
    exact hy

end Submissions.Erdos3SeparatedBlocks.Basic

#print axioms Submissions.Erdos3SeparatedBlocks.Basic.triple_same_block
#print axioms Submissions.Erdos3SeparatedBlocks.Basic.all_same_block
#print axioms Submissions.Erdos3SeparatedBlocks.Basic.progression_same_block
#print axioms Submissions.Erdos3SeparatedBlocks.Basic.proof
#print axioms Submissions.Erdos3SeparatedBlocks.Basic.base_four_separation
#print axioms Submissions.Erdos3SeparatedBlocks.Basic.base_four_nonempty
#print axioms Submissions.Erdos3SeparatedBlocks.Basic.base_four_union
#print axioms Submissions.Erdos3SeparatedBlocks.Basic.translated_union
