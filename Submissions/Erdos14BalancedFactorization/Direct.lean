import Mathlib

namespace Submissions.Erdos14BalancedFactorization.Direct

def pairFiber (X Y : Finset ℕ) (n : ℕ) : Finset (ℕ × ℕ) :=
  (X ×ˢ Y).filter fun p => p.1 + p.2 = n

def balancedTiles (M : ℕ) (X Y : Finset ℕ) : Prop :=
  X ⊆ Finset.Icc 0 M ∧
  Y ⊆ Finset.Icc 0 (M - 1) ∧
  M ∈ X ∧
  M - 1 ∈ Y ∧
  ∀ n ∈ Finset.range (2 * M), (pairFiber X Y n).card = 1

theorem proof :
    ∀ (M : ℕ) (X Y : Finset ℕ), 1 ≤ M →
      balancedTiles M X Y →
      X = {0, M} ∧ Y = Finset.range M := by
  intro M X Y hM htile
  rcases htile with ⟨hXsub, hYsub, hMmem, hMpredmem, htile⟩
  have hzeroRange : 0 ∈ Finset.range (2 * M) := by
    simp
    omega
  have hzeroCard := htile 0 hzeroRange
  have hzeroNonempty : (pairFiber X Y 0).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have := congrArg Finset.card hempty
    simp [hzeroCard] at this
  obtain ⟨p₀, hp₀⟩ := hzeroNonempty
  have hp₀data : (p₀.1 ∈ X ∧ p₀.2 ∈ Y) ∧ p₀.1 + p₀.2 = 0 := by
    simpa [pairFiber] using hp₀
  have hp₀fst : p₀.1 = 0 := by omega
  have hp₀snd : p₀.2 = 0 := by omega
  have hzeroX : 0 ∈ X := by simpa [hp₀fst] using hp₀data.1.1
  have hzeroY : 0 ∈ Y := by simpa [hp₀snd] using hp₀data.1.2
  have hunique :
      ∀ n ∈ Finset.range (2 * M),
        ∀ p ∈ pairFiber X Y n, ∀ q ∈ pairFiber X Y n, p = q := by
    intro n hn p hp q hq
    have hle : (pairFiber X Y n).card ≤ 1 := by
      rw [htile n hn]
    exact Finset.card_le_one.mp hle p hp q hq
  have hexists :
      ∀ n ∈ Finset.range (2 * M), ∃ p, p ∈ pairFiber X Y n := by
    intro n hn
    have hcard := htile n hn
    exact Finset.card_pos.mp (by omega)
  have hclass :
      ∀ r : ℕ, r < M → r ∈ Y ∧ (r = 0 ∨ r ∉ X) := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
        intro hrM
        by_cases hrzero : r = 0
        · subst r
          exact ⟨hzeroY, Or.inl rfl⟩
        · have hrpos : 0 < r := by omega
          have hprev := ih (r - 1) (by omega) (by omega)
          have hprevY : r - 1 ∈ Y := hprev.1
          have hrnotX : r ∉ X := by
            intro hrX
            let p : ℕ × ℕ := (r, M - 1)
            let q : ℕ × ℕ := (M, r - 1)
            let n := M + r - 1
            have hp : p ∈ pairFiber X Y n := by
              simp only [pairFiber, Finset.mem_filter, Finset.mem_product]
              exact ⟨⟨hrX, hMpredmem⟩, by dsimp only [p, n]; omega⟩
            have hq : q ∈ pairFiber X Y n := by
              simp only [pairFiber, Finset.mem_filter, Finset.mem_product]
              exact ⟨⟨hMmem, hprevY⟩, by dsimp only [q, n]; omega⟩
            have hn : n ∈ Finset.range (2 * M) := by
              simp only [Finset.mem_range]
              dsimp only [n]
              omega
            have hpq := hunique n hn p hp q hq
            have hfirst := congrArg Prod.fst hpq
            dsimp only [p, q] at hfirst
            omega
          have hrRange : r ∈ Finset.range (2 * M) := by
            simp only [Finset.mem_range]
            omega
          obtain ⟨p, hp⟩ := hexists r hrRange
          have hpdata : (p.1 ∈ X ∧ p.2 ∈ Y) ∧ p.1 + p.2 = r := by
            simpa [pairFiber] using hp
          have hpfirst : p.1 = 0 := by
            by_contra hpne
            have hppos : 0 < p.1 := Nat.pos_of_ne_zero hpne
            have hple : p.1 ≤ r := by omega
            by_cases hpeq : p.1 = r
            · exact hrnotX (by simpa [hpeq] using hpdata.1.1)
            · have hplt : p.1 < r := by omega
              have hsmall := ih p.1 hplt (by omega)
              have hpnotX : p.1 ∉ X := hsmall.2.resolve_left hpne
              exact hpnotX hpdata.1.1
          have hpsecond : p.2 = r := by omega
          have hrY : r ∈ Y := by simpa [hpsecond] using hpdata.1.2
          exact ⟨hrY, Or.inr hrnotX⟩
  constructor
  · ext a
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro ha
      have habounds := hXsub ha
      simp only [Finset.mem_Icc] at habounds
      by_cases hazero : a = 0
      · exact Or.inl hazero
      · by_cases haM : a = M
        · exact Or.inr haM
        · have haLt : a < M := by omega
          have haClass := hclass a haLt
          exact (haClass.2.resolve_left hazero ha).elim
    · intro ha
      rcases ha with rfl | rfl
      · exact hzeroX
      · exact hMmem
  · ext a
    simp only [Finset.mem_range]
    constructor
    · intro ha
      have habounds := hYsub ha
      simp only [Finset.mem_Icc] at habounds
      omega
    · intro ha
      exact (hclass a ha).1

end Submissions.Erdos14BalancedFactorization.Direct
