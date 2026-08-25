import Mathlib.Tactic

namespace Submissions.Erdos455GapsTendToInfinity.Direct

lemma monotone_bounded_eventually_constant
    (g : ℕ → ℕ) (hg : Monotone g) (B : ℕ) (hB : ∀ n, g n ≤ B) :
    ∃ N d, ∀ n ≥ N, g n = d := by
  have hR : (Set.range g).Finite := by
    refine (Set.finite_Iic B).subset ?_
    rintro x ⟨n, rfl⟩
    exact hB n
  let R : Finset ℕ := hR.toFinset
  have hRne : R.Nonempty := by
    refine ⟨g 0, ?_⟩
    simp [R]
  let d := R.max' hRne
  have hdR : d ∈ R := Finset.max'_mem R hRne
  have hdrange : d ∈ Set.range g := by
    simpa [R] using hdR
  obtain ⟨N, hN⟩ := hdrange
  refine ⟨N, d, ?_⟩
  intro n hn
  apply le_antisymm
  · apply Finset.le_max' R (g n)
    simp [R]
  · rw [← hN]
    exact hg hn

def gap (q : ℕ → ℕ) (n : ℕ) : ℕ := q (n + 1) - q n

lemma gap_monotone (q : ℕ → ℕ)
    (hgap : ∀ n, q (n + 2) - q (n + 1) ≥ q (n + 1) - q n) :
    Monotone (gap q) := by
  apply monotone_nat_of_le_succ
  intro n
  simpa [gap, Nat.add_assoc] using hgap n

lemma value_of_constant_gaps (q : ℕ → ℕ) (hq : StrictMono q)
    (N d : ℕ) (hconst : ∀ n ≥ N, gap q n = d) :
    ∀ k, q (N + k) = q N + k * d := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      have hlt : q (N + k) < q (N + k + 1) :=
        hq (by omega)
      have hstep : q (N + k + 1) = q (N + k) + d := by
        have hc := hconst (N + k) (by omega)
        rw [gap, Nat.sub_eq_iff_eq_add hlt.le] at hc
        omega
      rw [Nat.add_succ, hstep, ih, Nat.succ_mul]
      omega

/-- Route 3: primality prevents the nondecreasing gaps from being bounded. -/
theorem gaps_unbounded (q : ℕ → ℕ) (hq : StrictMono q)
    (hprime : ∀ n, (q n).Prime)
    (hgap : ∀ n, q (n + 2) - q (n + 1) ≥ q (n + 1) - q n) :
    ∀ B, ∃ n, B < gap q n := by
  intro B
  by_contra! hB
  obtain ⟨N, d, hconst⟩ :=
    monotone_bounded_eventually_constant (gap q) (gap_monotone q hgap) B hB
  have hdpos : 0 < d := by
    have hlt := hq (show N < N + 1 by omega)
    have := hconst N le_rfl
    simp only [gap] at this
    omega
  have hvalue := value_of_constant_gaps q hq N d hconst (q N)
  have hfactor :
      q N + q N * d = q N * (d + 1) := by
    rw [Nat.mul_succ]
    omega
  rw [hfactor] at hvalue
  have hnotprime : ¬(q N * (d + 1)).Prime :=
    Nat.not_prime_mul (hprime N).ne_one (by omega)
  exact hnotprime (hvalue ▸ hprime (N + q N))

/-- Equivalently, the consecutive gaps tend to infinity. -/
theorem proof :
    ∀ q : ℕ → ℕ, StrictMono q →
      (∀ n, (q n).Prime ∧
        q (n + 2) - q (n + 1) ≥ q (n + 1) - q n) →
      Filter.Tendsto (gap q) Filter.atTop Filter.atTop := by
  intro q hq h
  have hprime : ∀ n, (q n).Prime := fun n => (h n).1
  have hgap :
      ∀ n, q (n + 2) - q (n + 1) ≥ q (n + 1) - q n :=
    fun n => (h n).2
  apply (gap_monotone q hgap).tendsto_atTop_atTop
  intro B
  obtain ⟨n, hn⟩ := gaps_unbounded q hq hprime hgap B
  exact ⟨n, hn.le⟩

end Submissions.Erdos455GapsTendToInfinity.Direct
