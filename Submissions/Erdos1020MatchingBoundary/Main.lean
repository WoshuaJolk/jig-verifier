import Mathlib.Combinatorics.SetFamily.KruskalKatona

namespace Submissions.Erdos1020MatchingBoundary.Main

def Uniform {n : ℕ} (H : Finset (Finset (Fin n))) (r : ℕ) : Prop :=
  ∀ e ∈ H, e.card = r

def MatchingFree {n : ℕ} (H : Finset (Finset (Fin n))) (k : ℕ) : Prop :=
  ¬ ∃ M : Finset (Finset (Fin n)), M ⊆ H ∧ M.card = k ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f

/-- The Erdős matching bound when `k ≤ 2` or the ground set is too small for a
`k`-matching. The nontrivial case reuses Mathlib's Erdős–Ko–Rado theorem. -/
theorem proof :
    ∀ (n r k : ℕ), 3 ≤ r → 1 ≤ k → (k ≤ 2 ∨ n < r * k) →
      ∀ H : Finset (Finset (Fin n)), Uniform H r → MatchingFree H k →
        H.card ≤ max ((r * k - 1).choose r)
          (n.choose r - (n - k + 1).choose r) := by
  classical
  intro n r k hr hk hboundary H hU hM
  have hsized : (H : Set (Finset (Fin n))).Sized r := fun _ he => hU _ he
  have hcard : H.card ≤ n.choose r := by simpa using hsized.card_le
  by_cases hsmall : n < r * k
  · exact hcard.trans ((Nat.choose_le_choose r (by omega)).trans (le_max_left _ _))
  have hk2 : k ≤ 2 := hboundary.resolve_right hsmall
  have hcases : k = 1 ∨ k = 2 := by omega
  rcases hcases with rfl | rfl
  · have hHempty : H = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      apply hM
      refine ⟨{e}, Finset.singleton_subset_iff.mpr he, by simp, ?_⟩
      simp
    rw [hHempty, Finset.card_empty]
    exact Nat.zero_le _
  · have hinter : (H : Set (Finset (Fin n))).Intersecting := by
      intro e he f hf hdisj
      have hne : e ≠ f := by
        intro hef
        subst f
        have heempty : e = ∅ := (Finset.disjoint_self_iff_empty e).mp hdisj
        have hecard := hU e he
        rw [heempty, Finset.card_empty] at hecard
        omega
      apply hM
      refine ⟨{e, f}, Finset.insert_subset he (Finset.singleton_subset_iff.mpr hf), Finset.card_pair hne, ?_⟩
      intro a ha b hb hab
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact False.elim (hab rfl)
      · exact hdisj
      · exact hdisj.symm
      · exact False.elim (hab rfl)
    have hekr := Finset.erdos_ko_rado hinter hsized (show r ≤ n / 2 by omega)
    have hidx : n - 2 + 1 = n - 1 := by omega
    have hpascal := Nat.choose_eq_choose_pred_add
      (show 0 < n by omega) (show 0 < r by omega)
    have hright : n.choose r - (n - 2 + 1).choose r = (n - 1).choose (r - 1) := by
      rw [hidx, hpascal, Nat.add_sub_cancel]
    rw [← hright] at hekr
    exact hekr.trans (le_max_right _ _)

/-- After the proved boundary cases, exactly the interior parameters remain. -/
theorem reduction :
    (∀ (n r k : ℕ), 3 ≤ r → 1 ≤ k →
      ∀ H : Finset (Finset (Fin n)), Uniform H r → MatchingFree H k →
        H.card ≤ max ((r * k - 1).choose r)
          (n.choose r - (n - k + 1).choose r)) ↔
    (∀ (n r k : ℕ), 3 ≤ r → 3 ≤ k → r * k ≤ n →
      ∀ H : Finset (Finset (Fin n)), Uniform H r → MatchingFree H k →
        H.card ≤ max ((r * k - 1).choose r)
          (n.choose r - (n - k + 1).choose r)) := by
  constructor
  · intro h n r k hr hk _ H hU hM
    exact h n r k hr (by omega) H hU hM
  · intro h n r k hr hk H hU hM
    by_cases hb : k ≤ 2 ∨ n < r * k
    · exact proof n r k hr hk hb H hU hM
    · exact h n r k hr (by omega) (by omega) H hU hM

end Submissions.Erdos1020MatchingBoundary.Main
