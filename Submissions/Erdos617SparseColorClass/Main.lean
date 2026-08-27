import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Data.Sym.Sym2
import Mathlib.Tactic

namespace Submissions.Erdos617SparseColorClass.Main

private lemma arith (r m h : ℕ) (hr : 3 ≤ r)
    (h1 : 2 * m + 1 ≤ r * (r ^ 2 - r + 2))
    (h2 : 2 * m + 2 * h = (r ^ 2 + 1) * r ^ 2)
    (h3 : 2 * r * h ≤ ((r ^ 2 + 1) ^ 2 - 1) * (r - 1)) : False := by
  obtain ⟨p, rfl⟩ : ∃ p, r = p + 3 := ⟨r - 3, by omega⟩
  have hq : (p + 3) ^ 2 - (p + 3) + 2 = p ^ 2 + 5 * p + 8 := by
    have h' : (p + 3) ^ 2 = p ^ 2 + 6 * p + 9 := by ring
    omega
  have hA : ((p + 3) ^ 2 + 1) ^ 2 - 1 = p ^ 4 + 12 * p ^ 3 + 56 * p ^ 2 + 120 * p + 99 := by
    have h' : ((p + 3) ^ 2 + 1) ^ 2 = p ^ 4 + 12 * p ^ 3 + 56 * p ^ 2 + 120 * p + 100 := by
      ring
    omega
  have hB : (p + 3) - 1 = p + 2 := by omega
  rw [hq] at h1
  rw [hA, hB] at h3
  have hN : ((p + 3) ^ 2 + 1) * (p + 3) ^ 2
      = p ^ 4 + 12 * p ^ 3 + 55 * p ^ 2 + 114 * p + 90 := by ring
  rw [hN] at h2
  have k1 : (p + 3) * (2 * m + 1) ≤ (p + 3) * ((p + 3) * (p ^ 2 + 5 * p + 8)) :=
    Nat.mul_le_mul_left _ h1
  have k2 : (p + 3) * (2 * m + 2 * h)
      = (p + 3) * (p ^ 4 + 12 * p ^ 3 + 55 * p ^ 2 + 114 * p + 90) := by rw [h2]
  nlinarith [k1, k2, h3]

theorem proof :
    ∀ (r : ℕ), 3 ≤ r →
      ∀ {V : Type} [Fintype V] [DecidableEq V],
        Fintype.card V = r ^ 2 + 1 →
        ∀ coloring : Sym2 V → Fin r, ∀ c : Fin r,
          2 * (Finset.univ.filter
                fun e : Sym2 V => ¬ e.IsDiag ∧ coloring e = c).card
              < r * (r ^ 2 - r + 2) →
            ∃ (S : Finset V) (k : Fin r),
              S.card = r + 1 ∧
              ∀ u ∈ S, ∀ v ∈ S, u ≠ v → coloring s(u, v) ≠ k := by
  intro r hr V _ _ hcard coloring c hsparse
  classical
  let H : SimpleGraph V :=
    ⟨fun u v => u ≠ v ∧ coloring s(u, v) ≠ c,
      ⟨fun u v h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩⟩,
      ⟨fun u h => h.1 rfl⟩⟩
  have hHadj : ∀ u v : V, H.Adj u v ↔ u ≠ v ∧ coloring s(u, v) ≠ c :=
    fun u v => Iff.rfl
  by_cases hcf : H.CliqueFree (r + 1)
  · exfalso
    have hbound := hcf.card_edgeFinset_le
    simp only [hcard] at hbound
    have hmod : (r ^ 2 + 1) % r = 1 := by
      have h' : r ^ 2 + 1 = 1 + r * r := by ring
      rw [h', Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hmod] at hbound
    have hedge : H.edgeFinset =
        Finset.univ.filter fun e : Sym2 V => ¬ e.IsDiag ∧ ¬ coloring e = c := by
      ext e
      induction e with
      | _ u v =>
        simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, hHadj,
          Finset.mem_filter, Finset.mem_univ, true_and, Sym2.mk_isDiag_iff]
    have htop : (Finset.univ.filter fun e : Sym2 V => ¬ e.IsDiag).card =
        (Fintype.card V).choose 2 := by
      rw [← SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
      congr 1
      ext e
      induction e with
      | _ u v =>
        simp [Sym2.mk_isDiag_iff]
    have hsplit :
        (Finset.univ.filter fun e : Sym2 V => ¬ e.IsDiag ∧ coloring e = c).card
        + (Finset.univ.filter fun e : Sym2 V => ¬ e.IsDiag ∧ ¬ coloring e = c).card
        = (Finset.univ.filter fun e : Sym2 V => ¬ e.IsDiag).card := by
      rw [← Finset.filter_filter, ← Finset.filter_filter]
      exact Finset.card_filter_add_card_filter_not _
    rw [htop, hcard] at hsplit
    -- turn the choose into a product
    have heven : Even ((r ^ 2 + 1) * r ^ 2) := by
      rw [mul_comm]
      exact Nat.even_mul_succ_self (r ^ 2)
    have hchoose : 2 * ((r ^ 2 + 1).choose 2) = (r ^ 2 + 1) * r ^ 2 := by
      rw [Nat.choose_two_right, Nat.add_sub_cancel]
      exact Nat.two_mul_div_two_of_even heven
    -- Turán bound, multiplied out
    have hdivle : 2 * r * H.edgeFinset.card ≤ ((r ^ 2 + 1) ^ 2 - 1) * (r - 1) := by
      have h2r : 0 < 2 * r := by omega
      calc 2 * r * H.edgeFinset.card
          ≤ 2 * r * ((((r ^ 2 + 1) ^ 2 - 1 ^ 2) * (r - 1)) / (2 * r) + Nat.choose 1 2) := by
            exact Nat.mul_le_mul_left _ hbound
        _ = 2 * r * ((((r ^ 2 + 1) ^ 2 - 1) * (r - 1)) / (2 * r)) := by
            norm_num
        _ ≤ ((r ^ 2 + 1) ^ 2 - 1) * (r - 1) := Nat.mul_div_le _ _
  -- assemble the contradiction
    rw [hedge] at hdivle
    refine arith r
      (Finset.univ.filter fun e : Sym2 V => ¬ e.IsDiag ∧ coloring e = c).card
      (Finset.univ.filter fun e : Sym2 V => ¬ e.IsDiag ∧ ¬ coloring e = c).card
      hr (by omega) (by omega) hdivle
  · rw [SimpleGraph.CliqueFree] at hcf
    obtain ⟨t, ht⟩ := not_forall.mp hcf
    have ht := not_not.mp ht
    refine ⟨t, c, ht.card_eq, ?_⟩
    intro u hu v hv huv
    exact ((hHadj u v).mp (ht.isClique hu hv huv)).2

end Submissions.Erdos617SparseColorClass.Main
