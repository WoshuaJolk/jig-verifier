import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.ENNReal
import Mathlib.Order.Lattice.Nat
import Mathlib.Topology.Instances.ENat
import Mathlib.Tactic

open Filter

namespace Submissions.Erdos454SupportSlackReduction.AllOffsets

noncomputable local instance : ConditionallyCompleteLattice ℕ∞ :=
  WithTop.conditionallyCompleteLattice

noncomputable def f (n : ℕ) : ℕ :=
  if n ≤ 1 then 0 else
    ⨅ i : {i : Fin n // 0 < (i : ℕ)},
      (n + i).nth Nat.Prime + (n - i).nth Nat.Prime

lemma excess_ge_of_all_symmetric (n B : ℕ) (hn : 1 < n)
    (h : ∀ i : {i : Fin n // 0 < (i : ℕ)},
      2 * n.nth Nat.Prime + B ≤
        (n + i).nth Nat.Prime + (n - i).nth Nat.Prime) :
    B ≤ f n - 2 * n.nth Nat.Prime := by
  have hnonempty : Nonempty {i : Fin n // 0 < (i : ℕ)} :=
    ⟨⟨⟨1, hn⟩, by norm_num⟩⟩
  have hmin :
      2 * n.nth Nat.Prime + B ≤ f n := by
    rw [f, if_neg (by omega)]
    letI := hnonempty
    exact le_ciInf h
  omega

theorem proof :
    (∀ B : ℕ, ∃ᶠ n in atTop,
      1 < n ∧
        ∀ i : {i : Fin n // 0 < (i : ℕ)},
          2 * n.nth Nat.Prime + B ≤
            (n + i).nth Nat.Prime + (n - i).nth Nat.Prime) →
    limsup
      (fun n ↦ (f n - 2 * n.nth Nat.Prime : ℕ∞))
      atTop = ⊤ := by
  intro h
  apply top_unique
  rw [← ENat.forall_natCast_le_iff_le]
  intro B _
  apply le_limsup_of_frequently_le
  · exact (h B).mono fun n hn ↦ by
      exact ENat.natCast_le_natCast.mpr
        (excess_ge_of_all_symmetric n B hn.1 hn.2)
  · exact isBoundedUnder_of
      ⟨(⊤ : ℕ∞), fun n ↦ show
        (f n - 2 * n.nth Nat.Prime : ℕ∞) ≤ ⊤ from le_top⟩

end Submissions.Erdos454SupportSlackReduction.AllOffsets
