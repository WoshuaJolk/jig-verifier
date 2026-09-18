import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

-- Publication packaging: original lattice source retained line-for-line below.
namespace Submissions.J5P2ConvexLatticeOccupancy.Proof

/-!
Authored for Jig #2 from the parity-anchor argument in unit-ball-3d-notes.md.
The finite-fiber helper is reused verbatim from the checked GridUpperBound.lean
(SHA-256 c7d84ac58d616fa9972919beb008bd86df2bd4f642518dd354623eb9c802ba28).
New Mathlib source inspected at db584cd6d46c92f209a44c0f1c829460d327499d:
Convex.midpoint_mem and midpoint_eq_smul_add; all other mathematical APIs reuse
the recorded grid-proof audit. No Statements imports or admitted premises.
-/

namespace PlyLatticeConvex

noncomputable section

open Set Metric
open scoped BigOperators

abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Lattice (d : ℕ) := Fin d → ℤ
abbrev Parity (d : ℕ) := Fin d → Fin 2

def embed {d : ℕ} (z : Lattice d) : E d :=
  WithLp.toLp 2 (fun j => (z j : ℝ))

def parity {d : ℕ} (z : Lattice d) : Parity d :=
  fun j => ⟨(z j % 2).toNat, by omega⟩

def half {d : ℕ} (a b : Lattice d) : Lattice d :=
  fun j => (a j + b j) / 2

lemma twice_half {d : ℕ} {a b : Lattice d} (h : parity a = parity b) (j : Fin d) :
    2 * half a b j = a j + b j := by
  have he := congrArg (fun e : Parity d => (e j).val) h
  dsimp [parity, half] at *
  omega

lemma half_injective {d : ℕ} {a b c : Lattice d}
    (hba : parity b = parity a) (hca : parity c = parity a)
    (h : half b a = half c a) : b = c := by
  funext j
  have hb := twice_half hba j
  have hc := twice_half hca j
  have hh := congrFun h j
  omega

lemma embed_half {d : ℕ} {a b : Lattice d} (h : parity a = parity b) :
    embed (half a b) = (1 / 2 : ℝ) • (embed a + embed b) := by
  apply PiLp.ext
  intro j
  have hr : (2 : ℝ) * (half a b j : ℝ) = (a j : ℝ) + (b j : ℝ) := by
    exact_mod_cast twice_half h j
  simp only [embed, PiLp.smul_apply, PiLp.add_apply, PiLp.toLp_apply, smul_eq_mul]
  linarith

lemma half_mem {d : ℕ} {a b : Lattice d} (h : parity a = parity b)
    (x : E d) (r : ℝ) (ha : embed a ∈ closedBall x (2 * r)) :
    (1 / 2 : ℝ) • (x + embed b) ∈ closedBall (embed (half a b)) r := by
  have hid : (1 / 2 : ℝ) • (x + embed b) - embed (half a b) =
      (1 / 2 : ℝ) • (x - embed a) := by
    rw [embed_half h, ← smul_sub]
    congr 1
    abel
  rw [mem_closedBall, dist_eq_norm, hid, norm_smul]
  rw [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have hd : dist x (embed a) ≤ 2 * r := by
    rw [dist_comm]
    exact ha
  rw [dist_eq_norm] at hd
  linarith

lemma ncard_le_card_mul {α β : Type*} [Fintype α] [Fintype β]
    (P : α → Prop) (f : α → β) (k : ℕ)
    (h : ∀ b, {a | P a ∧ f a = b}.ncard ≤ k) :
    {a | P a}.ncard ≤ Fintype.card β * k := by
  classical
  let S := Finset.univ.filter P
  have hS : (S : Set α) = {a | P a} := by ext a; simp [S]
  calc
    {a | P a}.ncard = S.card := by rw [← hS, Set.ncard_coe_finset]
    _ = ∑ b : β, (S.filter (fun a => f a = b)).card :=
      Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
    _ ≤ ∑ _b : β, k := by
      apply Finset.sum_le_sum
      intro b _
      have hSb : ((S.filter (fun a => f a = b)) : Set α) =
          {a | P a ∧ f a = b} := by ext a; simp [S]
      simpa only [← Set.ncard_coe_finset, hSb] using h b
    _ = Fintype.card β * k := by simp

lemma subtype_count {α : Type*} (S : Set α) (P : α → Prop) :
    {a : S | P a}.ncard = {a | a ∈ S ∧ P a}.ncard := by
  simpa only [Set.inter_def, Set.mem_ofPred_eq, and_comm] using
    Set.ncard_subtype (fun a => a ∈ S) {a | P a}

/-- Parity-midpoint closure bounds radius-doubling occupancy at every query
center, including query centers outside the lattice or outside the finite set. -/
theorem parity_closed_bound {d : ℕ} (S : Set (Lattice d)) (hS : S.Finite)
    (hmid : ∀ a ∈ S, ∀ b ∈ S, parity a = parity b → half a b ∈ S)
    (r : ℝ) (k : ℕ)
    (hthin : ∀ p : E d,
      {z : Lattice d | z ∈ S ∧ p ∈ closedBall (embed z) r}.ncard ≤ k)
    (x : E d) :
    {z : Lattice d | z ∈ S ∧ embed z ∈ closedBall x (2 * r)}.ncard ≤ 2 ^ d * k := by
  classical
  let : Fintype S := hS.fintype
  let P : S → Prop := fun b => embed b ∈ closedBall x (2 * r)
  have hclass (e : Parity d) : {b : S | P b ∧ parity b = e}.ncard ≤ k := by
    by_cases he : ∃ a : S, parity a = e
    · obtain ⟨a, ha⟩ := he
      let q : E d := (1 / 2 : ℝ) • (x + embed a)
      calc
        _ ≤ {z : Lattice d | z ∈ S ∧ q ∈ closedBall (embed z) r}.ncard := by
          apply Set.ncard_le_ncard_of_injOn (fun b : S => half b a)
            (ht := hS.subset (fun _ hz => hz.1))
          · intro b hb
            have hba : parity (b : Lattice d) = parity (a : Lattice d) :=
              hb.2.trans ha.symm
            exact ⟨hmid b b.property a a.property hba, half_mem hba x r hb.1⟩
          · intro b hb c hc hbc
            apply Subtype.ext
            exact half_injective (a := (a : Lattice d))
              (b := (b : Lattice d)) (c := (c : Lattice d))
              (hb.2.trans ha.symm) (hc.2.trans ha.symm) hbc
        _ ≤ k := hthin q
    · have hempty : {b : S | P b ∧ parity b = e} = ∅ := by
        ext b
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro _ hb
        exact he ⟨b, hb⟩
      rw [hempty]
      simp
  have hb := ncard_le_card_mul P (fun b : S => parity (b : Lattice d)) k hclass
  have hcount : {b : S | P b}.ncard =
      {z : Lattice d | z ∈ S ∧ embed z ∈ closedBall x (2 * r)}.ncard :=
    subtype_count S (fun z => embed z ∈ closedBall x (2 * r))
  rw [hcount] at hb
  simpa [Parity, Fintype.card_fun] using hb

/-- Every finite set of all integer lattice points in an arbitrary convex
Euclidean set satisfies radius-doubling occupancy with coefficient `2^d`.
No bounded dimension, box-shape hypothesis, or lattice query center is assumed. -/
theorem convex_lattice_bound {d : ℕ} (C : Set (E d)) (hC : Convex ℝ C)
    (hfinite : {z : Lattice d | embed z ∈ C}.Finite) (r : ℝ) (k : ℕ)
    (hthin : ∀ p : E d,
      {z : Lattice d | embed z ∈ C ∧ p ∈ closedBall (embed z) r}.ncard ≤ k)
    (x : E d) :
    {z : Lattice d | embed z ∈ C ∧ embed z ∈ closedBall x (2 * r)}.ncard ≤ 2 ^ d * k := by
  apply parity_closed_bound {z : Lattice d | embed z ∈ C} hfinite ?_ r k hthin x
  intro a ha b hb hp
  change embed (half a b) ∈ C
  rw [embed_half hp]
  simpa only [midpoint_eq_smul_add, invOf_eq_inv, one_div] using hC.midpoint_mem ha hb

end

end PlyLatticeConvex

#print axioms PlyLatticeConvex.convex_lattice_bound

/- Direct alias of the preserved convex-lattice theorem; no new proof argument. -/
open Set Metric
open PlyLatticeConvex

theorem proof :
  ∀ {d : ℕ} (C : Set (E d)) (hC : Convex ℝ C)
      (hfinite : {z : Lattice d | embed z ∈ C}.Finite) (r : ℝ) (k : ℕ)
      (hthin : ∀ p : E d,
        {z : Lattice d | embed z ∈ C ∧ p ∈ closedBall (embed z) r}.ncard ≤ k)
      (x : E d),
      {z : Lattice d | embed z ∈ C ∧ embed z ∈ closedBall x (2 * r)}.ncard ≤ 2 ^ d * k
  := @PlyLatticeConvex.convex_lattice_bound

end Submissions.J5P2ConvexLatticeOccupancy.Proof
