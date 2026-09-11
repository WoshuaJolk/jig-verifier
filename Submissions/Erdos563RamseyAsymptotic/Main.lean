import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecificLimits.Basic


open Filter

namespace Submissions.Erdos563RamseyAsymptotic.Main.Finite

noncomputable def redEdgeCount {N : ℕ} (red : Fin N → Fin N → Prop)
    (X : Finset (Fin N)) : ℕ := by
  classical
  exact ((X ×ˢ X).filter fun e => e.1 < e.2 ∧ red e.1 e.2).card

noncomputable def blueEdgeCount {N : ℕ} (red : Fin N → Fin N → Prop)
    (X : Finset (Fin N)) : ℕ := by
  classical
  exact ((X ×ˢ X).filter fun e => e.1 < e.2 ∧ ¬red e.1 e.2).card

def IsBalancedAbove (N : ℕ) (α : ℝ) (m : ℕ) : Prop :=
  ∃ red : Fin N → Fin N → Prop, Symmetric red ∧
    ∀ X : Finset (Fin N), m ≤ X.card →
      α * X.card.choose 2 < redEdgeCount red X ∧
      α * X.card.choose 2 < blueEdgeCount red X

noncomputable def threshold (N : ℕ) (α : ℝ) : ℕ :=
  sInf {m : ℕ | IsBalancedAbove N α m}

def Monochromatic {N : ℕ} (red : Fin N → Fin N → Prop)
    (X : Finset (Fin N)) : Prop :=
  (∀ a ∈ X, ∀ b ∈ X, a < b → red a b) ∨
  (∀ a ∈ X, ∀ b ∈ X, a < b → ¬red a b)

def RamseyArrow (N m : ℕ) : Prop :=
  ∀ red : Fin N → Fin N → Prop, Symmetric red →
    ∃ X : Finset (Fin N), X.card = m ∧ Monochromatic red X

theorem threshold_set_nonempty (N : ℕ) (α : ℝ) :
    Set.Nonempty {m : ℕ | IsBalancedAbove N α m} := by
  refine ⟨N + 1, (fun _ _ => False), ?_, ?_⟩
  · intro a b h; exact h
  · intro X hX
    have hcard : X.card ≤ N := by simpa using Finset.card_le_univ X
    omega

theorem balanced_mono {N m n : ℕ} {α : ℝ} (hmn : m ≤ n)
    (h : IsBalancedAbove N α m) : IsBalancedAbove N α n := by
  obtain ⟨red, hs, h⟩ := h
  exact ⟨red, hs, fun X hX => h X (hmn.trans hX)⟩

theorem threshold_le_iff (N m : ℕ) (α : ℝ) :
    threshold N α ≤ m ↔ IsBalancedAbove N α m := by
  constructor
  · intro h
    exact balanced_mono h (csInf_mem (threshold_set_nonempty N α))
  · intro h
    exact csInf_le' h

theorem red_pos_iff {N : ℕ} (red : Fin N → Fin N → Prop) (X : Finset (Fin N)) :
    0 < redEdgeCount red X ↔ ∃ a ∈ X, ∃ b ∈ X, a < b ∧ red a b := by
  classical
  simp only [redEdgeCount, Finset.card_pos, Finset.filter_nonempty_iff,
    Finset.mem_product, Prod.exists]
  aesop

theorem blue_pos_iff {N : ℕ} (red : Fin N → Fin N → Prop) (X : Finset (Fin N)) :
    0 < blueEdgeCount red X ↔ ∃ a ∈ X, ∃ b ∈ X, a < b ∧ ¬red a b := by
  classical
  simp only [blueEdgeCount, Finset.card_pos, Finset.filter_nonempty_iff,
    Finset.mem_product, Prod.exists]
  aesop

theorem colors_pos_iff {N : ℕ} (red : Fin N → Fin N → Prop) (X : Finset (Fin N)) :
    (0 < redEdgeCount red X ∧ 0 < blueEdgeCount red X) ↔ ¬ Monochromatic red X := by
  classical
  rw [red_pos_iff, blue_pos_iff]
  simp only [Monochromatic]
  aesop

theorem colors_pos_mono {N : ℕ} (red : Fin N → Fin N → Prop)
    {X Y : Finset (Fin N)} (hXY : X ⊆ Y)
    (h : 0 < redEdgeCount red X ∧ 0 < blueEdgeCount red X) :
    0 < redEdgeCount red Y ∧ 0 < blueEdgeCount red Y := by
  rw [red_pos_iff, blue_pos_iff] at h ⊢
  obtain ⟨⟨a, ha, b, hb, hab⟩, ⟨c, hc, d, hd, hcd⟩⟩ := h
  exact ⟨⟨a, hXY ha, b, hXY hb, hab⟩, ⟨c, hXY hc, d, hXY hd, hcd⟩⟩

theorem balanced_zero_iff (N m : ℕ) :
    IsBalancedAbove N 0 m ↔ ¬ RamseyArrow N m := by
  classical
  constructor
  · rintro ⟨red, hs, h⟩ ha
    obtain ⟨X, hX, hm⟩ := ha red hs
    have hp : 0 < redEdgeCount red X ∧ 0 < blueEdgeCount red X := by
      simpa using h X (le_of_eq hX.symm)
    exact (colors_pos_iff red X).mp hp hm
  · intro hn
    simp only [RamseyArrow, not_forall, not_exists,
      not_and] at hn
    obtain ⟨red, hs, h⟩ := hn
    refine ⟨red, hs, ?_⟩
    intro X hX
    obtain ⟨Y, hYX, hY⟩ := Finset.exists_subset_card_eq hX
    have hp := (colors_pos_iff red Y).mpr (h Y hY)
    have hpos := colors_pos_mono red hYX hp
    simpa using hpos

theorem proof : ∀ N m : ℕ, threshold N 0 ≤ m ↔ ¬ RamseyArrow N m := by
  intro N m
  rw [threshold_le_iff, balanced_zero_iff]

end Submissions.Erdos563RamseyAsymptotic.Main.Finite


open Filter
open scoped Topology
namespace Submissions.Erdos563RamseyAsymptotic.Main.Inverse

/-- The exact discrete inverse relation, with all endpoint conventions stated. -/
def InverseRelation (F R : ℕ → ℕ) : Prop :=
  ∀ N m, F N ≤ m ↔ N < R m

theorem inverse_at_boundary {F R : ℕ → ℕ} (hR : StrictMono R)
    (h : InverseRelation F R) (m : ℕ) : F (R m) = m + 1 := by
  apply Nat.le_antisymm
  · exact (h (R m) (m + 1)).mpr (hR (Nat.lt_succ_self m))
  · apply Nat.succ_le_of_lt
    by_contra hn
    have hle : F (R m) ≤ m := by omega
    exact (lt_irrefl (R m)) ((h (R m) m).mp hle)

theorem rate_of_inverse_limit {F R : ℕ → ℕ} (hR : StrictMono R)
    (h : InverseRelation F R) {c : ℝ} (hc : c ≠ 0)
    (hlim : Tendsto (fun N : ℕ => (F N : ℝ) / Real.log N) atTop (𝓝 c)) :
    Tendsto (fun m : ℕ => Real.log (R m) / m) atTop (𝓝 c⁻¹) := by
  have hcomp := hlim.comp hR.tendsto_atTop
  have hmul := hcomp.mul (tendsto_natCast_div_add_atTop (1 : ℝ))
  have hn : Tendsto (fun m : ℕ => (m : ℝ) / Real.log (R m)) atTop (𝓝 c) := by
    convert hmul using 1
    · funext m
      simp only [Function.comp_apply, inverse_at_boundary hR h, Nat.cast_add, Nat.cast_one]
      have hm : (m : ℝ) + 1 ≠ 0 := by positivity
      field_simp
    · simp
  simpa only [inv_div] using hn.inv₀ hc

theorem inverse_tendsto {F R : ℕ → ℕ} (h : InverseRelation F R) :
    Tendsto F atTop atTop := by
  refine tendsto_atTop.2 fun m => ?_
  filter_upwards [eventually_ge_atTop (R m)] with N hN
  by_contra hn
  have hle : F N ≤ m := by omega
  exact (not_lt_of_ge hN) ((h N m).mp hle)

theorem predecessor_ratio :
    Tendsto (fun n : ℕ => ((n - 1 : ℕ) : ℝ) / n) atTop (𝓝 1) := by
  have h := (tendsto_natCast_div_add_atTop (1 : ℝ)).comp (tendsto_sub_atTop_nat 1)
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  simp only [Function.comp_apply]
  have he : ((n - 1 : ℕ) : ℝ) + 1 = n := by exact_mod_cast Nat.sub_add_cancel hn
  rw [he]

theorem inverse_limit_of_rate {F R : ℕ → ℕ} (hR : StrictMono R)
    (h : InverseRelation F R) {L : ℝ} (hL : L ≠ 0)
    (hrate : Tendsto (fun m : ℕ => Real.log (R m) / m) atTop (𝓝 L)) :
    Tendsto (fun N : ℕ => (F N : ℝ) / Real.log N) atTop (𝓝 L⁻¹) := by
  have hF := inverse_tendsto h
  have hK := (tendsto_sub_atTop_nat 1).comp hF
  have hupper := hrate.comp hF
  have hlower0 := (hrate.comp hK).mul (predecessor_ratio.comp hF)
  have hlower : Tendsto (fun N : ℕ => Real.log (R (F N - 1)) / F N)
      atTop (𝓝 L) := by
    apply (show Tendsto _ _ (𝓝 L) from by simpa using hlower0).congr'
    filter_upwards [hF.eventually (eventually_ge_atTop 2)] with N hN
    have hk : (((F N - 1 : ℕ)) : ℝ) ≠ 0 := by exact_mod_cast (show F N - 1 ≠ 0 by omega)
    field_simp
  have hmid : Tendsto (fun N : ℕ => Real.log N / F N) atTop (𝓝 L) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
    · filter_upwards [hF.eventually (eventually_ge_atTop 2)] with N hN
      have hp : 0 < F N - 1 := by omega
      have hRpos : 0 < R (F N - 1) := lt_of_lt_of_le hp (hR.id_le _)
      have hprev : R (F N - 1) ≤ N := by
        by_contra hn
        have hlt : N < R (F N - 1) := by omega
        have hb := (h N (F N - 1)).mpr hlt
        omega
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact Real.log_le_log (by exact_mod_cast hRpos) (by exact_mod_cast hprev)
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hnlt : N < R (F N) := (h N (F N)).mp le_rfl
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact Real.log_le_log (by exact_mod_cast (show 0 < N by omega))
        (by exact_mod_cast (le_of_lt hnlt))
  simpa only [inv_div] using hmid.inv₀ hL

theorem proof {F R : ℕ → ℕ} (hR : StrictMono R)
    (h : InverseRelation F R) {c : ℝ} (hc : c ≠ 0) :
    Tendsto (fun N : ℕ => (F N : ℝ) / Real.log N) atTop (𝓝 c) ↔
      Tendsto (fun m : ℕ => Real.log (R m) / m) atTop (𝓝 c⁻¹) := by
  constructor
  · exact rate_of_inverse_limit hR h hc
  · intro hr
    simpa using inverse_limit_of_rate hR h (inv_ne_zero hc) hr

end Submissions.Erdos563RamseyAsymptotic.Main.Inverse


/-!
Elementary finite Ramsey existence, following the classical Ramsey / Erdős–Szekeres
neighborhood induction. The independently written relation/finset proof uses the
same mathematical recurrence as the audited RamseyLean foundation at commit
90e87da214701dd6eb3d56a2c7121839d8269d14. This is a port of known mathematics,
not a solution of the diagonal Ramsey growth-limit problem.

-/

namespace Submissions.Erdos563RamseyAsymptotic.Main.Existence

universe u

def HasCliqueOn {V : Type u} (r : V → V → Prop) (X : Finset V) (k : ℕ) : Prop :=
  ∃ S : Finset V, S ⊆ X ∧ S.card = k ∧
    ∀ a ∈ S, ∀ b ∈ S, a ≠ b → r a b

private theorem hasClique_zero {V : Type u} (r : V → V → Prop) (X : Finset V) :
    HasCliqueOn r X 0 := by
  refine ⟨∅, Finset.empty_subset X, by simp, ?_⟩
  simp

private theorem hasClique_mono {V : Type u} {r : V → V → Prop}
    {X Y : Finset V} {k : ℕ} (hXY : X ⊆ Y) (h : HasCliqueOn r X k) :
    HasCliqueOn r Y k := by
  obtain ⟨S, hSX, hcard, hpair⟩ := h
  exact ⟨S, hSX.trans hXY, hcard, hpair⟩

private theorem hasClique_insert {V : Type u} [DecidableEq V] {r : V → V → Prop}
    (hs : Symmetric r) {X : Finset V} {k : ℕ} {v : V}
    (hv : v ∉ X) (h : HasCliqueOn r X k) (hadj : ∀ w ∈ X, r v w) :
    HasCliqueOn r (insert v X) (k + 1) := by
  classical
  obtain ⟨S, hSX, hcard, hpair⟩ := h
  have hvS : v ∉ S := fun h => hv (hSX h)
  refine ⟨insert v S, Finset.insert_subset_insert v hSX, ?_, ?_⟩
  · simp [Finset.card_insert_of_notMem hvS, hcard]
  · intro a ha b hb hab
    rcases Finset.mem_insert.mp ha with rfl | haS
    · rcases Finset.mem_insert.mp hb with rfl | hbS
      · exact False.elim (hab rfl)
      · exact hadj b (hSX hbS)
    · rcases Finset.mem_insert.mp hb with rfl | hbS
      · exact hs (hadj a (hSX haS))
      · exact hpair a haS b hbS hab

/-- A graph-independent finite bound for arbitrary symmetric relations.
The recursive witness uses `N + M + 1`, so no positivity boundary cases are needed. -/
theorem exists_bound (k ℓ : ℕ) :
    ∃ n : ℕ, ∀ (V : Type u) (red : V → V → Prop), Symmetric red →
      ∀ X : Finset V, n ≤ X.card →
        HasCliqueOn red X k ∨ HasCliqueOn (fun a b => ¬ red a b) X ℓ := by
  classical
  induction k generalizing ℓ with
  | zero =>
      refine ⟨0, ?_⟩
      intro V red hs X hX
      exact Or.inl (hasClique_zero red X)
  | succ k ih =>
      induction ℓ with
      | zero =>
          refine ⟨0, ?_⟩
          intro V red hs X hX
          exact Or.inr (hasClique_zero (fun a b => ¬ red a b) X)
      | succ ℓ ihℓ =>
          obtain ⟨N, hN⟩ := ih (ℓ + 1)
          obtain ⟨M, hM⟩ := ihℓ
          refine ⟨N + M + 1, ?_⟩
          intro V red hs X hX
          have hpos : 0 < X.card := by omega
          obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
          let A := (X.erase v).filter (red v)
          let B := (X.erase v).filter (fun w => ¬ red v w)
          have hAX : A ⊆ X := by
            intro w hw
            exact (Finset.mem_erase.mp (Finset.mem_filter.mp hw).1).2
          have hBX : B ⊆ X := by
            intro w hw
            exact (Finset.mem_erase.mp (Finset.mem_filter.mp hw).1).2
          have hvA : v ∉ A := by simp [A]
          have hvB : v ∉ B := by simp [B]
          have hAi : insert v A ⊆ X := Finset.insert_subset_iff.mpr ⟨hv, hAX⟩
          have hBi : insert v B ⊆ X := Finset.insert_subset_iff.mpr ⟨hv, hBX⟩
          have hsum : A.card + B.card = X.card - 1 := by
            simpa [A, B, Finset.card_erase_of_mem hv] using
              (Finset.card_filter_add_card_filter_not (s := X.erase v) (red v))
          by_cases hA : N ≤ A.card
          · rcases hN V red hs A hA with hred | hblue
            · left
              apply hasClique_mono hAi
              apply hasClique_insert hs hvA hred
              intro w hw
              exact (Finset.mem_filter.mp hw).2
            · exact Or.inr (hasClique_mono hAX hblue)
          · have hB : M ≤ B.card := by omega
            rcases hM V red hs B hB with hred | hblue
            · exact Or.inl (hasClique_mono hBX hred)
            · right
              apply hasClique_mono hBi
              have hsym : Symmetric (fun a b => ¬ red a b) := by
                intro a b hab hba
                exact hab (hs hba)
              apply hasClique_insert hsym hvB hblue
              intro w hw
              exact (Finset.mem_filter.mp hw).2

/-- Finite Ramsey existence for the exact relation-based predicate already used by #202. -/
theorem exists_ramseyArrow (m : ℕ) :
    ∃ N, Submissions.Erdos563RamseyAsymptotic.Main.Finite.RamseyArrow N m := by
  obtain ⟨N, hN⟩ := exists_bound.{0} m m
  refine ⟨N, ?_⟩
  intro red hs
  have hcard : N ≤ (Finset.univ : Finset (Fin N)).card := by simp
  rcases hN (Fin N) red hs Finset.univ hcard with hred | hblue
  · obtain ⟨S, hS, hcard, hpair⟩ := hred
    refine ⟨S, hcard, Or.inl ?_⟩
    intro a ha b hb hab
    exact hpair a ha b hb (ne_of_lt hab)
  · obtain ⟨S, hS, hcard, hpair⟩ := hblue
    refine ⟨S, hcard, Or.inr ?_⟩
    intro a ha b hb hab
    exact hpair a ha b hb (ne_of_lt hab)

end Submissions.Erdos563RamseyAsymptotic.Main.Existence


open Filter
open scoped Topology
open Submissions.Erdos563RamseyAsymptotic.Main.Finite

namespace Submissions.Erdos563RamseyAsymptotic.Main

theorem arrow_mono {N M m : ℕ} (hNM : N ≤ M) (h : RamseyArrow N m) :
    RamseyArrow M m := by
  classical
  intro red hs
  let e : Fin N ↪ Fin M := Fin.castLEEmb hNM
  obtain ⟨X, hX, hm⟩ := h (fun a b => red (e a) (e b)) (fun _ _ h => hs h)
  refine ⟨X.map e, by simpa using hX, ?_⟩
  rcases hm with hr | hb
  · left
    intro a ha b hb hab
    obtain ⟨a0, ha0, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨b0, hb0, rfl⟩ := Finset.mem_map.mp hb
    exact hr a0 ha0 b0 hb0 hab
  · right
    intro a ha b hb' hab
    obtain ⟨a0, ha0, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨b0, hb0, rfl⟩ := Finset.mem_map.mp hb'
    exact hb a0 ha0 b0 hb0 hab

theorem arrow_size_le {N m : ℕ} (h : RamseyArrow N m) : m ≤ N := by
  obtain ⟨X, hX, _⟩ := h (fun _ _ => False) (fun _ _ h => h)
  have hc : X.card ≤ N := by simpa using Finset.card_le_univ X
  omega

theorem arrow_zero (N : ℕ) : RamseyArrow N 0 := by
  intro red hs
  refine ⟨∅, rfl, Or.inl ?_⟩
  simp

/-- Removing the added vertex loses at most one member of a homogeneous set. -/
theorem arrow_remove_vertex {N m : ℕ} (h : RamseyArrow (N + 1) (m + 1)) :
    RamseyArrow N m := by
  classical
  by_cases hN : N = 0
  · subst N
    have hm := arrow_size_le h
    have : m = 0 := by omega
    subst m
    exact arrow_zero 0
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  intro red hs
  let p : Fin (N + 1) → Fin N := fun a => ⟨a.val % N, Nat.mod_lt _ hNpos⟩
  have hp (a : Fin N) : p a.castSucc = a := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt a.isLt
  obtain ⟨X, hX, hmono⟩ := h (fun a b => red (p a) (p b)) (fun _ _ h => hs h)
  let e : Fin N ↪ Fin (N + 1) := Fin.castLEEmb (Nat.le_succ N)
  let Y : Finset (Fin N) := Finset.univ.filter fun a => a.castSucc ∈ X
  have hcover : X ⊆ insert (Fin.last N) (Y.map e) := by
    intro a ha
    by_cases heq : a = Fin.last N
    · simpa [heq]
    · have haN : a.val < N := by
        have hne : a.val ≠ N := by
          intro hv
          apply heq
          exact Fin.ext hv
        have := a.isLt
        omega
      let b : Fin N := ⟨a.val, haN⟩
      have hba : b.castSucc = a := Fin.ext rfl
      apply Finset.mem_insert_of_mem
      apply Finset.mem_map.mpr
      refine ⟨b, ?_, ?_⟩
      · simp [Y, hba, ha]
      · exact Fin.ext rfl
  have hcard : m ≤ Y.card := by
    have hc := Finset.card_le_card hcover
    have hi := Finset.card_insert_le (Fin.last N) (Y.map e)
    have he : (Y.map e).card = Y.card := Finset.card_map e
    omega
  obtain ⟨Z, hZY, hZ⟩ := Finset.exists_subset_card_eq hcard
  refine ⟨Z, hZ, ?_⟩
  have hmem {a : Fin N} (ha : a ∈ Z) : a.castSucc ∈ X := by
    have := hZY ha
    simpa [Y] using this
  rcases hmono with hr | hb
  · left
    intro a ha b hb hab
    simpa only [hp] using hr a.castSucc (hmem ha) b.castSucc (hmem hb) hab
  · right
    intro a ha b hb' hab
    simpa only [hp] using hb a.castSucc (hmem ha) b.castSucc (hmem hb') hab

noncomputable def diagonalRamsey (m : ℕ) : ℕ := sInf {N : ℕ | RamseyArrow N m}

theorem ramsey_spec (hf : ∀ m, ∃ N, RamseyArrow N m) (m : ℕ) :
    RamseyArrow (diagonalRamsey m) m := csInf_mem (hf m)

theorem ramsey_le_iff (hf : ∀ m, ∃ N, RamseyArrow N m) (N m : ℕ) :
    diagonalRamsey m ≤ N ↔ RamseyArrow N m := by
  constructor
  · intro h
    exact arrow_mono h (ramsey_spec hf m)
  · intro h
    exact csInf_le' h

theorem ramsey_zero : diagonalRamsey 0 = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact csInf_le' (arrow_zero 0)

theorem ramsey_strictMono (hf : ∀ m, ∃ N, RamseyArrow N m) :
    StrictMono diagonalRamsey := by
  apply strictMono_nat_of_lt_succ
  intro m
  by_cases hm : m = 0
  · subst m
    rw [ramsey_zero]
    exact lt_of_lt_of_le Nat.zero_lt_one (arrow_size_le (ramsey_spec hf 1))
  have hRpos : 0 < diagonalRamsey m := by
    have := arrow_size_le (ramsey_spec hf m)
    omega
  by_contra hn
  have hle : diagonalRamsey (m + 1) ≤ diagonalRamsey m := by omega
  have hbig := arrow_mono hle (ramsey_spec hf (m + 1))
  have hremove : RamseyArrow (diagonalRamsey m - 1) m := by
    apply arrow_remove_vertex
    simpa only [Nat.sub_add_cancel (show 1 ≤ diagonalRamsey m by omega)] using hbig
  have hmin := (ramsey_le_iff hf (diagonalRamsey m - 1) m).mpr hremove
  omega

theorem threshold_inverse (hf : ∀ m, ∃ N, RamseyArrow N m) :
    Submissions.Erdos563RamseyAsymptotic.Main.Inverse.InverseRelation (fun N => threshold N 0)
      diagonalRamsey := by
  intro N m
  rw [Submissions.Erdos563RamseyAsymptotic.Main.Finite.proof, ← ramsey_le_iff hf]
  omega

theorem conditional_equivalence (hf : ∀ m, ∃ N, RamseyArrow N m)
    {c : ℝ} (hc : c ≠ 0) :
    Tendsto (fun N : ℕ => (threshold N 0 : ℝ) / Real.log N) atTop (𝓝 c) ↔
      Tendsto (fun m : ℕ => Real.log (diagonalRamsey m) / m) atTop (𝓝 c⁻¹) :=
  Submissions.Erdos563RamseyAsymptotic.Main.Inverse.proof (ramsey_strictMono hf) (threshold_inverse hf) hc

theorem proof {c : ℝ} (hc : 0 < c) :
    Tendsto (fun N : ℕ => (threshold N 0 : ℝ) / Real.log N) atTop (𝓝 c) ↔
      Tendsto (fun m : ℕ => Real.log (diagonalRamsey m) / m) atTop (𝓝 c⁻¹) :=
  conditional_equivalence Existence.exists_ramseyArrow (ne_of_gt hc)

end Submissions.Erdos563RamseyAsymptotic.Main
