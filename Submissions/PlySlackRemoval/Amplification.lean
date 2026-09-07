import Mathlib.Data.Set.Card
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Lattice
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace Submissions.PlySlackRemoval.Amplification


variable {ι X : Type*} [PseudoMetricSpace X] [ProperSpace X]

/-- An empty intersection of finitely many closed balls remains empty after a
small uniform increase of their radii. -/
theorem inflate_empty (x : ι → X) (r : ι → ℝ) (s : Finset ι)
    (hs : s.Nonempty)
    (hempty : ¬ ∃ p : X, ∀ i ∈ s, dist p (x i) ≤ r i) :
    ∃ ε : ℝ, 0 < ε ∧
      ¬ ∃ p : X, ∀ i ∈ s, dist p (x i) ≤ r i + ε := by
  classical
  obtain ⟨i₀, hi₀⟩ := hs
  let f : X → ℝ := fun p => s.sup' ⟨i₀, hi₀⟩ (fun i => dist p (x i) - r i)
  have hf : Continuous f :=
    Continuous.finset_sup'_apply ⟨i₀, hi₀⟩ fun _ _ =>
      (continuous_id.dist continuous_const).sub continuous_const
  have hfpos (p : X) : 0 < f p := by
    apply lt_of_not_ge
    intro h
    apply hempty
    refine ⟨p, fun i hi => ?_⟩
    exact sub_nonpos.mp ((Finset.le_sup' (fun i => dist p (x i) - r i) hi).trans h)
  obtain ⟨η, hη, hbound⟩ :=
    (isCompact_closedBall (x i₀) (r i₀ + 1)).exists_forall_le'
      hf.continuousOn (fun p _ => hfpos p)
  refine ⟨min 1 (η / 2), lt_min zero_lt_one (half_pos hη), ?_⟩
  rintro ⟨p, hp⟩
  have hpK : p ∈ Metric.closedBall (x i₀) (r i₀ + 1) :=
    (hp i₀ hi₀).trans (add_le_add le_rfl (min_le_left _ _))
  have hfp : f p ≤ min 1 (η / 2) := by
    apply Finset.sup'_le
    intro i hi
    exact sub_le_iff_le_add.mpr (by simpa only [add_comm] using hp i hi)
  exact (not_lt_of_ge (hbound p hpK))
    (hfp.trans_lt ((min_le_right _ _).trans_lt (half_lt_self hη)))

/-- A finite family of closed balls in a proper pseudometric space admits a
positive uniform radius increase preserving its ply bound. -/
theorem inflate [Fintype ι] (x : ι → X) (r : ι → ℝ) (k : ℕ)
    (hthin : ∀ p : X, {i : ι | dist p (x i) ≤ r i}.ncard ≤ k) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ p : X, {i : ι | dist p (x i) ≤ r i + ε}.ncard ≤ k := by
  classical
  have heach (s : Finset ι) :
      ∃ ε : ℝ, 0 < ε ∧
        ∀ p : X, (∀ i ∈ s, dist p (x i) ≤ r i + ε) → s.card ≤ k := by
    by_cases hcard : s.card ≤ k
    · exact ⟨1, zero_lt_one, fun _ _ => hcard⟩
    have hs : s.Nonempty :=
      Finset.card_pos.mp ((Nat.zero_le k).trans_lt (lt_of_not_ge hcard))
    have hempty : ¬ ∃ p : X, ∀ i ∈ s, dist p (x i) ≤ r i := by
      rintro ⟨p, hp⟩
      apply hcard
      calc
        s.card = (s : Set ι).ncard := (Set.ncard_coe_finset s).symm
        _ ≤ {i : ι | dist p (x i) ≤ r i}.ncard :=
          Set.ncard_le_ncard (fun i hi => hp i hi)
        _ ≤ k := hthin p
    obtain ⟨ε, hε, hemptyε⟩ := inflate_empty x r s hs hempty
    exact ⟨ε, hε, fun p hp => False.elim (hemptyε ⟨p, hp⟩)⟩
  choose e hepos he using heach
  obtain ⟨ε, hεpos, hε⟩ :=
    (Set.finite_range e).isCompact.exists_forall_le' continuous_id.continuousOn
      (by rintro y ⟨s, rfl⟩; exact hepos s)
  refine ⟨ε, hεpos, fun p => ?_⟩
  let S : Set ι := {i : ι | dist p (x i) ≤ r i + ε}
  change S.ncard ≤ k
  rw [Set.ncard_eq_toFinset_card']
  apply he S.toFinset p
  intro i hi
  have hpi : i ∈ S := Set.mem_toFinset.mp hi
  exact hpi.trans (add_le_add le_rfl (hε _ ⟨S.toFinset, rfl⟩))



open Set Metric

lemma positive_floor {ι : Type*} [Finite ι] (f : ι → ℝ) (h : ∀ i, 0 < f i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, ε ≤ f i := by
  obtain ⟨ε, hε, hf⟩ := (Set.finite_range f).isCompact.exists_forall_le'
    continuous_id.continuousOn (by rintro y ⟨i, rfl⟩; exact h i)
  exact ⟨ε, hε, fun i => hf (f i) ⟨i, rfl⟩⟩

/-- Distinct concentric copies inside a common radius envelope. -/
lemma copies {X ι : Type*} [MetricSpace X] [Fintype ι]
    (x : ι → X) (r : ι → ℝ)
    (hinj : Function.Injective (fun i => (x i, r i)))
    {ε : ℝ} (hε : 0 < ε) (m : ℕ) :
    ∃ R : ι × Fin m → ℝ,
      (∀ a, r a.1 < R a ∧ R a ≤ r a.1 + ε) ∧
      Function.Injective (fun a => (x a.1, R a)) := by
  classical
  let gap : ι × ι → ℝ := fun a => if r a.1 = r a.2 then 1 else |r a.1 - r a.2|
  have hgap : ∀ a, 0 < gap a := by
    intro a
    dsimp [gap]
    split_ifs with h
    · norm_num
    · exact abs_pos.mpr (sub_ne_zero.mpr h)
  obtain ⟨δ, hδ, hδgap⟩ := positive_floor gap hgap
  let e : ℝ := min ε (δ / 2)
  have he : 0 < e := lt_min hε (by positivity)
  have heε : e ≤ ε := min_le_left _ _
  have heδ : e < δ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  let t : Fin m → ℝ := fun a => e * ((a.val : ℝ) + 1) / ((m : ℝ) + 1)
  have ht : ∀ a, 0 < t a ∧ t a < e := by
    intro a
    have ha : (a.val : ℝ) < m := by exact_mod_cast a.isLt
    dsimp [t]
    constructor
    · positivity
    · apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) + 1)).2
      nlinarith
  refine ⟨fun a => r a.1 + t a.2, ?_, ?_⟩
  · intro a
    constructor <;> linarith [ht a.2]
  · intro a b hab
    have hx : x a.1 = x b.1 := congrArg Prod.fst hab
    have hR : r a.1 + t a.2 = r b.1 + t b.2 := congrArg Prod.snd hab
    have hri : r a.1 = r b.1 := by
      by_contra h
      have hg : δ ≤ |r a.1 - r b.1| := by
        simpa [gap, h] using hδgap (a.1, b.1)
      have habs : |r a.1 - r b.1| < e := by
        apply abs_lt.mpr
        constructor <;> linarith [ht a.2, ht b.2]
      linarith
    have hi : a.1 = b.1 := hinj (Prod.ext hx hri)
    have ht_eq : t a.2 = t b.2 := by linarith
    have hv : a.2.val = b.2.val := by
      dsimp [t] at ht_eq
      have hm : (m : ℝ) + 1 ≠ 0 := by positivity
      have he0 : e ≠ 0 := ne_of_gt he
      have : (a.2.val : ℝ) + 1 = (b.2.val : ℝ) + 1 := by
        exact mul_left_cancel₀ he0 ((div_left_inj' hm).mp ht_eq)
      exact_mod_cast (add_right_cancel this)
    exact Prod.ext hi (Fin.ext hv)

lemma closed_neighbors_card {X ι : Type*} [MetricSpace X] [Finite ι]
    (x : ι → X) (r : ι → ℝ) (hr : ∀ i, 0 ≤ r i) (i : ι) :
    {j | (closedBall (x j) (r j) ∩ closedBall (x i) (r i)).Nonempty}.ncard =
      {j | j ≠ i ∧ (closedBall (x j) (r j) ∩ closedBall (x i) (r i)).Nonempty}.ncard + 1 := by
  classical
  have hset : {j | (closedBall (x j) (r j) ∩ closedBall (x i) (r i)).Nonempty} =
      insert i {j | j ≠ i ∧ (closedBall (x j) (r j) ∩ closedBall (x i) (r i)).Nonempty} := by
    ext j
    by_cases h : j = i
    · subst j
      simp [nonempty_closedBall.mpr (hr i)]
    · simp [h]
  rw [hset, Set.ncard_insert_of_notMem (by simp)]

/-- A radius envelope bounds the ply of a family of copies. -/
lemma copies_thin {X ι : Type*} [MetricSpace X] [Finite ι]
    (x : ι → X) (r : ι → ℝ) (m k : ℕ) (ε : ℝ)
    (hthin : ∀ p, {i | p ∈ closedBall (x i) (r i + ε)}.ncard ≤ k)
    (R : ι × Fin m → ℝ) (hR : ∀ a, R a ≤ r a.1 + ε) :
    ∀ p, {a | p ∈ closedBall (x a.1) (R a)}.ncard ≤ k * m := by
  intro p
  calc
    _ ≤ ({i | p ∈ closedBall (x i) (r i + ε)} ×ˢ (Set.univ : Set (Fin m))).ncard :=
      Set.ncard_le_ncard (fun a ha => ⟨le_trans ha (hR a), Set.mem_univ _⟩)
    _ = {i | p ∈ closedBall (x i) (r i + ε)}.ncard * m := by simp
    _ ≤ k * m := Nat.mul_le_mul_right m (hthin p)

/-- Each old closed neighborhood contributes all of its copies to a new one. -/
lemma copies_neighbors {X ι : Type*} [MetricSpace X] [Finite ι]
    (x : ι → X) (r : ι → ℝ) (m : ℕ)
    (R : ι × Fin m → ℝ) (hR : ∀ a, r a.1 ≤ R a) (a : ι × Fin m) :
    {i | (closedBall (x i) (r i) ∩ closedBall (x a.1) (r a.1)).Nonempty}.ncard * m ≤
      {b | (closedBall (x b.1) (R b) ∩ closedBall (x a.1) (R a)).Nonempty}.ncard := by
  have hsub :
      {i | (closedBall (x i) (r i) ∩ closedBall (x a.1) (r a.1)).Nonempty} ×ˢ
        (Set.univ : Set (Fin m)) ⊆
      {b | (closedBall (x b.1) (R b) ∩ closedBall (x a.1) (R a)).Nonempty} := by
    rintro b ⟨⟨p, hp, hpa⟩, _⟩
    exact ⟨p, le_trans hp (hR b), le_trans hpa (hR a)⟩
  simpa using Set.ncard_le_ncard hsub



open Set Metric

abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

abbrev Root : Prop :=
  ∃ C : ℕ → ℕ,
    ∀ (d k n : ℕ), 1 ≤ d → 0 < n →
      ∀ (x : Fin n → E d) (r : Fin n → ℝ),
        (∀ i, 0 < r i) → Function.Injective (fun i => (x i, r i)) →
        (∀ p, {i | p ∈ closedBall (x i) (r i)}.ncard ≤ k) →
        ∃ i₀, {i | i ≠ i₀ ∧ (closedBall (x i) (r i) ∩
          closedBall (x i₀) (r i₀)).Nonempty}.ncard ≤ 2 ^ d * k + C d

abbrev Strict : Prop :=
  ∀ (d k n : ℕ), 1 ≤ d → 0 < n →
    ∀ (x : Fin n → E d) (r : Fin n → ℝ),
      (∀ i, 0 < r i) → Function.Injective (fun i => (x i, r i)) →
      (∀ p, {i | p ∈ closedBall (x i) (r i)}.ncard ≤ k) →
      ∃ i₀, {i | i ≠ i₀ ∧ (closedBall (x i) (r i) ∩
        closedBall (x i₀) (r i₀)).Nonempty}.ncard < 2 ^ d * k

lemma count_equiv {α β : Type*} (e : α ≃ β) (P : β → Prop) :
    {a | P (e a)}.ncard = {b | P b}.ncard := by
  apply Set.ncard_preimage_of_injective_subset_range e.injective
  intro b _
  exact e.surjective b

lemma root_finite (C : ℕ → ℕ)
    (hC : ∀ (d k n : ℕ), 1 ≤ d → 0 < n →
      ∀ (x : Fin n → E d) (r : Fin n → ℝ),
        (∀ i, 0 < r i) → Function.Injective (fun i => (x i, r i)) →
        (∀ p, {i | p ∈ closedBall (x i) (r i)}.ncard ≤ k) →
        ∃ i₀, {i | i ≠ i₀ ∧ (closedBall (x i) (r i) ∩
          closedBall (x i₀) (r i₀)).Nonempty}.ncard ≤ 2 ^ d * k + C d)
    {d k : ℕ} (hd : 1 ≤ d) {ι : Type*} [Fintype ι] [Nonempty ι]
    (x : ι → E d) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (hinj : Function.Injective (fun i => (x i, r i)))
    (hthin : ∀ p, {i | p ∈ closedBall (x i) (r i)}.ncard ≤ k) :
    ∃ i₀, {i | i ≠ i₀ ∧ (closedBall (x i) (r i) ∩
      closedBall (x i₀) (r i₀)).Nonempty}.ncard ≤ 2 ^ d * k + C d := by
  let e := Fintype.equivFin ι
  have hthin' : ∀ p,
      {i | p ∈ closedBall (x (e.symm i)) (r (e.symm i))}.ncard ≤ k := by
    intro p
    exact (count_equiv e.symm (fun j => p ∈ closedBall (x j) (r j))).le.trans (hthin p)
  obtain ⟨i, hi⟩ := hC d k (Fintype.card ι) hd Fintype.card_pos
    (fun j => x (e.symm j)) (fun j => r (e.symm j))
    (fun j => hr (e.symm j)) (hinj.comp e.symm.injective) hthin'
  refine ⟨e.symm i, ?_⟩
  have hc := count_equiv e.symm (fun j => j ≠ e.symm i ∧
    (closedBall (x j) (r j) ∩ closedBall (x (e.symm i)) (r (e.symm i))).Nonempty)
  simp only [ne_eq, Equiv.apply_eq_iff_eq] at hc
  rwa [← hc]

/-- Dimension-only additive slack is equivalent to the strict coefficient bound. -/
theorem proof : Root ↔ Strict := by
  constructor
  · rintro ⟨C, hC⟩ d k n hd hn x r hr hinj hthin
    classical
    by_contra hgoal
    push Not at hgoal
    obtain ⟨ε, hε, hεthin⟩ := inflate x r k hthin
    let m := C d + 2
    have hm : 0 < m := by omega
    have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
    have : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
    obtain ⟨R, hR, hRinj⟩ := copies x r hinj hε m
    have hRpos : ∀ a, 0 < R a := fun a => (hr a.1).trans (hR a).1
    have hcopythin := copies_thin x r m k ε hεthin R (fun a => (hR a).2)
    obtain ⟨a, ha⟩ := root_finite C hC hd (fun a : Fin n × Fin m => x a.1)
      R hRpos hRinj hcopythin
    have hcount := copies_neighbors x r m R (fun a => (hR a).1.le) a
    rw [closed_neighbors_card x r (fun i => (hr i).le) a.1,
      closed_neighbors_card (fun a : Fin n × Fin m => x a.1)
        R (fun a => (hRpos a).le) a] at hcount
    have hbase := hgoal a.1
    have hmul := Nat.mul_le_mul_right m hbase
    dsimp [m] at hcount hmul ha
    nlinarith
  · intro h
    refine ⟨fun _ => 0, ?_⟩
    intro d k n hd hn x r hr hinj hthin
    obtain ⟨i, hi⟩ := h d k n hd hn x r hr hinj hthin
    exact ⟨i, by simpa using hi.le⟩

end Submissions.PlySlackRemoval.Amplification
