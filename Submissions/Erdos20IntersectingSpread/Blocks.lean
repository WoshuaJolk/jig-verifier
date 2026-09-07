import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring


namespace Submissions.Erdos20IntersectingSpread.Blocks

open Set

abbrev Other {n : ℕ} (i : Fin n) := {j : Fin n // j ≠ i}

abbrev Param (n k : ℕ) := Σ i : Fin n, Other i → Fin k

/-- One complete row and one point in each remaining row, as in the
Lovett–Solomon–Zhang intersecting regular-family construction. -/
def member {n k : ℕ} (p : Param n k) : Set (Fin n × Fin k) :=
  Set.range (fun y : Fin k => (p.1, y)) ∪
    Set.range (fun j : Other p.1 => (j.1, p.2 j))

def family (n k : ℕ) : Set (Set (Fin n × Fin k)) := Set.range (@member n k)

theorem mem_member {n k : ℕ} (i : Fin n) (f : Other i → Fin k)
    (j : Fin n) (y : Fin k) :
    (j, y) ∈ member ⟨i, f⟩ ↔ j = i ∨ ∃ h : j ≠ i, y = f ⟨j, h⟩ := by
  constructor
  · rintro (⟨z, heq⟩ | ⟨z, heq⟩)
    · exact Or.inl (congrArg Prod.fst heq).symm
    · have hj : z.1 = j := congrArg Prod.fst heq
      subst j
      exact Or.inr ⟨z.2, (congrArg Prod.snd heq).symm⟩
  · rintro (rfl | ⟨h, rfl⟩)
    · exact Or.inl ⟨y, rfl⟩
    · exact Or.inr ⟨⟨j, h⟩, rfl⟩

@[simp] theorem other_card {n : ℕ} (i : Fin n) : Fintype.card (Other i) = n - 1 := by
  simp [Other]

theorem member_ncard {n k : ℕ} (p : Param n k) :
    (member p).ncard = n + k - 1 := by
  have hdis : Disjoint (Set.range (fun y : Fin k => (p.1, y)))
      (Set.range (fun j : Other p.1 => (j.1, p.2 j))) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨y, rfl⟩ ⟨j, heq⟩
    exact j.2 (congrArg Prod.fst heq)
  have h1 : Function.Injective (fun y : Fin k => (p.1, y)) := by
    intro y z h
    exact congrArg Prod.snd h
  have h2 : Function.Injective (fun j : Other p.1 => (j.1, p.2 j)) := by
    intro j l h
    exact Subtype.ext (congrArg Prod.fst h)
  rw [member, Set.ncard_union_eq hdis (Set.toFinite _) (Set.toFinite _),
    Set.ncard_range_of_injective h1, Set.ncard_range_of_injective h2,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_fin, other_card]
  have hn : 0 < n := Nat.zero_lt_of_lt p.1.isLt
  omega

theorem member_injective {n k : ℕ} (hk : 2 ≤ k) :
    Function.Injective (@member n k) := by
  classical
  let : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr hk
  rintro ⟨i, f⟩ ⟨j, g⟩ heq
  have hij : i = j := by
    by_contra hne
    obtain ⟨y, hy⟩ := exists_ne (g ⟨i, hne⟩)
    have hp : (i, y) ∈ member ⟨i, f⟩ := (mem_member i f i y).mpr (Or.inl rfl)
    rw [heq, mem_member] at hp
    rcases hp with h | ⟨h, he⟩
    · exact hne h
    · exact hy he
  subst j
  apply congrArg (Sigma.mk i)
  funext x
  have hp : (x.1, f x) ∈ member ⟨i, f⟩ :=
    (mem_member i f x.1 (f x)).mpr (Or.inr ⟨x.2, rfl⟩)
  rw [heq, mem_member] at hp
  rcases hp with h | ⟨h, he⟩
  · exact (x.2 h).elim
  · exact he

theorem family_ncard (n k : ℕ) (hk : 2 ≤ k) :
    (family n k).ncard = n * k ^ (n - 1) := by
  rw [family, Set.ncard_range_of_injective (member_injective hk), Nat.card_eq_fintype_card]
  simp [Param, Fintype.card_sigma]

theorem family_uniform (n k : ℕ) :
    ∀ A ∈ family n k, A.ncard = n + k - 1 := by
  rintro A ⟨p, rfl⟩
  exact member_ncard p

theorem members_intersect {n k : ℕ} (hk : 0 < k) (p q : Param n k) :
    (member p ∩ member q).Nonempty := by
  rcases p with ⟨i, f⟩
  rcases q with ⟨j, g⟩
  by_cases hij : i = j
  · subst j
    let y : Fin k := ⟨0, hk⟩
    exact ⟨(i, y), (mem_member i f i y).mpr (Or.inl rfl),
      (mem_member i g i y).mpr (Or.inl rfl)⟩
  · exact ⟨(i, g ⟨i, hij⟩), (mem_member i f i _).mpr (Or.inl rfl),
      (mem_member j g i _).mpr (Or.inr ⟨hij, rfl⟩)⟩

theorem family_intersecting (n k : ℕ) (hk : 0 < k) :
    ∀ A ∈ family n k, ∀ B ∈ family n k, (A ∩ B).Nonempty := by
  rintro A ⟨p, rfl⟩ B ⟨q, rfl⟩
  exact members_intersect hk p q

theorem family_nonempty (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    (family n k).Nonempty := by
  exact ⟨member ⟨⟨0, hn⟩, fun _ => ⟨0, hk⟩⟩, Set.mem_range_self _⟩

/-- Values of the chosen point in a row that cover the link's prescribed points.
An empty row allows k values, a singleton allows one, and any larger row allows none. -/
def allowed {n k : ℕ} (S : Set (Fin n × Fin k)) (j : Fin n) : Set (Fin k) :=
  {y | ∀ z, (j, z) ∈ S → z = y}

abbrev LinkParam {n k : ℕ} (S : Set (Fin n × Fin k)) :=
  Σ i : Fin n, (j : Other i) → allowed S j.1

def linkParamToParam {n k : ℕ} {S : Set (Fin n × Fin k)} (p : LinkParam S) : Param n k :=
  ⟨p.1, fun j => (p.2 j).1⟩

theorem linkParamToParam_injective {n k : ℕ} (S : Set (Fin n × Fin k)) :
    Function.Injective (@linkParamToParam n k S) := by
  rintro ⟨i, f⟩ ⟨j, g⟩ h
  have hij : i = j := congrArg Sigma.fst h
  subst j
  have hfg : (fun x => (f x).1) = (fun x => (g x).1) :=
    eq_of_heq (Sigma.mk.inj_iff.mp h).2
  apply congrArg (Sigma.mk i)
  funext x
  exact Subtype.ext (congrFun hfg x)

theorem link_eq_range {n k : ℕ} (S : Set (Fin n × Fin k)) :
    {A ∈ family n k | S ⊆ A} =
      Set.range (fun p : LinkParam S => member (linkParamToParam p)) := by
  ext A
  constructor
  · rintro ⟨⟨⟨i, f⟩, rfl⟩, hsub⟩
    refine ⟨⟨i, fun j => ⟨f j, ?_⟩⟩, rfl⟩
    intro z hz
    rcases (mem_member i f j.1 z).mp (hsub hz) with h | ⟨h, he⟩
    · exact (j.2 h).elim
    · exact he
  · rintro ⟨p, rfl⟩
    refine ⟨Set.mem_range_self _, ?_⟩
    rintro ⟨j, z⟩ hz
    by_cases hji : j = p.1
    · exact (mem_member p.1 _ j z).mpr (Or.inl hji)
    · exact (mem_member p.1 _ j z).mpr (Or.inr ⟨hji, (p.2 ⟨j, hji⟩).2 z hz⟩)

/-- Exact count for every link, before separating it into occupancy cases. -/
theorem link_ncard {n k : ℕ} (hk : 2 ≤ k) (S : Set (Fin n × Fin k)) :
    {A ∈ family n k | S ⊆ A}.ncard =
      ∑ i : Fin n, ∏ j : Other i, (allowed S j.1).ncard := by
  classical
  have hinj : Function.Injective (fun p : LinkParam S => member (linkParamToParam p)) :=
    (member_injective hk).comp (linkParamToParam_injective S)
  rw [link_eq_range, Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card]
  simp only [LinkParam, Fintype.card_sigma, Fintype.card_pi]
  simp only [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]

def row {n k : ℕ} (S : Set (Fin n × Fin k)) (j : Fin n) : Set (Fin k) :=
  (fun y => (j, y)) ⁻¹' S

theorem allowed_empty_row {n k : ℕ} {S : Set (Fin n × Fin k)} {j : Fin n}
    (h : row S j = ∅) : allowed S j = Set.univ := by
  ext y
  simp only [Set.mem_univ, iff_true]
  intro z hz
  have : z ∈ row S j := hz
  rw [h] at this
  exact this.elim

theorem allowed_singleton_row {n k : ℕ} {S : Set (Fin n × Fin k)} {j : Fin n}
    {z : Fin k} (h : row S j = {z}) : allowed S j = {z} := by
  ext y
  constructor
  · intro hy
    have hz : z ∈ row S j := by rw [h]; exact Set.mem_singleton z
    exact (hy z hz).symm
  · intro hy
    have hyz : y = z := hy
    subst y
    intro w hw
    have : w ∈ row S j := hw
    rw [h] at this
    exact this

theorem allowed_empty_of_two {n k : ℕ} {S : Set (Fin n × Fin k)} {j : Fin n}
    {y z : Fin k} (hy : y ∈ row S j) (hz : z ∈ row S j) (hne : y ≠ z) :
    allowed S j = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact hne ((hx y hy).trans (hx z hz).symm)

/-- The exact row-occupancy factor in the link-count formula. -/
theorem allowed_ncard {n k : ℕ} (S : Set (Fin n × Fin k)) (j : Fin n) :
    (allowed S j).ncard =
      if (row S j).ncard = 0 then k else if (row S j).ncard = 1 then 1 else 0 := by
  classical
  by_cases h0 : (row S j).ncard = 0
  · rw [if_pos h0, allowed_empty_row ((Set.ncard_eq_zero (Set.toFinite _)).mp h0)]
    simp
  · rw [if_neg h0]
    by_cases h1 : (row S j).ncard = 1
    · obtain ⟨z, hz⟩ := Set.ncard_eq_one.mp h1
      rw [if_pos h1, allowed_singleton_row hz, Set.ncard_singleton]
    · rw [if_neg h1]
      apply (Set.ncard_eq_zero (Set.toFinite _)).mpr
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro y hy
      have hsub : row S j ⊆ {y} := fun z hz => hy z hz
      have hle : (row S j).ncard ≤ 1 := by
        simpa using Set.ncard_le_ncard hsub
      omega

def rowsEquiv {n k : ℕ} (S : Set (Fin n × Fin k)) :
    S ≃ Σ j : Fin n, row S j where
  toFun x := ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
  invFun x := ⟨(x.1, x.2.1), x.2.2⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

theorem ncard_eq_sum_rows {n k : ℕ} (S : Set (Fin n × Fin k)) :
    S.ncard = ∑ j : Fin n, (row S j).ncard := by
  classical
  rw [← Nat.card_coe_set_eq, Nat.card_congr (rowsEquiv S), Nat.card_eq_fintype_card]
  simp only [Fintype.card_sigma]
  simp only [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]

theorem row_ncard_le {n k : ℕ} (S : Set (Fin n × Fin k)) (j : Fin n) :
    (row S j).ncard ≤ k := by
  simpa using Set.ncard_le_ncard (Set.subset_univ (row S j))

theorem link_ncard_by_occupancy {n k : ℕ} (hk : 2 ≤ k) (S : Set (Fin n × Fin k)) :
    {A ∈ family n k | S ⊆ A}.ncard =
      ∑ i : Fin n, ∏ j : Other i,
        (if (row S j.1).ncard = 0 then k
          else if (row S j.1).ncard = 1 then 1 else 0) := by
  rw [link_ncard hk S]
  simp_rw [allowed_ncard]

def IsSunflower {α : Type*} (F : Set (Set α)) : Prop :=
  ∃ K : Set α, F.Pairwise fun A B => A ∩ B = K

/-- A control distinguishing intersecting families from sunflower-free ones:
these examples themselves contain a k-petal ordinary sunflower. -/
theorem contains_ordinary_sunflower (n k : ℕ) (hn : 2 ≤ n) :
    ∃ F ⊆ family n k, F.ncard = k ∧ IsSunflower F := by
  classical
  let i : Fin n := ⟨0, by omega⟩
  let flat : Fin k → Set (Fin n × Fin k) := fun v => member ⟨i, fun _ => v⟩
  have hinj : Function.Injective flat := by
    intro v w h
    let j : Fin n := ⟨1, by omega⟩
    have hji : j ≠ i := by intro he; have := congrArg Fin.val he; simp [j, i] at this
    have hp : (j, v) ∈ flat v := (mem_member i _ j v).mpr (Or.inr ⟨hji, rfl⟩)
    rw [h] at hp
    rcases (mem_member i _ j v).mp hp with he | ⟨_, he⟩
    · exact (hji he).elim
    · exact he
  refine ⟨Set.range flat, ?_, ?_, Set.range (fun y : Fin k => (i, y)), ?_⟩
  · rintro A ⟨v, rfl⟩
    exact ⟨⟨i, fun _ => v⟩, rfl⟩
  · rw [Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin]
  · rintro _ ⟨v, rfl⟩ _ ⟨w, rfl⟩ hne
    have hvw : v ≠ w := fun h => hne (congrArg flat h)
    ext ⟨j, y⟩
    constructor
    · rintro ⟨hv, hw⟩
      by_cases hji : j = i
      · subst j
        exact ⟨y, rfl⟩
      · obtain ⟨_, hyv⟩ := ((mem_member i _ j y).mp hv).resolve_left hji
        obtain ⟨_, hyw⟩ := ((mem_member i _ j y).mp hw).resolve_left hji
        exact (hvw (hyv.symm.trans hyw)).elim
    · rintro ⟨z, he⟩
      have hji : j = i := (congrArg Prod.fst he).symm
      exact ⟨(mem_member i _ j y).mpr (Or.inl hji),
        (mem_member i _ j y).mpr (Or.inl hji)⟩

def block {n k : ℕ} (i : Fin n) : Set (Fin n × Fin k) :=
  Set.range (fun y : Fin k => (i, y))

@[simp] theorem block_ncard {n k : ℕ} (i : Fin n) : (@block n k i).ncard = k := by
  have hi : Function.Injective (fun y : Fin k => (i, y)) :=
    fun _ _ h => congrArg Prod.snd h
  rw [block, Set.ncard_range_of_injective hi, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem block_subset_member_iff {n k : ℕ} (hk : 2 ≤ k) (i : Fin n) (p : Param n k) :
    block i ⊆ member p ↔ p.1 = i := by
  classical
  let : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr hk
  rcases p with ⟨j, f⟩
  constructor
  · intro h
    by_contra hne
    obtain ⟨y, hy⟩ := exists_ne (f ⟨i, Ne.symm hne⟩)
    have hp := h (Set.mem_range_self y)
    rcases (mem_member j f i y).mp hp with hi | ⟨_, he⟩
    · exact hne hi.symm
    · exact hy he
  · intro h
    change j = i at h
    subst j
    rintro _ ⟨y, rfl⟩
    exact (mem_member i f i y).mpr (Or.inl rfl)

theorem full_block_link_ncard {n k : ℕ} (hk : 2 ≤ k) (i : Fin n) :
    {A ∈ family n k | block i ⊆ A}.ncard = k ^ (n - 1) := by
  classical
  have heq : {A ∈ family n k | block i ⊆ A} =
      Set.range (fun f : Other i → Fin k => member ⟨i, f⟩) := by
    ext A
    constructor
    · rintro ⟨⟨⟨j, f⟩, rfl⟩, h⟩
      have hj : j = i := (block_subset_member_iff hk i ⟨j, f⟩).mp h
      subst j
      exact ⟨f, rfl⟩
    · rintro ⟨f, rfl⟩
      exact ⟨⟨⟨i, f⟩, rfl⟩, (block_subset_member_iff hk i _).mpr rfl⟩
  have hi : Function.Injective (fun f : Other i → Fin k => member ⟨i, f⟩) := by
    intro f g h
    exact eq_of_heq (Sigma.mk.inj_iff.mp ((member_injective hk) h)).2
  rw [heq, Set.ncard_range_of_injective hi, Nat.card_eq_fintype_card]
  simp

theorem allowed_singleton_ncard {n k : ℕ} (i j : Fin n) (y : Fin k) :
    (allowed {(i, y)} j).ncard = if j = i then 1 else k := by
  by_cases hji : j = i
  · subst j
    have hr : row {(i, y)} i = {y} := by ext z; simp [row]
    rw [allowed_singleton_row hr]
    simp
  · have hr : row {(i, y)} j = ∅ := by ext z; simp [row, hji]
    rw [allowed_empty_row hr]
    simp [hji]

/-- Exact singleton degree with denominators cleared, valid even when n=1. -/
theorem singleton_link_ncard_mul {n k : ℕ} (hk : 2 ≤ k) (i : Fin n) (y : Fin k) :
    {A ∈ family n k | {(i, y)} ⊆ A}.ncard * k =
      (n + k - 1) * k ^ (n - 1) := by
  classical
  let q : Fin n → ℕ := fun j => if j = i then 1 else k
  let P : Fin n → ℕ := fun j => ∏ t : Other j, q t.1
  have hprod : (∏ j : Fin n, q j) = k ^ (n - 1) := by
    rw [Fintype.prod_eq_mul_prod_subtype_ne q i]
    have hother : ∀ j : Other i, q j.1 = k := fun j => if_neg j.2
    change q i * (∏ j : Other i, q j.1) = _
    simp_rw [hother]
    simp [q]
  have hterm (j : Fin n) : q j * P j = k ^ (n - 1) :=
    (Fintype.prod_eq_mul_prod_subtype_ne q j).symm.trans hprod
  have hi : P i = k ^ (n - 1) := by simpa [q] using hterm i
  have hj (j : Other i) : k * P j.1 = k ^ (n - 1) := by
    simpa [q, j.2] using hterm j.1
  calc
    {A ∈ family n k | {(i, y)} ⊆ A}.ncard * k = (∑ j : Fin n, P j) * k := by
      rw [link_ncard hk]
      simp_rw [allowed_singleton_ncard]
      rfl
    _ = k * (P i + ∑ j : Other i, P j.1) := by
      rw [Nat.mul_comm, Fintype.sum_eq_add_sum_subtype_ne P i]
    _ = k * P i + ∑ j : Other i, k * P j.1 := by
      rw [Nat.mul_add, Finset.mul_sum]
    _ = k * k ^ (n - 1) + (n - 1) * k ^ (n - 1) := by
      rw [hi]
      simp_rw [hj]
      simp
    _ = (n + k - 1) * k ^ (n - 1) := by
      rw [← Nat.add_mul]
      congr 1
      have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
      omega

/-- Cardinal form of spreadness under the uniform distribution on the family. -/
def IsSpread {α : Type*} (κ : ℕ) (F : Set (Set α)) : Prop :=
  ∀ S : Set α, {A ∈ F | S ⊆ A}.ncard * κ ^ S.ncard ≤ F.ncard

theorem spread_necessary (n k κ : ℕ) (hn : 0 < n) (hk : 2 ≤ k)
    (h : IsSpread κ (family n k)) :
    κ * (n + k - 1) ≤ n * k ∧ κ ^ k ≤ n := by
  let i : Fin n := ⟨0, hn⟩
  let y : Fin k := ⟨0, by omega⟩
  have hpow : 0 < k ^ (n - 1) := pow_pos (by omega) _
  constructor
  · have hs := h {(i, y)}
    rw [Set.ncard_singleton, pow_one, family_ncard n k hk] at hs
    have hm : (κ * (n + k - 1)) * k ^ (n - 1) ≤ (n * k) * k ^ (n - 1) := by
      calc
        (κ * (n + k - 1)) * k ^ (n - 1) = κ * ((n + k - 1) * k ^ (n - 1)) := by
          rw [Nat.mul_assoc]
        _ = κ * ({A ∈ family n k | {(i, y)} ⊆ A}.ncard * k) := by
          rw [singleton_link_ncard_mul hk i y]
        _ = ({A ∈ family n k | {(i, y)} ⊆ A}.ncard * κ) * k := by ac_rfl
        _ ≤ (n * k ^ (n - 1)) * k := Nat.mul_le_mul_right k hs
        _ = (n * k) * k ^ (n - 1) := by ac_rfl
    exact Nat.le_of_mul_le_mul_right hm hpow
  · have hf := h (block i)
    rw [full_block_link_ncard hk i, block_ncard, family_ncard n k hk] at hf
    exact Nat.le_of_mul_le_mul_right (by simpa [Nat.mul_comm] using hf) hpow

end Submissions.Erdos20IntersectingSpread.Blocks


open scoped BigOperators

namespace Submissions.Erdos20IntersectingSpread.Blocks

theorem light_spread_bound (n k q b : ℕ) (hn : 0 < n) (hk : 2 ≤ k)
    (h : q * (n + k - 1) ≤ n * k) :
    q^b * (n + b * (k - 1)) ≤ n * k^b := by
  have hqkn : q*n ≤ k*n := by
    calc
      q*n ≤ q*(n+k-1) := Nat.mul_le_mul_left q (by omega)
      _ ≤ n*k := h
      _ = k*n := Nat.mul_comm _ _
  have hqk : q ≤ k := by
    by_contra hnot
    have hlt := Nat.mul_lt_mul_of_pos_right (Nat.lt_of_not_ge hnot) hn
    omega
  have hfirst : q*(n+(k-1)) ≤ k*n := by
    have heq : n+(k-1) = n+k-1 := by omega
    simpa only [heq, Nat.mul_comm] using h
  induction b with
  | zero => simp
  | succ b ih =>
    have hstep : q*(n+(b+1)*(k-1)) ≤ k*(n+b*(k-1)) := by
      calc
        q*(n+(b+1)*(k-1)) = q*(n+(k-1))+q*(b*(k-1)) := by ring
        _ ≤ k*n+k*(b*(k-1)) := Nat.add_le_add hfirst (Nat.mul_le_mul_right _ hqk)
        _ = k*(n+b*(k-1)) := by ring
    calc
      q^(b+1)*(n+(b+1)*(k-1)) = q^b*(q*(n+(b+1)*(k-1))) := by rw [pow_succ]; ring
      _ ≤ q^b*(k*(n+b*(k-1))) := Nat.mul_le_mul_left _ hstep
      _ = k*(q^b*(n+b*(k-1))) := by ring
      _ ≤ k*(n*k^b) := Nat.mul_le_mul_left _ ih
      _ = n*k^(b+1) := by rw [pow_succ]; ring


def occupancyChoices (k m : ℕ) : ℕ :=
  if m = 0 then k else if m = 1 then 1 else 0

theorem scaled_occupancy_le {k q m : ℕ} (hqk : q ≤ k) :
    q^m * occupancyChoices k m ≤ k := by
  rcases m with _ | _ | m
  · simp [occupancyChoices]
  · simpa [occupancyChoices] using hqk
  · simp [occupancyChoices]

theorem scaled_occupancy_eq {k m : ℕ} (hm : m ≤ 1) :
    k^m * occupancyChoices k m = k := by
  rcases m with _ | m
  · simp [occupancyChoices]
  · have hm0 : m = 0 := by omega
    simp [hm0, occupancyChoices]

theorem scaled_occupancy_term {n : ℕ} (q k : ℕ) (a : Fin n → ℕ) (i : Fin n) :
    q^(∑ j, a j) * (∏ j : {j : Fin n // j ≠ i}, occupancyChoices k (a j.val)) =
      q^(a i) * ∏ j : {j : Fin n // j ≠ i}, (q^(a j.val) * occupancyChoices k (a j.val)) := by
  rw [Fintype.sum_eq_add_sum_subtype_ne a i, pow_add]
  rw [← Finset.prod_pow_eq_pow_sum]
  rw [mul_assoc, ← Finset.prod_mul_distrib]

theorem light_occupancy_identity {n : ℕ} (k : ℕ) (hk : 1 ≤ k)
    (a : Fin n → ℕ) (ha : ∀ i, a i ≤ 1) :
    k^(∑ i, a i) *
        (∑ i : Fin n, ∏ j : {j : Fin n // j ≠ i}, occupancyChoices k (a j.val)) =
      k^(n-1) * (n + (∑ i, a i) * (k-1)) := by
  have hp : ∀ i, k^(a i) = 1 + a i * (k-1) := by
    intro i
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (ha i) with h | h
    · simp [h]
    · simp [h]
      omega
  have hs : (∑ i, k^(a i)) = n + (∑ i, a i) * (k-1) := by
    simp_rw [hp]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    simp
  calc
    _ = ∑ i : Fin n, k^(a i) *
        ∏ j : {j : Fin n // j ≠ i}, (k^(a j.val) * occupancyChoices k (a j.val)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => scaled_occupancy_term k k a i
    _ = ∑ i : Fin n, k^(a i) * k^(n-1) := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      simp_rw [scaled_occupancy_eq (ha _)]
      simp
    _ = (∑ i, k^(a i)) * k^(n-1) := (Finset.sum_mul _ _ _).symm
    _ = k^(n-1) * (n + (∑ i, a i) * (k-1)) := by rw [hs]; exact Nat.mul_comm _ _

/-- Division-free containment inequality for the full-block construction. -/
theorem occupancy_spread_bound (n k q : ℕ) (hn : 0 < n) (hk : 2 ≤ k)
    (hq : 1 ≤ q) (a : Fin n → ℕ) (ha : ∀ i, a i ≤ k)
    (hsingle : q * (n+k-1) ≤ n*k) (hfull : q^k ≤ n) :
    q^(∑ i, a i) *
        (∑ i : Fin n, ∏ j : {j : Fin n // j ≠ i}, occupancyChoices k (a j.val)) ≤
      n * k^(n-1) := by
  classical
  have hqk : q ≤ k := by
    have hqkn : q*n ≤ k*n := by
      calc
        q*n ≤ q*(n+k-1) := Nat.mul_le_mul_left q (by omega)
        _ ≤ n*k := hsingle
        _ = k*n := Nat.mul_comm _ _
    exact (Nat.mul_le_mul_right_iff hn).mp hqkn
  by_cases hheavy : ∃ h : Fin n, 2 ≤ a h
  · obtain ⟨h, hh⟩ := hheavy
    have hz : occupancyChoices k (a h) = 0 := by
      simp [occupancyChoices, show a h ≠ 0 by omega, show a h ≠ 1 by omega]
    have hsum : (∑ i : Fin n, ∏ j : {j : Fin n // j ≠ i}, occupancyChoices k (a j.val)) =
        ∏ j : {j : Fin n // j ≠ h}, occupancyChoices k (a j.val) := by
      apply Finset.sum_eq_single h
      · intro i _ hih
        apply Finset.prod_eq_zero_iff.mpr
        exact ⟨⟨h, Ne.symm hih⟩, Finset.mem_univ _, hz⟩
      · simp
    rw [hsum, scaled_occupancy_term]
    have hpow : q^(a h) ≤ n :=
      (Nat.pow_le_pow_right (by omega) (ha h)).trans hfull
    have hprod : (∏ j : {j : Fin n // j ≠ h},
        (q^(a j.val) * occupancyChoices k (a j.val))) ≤ k^(n-1) := by
      calc
        _ ≤ ∏ _j : {j : Fin n // j ≠ h}, k := by
          apply Finset.prod_le_prod'
          intro j _
          exact scaled_occupancy_le hqk
        _ = k^(n-1) := by simp
    exact Nat.mul_le_mul hpow hprod
  · have hlight : ∀ i, a i ≤ 1 := by
      intro i
      have := not_exists.mp hheavy i
      omega
    have hident := light_occupancy_identity k (by omega) a hlight
    have hscalar := light_spread_bound n k q (∑ i, a i) hn hk hsingle
    apply Nat.le_of_mul_le_mul_left (c := k^(∑ i, a i)) ?_ (Nat.pow_pos (by omega))
    calc
      _ = q^(∑ i, a i) * (k^(∑ i, a i) *
          (∑ i : Fin n, ∏ j : {j : Fin n // j ≠ i}, occupancyChoices k (a j.val))) := by ring
      _ = k^(n-1) * (q^(∑ i, a i) * (n+(∑ i, a i)*(k-1))) := by rw [hident]; ring
      _ ≤ k^(n-1) * (n*k^(∑ i, a i)) := Nat.mul_le_mul_left _ hscalar
      _ = k^(∑ i, a i) * (n*k^(n-1)) := by ring

end Submissions.Erdos20IntersectingSpread.Blocks

namespace Submissions.Erdos20IntersectingSpread.Blocks

theorem spread_iff (n k κ : ℕ) (hn : 0 < n) (hk : 2 ≤ k) (hκ : 1 ≤ κ) :
    IsSpread κ (family n k) ↔ κ * (n + k - 1) ≤ n * k ∧ κ ^ k ≤ n := by
  constructor
  · exact spread_necessary n k κ hn hk
  · rintro ⟨hsingle, hfull⟩ S
    rw [family_ncard n k hk, link_ncard_by_occupancy hk S, ncard_eq_sum_rows S]
    simpa [occupancyChoices, Nat.mul_comm] using
      occupancy_spread_bound n k κ hn hk hκ (fun i => (row S i).ncard)
        (row_ncard_le S) hsingle hfull

/-- Explicit parameters give arbitrarily high natural spreadness while all
members intersect. This is a matching obstruction, not a sunflower obstruction. -/
theorem explicit_spread (κ : ℕ) (hκ : 2 ≤ κ) :
    IsSpread κ (family (κ ^ (κ + 1)) (κ + 1)) := by
  let n := κ ^ (κ + 1)
  have hn : 0 < n := pow_pos (by omega) _
  apply (spread_iff n (κ + 1) κ hn (by omega) (by omega)).mpr
  constructor
  · have hsquare : κ * κ ≤ n := by
      simpa [n, pow_two] using
        Nat.pow_le_pow_right (show 0 < κ by omega) (show 2 ≤ κ + 1 by omega)
    have hw : n + (κ + 1) - 1 = n + κ := by omega
    rw [hw, Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.mul_comm κ n]
    exact Nat.add_le_add_left hsquare (n * κ)
  · exact le_rfl

theorem arbitrarily_spread_intersecting (κ : ℕ) (hκ : 2 ≤ κ) :
    ∃ (α : Type) (w : ℕ) (F : Set (Set α)),
      0 < w ∧ F.Finite ∧ F.Nonempty ∧
      (∀ A ∈ F, A.ncard = w) ∧
      (∀ A ∈ F, ∀ B ∈ F, (A ∩ B).Nonempty) ∧ IsSpread κ F ∧
      (∃ G ⊆ F, G.ncard = κ + 1 ∧ IsSunflower G) := by
  let n := κ ^ (κ + 1)
  let k := κ + 1
  have hn : 2 ≤ n := by
    calc
      2 ≤ κ := hκ
      _ = κ ^ 1 := by simp
      _ ≤ κ ^ (κ + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  refine ⟨Fin n × Fin k, n + k - 1, family n k, by omega, Set.toFinite _,
    family_nonempty n k (by omega) (by dsimp [k]; omega), family_uniform n k,
    family_intersecting n k (by dsimp [k]; omega), explicit_spread κ hκ, ?_⟩
  exact contains_ordinary_sunflower n k hn

end Submissions.Erdos20IntersectingSpread.Blocks

namespace Submissions.Erdos20IntersectingSpread.Blocks

/-- Known obstruction from Lovett–Solomon–Zhang, Claim 6.8. -/
theorem proof : ∀ κ : ℕ, 2 ≤ κ →
    ∃ (α : Type) (w : ℕ) (F : Set (Set α)),
      0 < w ∧ F.Finite ∧ F.Nonempty ∧
      (∀ A ∈ F, A.ncard = w) ∧
      (∀ A ∈ F, ∀ B ∈ F, (A ∩ B).Nonempty) ∧
      (∀ S : Set α, {A ∈ F | S ⊆ A}.ncard * κ ^ S.ncard ≤ F.ncard) := by
  intro κ hκ
  obtain ⟨α, w, F, hw, hf, hn, hu, hi, hs, _⟩ := arbitrarily_spread_intersecting κ hκ
  exact ⟨α, w, F, hw, hf, hn, hu, hi, hs⟩

end Submissions.Erdos20IntersectingSpread.Blocks
