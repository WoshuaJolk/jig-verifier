import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Data.List.Sort

namespace Submissions.ErdosMultiplesTwoBases.Support

namespace Punctured

/-- A floor-function estimate for deleting every d-th point, d≥2. -/
lemma floor_piece_bound (q r d : ℕ) (hq : 1 ≤ q) (hd : 2 ≤ d)
    (hqr : q + 1 ≤ r) :
    (q + 1) * (r - r / d) ≤ 2 * r * (q - q / d) := by
  by_cases hgood : q + 1 ≤ 2 * (q - q / d)
  · have h1 := Nat.mul_le_mul_right (r - r / d) hgood
    have h2 := Nat.mul_le_mul_left (2 * (q - q / d))
      (Nat.sub_le r (r / d))
    nlinarith
  · have hdiv : q / d ≤ q := Nat.div_le_self q d
    have hprod : q / d * d ≤ q := Nat.div_mul_le_self q d
    have hd2 : d = 2 := by
      by_contra hne
      have hd3 : 3 ≤ d := by omega
      have h3 : 3 * (q / d) ≤ q := by nlinarith
      omega
    subst d
    have hq2 : 2 ≤ q := by omega
    have hqe : 2 * (q - q / 2) = q := by omega
    have hfr : 2 * (r - r / 2) ≤ r + 1 := by omega
    have hmul := Nat.mul_le_mul_left (q + 1) hfr
    have hstep := Nat.mul_le_mul_right r (show 1 ≤ q - 1 by omega)
    have hsub : q - 1 + 1 = q := by omega
    have hcore : (q + 1) * (r + 1) ≤ 2 * q * r := by nlinarith
    have heq := congrArg (fun t : ℕ => r * t) hqe
    nlinarith

/-- The count of surviving points is positive after the first point. -/
lemma count_pos (a d x : ℕ) (ha : 0 < a) (hd : 2 ≤ d) (hax : a ≤ x) :
    0 < x / a - x / (a * d) := by
  rw [← Nat.div_div_eq_div_mul]
  have hq : 1 ≤ x / a := (Nat.one_le_div_iff ha).mpr hax
  have hprod : (x / a / d) * d ≤ x / a := Nat.div_mul_le_self (x / a) d
  have hsmall : x / a / d < x / a := by nlinarith
  omega

/-- Shifted density bound for a progression with every d-th point deleted. -/
theorem shifted (a d n m : ℕ) (ha : 0 < a) (hd : 2 ≤ d)
    (han : a ≤ n) (hnm : n < m) :
    (n + 1) * (m / a - m / (a * d)) ≤
      2 * m * (n / a - n / (a * d)) := by
  rw [← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
  have hq : 1 ≤ n / a := (Nat.one_le_div_iff ha).mpr han
  have hqr : n / a ≤ m / a := Nat.div_le_div_right (Nat.le_of_lt hnm)
  by_cases heq : m / a = n / a
  · rw [heq]
    exact Nat.mul_le_mul_right _ (show n + 1 ≤ 2 * m by omega)
  · have hqr' : n / a + 1 ≤ m / a := by omega
    have hf := floor_piece_bound (n / a) (m / a) d hq hd hqr'
    have hn : n + 1 ≤ a * (n / a + 1) := by
      have h := Nat.lt_div_mul_add (a := n) ha
      nlinarith
    have hm : a * (m / a) ≤ m := Nat.mul_div_le m a
    have h1 := Nat.mul_le_mul_right (m / a - m / a / d) hn
    have h2 := Nat.mul_le_mul_left a hf
    have h3 := Nat.mul_le_mul_right (2 * (n / a - n / a / d)) hm
    nlinarith

/-- The strict Erdős bound for a progression with every d-th point deleted. -/
theorem strict (a d n m : ℕ) (ha : 0 < a) (hd : 2 ≤ d)
    (han : a ≤ n) (hnm : n < m) :
    n * (m / a - m / (a * d)) <
      2 * m * (n / a - n / (a * d)) := by
  have h := shifted a d n m ha hd han hnm
  have hp := count_pos a d m ha hd (by omega)
  nlinarith


end Punctured

namespace OrderedLCM

open Finset

/-- Every later intersection with the head is contained in its intersection
with the immediately following generator. This is a structural hypothesis. -/
def Good : List ℕ → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => Good (b :: rest) ∧ ∀ c ∈ rest, Nat.lcm a b ∣ Nat.lcm a c

def multiples (A : List ℕ) (x : ℕ) : Finset ℕ :=
  (Icc 1 x).filter (fun k => ∃ a ∈ A, a ∣ k)

def mult (a x : ℕ) : Finset ℕ := (Icc 1 x).filter (fun k => a ∣ k)

lemma card_mult (a x : ℕ) : (mult a x).card = x / a := by
  have h : (Icc 1 x) = Ioc 0 x := by
    simpa using Icc_add_one_left_eq_Ioc (0 : ℕ) x
  rw [mult, h, Nat.Ioc_filter_dvd_card_eq_div]

lemma multiples_singleton (a x : ℕ) : multiples [a] x = mult a x := by
  ext k
  simp [multiples, mult]

lemma multiples_cons (a : ℕ) (A : List ℕ) (x : ℕ) :
    multiples (a :: A) x = mult a x ∪ multiples A x := by
  ext k
  simp [multiples, mult, and_or_left]

lemma inter_head (a b : ℕ) (rest : List ℕ) (x : ℕ)
    (hchain : ∀ c ∈ rest, Nat.lcm a b ∣ Nat.lcm a c) :
    mult a x ∩ multiples (b :: rest) x = mult (Nat.lcm a b) x := by
  ext k
  constructor
  · intro hk
    obtain ⟨hka, hkt⟩ := mem_inter.mp hk
    obtain ⟨hkr, hak⟩ := mem_filter.mp hka
    obtain ⟨_, c, hc, hck⟩ := mem_filter.mp hkt
    apply mem_filter.mpr
    refine ⟨hkr, ?_⟩
    rcases List.mem_cons.mp hc with hcb | hcr
    · subst c
      exact Nat.lcm_dvd hak hck
    · exact dvd_trans (hchain c hcr) (Nat.lcm_dvd hak hck)
  · intro hk
    obtain ⟨hkr, hlk⟩ := mem_filter.mp hk
    apply mem_inter.mpr
    constructor
    · exact mem_filter.mpr ⟨hkr, dvd_trans (Nat.dvd_lcm_left a b) hlk⟩
    · exact mem_filter.mpr ⟨hkr, b, by simp, dvd_trans (Nat.dvd_lcm_right a b) hlk⟩

lemma count_cons (a b : ℕ) (rest : List ℕ) (x : ℕ)
    (hchain : ∀ c ∈ rest, Nat.lcm a b ∣ Nat.lcm a c) :
    (multiples (a :: b :: rest) x).card =
      (multiples (b :: rest) x).card + (x / a - x / Nat.lcm a b) := by
  have hc := card_union_add_card_inter (mult a x) (multiples (b :: rest) x)
  rw [← multiples_cons, inter_head a b rest x hchain, card_mult] at hc
  have hsub : mult (Nat.lcm a b) x ⊆ mult a x := by
    intro k hk
    obtain ⟨hkr, hlk⟩ := mem_filter.mp hk
    exact mem_filter.mpr ⟨hkr, dvd_trans (Nat.dvd_lcm_left a b) hlk⟩
  have hle := card_le_card hsub
  rw [card_mult, card_mult] at hle
  rw [card_mult] at hc
  omega

lemma singleton_bound (a n m : ℕ) (ha : 0 < a) (han : a ≤ n) (hnm : n < m) :
    n * (m / a) < 2 * m * (n / a) := by
  have hq : 1 ≤ n / a := (Nat.one_le_div_iff ha).mpr han
  have hn : n < (n / a + 1) * a := by
    simpa [Nat.add_mul] using (Nat.lt_div_mul_add (a := n) ha)
  have hn' : n < 2 * a * (n / a) := by nlinarith
  have hm : a * (m / a) ≤ m := Nat.mul_div_le m a
  have h1 := Nat.mul_le_mul_left n hm
  have h2 := Nat.mul_lt_mul_of_pos_right hn' (show 0 < m by omega)
  have h3 : a * (n * (m / a)) < a * (2 * m * (n / a)) := by nlinarith
  exact Nat.lt_of_mul_lt_mul_left h3

/-- Arbitrary-length ordered-LCM chains satisfy the Erdős multiples inequality.
This is a structural special case, not the unrestricted conjecture. -/
theorem bound (A : List ℕ) (hne : A ≠ []) (hgood : Good A)
    (hpos : ∀ a ∈ A, 0 < a) (n m : ℕ)
    (hmax : ∀ a ∈ A, a ≤ n) (hnm : n < m) :
    n * (multiples A m).card < 2 * m * (multiples A n).card := by
  induction A with
  | nil => exact (hne rfl).elim
  | cons a tail ih =>
    have ha : 0 < a := hpos a (by simp)
    have han : a ≤ n := hmax a (by simp)
    cases tail with
    | nil =>
      rw [multiples_singleton, multiples_singleton, card_mult, card_mult]
      exact singleton_bound a n m ha han hnm
    | cons b rest =>
      have hb : 0 < b := hpos b (by simp)
      have htail : n * (multiples (b :: rest) m).card <
          2 * m * (multiples (b :: rest) n).card :=
        ih (by simp) hgood.1 (fun c hc => hpos c (by simp [hc]))
          (fun c hc => hmax c (by simp [hc]))
      have hpiece : n * (m / a - m / Nat.lcm a b) ≤
          2 * m * (n / a - n / Nat.lcm a b) := by
        by_cases heq : Nat.lcm a b = a
        · simp [heq]
        · let d := Nat.lcm a b / a
          have hl : a * d = Nat.lcm a b := Nat.mul_div_cancel' (Nat.dvd_lcm_left a b)
          have hlpos : 0 < Nat.lcm a b := Nat.lcm_pos ha hb
          have hd : 2 ≤ d := by
            cases hdval : d with
            | zero =>
              rw [hdval, Nat.mul_zero] at hl
              exact (Nat.ne_of_gt hlpos) hl.symm |>.elim
            | succ e =>
              cases e with
              | zero =>
                rw [hdval, Nat.mul_one] at hl
                exact (heq hl.symm).elim
              | succ e => omega
          simpa [hl] using Nat.le_of_lt (Punctured.strict a d n m ha hd han hnm)
      rw [count_cons a b rest m hgood.2, count_cons a b rest n hgood.2]
      nlinarith

/-- The ordered-list theorem in the canonical finite-set counting vocabulary. -/
theorem finset_bound (A : Finset ℕ) (hne : A.Nonempty) (hzero : 0 ∉ A)
    (hchain : ∃ L : List ℕ, L.toFinset = A ∧ Good L) (n m : ℕ)
    (hmax : ∀ a ∈ A, a ≤ n) (hnm : n < m) :
    n * ((Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k)).card <
      2 * m * ((Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card := by
  obtain ⟨L, hL, hg⟩ := hchain
  have hneL : L ≠ [] := by
    intro h
    subst L
    simp only [List.toFinset_nil] at hL
    exact hne.ne_empty hL.symm
  have hposL : ∀ a ∈ L, 0 < a := by
    intro a ha
    have haA : a ∈ A := by rw [← hL]; exact List.mem_toFinset.mpr ha
    exact Nat.pos_of_ne_zero (fun hz => hzero (hz ▸ haA))
  have hmaxL : ∀ a ∈ L, a ≤ n := by
    intro a ha
    exact hmax a (by rw [← hL]; exact List.mem_toFinset.mpr ha)
  have hb := bound L hneL hg hposL n m hmaxL hnm
  simpa [multiples, ← hL] using hb

/-- An inline suffix predicate implies the recursive structural condition.
This bridge avoids requiring two separately named recursive definitions to be
definitionally equal in a downstream statement verifier. -/
lemma good_of_suffix (L : List ℕ)
    (h : ∀ (pre : List ℕ) (a b : ℕ) (rest : List ℕ),
      L = pre ++ a :: b :: rest →
      ∀ c ∈ rest, Nat.lcm a b ∣ Nat.lcm a c) : Good L := by
  induction L with
  | nil => trivial
  | cons a tail ih =>
    cases tail with
    | nil => trivial
    | cons b rest =>
      constructor
      · apply ih
        intro pre u v xs heq c hc
        apply h (a :: pre) u v xs ?_ c hc
        simpa only [List.cons_append] using congrArg (List.cons a) heq
      · exact h [] a b rest rfl

/-- Canonical counting vocabulary with the ordering hypothesis written as a
nonrecursive suffix predicate. -/
theorem finset_suffix_bound (A : Finset ℕ) (hne : A.Nonempty) (hzero : 0 ∉ A)
    (hchain : ∃ L : List ℕ, L.toFinset = A ∧
      ∀ (pre : List ℕ) (a b : ℕ) (rest : List ℕ),
        L = pre ++ a :: b :: rest →
        ∀ c ∈ rest, Nat.lcm a b ∣ Nat.lcm a c)
    (n m : ℕ) (hmax : ∀ a ∈ A, a ≤ n) (hnm : n < m) :
    n * ((Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k)).card <
      2 * m * ((Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card := by
  obtain ⟨L, hL, hs⟩ := hchain
  exact finset_bound A hne hzero ⟨L, hL, good_of_suffix L hs⟩ n m hmax hnm

/-- Exponents are nondecreasing in the first coordinate and nonincreasing in
    the second. Repeated or redundant generators are allowed. -/
def Staircase (L : List (ℕ × ℕ)) : Prop :=
  L.Pairwise (fun u v => u.1 ≤ v.1 ∧ v.2 ≤ u.2)

def encode (p q : ℕ) (u : ℕ × ℕ) : ℕ := p ^ u.1 * q ^ u.2

lemma middle_dvd_lcm (p q : ℕ) (hpq : p.Coprime q) (u v w : ℕ × ℕ)
    (he : v.1 ≤ w.1) (hf : v.2 ≤ u.2) :
    encode p q v ∣ Nat.lcm (encode p q u) (encode p q w) := by
  have hp : p ^ v.1 ∣ encode p q w :=
    dvd_mul_of_dvd_left (pow_dvd_pow p he) (q ^ w.2)
  have hq : q ^ v.2 ∣ encode p q u :=
    dvd_mul_of_dvd_right (pow_dvd_pow q hf) (p ^ u.1)
  exact (hpq.pow v.1 v.2).mul_dvd_of_dvd_of_dvd
    (dvd_trans hp (Nat.dvd_lcm_right _ _))
    (dvd_trans hq (Nat.dvd_lcm_left _ _))

lemma staircase_good (p q : ℕ) (hpq : p.Coprime q)
    (L : List (ℕ × ℕ)) (hs : Staircase L) : Good (L.map (encode p q)) := by
  induction L with
  | nil => trivial
  | cons u tail ih =>
    cases tail with
    | nil => trivial
    | cons v rest =>
      have hparts := List.pairwise_cons.mp hs
      have htail := ih hparts.2
      change Good ((v :: rest).map (encode p q)) ∧ _
      refine ⟨htail, ?_⟩
      intro c hc
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hc
      have huv := hparts.1 v (by simp)
      have hvw := (List.pairwise_cons.mp hparts.2).1 w hw
      exact Nat.lcm_dvd (Nat.dvd_lcm_left _ _)
        (middle_dvd_lcm p q hpq u v w hvw.1 huv.2)

/-- Any-length exponent staircase over two positive coprime bases satisfies
    Erdős #488. In particular the bases may be two distinct primes. -/
theorem staircase_bound (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hpq : p.Coprime q) (L : List (ℕ × ℕ)) (hne : L ≠ [])
    (hs : Staircase L) (n m : ℕ)
    (hmax : ∀ u ∈ L, encode p q u ≤ n) (hnm : n < m) :
    n * (multiples (L.map (encode p q)) m).card <
      2 * m * (multiples (L.map (encode p q)) n).card := by
  apply bound (L.map (encode p q)) (by simpa using hne)
    (staircase_good p q hpq L hs) ?_ n m ?_ hnm
  · intro a ha
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ha
    exact Nat.mul_pos (pow_pos hp u.1) (pow_pos hq u.2)
  · intro a ha
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ha
    exact hmax u hu


end OrderedLCM

namespace TwoPrimeSupport
open Finset
open OrderedLCM

/-- Remove generators already generated by a different, smaller divisor. -/
def basis (A : Finset ℕ) : Finset ℕ :=
  A.filter (fun a => ∀ b ∈ A, b ∣ a → a = b)

lemma basis_subset (A : Finset ℕ) : basis A ⊆ A := filter_subset _ _

lemma basis_primitive (A : Finset ℕ) {a b : ℕ}
    (ha : a ∈ basis A) (hb : b ∈ basis A) (hab : a ∣ b) : a = b := by
  exact ((mem_filter.mp hb).2 a (basis_subset A ha) hab).symm

lemma exists_basis_divisor (A : Finset ℕ) (hzero : 0 ∉ A) {a : ℕ} (ha : a ∈ A) :
    ∃ b ∈ basis A, b ∣ a := by
  let S := A.filter (fun b => b ∣ a)
  have hS : S.Nonempty := ⟨a, mem_filter.mpr ⟨ha, dvd_refl a⟩⟩
  let b := S.min' hS
  have hbS : b ∈ S := min'_mem S hS
  obtain ⟨hbA, hba⟩ := mem_filter.mp hbS
  refine ⟨b, mem_filter.mpr ⟨hbA, ?_⟩, hba⟩
  intro c hcA hcb
  have hcS : c ∈ S := mem_filter.mpr ⟨hcA, dvd_trans hcb hba⟩
  have hbc : b ≤ c := min'_le S c hcS
  have hbpos : 0 < b := Nat.pos_of_ne_zero (fun hz => hzero (hz ▸ hbA))
  exact Nat.le_antisymm hbc (Nat.le_of_dvd hbpos hcb)

lemma basis_covers (A : Finset ℕ) (hzero : 0 ∉ A) (k : ℕ) :
    (∃ a ∈ basis A, a ∣ k) ↔ (∃ a ∈ A, a ∣ k) := by
  constructor
  · rintro ⟨a, ha, hak⟩
    exact ⟨a, basis_subset A ha, hak⟩
  · rintro ⟨a, ha, hak⟩
    obtain ⟨b, hb, hba⟩ := exists_basis_divisor A hzero ha
    exact ⟨b, hb, dvd_trans hba hak⟩

lemma basis_nonempty (A : Finset ℕ) (hne : A.Nonempty) (hzero : 0 ∉ A) :
    (basis A).Nonempty := by
  obtain ⟨a, ha⟩ := hne
  obtain ⟨b, hb, _⟩ := exists_basis_divisor A hzero ha
  exact ⟨b, hb⟩

lemma reverse_exponent (p q : ℕ) (hp : 0 < p) (hq : 1 < q)
    (B : Finset ℕ)
    (hprimitive : ∀ a ∈ B, ∀ b ∈ B, a ∣ b → a = b)
    (u v : ℕ × ℕ) (hu : encode p q u ∈ B) (hv : encode p q v ∈ B)
    (he : u.1 ≤ v.1) : v.2 ≤ u.2 := by
  by_contra h
  have hf : u.2 < v.2 := by omega
  have hd : encode p q u ∣ encode p q v :=
    Nat.mul_dvd_mul (pow_dvd_pow p he) (pow_dvd_pow q (Nat.le_of_lt hf))
  have heq := hprimitive _ hu _ hv hd
  have hlt : encode p q u < encode p q v :=
    Nat.mul_lt_mul_of_le_of_lt (Nat.pow_le_pow_right hp he)
      (pow_lt_pow_right₀ hq hf) (pow_pos hp v.1)
  exact (Nat.ne_of_lt hlt) heq

/-- Sorting exponent witnesses of a primitive generator set produces an
arbitrary-length staircase. No factorization uniqueness theorem is required. -/
theorem exists_staircase (p q : ℕ) (hp : 0 < p) (hq : 1 < q)
    (B : Finset ℕ) (hne : B.Nonempty)
    (hprimitive : ∀ a ∈ B, ∀ b ∈ B, a ∣ b → a = b)
    (hrep : ∀ a ∈ B, ∃ e f : ℕ, a = p ^ e * q ^ f) :
    ∃ L : List (ℕ × ℕ), L ≠ [] ∧ Staircase L ∧
      (L.map (encode p q)).toFinset = B := by
  classical
  let rep : {a : ℕ // a ∈ B} → ℕ × ℕ := fun a =>
    ⟨Classical.choose (hrep a.val a.property),
      Classical.choose (Classical.choose_spec (hrep a.val a.property))⟩
  have henc (a : {a : ℕ // a ∈ B}) : encode p q (rep a) = a.val := by
    exact (Classical.choose_spec (Classical.choose_spec (hrep a.val a.property))).symm
  let raw : List (ℕ × ℕ) := B.attach.toList.map rep
  have hraw (u : ℕ × ℕ) (hu : u ∈ raw) : encode p q u ∈ B := by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hu
    rw [henc]
    exact a.property
  let cmp : (ℕ × ℕ) → (ℕ × ℕ) → Bool := fun u v => decide (u.1 ≤ v.1)
  let L := raw.mergeSort cmp
  have hperm : L.Perm raw := List.mergeSort_perm raw cmp
  have hfirst : L.Pairwise (fun u v => u.1 ≤ v.1) := by
    have hsort := List.pairwise_mergeSort (le := cmp)
      (fun u v w huv hvw => by
        simpa [cmp] using (Nat.le_trans (by simpa [cmp] using huv)
          (by simpa [cmp] using hvw)))
      (fun u v => by simpa [cmp] using Nat.le_total u.1 v.1) raw
    simpa [L, cmp] using hsort
  have hstair : Staircase L := by
    apply List.Pairwise.imp_of_mem (p := hfirst)
    intro u v hu hv he
    exact ⟨he, reverse_exponent p q hp hq B hprimitive u v
      (hraw u (hperm.mem_iff.mp hu)) (hraw v (hperm.mem_iff.mp hv)) he⟩
  have hset : (L.map (encode p q)).toFinset = B := by
    ext a
    constructor
    · intro ha
      obtain ⟨u, hu, hea⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
      rw [← hea]
      exact hraw u (hperm.mem_iff.mp hu)
    · intro ha
      apply List.mem_toFinset.mpr
      refine List.mem_map.mpr ⟨rep ⟨a, ha⟩, ?_, henc ⟨a, ha⟩⟩
      apply hperm.mem_iff.mpr
      exact List.mem_map.mpr ⟨⟨a, ha⟩, by simp, rfl⟩
  refine ⟨L, ?_, hstair, hset⟩
  intro hL
  have he : B = ∅ := by simpa [hL] using hset.symm
  exact hne.ne_empty he

/-- A two-base-supported set admits an ordered generating basis contained in
it. Redundant original generators do not need to admit a Good ordering. -/
theorem exists_ordered_basis (p q : ℕ) (hp : 0 < p) (hq : 1 < q)
    (hpq : p.Coprime q) (A : Finset ℕ) (hne : A.Nonempty) (hzero : 0 ∉ A)
    (hrep : ∀ a ∈ A, ∃ e f : ℕ, a = p ^ e * q ^ f) :
    ∃ L : List ℕ, L ≠ [] ∧ Good L ∧ (∀ a ∈ L, a ∈ A) ∧
      ∀ k : ℕ, (∃ a ∈ L, a ∣ k) ↔ (∃ a ∈ A, a ∣ k) := by
  obtain ⟨E, hEne, hEstair, hEset⟩ := exists_staircase p q hp hq (basis A)
    (basis_nonempty A hne hzero)
    (fun a ha b hb hab => basis_primitive A ha hb hab)
    (fun a ha => hrep a (basis_subset A ha))
  refine ⟨E.map (encode p q), by simpa using hEne,
    staircase_good p q hpq E hEstair, ?_, ?_⟩
  · intro a ha
    apply basis_subset A
    rw [← hEset]
    exact List.mem_toFinset.mpr ha
  · intro k
    have hmem : (∃ a ∈ E.map (encode p q), a ∣ k) ↔
        (∃ a ∈ basis A, a ∣ k) := by
      rw [← hEset]
      simp only [List.mem_toFinset]
    exact hmem.trans (basis_covers A hzero k)

/-- The root inequality for every finite set supported on two fixed positive
coprime bases (the second base exceeds1), without a primitiveness assumption. -/
theorem two_coprime_bases (p q : ℕ) (hp : 0 < p) (hq : 1 < q)
    (hpq : p.Coprime q) (A : Finset ℕ) (hne : A.Nonempty) (hzero : 0 ∉ A)
    (hrep : ∀ a ∈ A, ∃ e f : ℕ, a = p ^ e * q ^ f)
    (n m : ℕ) (hmax : ∀ a ∈ A, a ≤ n) (hnm : n < m) :
    n * ((Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k)).card <
      2 * m * ((Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card := by
  obtain ⟨L, hLne, hGood, hsub, hcover⟩ :=
    exists_ordered_basis p q hp hq hpq A hne hzero hrep
  have hpos : ∀ a ∈ L, 0 < a := by
    intro a ha
    exact Nat.pos_of_ne_zero (fun hz => hzero (hz ▸ hsub a ha))
  have hb := OrderedLCM.bound L hLne hGood hpos n m
    (fun a ha => hmax a (hsub a ha)) hnm
  simpa [multiples, hcover] using hb

/-- Every finite set of products of powers of two fixed distinct primes
satisfies Erdős #488, with arbitrary cardinality and redundant generators. -/
theorem two_primes (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (A : Finset ℕ) (hne : A.Nonempty) (hzero : 0 ∉ A)
    (hrep : ∀ a ∈ A, ∃ e f : ℕ, a = p ^ e * q ^ f)
    (n m : ℕ) (hmax : ∀ a ∈ A, a ≤ n) (hnm : n < m) :
    n * ((Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k)).card <
      2 * m * ((Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card := by
  exact two_coprime_bases p q hp.pos hq.one_lt
    ((Nat.coprime_primes hp hq).mpr hpq) A hne hzero hrep n m hmax hnm

/-- The motivating redundant set reduces to the expected generating basis. -/
theorem example_basis : basis {16,36,81,216} = {16,36,81} := by decide

theorem example_representation :
    ∀ a ∈ ({16,36,81,216} : Finset ℕ), ∃ e f : ℕ, a = 2 ^ e * 3 ^ f := by
  intro a ha
  simp only [mem_insert, mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · exact ⟨4, 0, by decide⟩
  · exact ⟨2, 2, by decide⟩
  · exact ⟨0, 4, by decide⟩
  · exact ⟨3, 3, by decide⟩


end TwoPrimeSupport

/-- Arbitrary finite sets supported on two fixed coprime bases. -/
theorem proof : ∀ p q : ℕ, 0 < p → 1 < q → p.Coprime q →
    ∀ A : Finset ℕ, A.Nonempty → 0 ∉ A →
    (∀ a ∈ A, ∃ e f : ℕ, a = p ^ e * q ^ f) → ∀ n m : ℕ,
    (∀ a ∈ A, a ≤ n) → n < m →
    n * ((Finset.Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k)).card <
      2 * m * ((Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card := by
  exact TwoPrimeSupport.two_coprime_bases

end Submissions.ErdosMultiplesTwoBases.Support
