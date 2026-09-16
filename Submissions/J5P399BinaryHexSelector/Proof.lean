import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Finite

/- Standalone partial proposal preserving the saved turn168 arithmetic proof.
No graph realization, full-root result, novelty, or publication validation is claimed.
Original source has no explicit license header; see CREDIT.md for pending review. -/
namespace Submissions.J5P399BinaryHexSelector.Proof

/- Generic arithmetic core of turn167. This file does not prove the graph
construction, Rubin's block lemma, or the unrestricted Jig399 root. -/
namespace BinaryHexSpectrum

def sign (b : Bool) : Int := if b then 1 else -1
def bit (b : Bool) : Int := if b then 1 else 0
def edgeCost (s a b : Bool) : Int := if a = b then 0 else sign s
def branch (l p : Bool) : Int := 1 + (sign l + sign p) / 2

/-- Twice the signed cost of the selected bits, with the final bit fixed false.
Malformed lengths return zero and are excluded in `Attains`. -/
def energy : Bool → List Bool → List Bool → Int
  | prev, s :: ss, b :: bs => 2 * bit b + edgeCost s prev b + energy b ss bs
  | prev, [s], [] => edgeCost s prev false
  | _, _, _ => 0

def Attains (l : Bool) (mid : List Bool) (r : Bool) (z : Int) : Prop :=
  ∃ bs : List Bool, bs.length = mid.length + 1 ∧
    energy false (l :: (mid ++ [r])) bs = 2 * z

def Shape (n : Int) (l r ap am : Bool) (z : Int) : Prop :=
  0 ≤ z ∧ z ≤ n + (sign l + sign r) / 2 ∧
  ((l = true ∧ r = true ∧ ap = true) → z ≠ 1) ∧
  ((l = true ∧ r = true ∧ am = true) → z ≠ n)

theorem shape_step (n z : Int) (l p r ap am : Bool)
    (hn : 1 ≤ n) (hc : (ap = true ∧ am = true) ↔ n = 1) :
    Shape (n + 1) l r (p && ap) ((!p) && am) z ↔
      Shape n p r ap am z ∨
      Shape n (!p) r ap am (z - branch l p) := by
  cases l <;> cases p <;> cases r <;> cases ap <;> cases am <;>
    simp_all [Shape, sign, branch] <;> omega

theorem false_step (l p : Bool) (tail bs : List Bool) :
    energy false (l :: p :: tail) (false :: bs) = energy false (p :: tail) bs := by
  simp [energy, bit, edgeCost]

theorem true_step (l p b : Bool) (tail bs : List Bool) :
    energy false (l :: p :: tail) (true :: b :: bs) =
      2 * branch l p + energy false ((!p) :: tail) (b :: bs) := by
  cases l <;> cases p <;> cases b <;>
    simp [energy, bit, edgeCost, sign, branch] <;> omega

theorem attains_nil (l r : Bool) (z : Int) :
    Attains l [] r z ↔ z = 0 ∨ z = branch l r := by
  constructor
  · rintro ⟨bs, hb, he⟩
    cases bs with
    | nil => simp at hb
    | cons b bs =>
      have hnil : bs = [] := by simpa using hb
      subst bs
      cases l <;> cases r <;> cases b <;>
        simp [energy, bit, edgeCost, sign] at he <;>
        simp [branch, sign] <;> omega
  · intro hz
    rcases hz with rfl | rfl
    · exact ⟨[false], by simp, by simp [energy, bit, edgeCost]⟩
    · refine ⟨[true], by simp, ?_⟩
      cases l <;> cases r <;> simp [energy, bit, edgeCost, sign, branch]

theorem attains_cons (l p r : Bool) (mid : List Bool) (z : Int) :
    Attains l (p :: mid) r z ↔
      Attains p mid r z ∨ Attains (!p) mid r (z - branch l p) := by
  constructor
  · rintro ⟨bs, hb, he⟩
    cases bs with
    | nil => simp at hb
    | cons b bs =>
      have hlen : bs.length = mid.length + 1 := by simpa using hb
      cases b with
      | false =>
        left
        refine ⟨bs, hlen, ?_⟩
        simpa only [List.cons_append, false_step] using he
      | true =>
        right
        refine ⟨bs, hlen, ?_⟩
        cases bs with
        | nil => simp at hlen
        | cons c cs =>
          simp only [List.cons_append, true_step] at he
          omega
  · intro h
    rcases h with ⟨bs, hb, he⟩ | ⟨bs, hb, he⟩
    · refine ⟨false :: bs, by simpa using hb, ?_⟩
      simpa only [List.cons_append, false_step] using he
    · refine ⟨true :: bs, by simpa using hb, ?_⟩
      cases bs with
      | nil => simp at hb
      | cons c cs =>
        simp only [List.cons_append, true_step]
        omega

theorem all_compat (mid : List Bool) :
    (mid.all id = true ∧ mid.all Bool.not = true) ↔
      (mid.length : Int) + 1 = 1 := by
  cases mid with
  | nil => simp
  | cons b bs =>
    cases b <;> simp <;> omega

/-- Exact spectrum for arbitrary length and arbitrary signs, with an actual
bit-list witness and a separately defined signed boundary cost. -/
theorem attains_iff (l r : Bool) (mid : List Bool) (z : Int) :
    Attains l mid r z ↔
      Shape ((mid.length : Int) + 1) l r (mid.all id) (mid.all Bool.not) z := by
  induction mid generalizing l r z with
  | nil =>
    rw [attains_nil]
    cases l <;> cases r <;> simp [Shape, sign, branch] <;> omega
  | cons p mid ih =>
    rw [attains_cons, ih, ih]
    have hs := shape_step ((mid.length : Int) + 1) z l p r
      (mid.all id) (mid.all Bool.not) (by omega) (all_compat mid)
    simpa using hs.symm

def falseCount : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 0 else 1) + falseCount bs

def negativeTotal (l r : Bool) (mid : List Bool) : Nat :=
  (if l then 0 else 1) + falseCount mid + (if r then 0 else 1)

theorem falseCount_le (mid : List Bool) : falseCount mid ≤ mid.length := by
  induction mid with
  | nil => simp [falseCount]
  | cons b bs ih => cases b <;> simp [falseCount] <;> omega

theorem falseCount_zero (mid : List Bool) (h : mid.all id = true) :
    falseCount mid = 0 := by
  induction mid with
  | nil => rfl
  | cons b bs ih => cases b <;> simp_all [falseCount]

theorem falseCount_full (mid : List Bool) (h : mid.all Bool.not = true) :
    falseCount mid = mid.length := by
  induction mid with
  | nil => rfl
  | cons b bs ih => cases b <;> simp_all [falseCount, Nat.add_comm]

theorem negativeTotal_le (l r : Bool) (mid : List Bool) :
    negativeTotal l r mid ≤ mid.length + 2 := by
  have h := falseCount_le mid
  cases l <;> cases r <;> simp [negativeTotal] <;> omega

theorem even_power (k : Nat) (hk : 1 ≤ k) : (2^k : Nat) % 2 = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  simp [pow_succ]

/-- The first power at or above an even m≥4 is either m or at most 2m−4. -/
theorem near_power (m : Nat) (hm : 4 ≤ m) (heven : m % 2 = 0) :
    ∃ k : Nat, 2 ≤ k ∧ m ≤ 2^k ∧ (2^k = m ∨ 2^k ≤ 2*m-4) := by
  have hex : ∃ k : Nat, m ≤ 2^k := ⟨m, Nat.le_of_lt Nat.lt_two_pow_self⟩
  let k := Nat.find hex
  have hspec : m ≤ 2^k := Nat.find_spec hex
  have hk : 2 ≤ k := by
    by_contra hn
    have hc : k = 0 ∨ k = 1 := by omega
    rcases hc with h | h <;> simp [h] at hspec <;> omega
  refine ⟨k, hk, hspec, ?_⟩
  by_cases heq : 2^k = m
  · exact Or.inl heq
  · right
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    have hprev : 2^j < m := by
      have hnot := Nat.find_min hex (show j < Nat.find hex by dsimp [k] at hj; omega)
      omega
    have hjeven := even_power j (by omega)
    have hp : 2^k = 2^j * 2 := by rw [hj, pow_succ]
    omega

def baseLength (l r : Bool) (mid : List Bool) : Nat :=
  mid.length + 2 + negativeTotal l r mid

theorem ordinary_power_shape (l r : Bool) (mid : List Bool) (P : Nat)
    (hg : 4 ≤ mid.length + 2)
    (hm : baseLength l r mid % 2 = 0) (hp : P % 2 = 0)
    (hlow : baseLength l r mid ≤ P) (hhigh : P ≤ 2*baseLength l r mid-4)
    (hbad : ¬(l = true ∧ r = true ∧ mid.all id = true ∧ P = baseLength l r mid + 2)) :
    Shape ((mid.length : Int)+1) l r (mid.all id) (mid.all Bool.not)
      (((P-baseLength l r mid)/2 : Nat) : Int) := by
  have hcount := negativeTotal_le l r mid
  have hlin : baseLength l r mid + 2*((P-baseLength l r mid)/2) = P := by omega
  refine ⟨by omega, ?_, ?_, ?_⟩
  · cases l <;> cases r <;> simp [sign] <;> dsimp [baseLength] at * <;> omega
  · rintro ⟨hl, hr, ha⟩ hz
    exact hbad ⟨hl, hr, ha, by omega⟩
  · rintro ⟨hl, hr, ha⟩ hz
    subst l; subst r
    have hc := falseCount_full mid ha
    simp [baseLength, negativeTotal, hc] at hz hlin hhigh
    omega

/-- A dyadic total length with the first cell fixed short. `energy` is the
actual signed bit/boundary cost, not an assumed interval oracle. -/
theorem exists_dyadic_energy (l r : Bool) (mid : List Bool)
    (hg : 4 ≤ mid.length + 2) (heven : baseLength l r mid % 2 = 0) :
    ∃ k : Nat, 2 ≤ k ∧ ∃ bs : List Bool,
      bs.length = mid.length+1 ∧
      (baseLength l r mid : Int) + energy false (l :: (mid ++ [r])) bs = (2^k : Nat) := by
  have hm : 4 ≤ baseLength l r mid := by dsimp [baseLength]; omega
  obtain ⟨k, hk, hlow, heq | hhigh⟩ := near_power (baseLength l r mid) hm heven
  · have hz : Attains l mid r 0 := by
      apply (attains_iff l r mid 0).mpr
      cases l <;> cases r <;> simp [Shape, sign] <;> omega
    obtain ⟨bs, hb, he⟩ := hz
    refine ⟨k, hk, bs, hb, ?_⟩
    simp [he, heq]
  · have hp := even_power k (by omega)
    by_cases hbad : l = true ∧ r = true ∧ mid.all id = true ∧ 2^k = baseLength l r mid + 2
    · rcases hbad with ⟨hl, hr, ha, hpow⟩
      subst l; subst r
      have hc := falseCount_zero mid ha
      have hmval : baseLength true true mid = mid.length+2 := by simp [baseLength, negativeTotal, hc]
      have hpow' : 2^(k+1) = 2*(mid.length+2)+4 := by rw [pow_succ, hpow, hmval]; omega
      let q := (2^(k+1)-baseLength true true mid)/2
      have hp' := even_power (k+1) (by omega)
      have hlin : baseLength true true mid + 2*q = 2^(k+1) := by dsimp [q]; omega
      have hz : Attains true mid true (q : Int) := by
        apply (attains_iff true true mid (q : Int)).mpr
        have hcompat := all_compat mid
        refine ⟨by omega, ?_, ?_, ?_⟩
        · simp [sign]
          omega
        · intro _
          omega
        · rintro ⟨_, _, hminus⟩ _
          have : (mid.length : Int)+1=1 := hcompat.mp ⟨ha,hminus⟩
          omega
      obtain ⟨bs, hb, he⟩ := hz
      refine ⟨k+1, by omega, bs, hb, ?_⟩
      omega
    · have hs := ordinary_power_shape l r mid (2^k) hg heven hp hlow hhigh hbad
      obtain ⟨bs, hb, he⟩ := (attains_iff l r mid _).mpr hs
      have hlin : baseLength l r mid + 2*((2^k-baseLength l r mid)/2) = 2^k := by omega
      refine ⟨k, hk, bs, hb, ?_⟩
      omega

def changes (prev last : Bool) : List Bool → Nat
  | [] => if prev = last then 0 else 1
  | a :: as => (if prev = a then 0 else 1) + changes a last as

def signs (prev last : Bool) : List Bool → List Bool
  | [] => [decide (prev = last)]
  | a :: as => decide (prev = a) :: signs a last as

def ones : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + ones bs

def xorBits : List Bool → List Bool → List Bool
  | a :: as, b :: bs => Bool.xor a b :: xorBits as bs
  | _, _ => []

theorem signs_length (prev last : Bool) (as : List Bool) :
    (signs prev last as).length = as.length+1 := by
  induction as generalizing prev with
  | nil => rfl
  | cons a as ih => simp [signs, ih]

theorem falseCount_append (as bs : List Bool) :
    falseCount (as ++ bs) = falseCount as + falseCount bs := by
  induction as with
  | nil => simp [falseCount]
  | cons a as ih => cases a <;> simp [falseCount, ih, Nat.add_assoc]

theorem falseCount_signs (prev last : Bool) (as : List Bool) :
    falseCount (signs prev last as) = changes prev last as := by
  induction as generalizing prev with
  | nil => cases prev <;> cases last <;> rfl
  | cons a as ih => cases prev <;> cases a <;> simp [signs, falseCount, changes, ih]

theorem changes_parity (prev last : Bool) (as : List Bool) :
    changes prev last as % 2 = if prev = last then 0 else 1 := by
  induction as generalizing prev with
  | nil => cases prev <;> cases last <;> rfl
  | cons a as ih =>
    have h := ih a
    cases prev <;> cases a <;> cases last <;> simp [changes] at * <;> omega

/-- The signed energy is exactly the change in actual rail switches, plus
twice the number of chosen long paths. -/
theorem energy_changes (prev last bp : Bool) (as bs : List Bool)
    (hlen : as.length = bs.length) :
    energy bp (signs prev last as) bs =
      2*(ones bs : Int) + (changes (Bool.xor prev bp) last (xorBits as bs) : Int) -
        (changes prev last as : Int) := by
  induction as generalizing prev bp bs with
  | nil =>
    have : bs = [] := by simpa using hlen.symm
    subst bs
    cases prev <;> cases last <;> cases bp <;>
      simp [signs, energy, edgeCost, sign, ones, xorBits, changes]
  | cons a as ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      have hsmall : as.length = bs.length := by simpa using hlen
      have h := ih a b bs hsmall
      cases prev <;> cases a <;> cases bp <;> cases b <;>
        simp [signs, energy, bit, edgeCost, sign, ones, xorBits, changes] at h ⊢ <;> omega

theorem exists_dyadic_signs (ss : List Bool) (hg : 4 ≤ ss.length)
    (heven : (ss.length + falseCount ss) % 2 = 0) :
    ∃ k : Nat, 2 ≤ k ∧ ∃ bs : List Bool,
      bs.length+1 = ss.length ∧
      ((ss.length + falseCount ss : Nat) : Int) + energy false ss bs = (2^k : Nat) := by
  cases ss with
  | nil => simp at hg
  | cons l rest =>
    rcases List.eq_nil_or_concat' rest with hnil | ⟨mid,r,h⟩
    · subst rest; simp at hg
    · subst rest
      have hbase : baseLength l r mid =
          (l :: (mid ++ [r])).length + falseCount (l :: (mid ++ [r])) := by
        simp [baseLength, negativeTotal, falseCount, falseCount_append, Nat.add_assoc]
      have hg' : 4 ≤ mid.length+2 := by simpa using hg
      have hev : baseLength l r mid % 2 = 0 := by rwa [hbase]
      obtain ⟨k,hk,bs,hb,he⟩ := exists_dyadic_energy l r mid hg' hev
      refine ⟨k,hk,bs,?_,?_⟩
      · simpa using congrArg (fun x : Nat => x+1) hb
      · simpa only [hbase] using he

/-- For every even cyclic short-side word of length at least four there is
a power-of-two winding length with cell zero fixed short. `bs` contains
the remaining long/short choices. The later graph bridge must prove that
the corresponding word is an actual simple cycle. -/
theorem exists_dyadic_selector (a0 : Bool) (as : List Bool)
    (hg : 4 ≤ as.length+1) (heven : (as.length+1) % 2 = 0) :
    ∃ k : Nat, 2 ≤ k ∧ ∃ bs : List Bool,
      bs.length = as.length ∧
      as.length+1 + 2*ones bs + changes a0 a0 (xorBits as bs) = 2^k := by
  have hs := signs_length a0 a0 as
  have hc := falseCount_signs a0 a0 as
  have hp := changes_parity a0 a0 as
  have hev : ((signs a0 a0 as).length + falseCount (signs a0 a0 as)) % 2 = 0 := by
    rw [hs, hc]
    have hp0 : changes a0 a0 as % 2 = 0 := by simpa using hp
    omega
  obtain ⟨k,hk,bs,hb,he⟩ := exists_dyadic_signs (signs a0 a0 as) (by omega) hev
  have hlen : as.length = bs.length := by omega
  have hcost := energy_changes a0 a0 false as bs hlen
  simp only [Bool.xor_false] at hcost
  simp only [hs, hc] at he
  refine ⟨k,hk,bs,by omega,?_⟩
  omega

end BinaryHexSpectrum

/- Proposed representation bridge only. The saved arithmetic theorem above is unchanged.
These proof scripts and the new common interface have not been compiled. -/
namespace Publication

def changes (prev last : Bool) (as : List Bool) : Nat :=
  (as.foldr (fun (a : Bool) (f : Bool → Nat) (p : Bool) =>
    (if p = a then 0 else 1) + f a)
    (fun (p : Bool) => if p = last then 0 else 1)) prev

def ones (bs : List Bool) : Nat :=
  bs.foldr (fun (b : Bool) (n : Nat) => (if b then 1 else 0) + n) 0

def xorBits (as bs : List Bool) : List Bool :=
  List.zipWith Bool.xor as bs

end Publication

theorem publication_changes_eq (prev last : Bool) (as : List Bool) :
    BinaryHexSpectrum.changes prev last as = Publication.changes prev last as := by
  induction as generalizing prev with
  | nil => simp only [BinaryHexSpectrum.changes, Publication.changes, List.foldr_nil]
  | cons a as ih =>
    simpa only [BinaryHexSpectrum.changes, Publication.changes, List.foldr_cons] using
      congrArg (fun n : Nat => (if prev = a then 0 else 1) + n) (ih a)

theorem publication_ones_eq (bs : List Bool) :
    BinaryHexSpectrum.ones bs = Publication.ones bs := by
  induction bs with
  | nil => simp only [BinaryHexSpectrum.ones, Publication.ones, List.foldr_nil]
  | cons b bs ih =>
    simpa only [BinaryHexSpectrum.ones, Publication.ones, List.foldr_cons] using
      congrArg (fun n : Nat => (if b then 1 else 0) + n) ih

theorem publication_xorBits_eq (as bs : List Bool) :
    BinaryHexSpectrum.xorBits as bs = Publication.xorBits as bs := by
  induction as generalizing bs with
  | nil => simp only [BinaryHexSpectrum.xorBits, Publication.xorBits, List.zipWith_nil_left]
  | cons a as ih =>
    cases bs with
    | nil => simp only [BinaryHexSpectrum.xorBits, Publication.xorBits, List.zipWith_nil_right]
    | cons b bs =>
      simpa only [BinaryHexSpectrum.xorBits, Publication.xorBits, List.zipWith_cons_cons] using
        congrArg (fun cs : List Bool => Bool.xor a b :: cs) (ih bs)

theorem proof (a0 : Bool) (as : List Bool)
    (hg : 4 ≤ as.length+1) (heven : (as.length+1) % 2 = 0) :
    ∃ k : Nat, 2 ≤ k ∧ ∃ bs : List Bool,
      bs.length = as.length ∧
      as.length+1 + 2*Publication.ones bs +
        Publication.changes a0 a0 (Publication.xorBits as bs) = 2^k := by
  simpa only [publication_ones_eq, publication_changes_eq, publication_xorBits_eq] using
    BinaryHexSpectrum.exists_dyadic_selector a0 as hg heven

end Submissions.J5P399BinaryHexSelector.Proof
