import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

set_option linter.style.header false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


/- Amalgamated from Transducer.lean. -/

namespace Hilbert193

inductive Digit where
  | d0 | d1 | d2 | d3
  deriving DecidableEq, Repr

inductive Bit where
  | zero | one
  deriving DecidableEq, Repr

namespace Bit

def xor : Bit → Bit → Bit
  | zero, b => b
  | one, zero => one
  | one, one => zero

@[simp] theorem zero_xor (b : Bit) : xor zero b = b := by cases b <;> rfl
@[simp] theorem one_xor_zero : xor one zero = one := rfl
@[simp] theorem one_xor_one : xor one one = zero := rfl
@[simp] theorem xor_self (b : Bit) : xor b b = zero := by cases b <;> rfl
@[simp] theorem xor_zero (b : Bit) : xor b zero = b := by cases b <;> rfl
@[simp] theorem xor_assoc (a b c : Bit) : xor (xor a b) c = xor a (xor b c) := by
  cases a <;> cases b <;> cases c <;> rfl
@[simp] theorem xor_comm (a b : Bit) : xor a b = xor b a := by cases a <;> cases b <;> rfl

def toNat : Bit → ℕ
  | zero => 0
  | one => 1

end Bit

abbrev BitPair := Bit × Bit

/-- A square symmetry: optional coordinate swap, then coordinate complements. -/
structure Orient where
  swap : Bit
  bx : Bit
  cy : Bit
  deriving DecidableEq, Repr

namespace Orient

def choose (s a b : Bit) : Bit := if s = Bit.zero then a else b

def act (g : Orient) (p : BitPair) : BitPair :=
  (Bit.xor (choose g.swap p.1 p.2) g.bx,
   Bit.xor (choose g.swap p.2 p.1) g.cy)

/-- `compose g h` means apply `h`, then apply `g`. -/
def compose (g h : Orient) : Orient where
  swap := Bit.xor g.swap h.swap
  bx := Bit.xor (choose g.swap h.bx h.cy) g.bx
  cy := Bit.xor (choose g.swap h.cy h.bx) g.cy

abbrev I : Orient := ⟨.zero, .zero, .zero⟩
abbrev X : Orient := ⟨.zero, .one, .zero⟩
abbrev Y : Orient := ⟨.zero, .zero, .one⟩
abbrev C : Orient := ⟨.zero, .one, .one⟩
abbrev S : Orient := ⟨.one, .zero, .zero⟩
abbrev R : Orient := ⟨.one, .one, .zero⟩
abbrev L : Orient := ⟨.one, .zero, .one⟩
abbrev T : Orient := ⟨.one, .one, .one⟩

@[simp] theorem act_I (p : BitPair) : act I p = p := by rcases p with ⟨x,y⟩; cases x <;> cases y <;> rfl
@[simp] theorem compose_I_left (g : Orient) : compose I g = g := by rcases g with ⟨s,x,y⟩; cases s <;> cases x <;> cases y <;> rfl
@[simp] theorem compose_I_right (g : Orient) : compose g I = g := by rcases g with ⟨s,x,y⟩; cases s <;> cases x <;> cases y <;> rfl

theorem act_compose (g h : Orient) (p : BitPair) : act (compose g h) p = act g (act h p) := by
  rcases g with ⟨gs,gx,gy⟩
  rcases h with ⟨hs,hx,hy⟩
  rcases p with ⟨x,y⟩
  cases gs <;> cases gx <;> cases gy <;> cases hs <;> cases hx <;> cases hy <;>
    cases x <;> cases y <;> rfl

theorem compose_assoc (g h k : Orient) : compose (compose g h) k = compose g (compose h k) := by
  rcases g with ⟨gs,gx,gy⟩
  rcases h with ⟨hs,hx,hy⟩
  rcases k with ⟨ks,kx,ky⟩
  cases gs <;> cases gx <;> cases gy <;> cases hs <;> cases hx <;> cases hy <;>
    cases ks <;> cases kx <;> cases ky <;> rfl

end Orient

open Orient

def child : Digit → BitPair
  | .d0 => (.zero, .zero)
  | .d1 => (.zero, .one)
  | .d2 => (.one, .one)
  | .d3 => (.one, .zero)

def refinement : Digit → Orient
  | .d0 => S
  | .d1 => I
  | .d2 => I
  | .d3 => T

def emit (state : Orient) (d : Digit) : BitPair := state.act (child d)
def next (state : Orient) (d : Digit) : Orient := state.compose (refinement d)

/-- One complete literal transducer row, ordered by digits 0,1,2,3. -/
def row (state : Orient) : List (BitPair × Orient) :=
  [(.d0),(.d1),(.d2),(.d3)].map fun d => (emit state d, next state d)

/-- The exact eight rows printed in the research memo. -/
theorem complete_table :
    row I = [((.zero,.zero),S),((.zero,.one),I),((.one,.one),I),((.one,.zero),T)] ∧
    row X = [((.one,.zero),R),((.one,.one),X),((.zero,.one),X),((.zero,.zero),L)] ∧
    row Y = [((.zero,.one),L),((.zero,.zero),Y),((.one,.zero),Y),((.one,.one),R)] ∧
    row C = [((.one,.one),T),((.one,.zero),C),((.zero,.zero),C),((.zero,.one),S)] ∧
    row S = [((.zero,.zero),I),((.one,.zero),S),((.one,.one),S),((.zero,.one),C)] ∧
    row R = [((.one,.zero),X),((.zero,.zero),R),((.zero,.one),R),((.one,.one),Y)] ∧
    row L = [((.zero,.one),Y),((.one,.one),L),((.one,.zero),L),((.zero,.zero),X)] ∧
    row T = [((.one,.one),C),((.zero,.one),T),((.zero,.zero),T),((.one,.zero),I)] := by
  decide

@[simp] theorem refinement_involution (d : Digit) :
    (refinement d).compose (refinement d) = I := by cases d <;> decide

@[simp] theorem refinement_fixes_child (d : Digit) :
    (refinement d).act (child d) = child d := by cases d <;> decide

/-- Reverse one labeled transition exactly. -/
theorem reverse_transition (g h : Orient) (d : Digit) (hh : next g d = h) :
    g = h.compose (refinement d) := by
  subst h
  symm
  calc
    (next g d).compose (refinement d) =
        (g.compose (refinement d)).compose (refinement d) := rfl
    _ = g.compose ((refinement d).compose (refinement d)) := Orient.compose_assoc _ _ _
    _ = g := by rw [refinement_involution, Orient.compose_I_right]

/-- The emitted bits can be read from the outgoing orientation. -/
theorem backward_emit (g : Orient) (d : Digit) : emit g d = emit (next g d) d := by
  simp only [emit, next, Orient.act_compose, refinement_fixes_child]

/-- Forward transduction of a most-significant-first digit word. -/
def run : Orient → List Digit → List BitPair × Orient
  | s, [] => ([], s)
  | s, d :: ds =>
      let tail := run (next s d) ds
      (emit s d :: tail.1, tail.2)

def terminal (ds : List Digit) : Orient := (run I ds).2

def bitValue (bits : List Bit) : ℕ := bits.foldl (fun n b => 2*n + b.toNat) 0

def coordinate (ds : List Digit) : ℕ × ℕ :=
  let bits := (run I ds).1
  (bitValue (bits.map Prod.fst), bitValue (bits.map Prod.snd))

@[simp] theorem run_nil (s : Orient) : run s [] = ([],s) := rfl

/-- Two leading zero digits add two zero output bits and restore the initial state. -/
theorem even_zero_padding (ds : List Digit) :
    run I (.d0 :: .d0 :: ds) =
      let tail := run I ds
      ((.zero,.zero) :: (.zero,.zero) :: tail.1, tail.2) := by
  have hSS : S.compose S = I := by decide
  simp [run, next, emit, child, refinement, Orient.act, Orient.choose, hSS]

/-- Counts of digits 0 and 3 modulo two, represented as a reachable orientation. -/
def parityState (ds : List Digit) : Orient :=
  ds.foldl (fun s d => next s d) I

theorem run_terminal (s : Orient) (ds : List Digit) :
    (run s ds).2 = ds.foldl (fun state d => next state d) s := by
  induction ds generalizing s with
  | nil => rfl
  | cons d ds ih => simp [run, ih]

/-- Contribution of one digit to the two terminal parities `(number of 0s, number of 3s)`. -/
def digitParity : Digit → BitPair
  | .d0 => (.one, .zero)
  | .d1 => (.zero, .zero)
  | .d2 => (.zero, .zero)
  | .d3 => (.zero, .one)

def xorPair (a b : BitPair) : BitPair := (Bit.xor a.1 b.1, Bit.xor a.2 b.2)

def wordParity : List Digit → BitPair
  | [] => (.zero, .zero)
  | d :: ds => xorPair (digitParity d) (wordParity ds)

def orientOfParity : BitPair → Orient
  | (.zero, .zero) => I
  | (.one, .zero) => S
  | (.zero, .one) => T
  | (.one, .one) => C

theorem refinement_eq_orientParity (d : Digit) :
    refinement d = orientOfParity (digitParity d) := by cases d <;> rfl

theorem orientOfParity_xor (a b : BitPair) :
    orientOfParity (xorPair a b) = (orientOfParity a).compose (orientOfParity b) := by
  rcases a with ⟨a₀,a₃⟩
  rcases b with ⟨b₀,b₃⟩
  cases a₀ <;> cases a₃ <;> cases b₀ <;> cases b₃ <;> decide

theorem run_state_parity (s : Orient) (ds : List Digit) :
    (run s ds).2 = s.compose (orientOfParity (wordParity ds)) := by
  induction ds generalizing s with
  | nil => simp [run, wordParity, orientOfParity]
  | cons d ds ih =>
      rw [show (run s (d :: ds)).2 = (run (next s d) ds).2 by rfl, ih]
      simp only [next, refinement_eq_orientParity, wordParity, orientOfParity_xor]
      rw [Orient.compose_assoc]

/-- The terminal state is exactly the two parities of complete digit counts. -/
theorem terminal_statistic (ds : List Digit) :
    terminal ds = orientOfParity (wordParity ds) := by
  rw [terminal, run_state_parity, Orient.compose_I_left]

theorem wordParity_append (a b : List Digit) :
    wordParity (a ++ b) = xorPair (wordParity a) (wordParity b) := by
  induction a with
  | nil =>
      change wordParity b = xorPair (.zero,.zero) (wordParity b)
      generalize wordParity b = p
      rcases p with ⟨x,y⟩
      cases x <;> cases y <;> decide
  | cons d ds ih =>
      simp only [List.cons_append, wordParity, ih]
      rcases digitParity d with ⟨a₁,a₂⟩
      rcases wordParity ds with ⟨b₁,b₂⟩
      rcases wordParity b with ⟨c₁,c₂⟩
      cases a₁ <;> cases a₂ <;> cases b₁ <;> cases b₂ <;>
        cases c₁ <;> cases c₂ <;> decide

/-- Two low base-4 digits that cancel a prescribed terminal parity. -/
def steeringDigits : BitPair → List Digit
  | (.zero, .zero) => [.d1, .d1]
  | (.one, .zero) => [.d0, .d1]
  | (.zero, .one) => [.d3, .d1]
  | (.one, .one) => [.d0, .d3]

/-- Appending the two steering digits sends every word to terminal state `I`. -/
theorem terminal_steered (ds : List Digit) :
    terminal (ds ++ steeringDigits (wordParity ds)) = I := by
  rw [terminal_statistic, wordParity_append]
  generalize hp : wordParity ds = p
  rcases p with ⟨p₀,p₃⟩
  cases p₀ <;> cases p₃ <;> decide

@[simp] theorem terminal_eq_parityState (ds : List Digit) : terminal ds = parityState ds := by
  simp [terminal, parityState, run_terminal]

end Hilbert193


/- Amalgamated from Valuation.lean. -/

namespace Hilbert193

abbrev Vec2 := ℤ × ℤ

/-- The ordinary 2-adic order on a nonzero integer coordinate. -/
def coordVal (z : ℤ) : ℕ := padicValNat 2 z.natAbs

/-- The pair valuation from the Hilbert low-digit mismatch table.
Zero coordinates are treated as having infinite order by handling them separately. -/
def pairVal (u : Vec2) : ℕ :=
  if u.1 = 0 then
    if u.2 = 0 then 0 else 2 * coordVal u.2
  else if u.2 = 0 then
    2 * coordVal u.1
  else
    2 * min (coordVal u.1) (coordVal u.2) +
      if coordVal u.1 = coordVal u.2 then 1 else 0

@[simp] theorem pairVal_zero : pairVal (0, 0) = 0 := by simp [pairVal]
@[simp] theorem coordVal_neg (z : ℤ) : coordVal (-z) = coordVal z := by
  simp [coordVal]

@[simp] theorem pairVal_neg (u : Vec2) : pairVal (-u.1, -u.2) = pairVal u := by
  rcases u with ⟨x, y⟩
  by_cases hx : x = 0 <;> by_cases hy : y = 0 <;>
    simp [pairVal, hx, hy, coordVal_neg]

private theorem coordVal_mul_nat (k : ℕ) (z : ℤ) (hk : k ≠ 0) (hz : z ≠ 0) :
    coordVal ((k : ℤ) * z) = coordVal z + padicValNat 2 k := by
  simp only [coordVal, Int.natAbs_mul, Int.natAbs_natCast]
  rw [padicValNat.mul]
  · omega
  · exact hk
  · simpa using hz

/-- Multiplying a nonzero planar vector by `k` adds twice the 2-adic order of `k`. -/
theorem pairVal_nsmul (k : ℕ) (u : Vec2) (hk : k ≠ 0) (hu : u ≠ (0, 0)) :
    pairVal ((k : ℤ) * u.1, (k : ℤ) * u.2) = pairVal u + 2 * padicValNat 2 k := by
  rcases u with ⟨x, y⟩
  by_cases hx : x = 0
  · subst x
    have hy : y ≠ 0 := by
      intro hy
      apply hu
      simp [hy]
    simp [pairVal, hk, hy, coordVal_mul_nat k y hk hy, Nat.mul_add]
    <;> omega
  · by_cases hy : y = 0
    · subst y
      have hx' : x ≠ 0 := hx
      simp [pairVal, hk, hx', coordVal_mul_nat k x hk hx', Nat.mul_add]
      <;> omega
    · have hkz : (k : ℤ) ≠ 0 := by exact_mod_cast hk
      have hkx : (k : ℤ) * x ≠ 0 := mul_ne_zero hkz hx
      have hky : (k : ℤ) * y ≠ 0 := mul_ne_zero hkz hy
      simp only [pairVal, hx, hy, hkx, hky, if_false]
      rw [coordVal_mul_nat k x hk hx, coordVal_mul_nat k y hk hy]
      have hmin : min (coordVal x + padicValNat 2 k) (coordVal y + padicValNat 2 k) =
          min (coordVal x) (coordVal y) + padicValNat 2 k := by omega
      rw [hmin]
      by_cases hxy : coordVal x = coordVal y
      · simp [hxy, Nat.mul_add]
        <;> omega
      · have hxy' : coordVal x + padicValNat 2 k ≠ coordVal y + padicValNat 2 k := by omega
        simp [hxy, hxy', Nat.mul_add]
        <;> omega

end Hilbert193


/- Amalgamated from PairLaw.lean. -/

namespace Hilbert193

open Orient

/-- Numeric value of one base-4 digit. -/
def Digit.toNat : Digit → ℕ
  | .d0 => 0 | .d1 => 1 | .d2 => 2 | .d3 => 3

/-- Evaluate a least-significant-digit-first base-4 word. -/
def indexLSB : List Digit → ℕ
  | [] => 0
  | d :: ds => d.toNat + 4 * indexLSB ds

/-- Reverse one transition, starting from its outgoing orientation. -/
def previous (out : Orient) (d : Digit) : Orient := out.compose (refinement d)

/-- Coordinate bits read from low to high, starting at the common terminal orientation. -/
def coordinateLSB : Orient → List Digit → ℕ × ℕ
  | _, [] => (0, 0)
  | out, d :: ds =>
      let b := emit out d
      let q := coordinateLSB (previous out d) ds
      (b.1.toNat + 2*q.1, b.2.toNat + 2*q.2)

abbrev intDelta (a b : ℕ) : ℤ := (a : ℤ) - (b : ℤ)

def coordinateDelta (out : Orient) (a b : List Digit) : Vec2 :=
  let x := coordinateLSB out a
  let y := coordinateLSB out b
  (intDelta x.1 y.1, intDelta x.2 y.2)

def indexDistance (a b : List Digit) : ℕ :=
  Int.natAbs (intDelta (indexLSB a) (indexLSB b))

@[simp] theorem previous_refinement (out : Orient) (d : Digit) :
    next (previous out d) d = out := by
  simp [previous, next, Orient.compose_assoc]

/-- Different digits emit different bit pairs in every outgoing orientation. -/
theorem emit_injective_out (out : Orient) {d e : Digit} (h : emit out d = emit out e) : d = e := by
  rcases out with ⟨s,x,y⟩
  cases s <;> cases x <;> cases y <;> cases d <;> cases e <;>
    simp_all [emit, child, Orient.act, Orient.choose]

private theorem bit_low_unique (a b : Bit) (x y : ℕ)
    (h : a.toNat + 2*x = b.toNat + 2*y) : a = b := by
  cases a <;> cases b <;> simp [Bit.toNat] at h ⊢ <;> omega

/-- Fixed-terminal low-end coordinates are injective on words of one length. -/
theorem coordinateLSB_injective (out : Orient) {a b : List Digit}
    (hlen : a.length = b.length) (hcoord : coordinateLSB out a = coordinateLSB out b) : a = b := by
  induction a generalizing out b with
  | nil =>
      cases b <;> simp_all
  | cons d ds ih =>
      cases b with
      | nil => simp at hlen
      | cons e es =>
          simp only [coordinateLSB] at hcoord
          have hx := congrArg Prod.fst hcoord
          have hy := congrArg Prod.snd hcoord
          simp only at hx hy
          have hbits : emit out d = emit out e := by
            apply Prod.ext
            · exact bit_low_unique _ _ _ _ hx
            · exact bit_low_unique _ _ _ _ hy
          have hde : d = e := emit_injective_out out hbits
          subst e
          have htail : coordinateLSB (previous out d) ds = coordinateLSB (previous out d) es := by
            apply Prod.ext
            · exact Nat.mul_left_cancel (by omega) (Nat.add_left_cancel hx)
            · exact Nat.mul_left_cancel (by omega) (Nat.add_left_cancel hy)
          have hlen' : ds.length = es.length := by simpa using hlen
          rw [ih (previous out d) hlen' htail]

private theorem padicValNat_eq_zero_of_odd {n : ℕ} (hodd : n % 2 = 1) :
    padicValNat 2 n = 0 := by
  apply padicValNat.eq_zero_of_not_dvd
  intro hd
  obtain ⟨k, rfl⟩ := hd
  omega

private theorem padicValNat_eq_one_of_mod_four_two {n : ℕ} (hmod : n % 4 = 2) :
    padicValNat 2 n = 1 := by
  have hn : n ≠ 0 := by omega
  have htwo : 2 ∣ n := by omega
  obtain ⟨q, rfl⟩ := htwo
  have hqodd : q % 2 = 1 := by omega
  rw [padicValNat.mul]
  · rw [padicValNat_base (by omega), padicValNat_eq_zero_of_odd hqodd]
  · omega
  · omega

private theorem indexDistance_head_mod (d e : Digit) (ds es : List Digit) :
    d ≠ e →
    (d.toNat + 4 * indexLSB ds) ≠ (e.toNat + 4 * indexLSB es) := by
  intro hde heq
  have hm : d.toNat % 4 = e.toNat % 4 := by omega
  cases d <;> cases e <;> simp [Digit.toNat] at hde hm

private theorem indexLSB_injective {a b : List Digit}
    (hlen : a.length = b.length) (hindex : indexLSB a = indexLSB b) : a = b := by
  induction a generalizing b with
  | nil =>
      cases b <;> simp_all
  | cons d ds ih =>
      cases b with
      | nil => simp at hlen
      | cons e es =>
          simp only [indexLSB] at hindex
          have hmod : d.toNat % 4 = e.toNat % 4 := by omega
          have hde : d = e := by
            cases d <;> cases e <;> simp_all [Digit.toNat]
          subst e
          have htail : indexLSB ds = indexLSB es := by omega
          have hlen' : ds.length = es.length := by simpa using hlen
          rw [ih hlen' htail]

private def bitDelta (a b : Bit) (x y : ℕ) : ℤ :=
  intDelta (a.toNat + 2*x) (b.toNat + 2*y)

private theorem bitDelta_ne_zero_of_ne {a b : Bit} (x y : ℕ) (hab : a ≠ b) :
    bitDelta a b x y ≠ 0 := by
  cases a <;> cases b <;> simp_all [bitDelta, intDelta, Bit.toNat]
  all_goals omega

private theorem coordVal_bitDelta_of_ne {a b : Bit} (x y : ℕ) (hab : a ≠ b) :
    coordVal (bitDelta a b x y) = 0 := by
  unfold coordVal
  apply padicValNat.eq_zero_of_not_dvd
  intro hd
  have hdI : (2 : ℤ) ∣ bitDelta a b x y := by
    apply Int.dvd_natAbs.mp
    exact Int.natCast_dvd_natCast.mpr hd
  obtain ⟨k, hk⟩ := hdI
  cases a <;> cases b <;> simp_all [bitDelta, intDelta, Bit.toNat]
  all_goals omega

private theorem coordVal_bitDelta_ne_zero_of_eq {a b : Bit} (x y : ℕ)
    (hab : a = b) (hz : bitDelta a b x y ≠ 0) :
    coordVal (bitDelta a b x y) ≠ 0 := by
  subst b
  unfold coordVal
  intro hv
  rw [padicValNat.eq_zero_iff] at hv
  rcases hv with hbad | hzero | hnotdvd
  · omega
  · exact hz (Int.natAbs_eq_zero.mp hzero)
  · apply hnotdvd
    have hdI : (2 : ℤ) ∣ bitDelta a a x y := by
      refine ⟨(x : ℤ) - y, ?_⟩
      cases a <;> simp [bitDelta, intDelta, Bit.toNat] <;> ring
    apply Int.natCast_dvd_natCast.mp
    exact Int.dvd_natAbs.mpr hdI

private theorem pairVal_bitDelta (a₁ a₂ b₁ b₂ : Bit) (x₁ x₂ y₁ y₂ : ℕ)
    (hmismatch : a₁ ≠ b₁ ∨ a₂ ≠ b₂) :
    pairVal (bitDelta a₁ b₁ x₁ y₁, bitDelta a₂ b₂ x₂ y₂) =
      if a₁ ≠ b₁ ∧ a₂ ≠ b₂ then 1 else 0 := by
  by_cases h₁ : a₁ = b₁ <;> by_cases h₂ : a₂ = b₂
  · exfalso
    exact hmismatch.elim (fun hn => hn h₁) (fun hn => hn h₂)
  · subst b₁
    have hz₂ := bitDelta_ne_zero_of_ne x₂ y₂ h₂
    have hv₂ := coordVal_bitDelta_of_ne x₂ y₂ h₂
    by_cases hz₁ : bitDelta a₁ a₁ x₁ y₁ = 0
    · simp [h₂, pairVal, hz₁, hz₂, hv₂]
    · have hv₁ := coordVal_bitDelta_ne_zero_of_eq x₁ y₁ rfl hz₁
      simp [h₂, pairVal, hz₁, hz₂, hv₁, hv₂]
  · subst b₂
    have hz₁ := bitDelta_ne_zero_of_ne x₁ y₁ h₁
    have hv₁ := coordVal_bitDelta_of_ne x₁ y₁ h₁
    by_cases hz₂ : bitDelta a₂ a₂ x₂ y₂ = 0
    · simp [h₁, pairVal, hz₁, hz₂, hv₁]
    · have hv₂ := coordVal_bitDelta_ne_zero_of_eq x₂ y₂ rfl hz₂
      simp [h₁, pairVal, hz₁, hz₂, hv₁, hv₂, Ne.symm hv₂]
  · have hz₁ := bitDelta_ne_zero_of_ne x₁ y₁ h₁
    have hz₂ := bitDelta_ne_zero_of_ne x₂ y₂ h₂
    have hv₁ := coordVal_bitDelta_of_ne x₁ y₁ h₁
    have hv₂ := coordVal_bitDelta_of_ne x₂ y₂ h₂
    simp [h₁, h₂, pairVal, hz₁, hz₂, hv₁, hv₂]

private theorem padicValNat_natAbs_eq_zero {z : ℤ} (hodd : ¬(2 : ℤ) ∣ z) :
    padicValNat 2 z.natAbs = 0 := by
  apply padicValNat.eq_zero_of_not_dvd
  intro hd
  apply hodd
  apply Int.dvd_natAbs.mp
  exact Int.natCast_dvd_natCast.mpr hd

private theorem padicValNat_natAbs_eq_one {z : ℤ}
    (htwo : (2 : ℤ) ∣ z) (hfour : ¬(4 : ℤ) ∣ z) :
    padicValNat 2 z.natAbs = 1 := by
  have htwoN : 2 ∣ z.natAbs := by
    apply Int.natCast_dvd_natCast.mp
    exact Int.dvd_natAbs.mpr htwo
  obtain ⟨q, hq⟩ := htwoN
  have hq0 : q ≠ 0 := by
    intro h
    subst q
    simp_all
  have hqodd : ¬2 ∣ q := by
    intro h
    apply hfour
    apply Int.dvd_natAbs.mp
    apply Int.natCast_dvd_natCast.mpr
    simpa [hq, mul_assoc] using Nat.mul_dvd_mul_left 2 h
  rw [hq, padicValNat.mul (by omega) hq0, padicValNat_base (by omega)]
  simp [padicValNat.eq_zero_of_not_dvd hqodd]

private theorem index_mismatch_val (d e : Digit) (ds es : List Digit) (hde : d ≠ e) :
    padicValNat 2 (indexDistance (d :: ds) (e :: es)) =
      if d.toNat % 2 = e.toNat % 2 then 1 else 0 := by
  by_cases hp : d.toNat % 2 = e.toNat % 2
  · rw [if_pos hp]
    apply padicValNat_natAbs_eq_one
    · unfold intDelta indexLSB
      cases d <;> cases e <;> simp [Digit.toNat] at hde hp ⊢ <;> omega
    · unfold intDelta indexLSB
      cases d <;> cases e <;> simp [Digit.toNat] at hde hp ⊢
      all_goals
        rintro ⟨k, hk⟩
        omega
  · rw [if_neg hp]
    apply padicValNat_natAbs_eq_zero
    unfold intDelta indexLSB
    cases d <;> cases e <;> simp [Digit.toNat] at hde hp ⊢ <;> omega

/-- At the first low digit mismatch, both sides of the pair law are 0 or 1
according to whether the two base-4 digits differ in one or two Gray bits. -/
theorem first_mismatch_pairVal (out : Orient) (d e : Digit) (ds es : List Digit)
    (hde : d ≠ e) :
    pairVal (coordinateDelta out (d :: ds) (e :: es)) =
      padicValNat 2 (indexDistance (d :: ds) (e :: es)) := by
  have hm : emit out d ≠ emit out e := fun h => hde (emit_injective_out out h)
  rw [index_mismatch_val d e ds es hde]
  simp only [coordinateDelta, coordinateLSB]
  rw [show
    (intDelta ((emit out d).1.toNat + 2 * (coordinateLSB (previous out d) ds).1)
        ((emit out e).1.toNat + 2 * (coordinateLSB (previous out e) es).1),
      intDelta ((emit out d).2.toNat + 2 * (coordinateLSB (previous out d) ds).2)
        ((emit out e).2.toNat + 2 * (coordinateLSB (previous out e) es).2)) =
    (bitDelta (emit out d).1 (emit out e).1
        (coordinateLSB (previous out d) ds).1 (coordinateLSB (previous out e) es).1,
      bitDelta (emit out d).2 (emit out e).2
        (coordinateLSB (previous out d) ds).2 (coordinateLSB (previous out e) es).2) by
      rfl]
  rw [pairVal_bitDelta _ _ _ _ _ _ _ _ (by
    by_contra h
    push_neg at h
    exact hm (Prod.ext h.1 h.2))]
  rcases out with ⟨s,x,y⟩
  cases s <;> cases x <;> cases y <;> cases d <;> cases e <;>
    simp_all [Digit.toNat, emit, child, Orient.act, Orient.choose]

/-- The exact same-terminal low-end pair law for equal-length words. -/
theorem pair_law_words (out : Orient) {a b : List Digit}
    (hlen : a.length = b.length) (hne : a ≠ b) :
    pairVal (coordinateDelta out a b) = padicValNat 2 (indexDistance a b) := by
  induction a generalizing out b with
  | nil =>
      cases b <;> simp_all
  | cons d ds ih =>
      cases b with
      | nil => simp at hlen
      | cons e es =>
          by_cases hde : d = e
          · subst e
            have hlen' : ds.length = es.length := by simpa using hlen
            have hne' : ds ≠ es := by simpa using hne
            have htail := ih (previous out d) hlen' hne'
            have hcoord : coordinateDelta out (d :: ds) (d :: es) =
                ((2 : ℤ) * (coordinateDelta (previous out d) ds es).1,
                 (2 : ℤ) * (coordinateDelta (previous out d) ds es).2) := by
              simp [coordinateDelta, coordinateLSB, intDelta]
              constructor <;> ring
            have hindex : indexDistance (d :: ds) (d :: es) =
                4 * indexDistance ds es := by
              unfold indexDistance intDelta
              change
                Int.natAbs
                    (((d.toNat + 4 * indexLSB ds : ℕ) : ℤ) -
                      ((d.toNat + 4 * indexLSB es : ℕ) : ℤ)) =
                  4 * Int.natAbs ((indexLSB ds : ℤ) - indexLSB es)
              rw [show
                ((d.toNat + 4 * indexLSB ds : ℕ) : ℤ) -
                    ((d.toNat + 4 * indexLSB es : ℕ) : ℤ) =
                  (4 : ℤ) * ((indexLSB ds : ℤ) - indexLSB es) by
                    push_cast
                    ring]
              rw [Int.natAbs_mul]
              norm_num
            have htail_ne : coordinateDelta (previous out d) ds es ≠ (0,0) := by
              intro hz
              have hx := congrArg Prod.fst hz
              have hy := congrArg Prod.snd hz
              simp [coordinateDelta, intDelta] at hx hy
              have hc : coordinateLSB (previous out d) ds =
                  coordinateLSB (previous out d) es := by
                apply Prod.ext <;> omega
              exact hne' (coordinateLSB_injective _ hlen' hc)
            have hdist : indexDistance ds es ≠ 0 := by
              intro hz
              unfold indexDistance intDelta at hz
              have hiZ : (indexLSB ds : ℤ) = indexLSB es := by
                apply Int.sub_eq_zero.mp
                exact Int.natAbs_eq_zero.mp hz
              have hi : indexLSB ds = indexLSB es := by exact_mod_cast hiZ
              exact hne' (indexLSB_injective hlen' hi)
            have hscale :
                pairVal ((2 : ℤ) * (coordinateDelta (previous out d) ds es).1,
                  (2 : ℤ) * (coordinateDelta (previous out d) ds es).2) =
                pairVal (coordinateDelta (previous out d) ds es) +
                  2 * padicValNat 2 2 := by
              simpa using pairVal_nsmul 2 _ (by omega) htail_ne
            rw [hcoord, hscale, hindex, padicValNat.mul (by omega) hdist]
            have hval2 : padicValNat 2 2 = 1 := padicValNat_base (by omega)
            have hval4 : padicValNat 2 4 = 2 := by
              rw [show 4 = 2 * 2 by norm_num, padicValNat.mul (by omega) (by omega), hval2]
            rw [hval4, hval2, htail]
            omega
          · exact first_mismatch_pairVal out d e ds es hde

/-- Orientation reached while undoing low digits from a fixed outgoing state. -/
def backwardState : Orient → List Digit → Orient
  | out, [] => out
  | out, d :: ds => backwardState (previous out d) ds

@[simp] theorem backwardState_append (out : Orient) (a b : List Digit) :
    backwardState out (a ++ b) = backwardState (backwardState out a) b := by
  induction a generalizing out with
  | nil => rfl
  | cons d ds ih => simp [backwardState, ih]

theorem backwardState_run_reverse (s : Orient) (ds : List Digit) :
    backwardState (run s ds).2 ds.reverse = s := by
  induction ds generalizing s with
  | nil => rfl
  | cons d ds ih =>
      rw [show (run s (d :: ds)).2 = (run (next s d) ds).2 by rfl,
        List.reverse_cons, backwardState_append, ih]
      simp [backwardState, previous, next, Orient.compose_assoc,
        refinement_involution, Orient.compose_I_right]

theorem coordinateLSB_append (out : Orient) (a b : List Digit) :
    coordinateLSB out (a ++ b) =
      ((coordinateLSB out a).1 +
          2 ^ a.length * (coordinateLSB (backwardState out a) b).1,
        (coordinateLSB out a).2 +
          2 ^ a.length * (coordinateLSB (backwardState out a) b).2) := by
  induction a generalizing out with
  | nil => simp [coordinateLSB, backwardState]
  | cons d ds ih =>
      simp only [List.cons_append, coordinateLSB, backwardState, List.length_cons,
        Nat.pow_succ]
      rw [ih]
      apply Prod.ext <;> simp <;> ring

/-- Any number of high zero digit-pairs. -/
def zeroPairs : ℕ → List Digit
  | 0 => []
  | k + 1 => .d0 :: .d0 :: zeroPairs k

@[simp] theorem zeroPairs_length (k : ℕ) : (zeroPairs k).length = 2 * k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [zeroPairs, ih]; omega

@[simp] theorem indexLSB_zeroPairs (k : ℕ) : indexLSB (zeroPairs k) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [zeroPairs, indexLSB, Digit.toNat, ih]

@[simp] theorem coordinateLSB_I_zeroPairs (k : ℕ) :
    coordinateLSB I (zeroPairs k) = (0,0) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hSS : S.compose S = I := by decide
      simp [zeroPairs, coordinateLSB, previous, emit, child, Orient.act,
        Orient.choose, refinement, Digit.toNat, Bit.toNat, hSS, ih]

@[simp] theorem backwardState_I_zeroPairs (k : ℕ) :
    backwardState I (zeroPairs k) = I := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hSS : S.compose S = I := by decide
      simp [zeroPairs, backwardState, previous, refinement, hSS, ih]

theorem indexLSB_append_zeroPairs (a : List Digit) (k : ℕ) :
    indexLSB (a ++ zeroPairs k) = indexLSB a := by
  induction a with
  | nil => simp [indexLSB]
  | cons d ds ih => simp [indexLSB, ih]

theorem coordinateLSB_append_zeroPairs (a : List Digit) (k : ℕ)
    (hback : backwardState I a = I) :
    coordinateLSB I (a ++ zeroPairs k) = coordinateLSB I a := by
  rw [coordinateLSB_append, hback, coordinateLSB_I_zeroPairs]
  simp

/-- The pair law remains valid for unequal even word lengths once both words
undo to the same terminal orientation; high zero-pairs provide a common length. -/
theorem pair_law_even_words {a b : List Digit}
    (haeven : Even a.length) (hbeven : Even b.length)
    (haback : backwardState I a = I) (hbback : backwardState I b = I)
    (hindex : indexLSB a ≠ indexLSB b) :
    pairVal (coordinateDelta I a b) = padicValNat 2 (indexDistance a b) := by
  obtain ⟨la, hla⟩ := haeven
  obtain ⟨lb, hlb⟩ := hbeven
  let ap := a ++ zeroPairs lb
  let bp := b ++ zeroPairs la
  have hlen : ap.length = bp.length := by
    simp [ap, bp, hla, hlb]
    omega
  have hcoordA : coordinateLSB I ap = coordinateLSB I a :=
    coordinateLSB_append_zeroPairs a lb haback
  have hcoordB : coordinateLSB I bp = coordinateLSB I b :=
    coordinateLSB_append_zeroPairs b la hbback
  have hindexA : indexLSB ap = indexLSB a := indexLSB_append_zeroPairs a lb
  have hindexB : indexLSB bp = indexLSB b := indexLSB_append_zeroPairs b la
  have hne : ap ≠ bp := by
    intro h
    apply hindex
    rw [← hindexA, ← hindexB, h]
  have hp := pair_law_words I hlen hne
  simpa [coordinateDelta, indexDistance, hcoordA, hcoordB, hindexA, hindexB] using hp

theorem coordinateLSB_even_injective {a b : List Digit}
    (haeven : Even a.length) (hbeven : Even b.length)
    (haback : backwardState I a = I) (hbback : backwardState I b = I)
    (hindex : indexLSB a ≠ indexLSB b) :
    coordinateLSB I a ≠ coordinateLSB I b := by
  obtain ⟨la, hla⟩ := haeven
  obtain ⟨lb, hlb⟩ := hbeven
  let ap := a ++ zeroPairs lb
  let bp := b ++ zeroPairs la
  have hlen : ap.length = bp.length := by
    simp [ap, bp, hla, hlb]
    omega
  have hcoordA : coordinateLSB I ap = coordinateLSB I a :=
    coordinateLSB_append_zeroPairs a lb haback
  have hcoordB : coordinateLSB I bp = coordinateLSB I b :=
    coordinateLSB_append_zeroPairs b la hbback
  intro hcoord
  have hp : ap = bp := coordinateLSB_injective I hlen (by simpa [hcoordA, hcoordB])
  apply hindex
  have hi := congrArg indexLSB hp
  simpa [ap, bp, indexLSB_append_zeroPairs] using hi

/-- A primitive positive time ratio forces coordinatewise scalar decomposition
of two planar chords satisfying the cross-multiplication equations. -/
theorem common_direction_of_cross (r s : ℕ) (u v : Vec2)
    (hr : r ≠ 0) (hrs : Nat.Coprime r s)
    (hx : (s : ℤ) * u.1 = (r : ℤ) * v.1)
    (hy : (s : ℤ) * u.2 = (r : ℤ) * v.2) :
    ∃ w : Vec2,
      u = ((r : ℤ) * w.1, (r : ℤ) * w.2) ∧
      v = ((s : ℤ) * w.1, (s : ℤ) * w.2) := by
  have hgcd : Int.gcd (r : ℤ) (s : ℤ) = 1 := by
    simpa [Int.gcd_eq_natAbs, Nat.coprime_iff_gcd_eq_one] using hrs
  have hdx : (r : ℤ) ∣ u.1 := by
    apply Int.dvd_of_dvd_mul_right_of_gcd_one _ hgcd
    exact ⟨v.1, hx⟩
  have hdy : (r : ℤ) ∣ u.2 := by
    apply Int.dvd_of_dvd_mul_right_of_gcd_one _ hgcd
    exact ⟨v.2, hy⟩
  obtain ⟨wx, hwx⟩ := hdx
  obtain ⟨wy, hwy⟩ := hdy
  refine ⟨(wx, wy), ?_, ?_⟩
  · exact Prod.ext hwx hwy
  · apply Prod.ext
    · have hrZ : (r : ℤ) ≠ 0 := by exact_mod_cast hr
      apply Int.eq_of_mul_eq_mul_left hrZ
      calc
        (r : ℤ) * v.1 = (s : ℤ) * u.1 := hx.symm
        _ = (s : ℤ) * ((r : ℤ) * wx) := by rw [hwx]
        _ = (r : ℤ) * ((s : ℤ) * wx) := by ring
    · have hrZ : (r : ℤ) ≠ 0 := by exact_mod_cast hr
      apply Int.eq_of_mul_eq_mul_left hrZ
      calc
        (r : ℤ) * v.2 = (s : ℤ) * u.2 := hy.symm
        _ = (s : ℤ) * ((r : ℤ) * wy) := by rw [hwy]
        _ = (r : ℤ) * ((s : ℤ) * wy) := by ring

/-- The three-gap valuation contradiction.  Once two adjacent planar chords
are odd scalar multiples of one common nonzero direction, the pair law for
the two gaps and their sum is impossible. -/
theorem three_gap_contradiction (r s g : ℕ) (w : Vec2)
    (hr : r ≠ 0) (hs : s ≠ 0) (hg : g ≠ 0) (hw : w ≠ (0,0))
    (hrodd : r % 2 = 1) (hsodd : s % 2 = 1)
    (h₁ : pairVal ((r : ℤ) * w.1, (r : ℤ) * w.2) = padicValNat 2 (r * g))
    (h₂ : pairVal ((s : ℤ) * w.1, (s : ℤ) * w.2) = padicValNat 2 (s * g))
    (h₃ : pairVal (((r + s : ℕ) : ℤ) * w.1, ((r + s : ℕ) : ℤ) * w.2) =
      padicValNat 2 ((r + s) * g)) : False := by
  have hvr : padicValNat 2 r = 0 := padicValNat_eq_zero_of_odd hrodd
  have hvs : padicValNat 2 s = 0 := padicValNat_eq_zero_of_odd hsodd
  have hrs : r + s ≠ 0 := by omega
  have hsumEven : 2 ∣ r + s := by omega
  have hvsum : padicValNat 2 (r + s) ≠ 0 := by
    intro hz
    rw [padicValNat.eq_zero_iff] at hz
    rcases hz with hbad | hzero | hnotdvd
    · omega
    · exact hrs hzero
    · exact hnotdvd hsumEven
  have hscale₁ := pairVal_nsmul r w hr hw
  have hscale₃ := pairVal_nsmul (r + s) w hrs hw
  rw [padicValNat.mul hr hg, hvr] at h₁
  rw [padicValNat.mul hrs hg] at h₃
  have hvw : pairVal w = padicValNat 2 g := by omega
  rw [hscale₃, hvw] at h₃
  omega

/-- Pair laws for two adjacent gaps and their sum rule out the exact
cross-multiplication equations imposed by collinearity after the time lift. -/
theorem no_collinear_from_pair_laws (A B : ℕ) (u v : Vec2)
    (hA : A ≠ 0) (hB : B ≠ 0) (hu0 : u ≠ (0,0)) (hv0 : v ≠ (0,0))
    (hx : (B : ℤ) * u.1 = (A : ℤ) * v.1)
    (hy : (B : ℤ) * u.2 = (A : ℤ) * v.2)
    (hU : pairVal u = padicValNat 2 A)
    (hV : pairVal v = padicValNat 2 B)
    (hUV : pairVal (u.1 + v.1, u.2 + v.2) = padicValNat 2 (A + B)) :
    False := by
  have hscaleA := pairVal_nsmul A v hA hv0
  have hscaleB := pairVal_nsmul B u hB hu0
  have hscaled :
      ((B : ℤ) * u.1, (B : ℤ) * u.2) =
        ((A : ℤ) * v.1, (A : ℤ) * v.2) := Prod.ext hx hy
  have hval : padicValNat 2 A = padicValNat 2 B := by
    rw [hscaled, hscaleA] at hscaleB
    rw [hU, hV] at hscaleB
    omega
  let g := Nat.gcd A B
  let r := A / g
  let s := B / g
  have hg : g ≠ 0 := Nat.gcd_ne_zero_left hA
  have hgA : g ∣ A := Nat.gcd_dvd_left A B
  have hgB : g ∣ B := Nat.gcd_dvd_right A B
  have hAr : A = r * g := (Nat.div_mul_cancel hgA).symm
  have hBs : B = s * g := (Nat.div_mul_cancel hgB).symm
  have hr : r ≠ 0 := by
    intro hz
    rw [hAr, hz, zero_mul] at hA
    exact hA rfl
  have hs : s ≠ 0 := by
    intro hz
    rw [hBs, hz, zero_mul] at hB
    exact hB rfl
  have hrs : Nat.Coprime r s := by
    exact Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left B (Nat.pos_of_ne_zero hA))
  have hvrvs : padicValNat 2 r = padicValNat 2 s := by
    rw [hAr, hBs, padicValNat.mul hr hg, padicValNat.mul hs hg] at hval
    omega
  have hvr : padicValNat 2 r = 0 := by
    by_contra hnonzero
    have hdr : 2 ∣ r := by
      by_contra hnd
      exact hnonzero (padicValNat.eq_zero_of_not_dvd hnd)
    have hds : 2 ∣ s := by
      by_contra hnd
      have hz := padicValNat.eq_zero_of_not_dvd hnd
      exact hnonzero (hvrvs.trans hz)
    have hdg : 2 ∣ Nat.gcd r s := Nat.dvd_gcd hdr hds
    rw [hrs.gcd_eq_one] at hdg
    omega
  have hvs : padicValNat 2 s = 0 := hvrvs.symm.trans hvr
  have hrodd : r % 2 = 1 := by
    apply Nat.mod_two_ne_zero.mp
    intro hm
    have hd : 2 ∣ r := Nat.dvd_iff_mod_eq_zero.mpr hm
    rw [padicValNat.eq_zero_iff] at hvr
    rcases hvr with hbad | hzero | hnot
    · omega
    · exact hr hzero
    · exact hnot hd
  have hsodd : s % 2 = 1 := by
    apply Nat.mod_two_ne_zero.mp
    intro hm
    have hd : 2 ∣ s := Nat.dvd_iff_mod_eq_zero.mpr hm
    rw [padicValNat.eq_zero_iff] at hvs
    rcases hvs with hbad | hzero | hnot
    · omega
    · exact hs hzero
    · exact hnot hd
  have hcrossR : (s : ℤ) * u.1 = (r : ℤ) * v.1 := by
    have hgZ : (g : ℤ) ≠ 0 := by exact_mod_cast hg
    apply Int.eq_of_mul_eq_mul_left hgZ
    calc
      (g : ℤ) * ((s : ℤ) * u.1) = ((s * g : ℕ) : ℤ) * u.1 := by push_cast; ring
      _ = (B : ℤ) * u.1 := by rw [← hBs]
      _ = (A : ℤ) * v.1 := hx
      _ = ((r * g : ℕ) : ℤ) * v.1 := by rw [← hAr]
      _ = (g : ℤ) * ((r : ℤ) * v.1) := by push_cast; ring
  have hcrossS : (s : ℤ) * u.2 = (r : ℤ) * v.2 := by
    have hgZ : (g : ℤ) ≠ 0 := by exact_mod_cast hg
    apply Int.eq_of_mul_eq_mul_left hgZ
    calc
      (g : ℤ) * ((s : ℤ) * u.2) = ((s * g : ℕ) : ℤ) * u.2 := by push_cast; ring
      _ = (B : ℤ) * u.2 := by rw [← hBs]
      _ = (A : ℤ) * v.2 := hy
      _ = ((r * g : ℕ) : ℤ) * v.2 := by rw [← hAr]
      _ = (g : ℤ) * ((r : ℤ) * v.2) := by push_cast; ring
  obtain ⟨w, huw, hvw⟩ := common_direction_of_cross r s u v hr hrs hcrossR hcrossS
  have hw : w ≠ (0,0) := by
    intro hw0
    apply hu0
    rw [huw, hw0]
    simp
  apply three_gap_contradiction r s g w hr hs hg hw hrodd hsodd
  · simpa [huw, hAr] using hU
  · simpa [hvw, hBs] using hV
  · have hsum : A + B = (r + s) * g := by
      rw [hAr, hBs, Nat.add_mul]
    rw [hsum] at hUV
    have hchord :
        (u.1 + v.1, u.2 + v.2) =
          (((r + s : ℕ) : ℤ) * w.1, ((r + s : ℕ) : ℤ) * w.2) := by
      rw [huw, hvw]
      push_cast
      apply Prod.ext <;> simp <;> ring
    rw [hchord] at hUV
    exact hUV

end Hilbert193


/- Amalgamated from Construction.lean. -/

namespace Hilbert193
open Orient

/-- Numeric value of the two-digit suffix used to cancel a terminal parity. -/
def steeringValue : BitPair → ℕ
  | (.zero, .zero) => 5   -- `11₄`
  | (.one, .zero) => 1    -- `01₄`
  | (.zero, .one) => 13   -- `31₄`
  | (.one, .one) => 3     -- `03₄`

@[simp] theorem steeringValue_bounds (p : BitPair) :
    1 ≤ steeringValue p ∧ steeringValue p ≤ 13 := by
  rcases p with ⟨p₀,p₃⟩
  cases p₀ <;> cases p₃ <;> decide

/-- One representative in every consecutive block of sixteen Hilbert indices. -/
def selectedIndex (state : ℕ → BitPair) (a : ℕ) : ℕ :=
  16 * a + steeringValue (state a)

/-- Consecutive representatives have index gap between 4 and 28. -/
theorem selectedIndex_succ_gap (state : ℕ → BitPair) (a : ℕ) :
    ∃ gap, 4 ≤ gap ∧ gap ≤ 28 ∧
      selectedIndex state (a + 1) = selectedIndex state a + gap := by
  have ha := steeringValue_bounds (state a)
  have hb := steeringValue_bounds (state (a + 1))
  refine ⟨16 + steeringValue (state (a + 1)) - steeringValue (state a), ?_⟩
  unfold selectedIndex
  omega

/-- The selected indices are strictly increasing. -/
theorem selectedIndex_strictMono (state : ℕ → BitPair) :
    StrictMono (selectedIndex state) := by
  apply strictMono_nat_of_lt_succ
  intro a
  obtain ⟨gap, hgap, _, heq⟩ := selectedIndex_succ_gap state a
  omega


def digitOfNat (n : ℕ) : Digit :=
  match n % 4 with
  | 0 => .d0
  | 1 => .d1
  | 2 => .d2
  | _ => .d3

theorem Digit.toNat_digitOfNat {n : ℕ} (hn : n < 4) :
    (digitOfNat n).toNat = n := by
  interval_cases n <;> decide

def rawDigits (n : ℕ) : List Digit :=
  (Nat.digits 4 n).map digitOfNat
private theorem indexLSB_map_digitOfNat (ns : List ℕ) (hsmall : ∀ n ∈ ns, n < 4) :
    indexLSB (ns.map digitOfNat) = Nat.ofDigits 4 ns := by
  induction ns with
  | nil => rfl
  | cons n ns ih =>
      simp only [List.map_cons, indexLSB, Nat.ofDigits]
      rw [Digit.toNat_digitOfNat (hsmall n (by simp))]
      congr 1
      exact congrArg (fun z => 4 * z) (ih (fun x hx => hsmall x (by simp [hx])))

@[simp] theorem indexLSB_rawDigits (n : ℕ) : indexLSB (rawDigits n) = n := by
  rw [rawDigits, indexLSB_map_digitOfNat, Nat.ofDigits_digits]
  intro d hd
  exact Nat.digits_lt_base (by omega) hd

private theorem indexLSB_append_d0 (ds : List Digit) :
    indexLSB (ds ++ [.d0]) = indexLSB ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp [indexLSB, ih]

/-- Add one high zero digit exactly when needed to make the digit count even. -/
def evenDigits (n : ℕ) : List Digit :=
  let ds := rawDigits n
  if Even ds.length then ds else ds ++ [.d0]

@[simp] theorem indexLSB_evenDigits (n : ℕ) : indexLSB (evenDigits n) = n := by
  by_cases h : Even (rawDigits n).length
  · simp [evenDigits, h]
  · simp [evenDigits, h, indexLSB_append_d0]

theorem evenDigits_length_even (n : ℕ) : Even (evenDigits n).length := by
  by_cases h : Even (rawDigits n).length
  · simpa [evenDigits, h]
  · have hodd : Odd (rawDigits n).length := Nat.not_even_iff_odd.mp h
    obtain ⟨k, hk⟩ := hodd
    refine ⟨k + 1, ?_⟩
    simp [evenDigits, h, hk]

    omega
theorem wordParity_reverse (ds : List Digit) :
    wordParity ds.reverse = wordParity ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
      rw [List.reverse_cons, wordParity_append, ih]
      simp only [wordParity]
      rcases digitParity d with ⟨a,b⟩
      rcases wordParity ds with ⟨x,y⟩
      cases a <;> cases b <;> cases x <;> cases y <;> decide

@[simp] theorem steeringDigits_length (p : BitPair) :
    (steeringDigits p).length = 2 := by
  rcases p with ⟨p₀,p₃⟩
  cases p₀ <;> cases p₃ <;> rfl

@[simp] theorem indexLSB_steering_reverse (p : BitPair) :
    indexLSB (steeringDigits p).reverse = steeringValue p := by
  rcases p with ⟨p₀,p₃⟩
  cases p₀ <;> cases p₃ <;> decide

theorem indexLSB_append (a b : List Digit) :
    indexLSB (a ++ b) = indexLSB a + 4 ^ a.length * indexLSB b := by
  induction a with
  | nil => simp [indexLSB]
  | cons d ds ih =>
      simp only [List.cons_append, indexLSB, List.length_cons, Nat.pow_succ, ih]
      ring

/-- Least-significant-first base-4 word of the selected Hilbert index in block `a`. -/
def selectedWord (a : ℕ) : List Digit :=
  let pfx := evenDigits a
  (steeringDigits (wordParity pfx)).reverse ++ pfx

def selectedState (a : ℕ) : BitPair := wordParity (evenDigits a)

@[simp] theorem selectedWord_index (a : ℕ) :
    indexLSB (selectedWord a) = selectedIndex selectedState a := by
  simp [selectedWord, selectedIndex, selectedState, indexLSB_append]
  ring

theorem selectedWord_length_even (a : ℕ) : Even (selectedWord a).length := by
  obtain ⟨k, hk⟩ := evenDigits_length_even a
  refine ⟨k + 1, ?_⟩
  simp [selectedWord, hk]
  omega

theorem selectedWord_terminal (a : ℕ) :
    terminal (selectedWord a).reverse = I := by
  simp only [selectedWord, List.reverse_append, List.reverse_reverse]
  rw [← wordParity_reverse (evenDigits a)]
  exact terminal_steered (evenDigits a).reverse

theorem selectedWord_backward (a : ℕ) :
    backwardState I (selectedWord a) = I := by
  have h := backwardState_run_reverse I (selectedWord a).reverse
  rw [show (run I (selectedWord a).reverse).2 = I by
    exact selectedWord_terminal a, List.reverse_reverse] at h
  exact h

/-- Planar point of the selected Hilbert index. -/
def selectedPlanar (a : ℕ) : ℕ × ℕ :=
  coordinateLSB I (selectedWord a)

theorem selected_pair_law {a b : ℕ} (hne : a ≠ b) :
    pairVal
        (intDelta (selectedPlanar a).1 (selectedPlanar b).1,
          intDelta (selectedPlanar a).2 (selectedPlanar b).2) =
      padicValNat 2 (Int.natAbs ((selectedIndex selectedState a : ℤ) -
        selectedIndex selectedState b)) := by
  have hindex : indexLSB (selectedWord a) ≠ indexLSB (selectedWord b) := by
    rw [selectedWord_index, selectedWord_index]
    exact (selectedIndex_strictMono selectedState).injective.ne hne

  have hp := pair_law_even_words (selectedWord_length_even a)
    (selectedWord_length_even b) (selectedWord_backward a) (selectedWord_backward b) hindex
  simpa [selectedPlanar, coordinateDelta, indexDistance, selectedWord_index] using hp

theorem selectedPlanar_ne {a b : ℕ} (hne : a ≠ b) :
    selectedPlanar a ≠ selectedPlanar b := by
  apply coordinateLSB_even_injective (selectedWord_length_even a)
    (selectedWord_length_even b) (selectedWord_backward a) (selectedWord_backward b)
  rw [selectedWord_index, selectedWord_index]
  exact (selectedIndex_strictMono selectedState).injective.ne hne

structure Point3 where
  x : ℤ
  y : ℤ
  z : ℤ
  deriving DecidableEq

/-- The explicit time-lifted selected Hilbert walk. -/
def selectedLift (a : ℕ) : Point3 where
  x := (selectedPlanar a).1
  y := (selectedPlanar a).2
  z := selectedIndex selectedState a

/-- Exact ordered collinearity equations for points whose `z` coordinates
increase from `p` through `q` to `r`. -/
def OrderedCollinear (p q r : Point3) : Prop :=
  (r.z - q.z) * (q.x - p.x) = (q.z - p.z) * (r.x - q.x) ∧
  (r.z - q.z) * (q.y - p.y) = (q.z - p.z) * (r.y - q.y)

/-- No three points of the explicit selected time-lifted Hilbert walk are collinear. -/
theorem selectedLift_no_three {i j k : ℕ} (hij : i < j) (hjk : j < k) :
    ¬OrderedCollinear (selectedLift i) (selectedLift j) (selectedLift k) := by
  intro hcol
  let ni := selectedIndex selectedState i
  let nj := selectedIndex selectedState j
  let nk := selectedIndex selectedState k
  have hnij : ni < nj := selectedIndex_strictMono selectedState hij
  have hnjk : nj < nk := selectedIndex_strictMono selectedState hjk
  let A := nj - ni
  let B := nk - nj
  have hA : A ≠ 0 := by omega
  have hB : B ≠ 0 := by omega
  let u : Vec2 :=
    (intDelta (selectedPlanar j).1 (selectedPlanar i).1,
      intDelta (selectedPlanar j).2 (selectedPlanar i).2)
  let v : Vec2 :=
    (intDelta (selectedPlanar k).1 (selectedPlanar j).1,
      intDelta (selectedPlanar k).2 (selectedPlanar j).2)
  have hu0 : u ≠ (0,0) := by
    intro hu
    have hx := congrArg Prod.fst hu
    have hy := congrArg Prod.snd hu
    simp [u, intDelta] at hx hy
    apply selectedPlanar_ne (ne_of_lt hij)
    apply Prod.ext <;> omega
  have hv0 : v ≠ (0,0) := by
    intro hv
    have hx := congrArg Prod.fst hv
    have hy := congrArg Prod.snd hv
    simp [v, intDelta] at hx hy
    apply selectedPlanar_ne (ne_of_lt hjk)
    apply Prod.ext <;> omega
  have hcastA : (A : ℤ) = (nj : ℤ) - ni := by omega
  have hcastB : (B : ℤ) = (nk : ℤ) - nj := by omega
  have hx : (B : ℤ) * u.1 = (A : ℤ) * v.1 := by
    rcases hcol with ⟨hcolx, hcoly⟩
    simpa [OrderedCollinear, selectedLift, ni, nj, nk, u, v, hcastA, hcastB,
      intDelta] using hcolx
  have hy : (B : ℤ) * u.2 = (A : ℤ) * v.2 := by
    rcases hcol with ⟨hcolx, hcoly⟩
    simpa [OrderedCollinear, selectedLift, ni, nj, nk, u, v, hcastA, hcastB,
      intDelta] using hcoly
  have hU : pairVal u = padicValNat 2 A := by
    have hp := selected_pair_law (a := j) (b := i) (ne_of_gt hij)
    have hgap : Int.natAbs ((nj : ℤ) - ni) = A := by
      apply Nat.cast_injective (R := ℤ)
      rw [Int.natAbs_of_nonneg (by omega)]
      exact hcastA.symm
    rw [hgap] at hp
    exact hp
  have hV : pairVal v = padicValNat 2 B := by
    have hp := selected_pair_law (a := k) (b := j) (ne_of_gt hjk)
    have hgap : Int.natAbs ((nk : ℤ) - nj) = B := by
      apply Nat.cast_injective (R := ℤ)
      rw [Int.natAbs_of_nonneg (by omega)]
      exact hcastB.symm
    rw [hgap] at hp
    exact hp
  have hUV : pairVal (u.1 + v.1, u.2 + v.2) = padicValNat 2 (A + B) := by
    have hp := selected_pair_law (a := k) (b := i) (ne_of_gt (lt_trans hij hjk))
    have hgap : Int.natAbs ((nk : ℤ) - ni) = A + B := by
      apply Nat.cast_injective (R := ℤ)
      rw [Int.natAbs_of_nonneg (by omega)]
      push_cast
      omega
    rw [hgap] at hp
    have hchord :
        (u.1 + v.1, u.2 + v.2) =
          (intDelta (selectedPlanar k).1 (selectedPlanar i).1,
            intDelta (selectedPlanar k).2 (selectedPlanar i).2) := by
      apply Prod.ext
      · change
          intDelta (selectedPlanar j).1 (selectedPlanar i).1 +
              intDelta (selectedPlanar k).1 (selectedPlanar j).1 =
            intDelta (selectedPlanar k).1 (selectedPlanar i).1
        unfold intDelta
        ring
      · change
          intDelta (selectedPlanar j).2 (selectedPlanar i).2 +
              intDelta (selectedPlanar k).2 (selectedPlanar j).2 =
            intDelta (selectedPlanar k).2 (selectedPlanar i).2
        unfold intDelta
        ring
    rw [hchord]
    exact hp
  exact no_collinear_from_pair_laws A B u v hA hB hu0 hv0 hx hy hU hV hUV
end Hilbert193


/- Amalgamated from Continuity.lean. -/

namespace Hilbert193

open Orient


/-- Most-significant-first evaluation of a base-4 word. -/
def indexMSB : List Digit → ℕ
  | [] => 0
  | d :: ds => d.toNat * 4 ^ ds.length + indexMSB ds

/-- Most-significant-first coordinate evaluation, generalized to an incoming orientation. -/
def coordinateMSB : Orient → List Digit → ℕ × ℕ
  | _, [] => (0, 0)
  | s, d :: ds =>
      let b := emit s d
      let q := coordinateMSB (next s d) ds
      (b.1.toNat * 2 ^ ds.length + q.1,
        b.2.toNat * 2 ^ ds.length + q.2)

/-- Apply a square orientation to coordinates in `[0,m]²`. -/
def Orient.actNat (s : Orient) (m : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  let x := if s.swap = .zero then p.1 else p.2
  let y := if s.swap = .zero then p.2 else p.1
  (if s.bx = .zero then x else m - x,
    if s.cy = .zero then y else m - y)

private def zeroWord (n : ℕ) : List Digit := List.replicate n .d0
private def threeWord (n : ℕ) : List Digit := List.replicate n .d3

@[simp] private theorem zeroWord_succ (n : ℕ) :
    zeroWord (n + 1) = .d0 :: zeroWord n := by
  simpa [zeroWord] using (List.replicate_succ (a := Digit.d0) (n := n))

@[simp] private theorem threeWord_succ (n : ℕ) :
    threeWord (n + 1) = .d3 :: threeWord n := by
  simpa [threeWord] using (List.replicate_succ (a := Digit.d3) (n := n))

@[simp] private theorem zeroWord_length (n : ℕ) : (zeroWord n).length = n := by
  simp [zeroWord]

@[simp] private theorem threeWord_length (n : ℕ) : (threeWord n).length = n := by
  simp [threeWord]

private theorem coordinateMSB_endpoints (s : Orient) (n : ℕ) :
    coordinateMSB s (zeroWord n) = s.actNat (2 ^ n - 1) (0, 0) ∧
    coordinateMSB s (threeWord n) = s.actNat (2 ^ n - 1) (2 ^ n - 1, 0) := by
  induction n generalizing s with
  | zero =>
      rcases s with ⟨sw, bx, cy⟩
      cases sw <;> cases bx <;> cases cy <;>
        decide
  | succ n ih =>
      rcases s with ⟨sw, bx, cy⟩
      cases sw <;> cases bx <;> cases cy <;>
        simp only [zeroWord_succ, threeWord_succ, coordinateMSB,
          zeroWord_length, threeWord_length, Bit.toNat, ih] <;>
        simp [Orient.actNat, emit, next, child, refinement, Orient.act,
          Orient.compose, Orient.choose, Nat.pow_succ] <;>
        omega

/-- Lexicographic base-4 successor on fixed-length words. -/
inductive WordSucc : List Digit → List Digit → Prop
  | tail (d : Digit) {a b : List Digit} (h : WordSucc a b) : WordSucc (d :: a) (d :: b)
  | d01 (n : ℕ) : WordSucc (.d0 :: threeWord n) (.d1 :: zeroWord n)
  | d12 (n : ℕ) : WordSucc (.d1 :: threeWord n) (.d2 :: zeroWord n)
  | d23 (n : ℕ) : WordSucc (.d2 :: threeWord n) (.d3 :: zeroWord n)

theorem WordSucc.length_eq {a b : List Digit} (h : WordSucc a b) :
    a.length = b.length := by
  induction h with
  | tail d h ih => simp [ih]
  | d01 n => simp [zeroWord, threeWord]
  | d12 n => simp [zeroWord, threeWord]
  | d23 n => simp [zeroWord, threeWord]

private theorem indexMSB_lt_pow (ds : List Digit) :
    indexMSB ds < 4 ^ ds.length := by
  induction ds with
  | nil => simp [indexMSB]
  | cons d ds ih =>
      cases d <;> simp [indexMSB, Digit.toNat, Nat.pow_succ] at ih ⊢ <;> omega

private theorem indexMSB_eq_zero (ds : List Digit) (h : indexMSB ds = 0) :
    ds = zeroWord ds.length := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
      cases d <;> simp [indexMSB, Digit.toNat] at h
      · change Digit.d0 :: ds = Digit.d0 :: zeroWord ds.length
        congr
        exact ih h

private theorem indexMSB_eq_max (ds : List Digit)
    (h : indexMSB ds = 4 ^ ds.length - 1) :
    ds = threeWord ds.length := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
      have ht := indexMSB_lt_pow ds
      cases d <;>
        simp [indexMSB, Digit.toNat, Nat.pow_succ] at h
      all_goals
        try omega
      change Digit.d3 :: ds = Digit.d3 :: threeWord ds.length
      congr
      exact ih (by omega)

private theorem carry_bounds {A B p : ℕ} (hp : 0 < p) (hA : A < p) (hB : B < p)
    (h : A + 1 = p + B) : A = p - 1 ∧ B = 0 := by
  omega

/-- Numeric succession characterizes lexicographic base-4 word succession at
fixed length. -/
theorem WordSucc.of_index {a b : List Digit} (hlen : a.length = b.length)
    (hindex : indexMSB a + 1 = indexMSB b) : WordSucc a b := by
  induction a generalizing b with
  | nil =>
      cases b <;> simp_all [indexMSB]
  | cons d ds ih =>
      cases b with
      | nil => simp at hlen
      | cons e es =>
          have hlen' : ds.length = es.length := by simpa using hlen
          have ha := indexMSB_lt_pow ds
          have hb := indexMSB_lt_pow es
          simp only [indexMSB, List.length_cons] at hindex
          rw [hlen'] at hindex ha
          cases d <;> cases e
          all_goals simp only [Digit.toNat] at hindex
          · exact .tail .d0 (ih hlen' (by omega))
          · have hc : indexMSB ds + 1 = 4 ^ es.length + indexMSB es := by omega
            obtain ⟨hmax, hzero⟩ := carry_bounds (by positivity) ha hb hc
            have hmax' : indexMSB ds = 4 ^ ds.length - 1 := by simpa [hlen'] using hmax
            rw [indexMSB_eq_max ds hmax', indexMSB_eq_zero es hzero]
            simpa [hlen'] using WordSucc.d01 ds.length
          · omega
          · omega
          · omega
          · exact .tail .d1 (ih hlen' (by omega))
          · have hc : indexMSB ds + 1 = 4 ^ es.length + indexMSB es := by omega
            obtain ⟨hmax, hzero⟩ := carry_bounds (by positivity) ha hb hc
            have hmax' : indexMSB ds = 4 ^ ds.length - 1 := by simpa [hlen'] using hmax
            rw [indexMSB_eq_max ds hmax', indexMSB_eq_zero es hzero]
            simpa [hlen'] using WordSucc.d12 ds.length
          · omega
          · omega
          · omega
          · exact .tail .d2 (ih hlen' (by omega))
          · have hc : indexMSB ds + 1 = 4 ^ es.length + indexMSB es := by omega
            obtain ⟨hmax, hzero⟩ := carry_bounds (by positivity) ha hb hc
            have hmax' : indexMSB ds = 4 ^ ds.length - 1 := by simpa [hlen'] using hmax
            rw [indexMSB_eq_max ds hmax', indexMSB_eq_zero es hzero]
            simpa [hlen'] using WordSucc.d23 ds.length
          · omega
          · omega
          · omega
          · exact .tail .d3 (ih hlen' (by omega))

@[simp] theorem indexMSB_append (a b : List Digit) :
    indexMSB (a ++ b) = indexMSB a * 4 ^ b.length + indexMSB b := by
  induction a with
  | nil => simp [indexMSB]
  | cons d ds ih =>
      simp only [List.cons_append, indexMSB, List.length_append, List.length_cons, ih]
      ring

@[simp] theorem indexMSB_reverse (ds : List Digit) :
    indexMSB ds.reverse = indexLSB ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
      rw [List.reverse_cons, indexMSB_append, ih]
      simp [indexMSB, indexLSB]
      ring

theorem indexLSB_injective_of_length {a b : List Digit}
    (hlen : a.length = b.length) (hindex : indexLSB a = indexLSB b) : a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp_all
  | cons d ds ih =>
      cases b with
      | nil => simp at hlen
      | cons e es =>
          simp only [indexLSB] at hindex
          have hmod : d.toNat % 4 = e.toNat % 4 := by omega
          have hde : d = e := by
            cases d <;> cases e <;> simp_all [Digit.toNat]
          subst e
          have htail : indexLSB ds = indexLSB es := by omega
          have hlen' : ds.length = es.length := by simpa using hlen
          rw [ih hlen' htail]

private theorem indexLSB_map_digitOfNat_fixed (ns : List ℕ)
    (hsmall : ∀ n ∈ ns, n < 4) :
    indexLSB (ns.map digitOfNat) = Nat.ofDigits 4 ns := by
  induction ns with
  | nil => rfl
  | cons n ns ih =>
      simp only [List.map_cons, indexLSB, Nat.ofDigits]
      rw [Digit.toNat_digitOfNat (hsmall n (by simp))]
      congr 1
      exact congrArg (fun z => 4 * z) (ih (fun x hx => hsmall x (by simp [hx])))

def fixedWord (k n : ℕ) : List Digit :=
  (Nat.digitsAppend 4 k n).map digitOfNat

theorem fixedWord_length {k n : ℕ} (hn : n < 4 ^ k) :
    (fixedWord k n).length = k := by
  simp [fixedWord, Nat.length_digitsAppend (by omega) k hn]

@[simp] theorem fixedWord_index {k n : ℕ} (hn : n < 4 ^ k) :
    indexLSB (fixedWord k n) = n := by
  have hsmall : ∀ d ∈ Nat.digitsAppend 4 k n, d < 4 :=
    fun d hd => Nat.lt_of_mem_digitsAppend (by omega) k d hd
  unfold fixedWord
  rw [indexLSB_map_digitOfNat_fixed _ hsmall]
  exact (Nat.setInvOn_digitsAppend_ofDigits (b := 4) (by omega) k).2 hn

def planarDist (p q : ℕ × ℕ) : ℕ :=
  Int.natAbs ((q.1 : ℤ) - p.1) + Int.natAbs ((q.2 : ℤ) - p.2)

theorem planarDist_triangle (p q r : ℕ × ℕ) :
    planarDist p r ≤ planarDist p q + planarDist q r := by
  have hx := Int.natAbs_add_le ((r.1 : ℤ) - q.1) ((q.1 : ℤ) - p.1)
  have hy := Int.natAbs_add_le ((r.2 : ℤ) - q.2) ((q.2 : ℤ) - p.2)
  have hx' : Int.natAbs ((r.1 : ℤ) - p.1) ≤
      Int.natAbs ((r.1 : ℤ) - q.1) + Int.natAbs ((q.1 : ℤ) - p.1) := by
    convert hx using 1 <;> ring
  have hy' : Int.natAbs ((r.2 : ℤ) - p.2) ≤
      Int.natAbs ((r.2 : ℤ) - q.2) + Int.natAbs ((q.2 : ℤ) - p.2) := by
    convert hy using 1 <;> ring
  unfold planarDist
  omega

def fixedPoint (k n : ℕ) : ℕ × ℕ :=
  coordinateMSB I (fixedWord k n).reverse

/-- Consecutive fixed-order Hilbert words map to unit lattice neighbors. -/
theorem coordinateMSB_wordSucc {a b : List Digit} (h : WordSucc a b) (s : Orient) :
    Int.natAbs ((coordinateMSB s b).1 - (coordinateMSB s a).1) +
      Int.natAbs ((coordinateMSB s b).2 - (coordinateMSB s a).2) = 1 := by
  induction h generalizing s with
  | tail d h ih =>
      simp only [coordinateMSB]
      have hlen := h.length_eq
      rw [hlen]
      have ht := ih (next s d)
      push_cast
      simpa only [add_sub_add_left_eq_sub] using ht
  | d01 n =>
      simp only [coordinateMSB, zeroWord_length, threeWord_length]
      rw [(coordinateMSB_endpoints (next s .d1) n).1,
        (coordinateMSB_endpoints (next s .d0) n).2]
      rcases s with ⟨sw, bx, cy⟩
      cases sw <;> cases bx <;> cases cy <;>
        simp [Orient.actNat, emit, next, child, refinement, Orient.act,
          Orient.compose, Orient.choose, Nat.pow_succ] <;>
        all_goals
          have hp : 1 ≤ 2 ^ n := one_le_pow₀ (by decide)
          norm_num [Bit.toNat, Nat.cast_sub hp, Int.natAbs] <;> decide
  | d12 n =>
      simp only [coordinateMSB, zeroWord_length, threeWord_length]
      rw [(coordinateMSB_endpoints (next s .d2) n).1,
        (coordinateMSB_endpoints (next s .d1) n).2]
      rcases s with ⟨sw, bx, cy⟩
      cases sw <;> cases bx <;> cases cy <;>
        simp [Orient.actNat, emit, next, child, refinement, Orient.act,
          Orient.compose, Orient.choose, Nat.pow_succ] <;>
        all_goals
          have hp : 1 ≤ 2 ^ n := one_le_pow₀ (by decide)
          norm_num [Bit.toNat, Nat.cast_sub hp, Int.natAbs] <;> decide
  | d23 n =>
      simp only [coordinateMSB, zeroWord_length, threeWord_length]
      rw [(coordinateMSB_endpoints (next s .d3) n).1,
        (coordinateMSB_endpoints (next s .d2) n).2]
      rcases s with ⟨sw, bx, cy⟩
      cases sw <;> cases bx <;> cases cy <;>
        simp [Orient.actNat, emit, next, child, refinement, Orient.act,
          Orient.compose, Orient.choose, Nat.pow_succ] <;>
        all_goals
          have hp : 1 ≤ 2 ^ n := one_le_pow₀ (by decide)
          norm_num [Bit.toNat, Nat.cast_sub hp, Int.natAbs] <;> decide

theorem fixedPoint_succ {k n : ℕ} (hn : n + 1 < 4 ^ k) :
    planarDist (fixedPoint k n) (fixedPoint k (n + 1)) = 1 := by
  have hn0 : n < 4 ^ k := by omega
  have hlen : (fixedWord k n).reverse.length = (fixedWord k (n + 1)).reverse.length := by
    simp [fixedWord_length hn0, fixedWord_length hn]
  have hsucc : WordSucc (fixedWord k n).reverse (fixedWord k (n + 1)).reverse := by
    apply WordSucc.of_index hlen
    simp [fixedWord_index hn0, fixedWord_index hn]
  simpa [fixedPoint, planarDist] using coordinateMSB_wordSucc hsucc I

theorem fixedPoint_add_dist_le {k n r : ℕ} (hbound : n + r < 4 ^ k) :
    planarDist (fixedPoint k n) (fixedPoint k (n + r)) ≤ r := by
  induction r with
  | zero => simp [planarDist]
  | succ r ih =>
      have hprev : n + r < 4 ^ k := by omega
      have hstep : n + r + 1 < 4 ^ k := by omega
      calc
        planarDist (fixedPoint k n) (fixedPoint k (n + (r + 1))) ≤
            planarDist (fixedPoint k n) (fixedPoint k (n + r)) +
              planarDist (fixedPoint k (n + r)) (fixedPoint k (n + r + 1)) := by
                apply planarDist_triangle
        _ ≤ r + 1 := by
          rw [fixedPoint_succ hstep]
          omega

/-- The low-to-high evaluator is the same Hilbert coordinate map read backwards
from the terminal orientation. -/
theorem coordinateMSB_eq_coordinateLSB_reverse (s : Orient) (ds : List Digit) :
    coordinateMSB s ds = coordinateLSB (run s ds).2 ds.reverse := by
  induction ds generalizing s with
  | nil => rfl
  | cons d ds ih =>
      rw [show (run s (d :: ds)).2 = (run (next s d) ds).2 by rfl,
        List.reverse_cons, coordinateLSB_append]
      rw [backwardState_run_reverse]
      rw [← ih (next s d)]
      simp only [coordinateLSB, List.length_reverse, List.length_cons, List.length_nil,
        Nat.zero_add]
      rw [← backward_emit s d]
      apply Prod.ext <;> simp [coordinateMSB] <;> ring

theorem run_state_append (s : Orient) (a b : List Digit) :
    (run s (a ++ b)).2 = (run (run s a).2 b).2 := by
  induction a generalizing s with
  | nil => rfl
  | cons d ds ih => simpa [run] using ih (next s d)

theorem run_backwardState_reverse (out : Orient) (ds : List Digit) :
    (run (backwardState out ds) ds.reverse).2 = out := by
  induction ds generalizing out with
  | nil => rfl
  | cons d ds ih =>
      simp only [backwardState, List.reverse_cons, run_state_append]
      rw [ih]
      exact previous_refinement out d

theorem coordinateMSB_reverse_of_backward (a : List Digit)
    (hback : backwardState I a = I) :
    coordinateMSB I a.reverse = coordinateLSB I a := by
  have hout := run_backwardState_reverse I a
  rw [hback] at hout
  have h := coordinateMSB_eq_coordinateLSB_reverse I a.reverse
  rw [List.reverse_reverse, hout] at h
  exact h

def paddedSelected (a k : ℕ) : List Digit :=
  selectedWord a ++ zeroPairs k

@[simp] theorem paddedSelected_length (a k : ℕ) :
    (paddedSelected a k).length = (selectedWord a).length + 2 * k := by
  simp [paddedSelected]

@[simp] theorem paddedSelected_index (a k : ℕ) :
    indexLSB (paddedSelected a k) = selectedIndex selectedState a := by
  simp [paddedSelected, indexLSB_append_zeroPairs, selectedWord_index]

@[simp] theorem paddedSelected_backward (a k : ℕ) :
    backwardState I (paddedSelected a k) = I := by
  simp [paddedSelected, backwardState_append, selectedWord_backward]

@[simp] theorem paddedSelected_coordinate (a k : ℕ) :
    coordinateLSB I (paddedSelected a k) = selectedPlanar a := by
  simp [paddedSelected, coordinateLSB_append_zeroPairs, selectedWord_backward,
    selectedPlanar]

theorem paddedSelected_index_bound (a k : ℕ) :
    selectedIndex selectedState a < 4 ^ (paddedSelected a k).length := by
  have h := indexMSB_lt_pow (paddedSelected a k).reverse
  rw [indexMSB_reverse, List.length_reverse] at h
  simpa using h

theorem paddedSelected_fixedPoint (a k : ℕ) :
    fixedPoint (paddedSelected a k).length (selectedIndex selectedState a) =
      selectedPlanar a := by
  have hbound := paddedSelected_index_bound a k
  have heq : paddedSelected a k =
      fixedWord (paddedSelected a k).length (selectedIndex selectedState a) := by
    apply indexLSB_injective_of_length
    · rw [fixedWord_length hbound]
    · rw [paddedSelected_index, fixedWord_index hbound]
  rw [fixedPoint, ← heq, coordinateMSB_reverse_of_backward]
  · exact paddedSelected_coordinate a k
  · exact paddedSelected_backward a k

theorem selectedPair_fixedPoint (a b : ℕ) :
    ∃ K,
      fixedPoint K (selectedIndex selectedState a) = selectedPlanar a ∧
      fixedPoint K (selectedIndex selectedState b) = selectedPlanar b ∧
      selectedIndex selectedState b < 4 ^ K := by
  obtain ⟨ka, hka⟩ := selectedWord_length_even a
  obtain ⟨kb, hkb⟩ := selectedWord_length_even b
  let K := (selectedWord a).length + (selectedWord b).length
  have hlenA : (paddedSelected a kb).length = K := by
    rw [paddedSelected_length]
    unfold K
    omega
  have hlenB : (paddedSelected b ka).length = K := by
    rw [paddedSelected_length]
    unfold K
    omega
  refine ⟨K, ?_, ?_, ?_⟩
  · rw [← hlenA]
    exact paddedSelected_fixedPoint a kb
  · rw [← hlenB]
    exact paddedSelected_fixedPoint b ka
  · rw [← hlenB]
    exact paddedSelected_index_bound b ka

theorem selectedPlanar_succ_dist_le (a : ℕ) :
    planarDist (selectedPlanar a) (selectedPlanar (a + 1)) ≤ 28 := by
  obtain ⟨gap, _, hgap, heq⟩ := selectedIndex_succ_gap selectedState a
  obtain ⟨K, hcoordA, hcoordB, hbound⟩ := selectedPair_fixedPoint a (a + 1)
  rw [← hcoordA, ← hcoordB]
  have hd := fixedPoint_add_dist_le
    (k := K) (n := selectedIndex selectedState a) (r := gap) (by rwa [← heq])
  rw [← heq] at hd
  omega

def displacement (p q : Point3) : Point3 where
  x := q.x - p.x
  y := q.y - p.y
  z := q.z - p.z
def finiteStepMenu : Set Point3 :=
  (fun p : (ℤ × ℤ) × ℤ => { x := p.1.1, y := p.1.2, z := p.2 }) ''
    (((Set.Icc (-28 : ℤ) 28).prod (Set.Icc (-28 : ℤ) 28)).prod
      (Set.Icc (4 : ℤ) 28))

theorem finiteStepMenu_finite : finiteStepMenu.Finite := by
  apply Set.Finite.image
  exact ((Set.finite_Icc (-28 : ℤ) 28).prod (Set.finite_Icc (-28 : ℤ) 28)).prod
    (Set.finite_Icc (4 : ℤ) 28)

private theorem int_bounds_of_natAbs_le {z : ℤ} (h : z.natAbs ≤ 28) :
    -28 ≤ z ∧ z ≤ 28 := by
  cases z <;> simp [Int.natAbs] at h ⊢ <;> omega

theorem selectedLift_step_mem (a : ℕ) :
    displacement (selectedLift a) (selectedLift (a + 1)) ∈ finiteStepMenu := by
  classical
  have hplanar := selectedPlanar_succ_dist_le a
  have hxabs : Int.natAbs (((selectedPlanar (a + 1)).1 : ℤ) -
      (selectedPlanar a).1) ≤ 28 := by
    unfold planarDist at hplanar
    omega
  have hyabs : Int.natAbs (((selectedPlanar (a + 1)).2 : ℤ) -
      (selectedPlanar a).2) ≤ 28 := by
    unfold planarDist at hplanar
    omega
  have hx := int_bounds_of_natAbs_le hxabs
  have hy := int_bounds_of_natAbs_le hyabs
  have haBounds := steeringValue_bounds (selectedState a)
  have hbBounds := steeringValue_bounds (selectedState (a + 1))
  have hz : (4 : ℤ) ≤
      (selectedIndex selectedState (a + 1) : ℤ) -
        selectedIndex selectedState a ∧
      (selectedIndex selectedState (a + 1) : ℤ) -
        selectedIndex selectedState a ≤ 28 := by
    unfold selectedIndex
    push_cast
    omega
  let v : (ℤ × ℤ) × ℤ :=
    ((((selectedPlanar (a + 1)).1 : ℤ) - (selectedPlanar a).1,
      ((selectedPlanar (a + 1)).2 : ℤ) - (selectedPlanar a).2),
      (selectedIndex selectedState (a + 1) : ℤ) -
        selectedIndex selectedState a)
  refine ⟨v, ?_, ?_⟩
  · exact ⟨⟨hx, hy⟩, hz⟩
  · rfl

/-- Unconditional finite-step, no-three-in-line walk in `ℤ³`. -/
theorem erdos193_unconditional :
    ∃ (S : Set Point3) (P : ℕ → Point3),
      S.Finite ∧
      (∀ n, displacement (P n) (P (n + 1)) ∈ S) ∧
      (∀ ⦃i j k⦄, i < j → j < k → ¬ OrderedCollinear (P i) (P j) (P k)) := by
  refine ⟨finiteStepMenu, selectedLift, finiteStepMenu_finite, ?_, ?_⟩
  · intro n
    exact selectedLift_step_mem n
  · intro i j k hij hjk
    exact selectedLift_no_three hij hjk
end Hilbert193


/- Amalgamated from Bridge.lean. -/

namespace Submissions.Erdos193HilbertCounterexample.Published

open Set

def IsSWalk {V : Type*} [AddCommGroup V] (S : Set V) (a : ℕ → V) : Prop :=
  ∀ n, a (n + 1) - a n ∈ S

def HasCollinearTriple (R) {V : Type*} [DivisionRing R] [AddCommGroup V]
    [Module R V] (A : Set V) : Prop :=
  ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
    x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ Collinear R ({x, y, z} : Set V)

abbrev statement : Prop :=
  ∀ S : Set (Fin 3 → ℤ), S.Finite →
    ∀ a : ℕ → Fin 3 → ℤ, IsSWalk S a → (range a).Infinite →
      HasCollinearTriple ℚ
        (range (fun n ↦ (↑) ∘ a n : ℕ → Fin 3 → ℚ))

open Hilbert193

def asVec (p : Point3) : Fin 3 → ℤ :=
  ![p.x, p.y, p.z]

def asRatVec (p : Point3) : Fin 3 → ℚ :=
  fun i ↦ (asVec p i : ℚ)

abbrev CanonicalCollinear (s : Set (Fin 3 → ℚ)) : Prop :=
  @Collinear ℚ (Fin 3 → ℚ) (Fin 3 → ℚ) _ _ _
    (AddGroup.instAddTorsor (Fin 3 → ℚ)) s

@[simp] theorem asVec_displacement (p q : Point3) :
    asVec (displacement p q) = asVec q - asVec p := by
  funext i
  fin_cases i <;> rfl

theorem asVec_selectedLift_injective :
    Function.Injective (fun n ↦ asVec (selectedLift n)) := by
  intro i j hij
  have hz := congrFun hij (2 : Fin 3)
  simp [asVec, selectedLift] at hz
  exact (selectedIndex_strictMono selectedState).injective hz

theorem orderedCollinear_of_collinear (p q r : Point3)
    (h : CanonicalCollinear ({asRatVec p, asRatVec q, asRatVec r} :
      Set (Fin 3 → ℚ))) :
    OrderedCollinear p q r := by
  have hp : asRatVec p ∈
      ({asRatVec p, asRatVec q, asRatVec r} : Set (Fin 3 → ℚ)) := by
    simp
  unfold CanonicalCollinear at h
  rw [collinear_iff_of_mem hp] at h
  obtain ⟨v, hv⟩ := h
  obtain ⟨sq, hq⟩ := hv (asRatVec q) (by simp)
  obtain ⟨sr, hr⟩ := hv (asRatVec r) (by simp)
  have hq0 := congrFun hq (0 : Fin 3)
  have hq1 := congrFun hq (1 : Fin 3)
  have hq2 := congrFun hq (2 : Fin 3)
  have hr0 := congrFun hr (0 : Fin 3)
  have hr1 := congrFun hr (1 : Fin 3)
  have hr2 := congrFun hr (2 : Fin 3)
  simp [asRatVec, asVec] at hq0 hq1 hq2 hr0 hr1 hr2
  unfold OrderedCollinear
  constructor <;> norm_num at *
  · exact_mod_cast (show
      ((r.z : ℚ) - q.z) * ((q.x : ℚ) - p.x) =
        ((q.z : ℚ) - p.z) * ((r.x : ℚ) - q.x) by
      rw [hq0, hq2, hr0, hr2]
      ring)
  · exact_mod_cast (show
      ((r.z : ℚ) - q.z) * ((q.y : ℚ) - p.y) =
        ((q.z : ℚ) - p.z) * ((r.y : ℚ) - q.y) by
      rw [hq1, hq2, hr1, hr2]
      ring)

theorem no_collinear_distinct {i j k : ℕ}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ¬CanonicalCollinear
      ({asRatVec (selectedLift i), asRatVec (selectedLift j),
        asRatVec (selectedLift k)} : Set (Fin 3 → ℚ)) := by
  intro h
  rcases lt_or_gt_of_ne hij with hij' | hji
  · rcases lt_or_gt_of_ne hjk with hjk' | hkj
    · exact selectedLift_no_three hij' hjk'
        (orderedCollinear_of_collinear _ _ _ h)
    · rcases lt_or_gt_of_ne hik with hik' | hki
      · have h' : CanonicalCollinear
            ({asRatVec (selectedLift i), asRatVec (selectedLift k),
              asRatVec (selectedLift j)} : Set (Fin 3 → ℚ)) := by
          convert h using 1 <;> ext x <;> simp [or_comm, or_left_comm, or_assoc]
        exact selectedLift_no_three hik' hkj
          (orderedCollinear_of_collinear _ _ _ h')
      · have h' : CanonicalCollinear
            ({asRatVec (selectedLift k), asRatVec (selectedLift i),
              asRatVec (selectedLift j)} : Set (Fin 3 → ℚ)) := by
          convert h using 1 <;> ext x <;> simp [or_comm, or_left_comm, or_assoc]
        exact selectedLift_no_three hki hij'
          (orderedCollinear_of_collinear _ _ _ h')
  · rcases lt_or_gt_of_ne hik with hik' | hki
    · have h' : CanonicalCollinear
          ({asRatVec (selectedLift j), asRatVec (selectedLift i),
            asRatVec (selectedLift k)} : Set (Fin 3 → ℚ)) := by
        convert h using 1 <;> ext x <;> simp [or_comm, or_left_comm, or_assoc]
      exact selectedLift_no_three hji hik'
        (orderedCollinear_of_collinear _ _ _ h')
    · rcases lt_or_gt_of_ne hjk with hjk' | hkj
      · have h' : CanonicalCollinear
            ({asRatVec (selectedLift j), asRatVec (selectedLift k),
              asRatVec (selectedLift i)} : Set (Fin 3 → ℚ)) := by
          convert h using 1 <;> ext x <;> simp [or_comm, or_left_comm, or_assoc]
        exact selectedLift_no_three hjk' hki
          (orderedCollinear_of_collinear _ _ _ h')
      · have h' : CanonicalCollinear
            ({asRatVec (selectedLift k), asRatVec (selectedLift j),
              asRatVec (selectedLift i)} : Set (Fin 3 → ℚ)) := by
          convert h using 1 <;> ext x <;> simp [or_comm, or_left_comm, or_assoc]
        exact selectedLift_no_three hkj hji
          (orderedCollinear_of_collinear _ _ _ h')

theorem proof : ¬statement := by
  intro hroot
  let S : Set (Fin 3 → ℤ) := asVec '' finiteStepMenu
  let a : ℕ → Fin 3 → ℤ := fun n ↦ asVec (selectedLift n)
  have hS : S.Finite := finiteStepMenu_finite.image asVec
  have ha : IsSWalk S a := by
    intro n
    rw [← asVec_displacement]
    exact ⟨displacement (selectedLift n) (selectedLift (n + 1)),
      selectedLift_step_mem n, rfl⟩
  have hinf : (range a).Infinite :=
    Set.infinite_range_of_injective asVec_selectedLift_injective
  obtain ⟨x, ⟨i, rfl⟩, y, ⟨j, rfl⟩, z, ⟨k, rfl⟩,
      hxy, hyz, hxz, hcol⟩ := hroot S hS a ha hinf
  apply no_collinear_distinct
      (i := i) (j := j) (k := k)
  · intro hij
    subst j
    exact hxy rfl
  · intro hjk
    subst k
    exact hyz rfl
  · intro hik
    subst k
    exact hxz rfl
  · change CanonicalCollinear
      ({asRatVec (selectedLift i), asRatVec (selectedLift j),
        asRatVec (selectedLift k)} : Set (Fin 3 → ℚ)) at hcol
    exact hcol


end Submissions.Erdos193HilbertCounterexample.Published
