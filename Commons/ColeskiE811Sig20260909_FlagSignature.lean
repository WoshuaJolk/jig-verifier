import Commons.ColeskiE811Sig20260909_PatternScalar
import Commons.ColeskiE811Sig20260909_TablePermutations

/- BEGIN bundled local module FlagSignature -/


namespace ColeskiFlagSignature

open ColeskiK4Coverage ColeskiK5Coverage ColeskiPatternAction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev FivePattern := Pattern (Fin 5) (Fin 6)
abbrev FiveFlag := Fin 5 × Fin 6

def modulus : Nat := 2305843009213693951
def multiplier : Nat := 1000003
def seed : Nat := 1469598103934665603

def mixStep (h x : Nat) : Nat := (h * multiplier + x + 97) % modulus

def mix3 (x y z : Nat) : Nat :=
  mixStep (mixStep (mixStep seed x) y) z

def mix4 (w x y z : Nat) : Nat :=
  mixStep (mixStep (mixStep (mixStep seed w) x) y) z

def paletteColor (p : Fin 60) (c : Fin 6) : Fin 6 :=
  ⟨digit colorPermutations[p.val]! c.val, Nat.mod_lt _ (by decide)⟩

def optionCode (p : Fin 60) : Option (Fin 6) → Nat
  | none => 0
  | some c => 1 + (paletteColor p c).val

def bagSum {V : Type*} [Fintype V] (f : V → Nat) : Nat :=
  (∑ v, f v) % modulus

def bagSquareSum {V : Type*} [Fintype V] (f : V → Nat) : Nat :=
  (∑ v, (f v * f v) % modulus) % modulus

def degreeCount (x : FivePattern) (p : Fin 60) (v : Fin 5) (c : Fin 6) : Nat :=
  ∑ w : Fin 5, if optionCode p (x v w) = 1 + c.val then 1 else 0

def degreeCode (x : FivePattern) (p : Fin 60) (v : Fin 5) : Nat :=
  ∑ c : Fin 6, degreeCount x p v c * 5 ^ c.val

def initialLabel (x : FivePattern) (mark : Fin 5) (p : Fin 60) (v : Fin 5) : Nat :=
  degreeCode x p v + 15625 * (if v = mark then 0 else optionCode p (x mark v))

def neighborValue (x : FivePattern) (mark : Fin 5) (p : Fin 60)
    (v w : Fin 5) : Nat :=
  if w = v then 0 else optionCode p (x v w) + 7 * initialLabel x mark p w

def refinedLabel (x : FivePattern) (mark : Fin 5) (p : Fin 60) (v : Fin 5) : Nat :=
  mix3 (initialLabel x mark p v)
    (bagSum (neighborValue x mark p v))
    (bagSquareSum (neighborValue x mark p v))

def otherRefinedValue (x : FivePattern) (mark : Fin 5) (p : Fin 60)
    (v : Fin 5) : Nat :=
  if v = mark then 0 else refinedLabel x mark p v

def candidate (x : FivePattern) (flag : FiveFlag) (p : Fin 60) : Nat :=
  mix4 (1 + (paletteColor p flag.2).val)
    (refinedLabel x flag.1 p flag.1)
    (bagSum (otherRefinedValue x flag.1 p))
    (bagSquareSum (otherRefinedValue x flag.1 p))

def signature (x : FivePattern) (flag : FiveFlag) : Nat :=
  mixStep (mixStep seed (bagSum (candidate x flag)))
    (bagSquareSum (candidate x flag))

end ColeskiFlagSignature

/- END bundled local module FlagSignature -/
