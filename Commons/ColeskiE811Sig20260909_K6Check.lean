import Commons.ColeskiE811Sig20260909_OrbitChecks
import Commons.ColeskiE811Sig20260909_PatternScalar

/- BEGIN bundled local module K6Check -/

namespace ColeskiK6Check
open ColeskiK4Coverage ColeskiK5Coverage ColeskiPatternCode ColeskiOrbitChecks

def edgeColor (r a i j : Nat) : Nat :=
  if i = j then 0 else
    let lo := min i j
    let hi := max i j
    if hi = 5 then digit a lo else digit r (edgeIndex lo hi)

def skip (z i : Nat) : Nat := if i < z then i else i+1

def deletionCode (r a z : Nat) : Nat :=
  (List.range 10).foldl (fun acc e =>
    acc + 6^e * edgeColor r a (skip z (edgeLeft5 e)) (skip z (edgeRight5 e))) 0

def deletionCheck (r a z w : Nat) : Bool :=
  0 < w && w ≤ 3967200 && transformed5 w == deletionCode r a z

def flagWeight (w mark color : Nat) : Int :=
  let k := w-1
  (weight (k/7200) (digit vertexPermutations5[k/60%120]! mark)
    (digit inverseColors[k%60]! color) : Int) - 170

def contribution (r a z w mark : Nat) : Int :=
  6 * flagWeight w mark (edgeColor r a (skip z mark) z) -
    ((List.range 6).map (fun c => flagWeight w mark c)).sum

def total (r a : Nat) (ws : Array Nat) : Int :=
  ((List.range 6).map (fun z =>
    ((List.range 5).map (fun mark => contribution r a z ws[z]! mark)).sum)).sum

def checkPositive (r a : Nat) (ws : Array Nat) : Bool :=
  (List.range 6).all (fun z => deletionCheck r a z ws[z]!) && 0 < total r a ws
end ColeskiK6Check

/- END bundled local module K6Check -/
