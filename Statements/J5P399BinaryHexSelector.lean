import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Finite

namespace Statements.J5P399BinaryHexSelector

def changes (prev last : Bool) (as : List Bool) : Nat :=
  (as.foldr (fun (a : Bool) (f : Bool → Nat) (p : Bool) =>
    (if p = a then 0 else 1) + f a)
    (fun (p : Bool) => if p = last then 0 else 1)) prev

def ones (bs : List Bool) : Nat :=
  bs.foldr (fun (b : Bool) (n : Nat) => (if b then 1 else 0) + n) 0

def xorBits (as bs : List Bool) : List Bool :=
  List.zipWith Bool.xor as bs

def statement : Prop :=
  ∀ (a0 : Bool) (as : List Bool)
    (hg : 4 ≤ as.length+1) (heven : (as.length+1) % 2 = 0),
    ∃ k : Nat, 2 ≤ k ∧ ∃ bs : List Bool,
      bs.length = as.length ∧
      as.length+1 + 2*ones bs + changes a0 a0 (xorBits as bs) = 2^k

end Statements.J5P399BinaryHexSelector
