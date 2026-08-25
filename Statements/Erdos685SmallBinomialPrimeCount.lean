import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.PrimeFin

namespace Statements.Erdos685SmallBinomialPrimeCount

abbrev statement : Prop :=
  (Nat.choose 2 1).primeFactors.card = 1

theorem target : statement := sorry

end Statements.Erdos685SmallBinomialPrimeCount
