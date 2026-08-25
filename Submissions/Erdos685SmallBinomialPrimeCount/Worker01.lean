import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.PrimeFin

namespace Submissions.Erdos685SmallBinomialPrimeCount.Worker01

theorem proof : (Nat.choose 2 1).primeFactors.card = 1 := by
  simp [Nat.primeFactors]

end Submissions.Erdos685SmallBinomialPrimeCount.Worker01
