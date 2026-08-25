import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Set.Card
import Mathlib.Tactic

namespace Submissions.Erdos371InfinitelyManyRises.Direct

def largestPrimeFactor (n : ℕ) : ℕ :=
  if n = 1 then 1 else n.primeFactorsList.getLastI

lemma largestPrimeFactor_dvd : ∀ n : ℕ, largestPrimeFactor n ∣ n
  | 0 => by simp [largestPrimeFactor, List.getLastI]
  | 1 => by simp [largestPrimeFactor]
  | n + 2 => by
    have hn : 1 < n + 2 := by omega
    have hlist : (n + 2).primeFactorsList ≠ [] :=
      (Nat.primeFactorsList_ne_nil (n + 2)).2 hn
    have hmem :
        (n + 2).primeFactorsList.getLast hlist ∈
          (n + 2).primeFactorsList :=
      List.getLast_mem hlist
    have hdvd :
        (n + 2).primeFactorsList.getLast hlist ∣ n + 2 :=
      Nat.dvd_of_mem_primeFactorsList hmem
    simpa [largestPrimeFactor, hn.ne', List.getLastI_eq_getLast?_getD,
      List.getLast?_eq_getLast_of_ne_nil hlist] using hdvd

lemma largestPrimeFactor_le (n : ℕ) : largestPrimeFactor n ≤ n := by
  obtain rfl | rfl | n := n
  · simp [largestPrimeFactor, List.getLastI]
  · simp [largestPrimeFactor]
  · exact Nat.le_of_dvd (by omega) (largestPrimeFactor_dvd (n + 2))

lemma prime_largestPrimeFactor {p : ℕ} (hp : p.Prime) :
    largestPrimeFactor p = p := by
  simp [largestPrimeFactor, hp.ne_one, Nat.primeFactorsList_prime hp,
    List.getLastI]

lemma shifted_prime_rises (p : ℕ) (hp : p.Prime) :
    largestPrimeFactor ((p - 1) + 1) > largestPrimeFactor (p - 1) := by
  rw [Nat.sub_add_cancel hp.one_le, prime_largestPrimeFactor hp]
  exact (largestPrimeFactor_le (p - 1)).trans_lt
    (Nat.sub_lt hp.pos zero_lt_one)

theorem proof :
    {n : ℕ | largestPrimeFactor (n + 1) >
      largestPrimeFactor n}.Infinite := by
  have hinj : Set.InjOn (fun p : ℕ => p - 1) {p | p.Prime} := by
    intro p hp q hq hpq
    change p.Prime at hp
    change q.Prime at hq
    change p - 1 = q - 1 at hpq
    have hp2 := hp.two_le
    have hq2 := hq.two_le
    omega
  have himage : ((fun p : ℕ => p - 1) '' {p | p.Prime}).Infinite :=
    Nat.infinite_setOfPred_prime.image hinj
  refine himage.mono ?_
  rintro n ⟨p, hp, rfl⟩
  exact shifted_prime_rises p hp

end Submissions.Erdos371InfinitelyManyRises.Direct
