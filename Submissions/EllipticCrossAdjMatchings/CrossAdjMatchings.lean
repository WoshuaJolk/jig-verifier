import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

namespace Submissions.EllipticCrossAdjMatchings.CrossAdjMatchings

def cOffset {r N : ℕ} (c : Fin r) : ZMod (2 * N) :=
  (2 * c.val : ℕ)

def dOffset {r N : ℕ} (d : Fin r) : ZMod (2 * N) :=
  (2 * d.val + 1 + if d.val + 1 = r then 2 else 0 : ℕ)

lemma cOffset_injective
    {r N : ℕ} (hN : r + 2 ≤ N) :
    Function.Injective (cOffset : Fin r → ZMod (2 * N)) := by
  intro c c' h
  have hm : 2 * c.val ≡ 2 * c'.val [MOD 2 * N] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp h
  have heq : 2 * c.val = 2 * c'.val :=
    hm.eq_of_lt_of_lt (by omega) (by omega)
  exact Fin.ext (by omega)

lemma dOffset_injective
    {r N : ℕ} (hN : r + 2 ≤ N) :
    Function.Injective (dOffset : Fin r → ZMod (2 * N)) := by
  intro d d' h
  have hm :
      2 * d.val + 1 + (if d.val + 1 = r then 2 else 0) ≡
        2 * d'.val + 1 + (if d'.val + 1 = r then 2 else 0)
        [MOD 2 * N] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp h
  have heq :
      2 * d.val + 1 + (if d.val + 1 = r then 2 else 0) =
        2 * d'.val + 1 + (if d'.val + 1 = r then 2 else 0) :=
    hm.eq_of_lt_of_lt (by split <;> omega) (by split <;> omega)
  by_cases hd : d.val + 1 = r <;>
    by_cases hd' : d'.val + 1 = r
  · exact Fin.ext (by omega)
  · simp [hd, hd'] at heq
    omega
  · simp [hd, hd'] at heq
    omega
  · simp [hd, hd'] at heq
    exact Fin.ext (by omega)

lemma cross_disjoint
    {r N : ℕ} (hN : r + 2 ≤ N)
    (i : ZMod (2 * N)) (c d : Fin r) :
    i + cOffset c ≠ -i + dOffset d := by
  haveI : NeZero (2 * N) := ⟨by omega⟩
  intro h
  have h' : i + i + cOffset c = dOffset d := by
    linear_combination h
  rw [← ZMod.natCast_zmod_val i] at h'
  have hcast :
      ((2 * i.val + 2 * c.val : ℕ) : ZMod (2 * N)) =
        (2 * d.val + 1 + (if d.val + 1 = r then 2 else 0) : ℕ) := by
    simpa [cOffset, dOffset, Nat.cast_add, Nat.cast_mul, two_mul] using h'
  have hm :
      2 * i.val + 2 * c.val ≡
        2 * d.val + 1 + (if d.val + 1 = r then 2 else 0)
        [MOD 2 * N] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
  have hm2 := hm.of_dvd (by omega : 2 ∣ 2 * N)
  by_cases hd : d.val + 1 = r <;> simp [Nat.ModEq, hd] at hm2

theorem proof :
    ∀ r N : ℕ, 2 ≤ r → r + 2 ≤ N →
      (Function.Injective (cOffset : Fin r → ZMod (2 * N))) ∧
      (Function.Injective (dOffset : Fin r → ZMod (2 * N))) ∧
      (∀ i : ZMod (2 * N),
        Function.Injective (fun c : Fin r => i + cOffset c) ∧
        Function.Injective (fun d : Fin r => -i + dOffset d) ∧
        (∀ (c d : Fin r), i + cOffset c ≠ -i + dOffset d)) := by
  intro r N _ hN
  have hc := cOffset_injective hN
  have hd := dOffset_injective hN
  refine ⟨hc, hd, ?_⟩
  intro i
  refine ⟨?_, ?_, ?_⟩
  · intro c c' h
    exact hc (add_left_cancel h)
  · intro d d' h
    exact hd (add_left_cancel h)
  · exact cross_disjoint hN i

end Submissions.EllipticCrossAdjMatchings.CrossAdjMatchings
