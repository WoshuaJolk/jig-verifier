import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic
import Mathlib.Data.Nat.Find

namespace Submissions.Erdos687CRTFiniteReduction.Declan

open scoped BigOperators

def smallPrimes (X : ℕ) : Finset ℕ :=
  (Finset.range (X + 1)).filter Nat.Prime

def primorial (X : ℕ) : ℕ := ∏ p ∈ smallPrimes X, p

def CoversInitialInterval (X y : ℕ) : Prop :=
  ∃ residue : ℕ → ℕ,
    ∀ m : ℕ, 1 ≤ m → m ≤ y →
      ∃ p : ℕ, p.Prime ∧ p ≤ X ∧ m % p = residue p % p

@[simp] theorem mem_smallPrimes {X p : ℕ} :
    p ∈ smallPrimes X ↔ p.Prime ∧ p ≤ X := by
  simp [smallPrimes, and_comm]

theorem primorial_pos (X : ℕ) : 0 < primorial X := by
  apply Finset.prod_pos
  intro p hp
  exact (mem_smallPrimes.mp hp).1.pos

theorem primes_pairwise (X : ℕ) :
    Set.Pairwise (smallPrimes X : Set ℕ) Nat.Coprime := by
  intro p hp q hq hpq
  exact (Nat.coprime_primes (mem_smallPrimes.mp hp).1
    (mem_smallPrimes.mp hq).1).mpr hpq

theorem crt (X : ℕ) (r : ℕ → ℕ) :
    ∃ a < primorial X, ∀ p ∈ smallPrimes X, Nat.ModEq p a (r p) := by
  have hp : ∀ p ∈ smallPrimes X, p ≠ 0 := by
    intro p hp
    exact (mem_smallPrimes.mp hp).1.ne_zero
  let a := Nat.chineseRemainderOfFinset r id (smallPrimes X) hp (primes_pairwise X)
  exact ⟨a, Nat.chineseRemainderOfFinset_lt_prod r id hp (primes_pairwise X), a.property⟩

theorem complement_zero {p r : ℕ} (hp : 0 < p) :
    Nat.ModEq p ((p - r % p) + r) 0 := by
  change ((p - r % p) + r) % p = 0 % p
  have hh : ((p - r % p) + r) % p = ((p - r % p) + r % p) % p := by
    simp only [Nat.add_mod, Nat.mod_mod]
  rw [hh, Nat.sub_add_cancel (Nat.le_of_lt (Nat.mod_lt r hp))]
  simp

theorem div_iff_residue {p a m r : ℕ} (ha : Nat.ModEq p (a + r) 0) :
    p ∣ a + m ↔ m % p = r % p := by
  change p ∣ a + m ↔ Nat.ModEq p m r
  rw [← Nat.modEq_zero_iff_dvd]
  constructor
  · intro hm
    exact Nat.ModEq.add_left_cancel' a (hm.trans ha.symm)
  · intro hm
    exact (hm.add_left a).trans ha

theorem coprime_primorial_iff (X n : ℕ) :
    Nat.Coprime (primorial X) n ↔
      ∀ p, p.Prime → p ≤ X → ¬ p ∣ n := by
  simp only [primorial, Nat.coprime_prod_left_iff, mem_smallPrimes]
  constructor
  · intro h p hp hpx
    exact hp.coprime_iff_not_dvd.mp (h p ⟨hp,hpx⟩)
  · intro h p hp
    exact hp.1.coprime_iff_not_dvd.mpr (h p hp.1 hp.2)

theorem not_coprime_primorial_iff (X n : ℕ) :
    ¬ Nat.Coprime (primorial X) n ↔
      ∃ p, p.Prime ∧ p ≤ X ∧ p ∣ n := by
  rw [coprime_primorial_iff]
  push Not
  rfl

theorem covers_iff_shift (X y : ℕ) :
    CoversInitialInterval X y ↔
      ∃ a < primorial X, ∀ m, 1 ≤ m → m ≤ y →
        ¬ Nat.Coprime (primorial X) (a + m) := by
  constructor
  · rintro ⟨r, hr⟩
    obtain ⟨a, ha, hamod⟩ := crt X (fun p => p - r p % p)
    refine ⟨a, ha, ?_⟩
    intro m hm hmy
    obtain ⟨p, hp, hpX, hmr⟩ := hr m hm hmy
    apply (not_coprime_primorial_iff X (a + m)).mpr
    refine ⟨p, hp, hpX, ?_⟩
    apply (div_iff_residue ?_).mpr hmr
    exact ((hamod p (mem_smallPrimes.mpr ⟨hp,hpX⟩)).add_right (r p)).trans
      (complement_zero hp.pos)
  · rintro ⟨a, ha, hr⟩
    refine ⟨fun p => p - a % p, ?_⟩
    intro m hm hmy
    obtain ⟨p,hp,hpX,hpdiv⟩ := (not_coprime_primorial_iff X (a+m)).mp (hr m hm hmy)
    refine ⟨p,hp,hpX,?_⟩
    apply (div_iff_residue ?_).mp hpdiv
    simpa [Nat.add_comm] using (complement_zero (r:=a) hp.pos)

theorem covers_lt_primorial {X y : ℕ} (h : CoversInitialInterval X y) :
    y < primorial X := by
  obtain ⟨a, ha, hgap⟩ := (covers_iff_shift X y).mp h
  by_contra! hyp
  by_cases ha0 : a = 0
  · have hh := hgap 1 (by omega) (by have := primorial_pos X; omega)
    subst a
    simpa using hh
  · have ham : a + (primorial X - a + 1) = primorial X + 1 := by omega
    have hh := hgap (primorial X - a + 1) (by omega) (by omega)
    rw [ham] at hh
    simpa using hh

theorem covers_zero (X : ℕ) : CoversInitialInterval X 0 := by
  refine ⟨fun _ => 0, ?_⟩
  intro m hm hm0
  omega

theorem exists_maximum (X : ℕ) :
    ∃ Y < primorial X, CoversInitialInterval X Y ∧
      ∀ y, CoversInitialInterval X y → y ≤ Y := by
  classical
  let Y := Nat.findGreatest (CoversInitialInterval X) (primorial X - 1)
  have hY : CoversInitialInterval X Y :=
    Nat.findGreatest_spec (Nat.zero_le _) (covers_zero X)
  refine ⟨Y, covers_lt_primorial hY, hY, ?_⟩
  intro y hy
  exact Nat.le_findGreatest (by have := covers_lt_primorial hy; omega) hy

abbrev statement : Prop :=
  (∀ X y : ℕ, CoversInitialInterval X y ↔
    ∃ a < primorial X, ∀ m, 1 ≤ m → m ≤ y →
      ¬ Nat.Coprime (primorial X) (a + m)) ∧
  (∀ X y : ℕ, CoversInitialInterval X y → y < primorial X) ∧
  (∀ X : ℕ, ∃ Y < primorial X, CoversInitialInterval X Y ∧
    ∀ y, CoversInitialInterval X y → y ≤ Y)

theorem proof : statement := by
  exact ⟨covers_iff_shift, fun _ _ h => covers_lt_primorial h, exists_maximum⟩

#print axioms proof

end Submissions.Erdos687CRTFiniteReduction.Declan
