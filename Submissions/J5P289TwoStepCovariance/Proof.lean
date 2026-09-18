import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.NormNum

/-!
An exact obstruction to applying ferromagnetic monomial correlation inequalities
to the uniform strict SAW law. The walk definitions are copied from Jig #289.
This finite calculation does not refute the endpoint superdiffusivity conjecture.
-/
namespace PlanarSAWTwoStepCorrelation

abbrev Point := ℤ × ℤ

def step (d : Fin 4) : Point :=
  if d = 0 then (1, 0)
  else if d = 1 then (-1, 0)
  else if d = 2 then (0, 1)
  else (0, -1)

def position {n : ℕ} (s : Fin n → Fin 4) (t : Fin (n + 1)) : Point :=
  let ht : t.val ≤ n := Nat.le_of_lt_succ t.isLt
  ∑ i : Fin t.val, step (s (Fin.castLE ht i))

def IsSelfAvoidingWalk {n : ℕ} (s : Fin n → Fin 4) : Prop :=
  Function.Injective (position s)

noncomputable def walks (n : ℕ) : Finset (Fin n → Fin 4) := by
  classical
  exact Finset.univ.filter IsSelfAvoidingWalk

abbrev Word := Fin 2 → Fin 4

def spinU (d : Fin 4) : ℤ := (step d).1 + (step d).2
def spinV (d : Fin 4) : ℤ := (step d).1 - (step d).2
def A (s : Word) : ℤ := spinU (s 0) * spinU (s 1)
def B (s : Word) : ℤ := spinV (s 0) * spinV (s 1)

def twoWalks : Finset Word :=
  Finset.univ.filter (fun s => step (s 0) + step (s 1) ≠ (0, 0))

theorem two_saw_iff : ∀ s : Word,
    IsSelfAvoidingWalk s ↔ step (s 0) + step (s 1) ≠ (0, 0) := by
  unfold IsSelfAvoidingWalk Function.Injective
  decide

theorem canonical_walks_two : walks 2 = twoWalks := by
  classical
  ext s
  simp [walks, twoWalks, two_saw_iff]

theorem exact_counts : (walks 2).card = 12 ∧
    (∑ s ∈ walks 2, A s) = 4 ∧
    (∑ s ∈ walks 2, B s) = 4 ∧
    (∑ s ∈ walks 2, A s * B s) = -4 := by
  rw [canonical_walks_two]
  decide

noncomputable def mean (f : Word → ℤ) : ℚ :=
  ((∑ s ∈ walks 2, f s : ℤ) : ℚ) / (walks 2).card

/-- The full uniform 12-walk law has a negative monomial covariance. -/
theorem covariance_negative :
    mean (fun s => A s * B s) - mean A * mean B = -4 / 9 ∧
    mean (fun s => A s * B s) < mean A * mean B := by
  obtain ⟨hc, ha, hb, hab⟩ := exact_counts
  norm_num [mean, hc, ha, hb, hab]

#print axioms two_saw_iff
#print axioms exact_counts
#print axioms covariance_negative

end PlanarSAWTwoStepCorrelation

/- Packaging alias: combines the two unchanged saved declarations. -/
namespace Submissions.J5P289TwoStepCovariance.Proof

open PlanarSAWTwoStepCorrelation

theorem proof :
  ((walks 2).card = 12 ∧
    (∑ s ∈ walks 2, A s) = 4 ∧
    (∑ s ∈ walks 2, B s) = 4 ∧
    (∑ s ∈ walks 2, A s * B s) = -4) ∧
  (mean (fun s => A s * B s) - mean A * mean B = -4 / 9 ∧
    mean (fun s => A s * B s) < mean A * mean B) :=
  ⟨PlanarSAWTwoStepCorrelation.exact_counts,
    PlanarSAWTwoStepCorrelation.covariance_negative⟩

end Submissions.J5P289TwoStepCovariance.Proof
