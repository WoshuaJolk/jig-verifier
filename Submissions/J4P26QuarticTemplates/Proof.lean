import Init

namespace Submissions.J4P26QuarticTemplates.Proof

def det (z i j k : Fin 4) : Int :=
  (z.val : Int)*((j.val : Int)-(i.val : Int))-((k.val : Int)-(i.val : Int))

theorem det_bound : ∀ z i j k : Fin 4, (det z i j k).natAbs ≤ 18 := by
  decide

theorem mod_lift (p : Nat) (hp : 31 ≤ p) (z i j k : Fin 4) :
    det z i j k % (p : Int) = 0 ↔ det z i j k = 0 := by
  constructor
  · intro h
    apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (Int.dvd_of_emod_eq_zero h)
    have hb := det_bound z i j k
    simpa only [Int.natAbs_natCast] using (show (det z i j k).natAbs < p by omega)
  · intro h
    rw [h]
    exact Int.zero_emod _

theorem integer_triple_templates : ∀ i j : Fin 4,
    (i ≠ j ∧ ∃ k : Fin 4, det 2 i j k = 0) ↔
    ((i=0 ∧ j=1) ∨ (i=1 ∧ j=2) ∨ (i=2 ∧ j=1) ∨ (i=3 ∧ j=2)) := by
  decide

theorem integer_gapped_templates : ∀ i j : Fin 4,
    (i ≠ j ∧ ∃ k : Fin 4, det 3 i j k = 0) ↔
    ((i=0 ∧ j=1) ∨ (i=3 ∧ j=2)) := by
  decide

theorem integer_automorphism_templates : ∀ i j : Fin 4,
    (i ≠ j ∧ (∃ k : Fin 4, det 2 i j k = 0) ∧ (∃ k : Fin 4, det 3 i j k = 0)) ↔
    ((i=0 ∧ j=1) ∨ (i=3 ∧ j=2)) := by
  decide

theorem triple_templates (p : Nat) (hp : 31 ≤ p) (i j : Fin 4) :
    (i ≠ j ∧ ∃ k : Fin 4, det 2 i j k % (p : Int) = 0) ↔
    ((i=0 ∧ j=1) ∨ (i=1 ∧ j=2) ∨ (i=2 ∧ j=1) ∨ (i=3 ∧ j=2)) := by
  simp only [mod_lift p hp]
  exact integer_triple_templates i j

theorem gapped_templates (p : Nat) (hp : 31 ≤ p) (i j : Fin 4) :
    (i ≠ j ∧ ∃ k : Fin 4, det 3 i j k % (p : Int) = 0) ↔
    ((i=0 ∧ j=1) ∨ (i=3 ∧ j=2)) := by
  simp only [mod_lift p hp]
  exact integer_gapped_templates i j

theorem automorphism_templates (p : Nat) (hp : 31 ≤ p) (i j : Fin 4) :
    (i ≠ j ∧ (∃ k : Fin 4, det 2 i j k % (p : Int) = 0) ∧
      (∃ k : Fin 4, det 3 i j k % (p : Int) = 0)) ↔
    ((i=0 ∧ j=1) ∨ (i=3 ∧ j=2)) := by
  simp only [mod_lift p hp]
  exact integer_automorphism_templates i j

theorem solves :
(∀ (p : Nat) (hp : 31 ≤ p) (i j : Fin 4),
(i ≠ j ∧ ∃ k : Fin 4, det 2 i j k % (p : Int) = 0) ↔
    ((i=0 ∧ j=1) ∨ (i=1 ∧ j=2) ∨ (i=2 ∧ j=1) ∨ (i=3 ∧ j=2))) ∧
(∀ (p : Nat) (hp : 31 ≤ p) (i j : Fin 4),
(i ≠ j ∧ ∃ k : Fin 4, det 3 i j k % (p : Int) = 0) ↔
    ((i=0 ∧ j=1) ∨ (i=3 ∧ j=2))) ∧
(∀ (p : Nat) (hp : 31 ≤ p) (i j : Fin 4),
(i ≠ j ∧ (∃ k : Fin 4, det 2 i j k % (p : Int) = 0) ∧
      (∃ k : Fin 4, det 3 i j k % (p : Int) = 0)) ↔
    ((i=0 ∧ j=1) ∨ (i=3 ∧ j=2))) := by
  exact ⟨@triple_templates, @gapped_templates, @automorphism_templates⟩

end Submissions.J4P26QuarticTemplates.Proof

