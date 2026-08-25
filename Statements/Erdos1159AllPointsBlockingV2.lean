import Mathlib.Data.Finset.Card

namespace Statements.Erdos1159AllPointsBlockingV2

noncomputable def pointsOnLine
    {Point Line : Type} (pointFintype : Fintype Point)
    (pointDecidableEq : DecidableEq Point)
    (Incidence : Point → Line → Prop)
    (incidenceDecidable : DecidableRel Incidence)
    (l : Line) : Finset Point := by
  letI := pointFintype
  letI := pointDecidableEq
  letI := incidenceDecidable
  exact Finset.univ.filter fun p => Incidence p l

noncomputable def linesOnPoint
    {Point Line : Type} (lineFintype : Fintype Line)
    (lineDecidableEq : DecidableEq Line)
    (Incidence : Point → Line → Prop)
    (incidenceDecidable : DecidableRel Incidence)
    (p : Point) : Finset Line := by
  letI := lineFintype
  letI := lineDecidableEq
  letI := incidenceDecidable
  exact Finset.univ.filter fun l => Incidence p l

noncomputable def lineIntersectionCard
    {Point Line : Type} (pointDecidableEq : DecidableEq Point)
    (Incidence : Point → Line → Prop)
    (incidenceDecidable : DecidableRel Incidence)
    (S : Finset Point) (l : Line) : ℕ := by
  letI := pointDecidableEq
  letI := incidenceDecidable
  exact (S.filter fun p => Incidence p l).card

/-- Selecting every point meets every line in exactly `q+1` points. -/
abbrev statement : Prop :=
  ∀ (Point Line : Type)
    (pointFintype : Fintype Point) (lineFintype : Fintype Line)
    (pointDecidableEq : DecidableEq Point)
    (lineDecidableEq : DecidableEq Line)
    (Incidence : Point → Line → Prop)
    (incidenceDecidable : DecidableRel Incidence) (order : ℕ),
    2 ≤ order →
    (∀ l : Line,
      (pointsOnLine pointFintype pointDecidableEq
        Incidence incidenceDecidable l).card = order + 1) →
    (∀ p : Point,
      (linesOnPoint lineFintype lineDecidableEq
        Incidence incidenceDecidable p).card = order + 1) →
    (∀ p q : Point, p ≠ q →
      ∃ l : Line, Incidence p l ∧ Incidence q l) →
    (∀ p q : Point, ∀ l m : Line, p ≠ q →
      Incidence p l → Incidence q l →
      Incidence p m → Incidence q m → l = m) →
    (∀ l m : Line, l ≠ m →
      ∃ p : Point, Incidence p l ∧ Incidence p m) →
    (∀ l m : Line, ∀ p q : Point, l ≠ m →
      Incidence p l → Incidence p m →
      Incidence q l → Incidence q m → p = q) →
    ∃ S : Finset Point, ∀ l : Line,
      lineIntersectionCard pointDecidableEq
        Incidence incidenceDecidable S l = order + 1

theorem target : statement := sorry

end Statements.Erdos1159AllPointsBlockingV2
