import Mathlib.Data.Finset.Card

namespace Statements.Erdos1159AllPointsBlocking

structure FiniteProjectivePlane where
  Point : Type
  Line : Type
  pointFintype : Fintype Point
  lineFintype : Fintype Line
  pointDecidableEq : DecidableEq Point
  lineDecidableEq : DecidableEq Line
  Incidence : Point → Line → Prop
  incidenceDecidable : DecidableRel Incidence
  order : ℕ
  order_ge_two : 2 ≤ order
  points_per_line :
    ∀ l : Line,
      (@Finset.filter Point
          (fun p => Incidence p l) (fun p => incidenceDecidable p l)
          (@Finset.univ Point pointFintype)).card =
        order + 1
  lines_per_point :
    ∀ p : Point,
      (@Finset.filter Line
          (fun l => Incidence p l) (incidenceDecidable p)
          (@Finset.univ Line lineFintype)).card =
        order + 1
  line_through :
    ∀ {p q : Point}, p ≠ q →
      ∃ l : Line, Incidence p l ∧ Incidence q l
  line_unique :
    ∀ {p q : Point} {l m : Line}, p ≠ q →
      Incidence p l → Incidence q l →
      Incidence p m → Incidence q m → l = m
  point_on_both :
    ∀ {l m : Line}, l ≠ m →
      ∃ p : Point, Incidence p l ∧ Incidence p m
  point_unique :
    ∀ {l m : Line} {p q : Point}, l ≠ m →
      Incidence p l → Incidence p m →
      Incidence q l → Incidence q m → p = q

noncomputable def lineIntersectionCard
    (P : FiniteProjectivePlane) (S : Finset P.Point) (l : P.Line) : ℕ := by
  letI := P.pointDecidableEq
  letI := P.incidenceDecidable
  exact (S.filter fun p => P.Incidence p l).card

/-- The whole point set is a blocking set meeting every line in
exactly `q+1` points. -/
abbrev statement : Prop :=
  ∀ P : FiniteProjectivePlane,
    ∃ S : Finset P.Point, ∀ l : P.Line,
      lineIntersectionCard P S l = P.order + 1

theorem target : statement := sorry

end Statements.Erdos1159AllPointsBlocking
