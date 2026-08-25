import Mathlib.Data.Finset.Card

namespace Statements.Erdos1159BoundedBlockingSet

/-- A finite projective plane presented as its finite incidence structure
of order at least two. The cardinality axioms are the standard definition
of the order; the two uniqueness axioms are the projective-plane axioms. -/
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

/-- Erdős Problem 1159: one absolute constant should bound the
nonempty intersections of a blocking set with every line in every
finite projective plane. -/
abbrev statement : Prop :=
  ∃ C : ℕ, 1 < C ∧
    ∀ P : FiniteProjectivePlane,
      ∃ S : Finset P.Point, ∀ l : P.Line,
        1 ≤ lineIntersectionCard P S l ∧
          lineIntersectionCard P S l ≤ C

theorem target : statement := sorry

end Statements.Erdos1159BoundedBlockingSet
