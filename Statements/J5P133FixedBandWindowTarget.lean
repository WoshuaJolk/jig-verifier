import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Fin
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Data.Multiset.Fintype
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Order.Monotone.Basic

/- Independent canonical proposal: exact saved definitions and conditional target.
   No submission/owner import, root-resolution or novelty assertion.
   Uncompiled; namespace/definitional bridge and inhabited controls remain pending. -/

namespace Statements.J5P133FixedBandWindowTarget

section
/- Exact definition scope from FixedTargetDensity. -/
noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology ENNReal
namespace Jig133.FixedTargetDensity

def leak (E : Set ℝ) (r x : ℝ) : ℝ := volume.real (closedBall x r \ E)

def scaledLeak (E : Set ℝ) (k : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (n : ℝ) * leak E (k / n) x

end Jig133.FixedTargetDensity
end
end

section
/- Exact definition scope from FixedTargetHalos. -/
noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology ENNReal
namespace Jig133.FixedTargetHalos
open FixedTargetDensity

def good (E : Set ℝ) (R : ℕ → ℕ) (n : ℕ) : Set ℝ :=
  E ∩ {x | scaledLeak E (R n) n x < 1 / (R n : ℝ)}

end Jig133.FixedTargetHalos
end
end

section
/- Exact definition scope from FullProductLocalBand. -/
noncomputable section
open Set Polynomial
open scoped BigOperators
namespace Jig133.FullProductLocalBand
local instance : DecidableEq ℂ := Classical.decEq _

abbrev RootIndex (P : ℝ[X]) : Type := (P.map Complex.ofRealHom).roots

def root (P : ℝ[X]) (i : RootIndex P) : ℂ := i

end Jig133.FullProductLocalBand
end
end

section
/- Exact definition scope from FullProductBandScale. -/
noncomputable section
open Set Polynomial
namespace Jig133.FullProductBandScale
open FullProductLocalBand

def width (c B L : ℝ) : ℝ := min (c / 4) (min (1 / (4 * L)) (min (c / (64 * B)) (1 / 16)))

end Jig133.FullProductBandScale
end
end

section
/- Exact definition scope from FiniteRootDensity. -/
open Set MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
namespace Jig133.FiniteRootDensity
variable {ι : Type*} [Fintype ι]
attribute [local instance] Classical.propDecidable

def count (nodes : ι → ℝ) (c r : ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => |c - nodes i| ≤ r)).card

def densitySet (nodes : ι → ℝ) (L : ℝ) : Set ℝ :=
  {x | ∃ r : ℝ, 0 < r ∧ L * r < (count nodes x r : ℝ)}

end Jig133.FiniteRootDensity
end
end

section
/- Exact definition scope from FullProductProjectedFilter. -/
noncomputable section
open Set MeasureTheory Polynomial
open scoped ENNReal BigOperators
namespace Jig133.FullProductProjectedFilter
open FullProductLocalBand

def projected (P : ℝ[X]) (i : RootIndex P) : ℝ := (root P i).re

def near (P : ℝ[X]) (c : ℝ) (n : ℕ) : Set ℝ :=
  ⋃ i : RootIndex P, Icc (projected P i - c / n) (projected P i + c / n)

def bad (P : ℝ[X]) (c B : ℝ) (n : ℕ) : Set ℝ :=
  FiniteRootDensity.densitySet (projected P) (2 * B * n) ∪ near P c n

end Jig133.FullProductProjectedFilter
end
end

section
/- Exact definition scope from FullProductRootFilter. -/
noncomputable section
open Set MeasureTheory Polynomial
open scoped ENNReal
namespace Jig133.FullProductRootFilter
open FullProductLocalBand FullProductBandScale

def bad (P : ℝ[X]) (c B L : ℝ) (n : ℕ) : Set ℝ :=
  FullProductProjectedFilter.bad P c B n ∪ {x | L * n < |P.derivative.eval x / P.eval x|}

end Jig133.FullProductRootFilter
end
end

section
/- Exact definition scope from FiniteSourceNets. -/
open Set
open scoped BigOperators
namespace Jig133.FiniteSourceNets
noncomputable section
attribute [local instance] Classical.propDecidable

def Separated (Y : Finset ℝ) (ρ : ℝ) : Prop :=
  ∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → ρ ≤ |x - y|

def IsSourceNet (X Y : Finset ℝ) (ρ : ℝ) : Prop :=
  Y ⊆ X ∧ Separated Y ρ ∧ ∀ x ∈ X, ∃ y ∈ Y, |x - y| < ρ

def window {D : ℕ} (a b : Fin D → ℝ) : Set ℝ := ⋃ i, Icc (a i) (b i)

end
end Jig133.FiniteSourceNets
end

section
/- Exact definition scope from FiniteSourceGaps. -/
noncomputable section
open Set
open scoped BigOperators
namespace Jig133.FiniteSourceGaps
attribute [local instance] Classical.propDecidable

def vertices (Y : Finset ℝ) : Finset ℝ := insert (-1) (insert 1 Y)

def count (Y : Finset ℝ) : ℕ := (vertices Y).card - 1

theorem vertices_nonempty (Y : Finset ℝ) : (vertices Y).Nonempty :=
  ⟨-1, Finset.mem_insert_self _ _⟩

def point (Y : Finset ℝ) : Fin (count Y + 1) ↪o ℝ :=
  (vertices Y).orderEmbOfFin (Nat.sub_add_cancel
    (Finset.card_pos.mpr (vertices_nonempty Y))).symm

def left (Y : Finset ℝ) (i : Fin (count Y)) : ℝ := point Y i.castSucc

def right (Y : Finset ℝ) (i : Fin (count Y)) : ℝ := point Y i.succ

end Jig133.FiniteSourceGaps
end
end

section
/- Exact definition scope from LongSourceGapBound. -/
noncomputable section
open Set
open scoped BigOperators
namespace Jig133.LongSourceGapBound
open FiniteSourceGaps FiniteSourceNets
attribute [local instance] Classical.propDecidable

def indices (Y : Finset ℝ) (H : ℝ) (n : ℕ) : Finset (Fin (count Y)) :=
  Finset.univ.filter (fun i => H / (n : ℝ) < right Y i - left Y i)

def gaps (Y : Finset ℝ) (H : ℝ) (n : ℕ) : Set ℝ :=
  ⋃ i ∈ indices Y H n, Icc (left Y i) (right Y i)

end Jig133.LongSourceGapBound
end
end

section
/- Exact definition scope from DiscreteRankDensity. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace Jig133.DiscreteRankDensity
attribute [local instance] Classical.propDecidable
variable {m : ℕ}

def span (g : Fin m → ℝ) (a b : Fin m) : ℝ := ∑ j ∈ Finset.Icc a b, g j

def badIndices (g : Fin m → ℝ) (T : ℝ) : Finset (Fin m) :=
  Finset.univ.filter (fun i => ∃ a b : Fin m, a ≤ i ∧ i ≤ b ∧
    T * ((b.val + 1 - a.val : ℕ) : ℝ) < span g a b)

end Jig133.DiscreteRankDensity
end
end

section
/- Exact definition scope from SourceRankGeometry. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Jig133.SourceRankGeometry
open FiniteSourceGaps
attribute [local instance] Classical.propDecidable

def length (Y : Finset ℝ) (i : Fin (count Y)) : ℝ := right Y i - left Y i

def badIndices (Y : Finset ℝ) (C : ℝ) (n : ℕ) : Finset (Fin (count Y)) :=
  DiscreteRankDensity.badIndices (length Y) (C / n)

def shortBad (Y : Finset ℝ) (C G : ℝ) (n : ℕ) : Finset (Fin (count Y)) :=
  (badIndices Y C n).filter (fun i => length Y i ≤ G / n)

def shortBadUnion (Y : Finset ℝ) (C G : ℝ) (n : ℕ) : Set ℝ :=
  ⋃ i ∈ shortBad Y C G n, Icc (left Y i) (right Y i)

end Jig133.SourceRankGeometry
end
end

section
/- Exact definition scope from SourceGapSelection. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Jig133.SourceGapSelection
open FiniteSourceGaps
attribute [local instance] Classical.propDecidable

def qualifies (Y : Finset ℝ) (Q : Set ℝ) (i : Fin (count Y)) : Prop :=
  left Y i ∈ Y ∧ right Y i ∈ Y ∧ (Q ∩ Ioo (left Y i) (right Y i)).Nonempty

def indices (Y : Finset ℝ) (Q : Set ℝ) : Finset (Fin (count Y)) :=
  Finset.univ.filter (qualifies Y Q)

def anchor (Y : Finset ℝ) (Q : Set ℝ) (i : Fin (count Y)) : ℝ :=
  if h : qualifies Y Q i then Classical.choose h.2.2 else 0

end Jig133.SourceGapSelection
end
end

section
/- Exact definition scope from SourceGapWindows. -/
noncomputable section
open Set MeasureTheory Polynomial
namespace Jig133.SourceGapWindows
open FiniteSourceGaps SourceGapSelection FullProductBandScale
attribute [local instance] Classical.propDecidable

def window (Y : Finset ℝ) (Q : Set ℝ) (c B L : ℝ) (n : ℕ)
    (i : Fin (count Y)) : Set ℝ :=
  Icc (anchor Y Q i - width c B L / n) (anchor Y Q i + width c B L / n)

def windows (Y : Finset ℝ) (Q : Set ℝ) (c B L : ℝ) (n : ℕ) : Set ℝ :=
  ⋃ i ∈ indices Y Q, window Y Q c B L n i

end Jig133.SourceGapWindows
end
end

section
/- Exact definition scope from BandTargetMeasure. -/
noncomputable section
open Set MeasureTheory Polynomial
open scoped ENNReal
namespace Jig133.BandTargetMeasure

def edge (ρ : ℝ) : Set ℝ := Icc (-1 : ℝ) 1 \ Ioo (-1 + ρ) (1 - ρ)

def band (P : ℝ[X]) (η T A : ℝ) : Set ℝ :=
  {x | η * A ≤ |P.eval x| ∧ |P.eval x| ≤ T * A}

def excluded (E : Set ℝ) (R : ℕ → ℕ) (Y : Finset ℝ) (P : ℝ[X])
    (c B L C G ρ : ℝ) (n : ℕ) : Set ℝ :=
  (((edge ρ ∪ (E ∩ LongSourceGapBound.gaps Y G n)) ∪
    SourceRankGeometry.shortBadUnion Y C G n) ∪
    FullProductRootFilter.bad P c B L n) ∪ (E \ FixedTargetHalos.good E R n)

def target (E : Set ℝ) (R : ℕ → ℕ) (Y : Finset ℝ) (P : ℝ[X])
    (η T A c B L C G ρ : ℝ) (n : ℕ) : Set ℝ :=
  (E ∩ band P η T A) \ excluded E R Y P c B L C G ρ n

end Jig133.BandTargetMeasure
end
end

section
/- Exact definition scope from BandTargetConstants. -/
noncomputable section
open Set MeasureTheory Polynomial
namespace Jig133.BandTargetConstants
open BandTargetMeasure

def clearance (δ : ℝ) : ℝ := δ / 128

def density (δ : ℝ) : ℝ := 384 / δ

def slope (δ : ℝ) : ℝ := 215040 / δ

def rank (δ G : ℝ) : ℝ := max 1 (384 * G / δ)

def buffer (δ : ℝ) : ℝ := δ / 16

def retained (E : Set ℝ) (R : ℕ → ℕ) (Y : Finset ℝ) (P : ℝ[X])
    (η T A δ G : ℝ) (n : ℕ) : Set ℝ :=
  target E R Y P η T A (clearance δ) (density δ) (slope δ) (rank δ G) G (buffer δ) n

end Jig133.BandTargetConstants
end
end

section
/- Exact definition scope from SparseSourceRows. -/
open Set MeasureTheory
noncomputable section
namespace Jig133.SparseSourceRows
open FiniteSourceNets
attribute [local instance] Classical.propDecidable

def rowNodes (nodes : (n : ℕ) → Fin n → ℝ) (n : ℕ) : Finset ℝ :=
  Finset.univ.image (nodes n)

def SourceCountAt (nodes : (n : ℕ) → Fin n → ℝ) (E : Set ℝ) (δ : ℝ) : Prop :=
  ∃ η c : ℝ, 0 < η ∧ 0 < c ∧ ∃ N : ℕ, 1 ≤ N ∧
    ∀ n : ℕ, N ≤ n → ∀ Y : Finset ℝ,
      IsSourceNet (rowNodes nodes n) Y (1 / (n : ℝ)) →
      ∀ D : ℕ, ∀ a b : Fin D → ℝ,
        (∀ i, a i ≤ b i) → (D : ℝ) ≤ c * (n : ℝ) →
        δ ≤ volume.real (E ∩ window a b) →
        η * (n : ℝ) ≤ ((Y.filter (fun x => x ∈ window a b)).card : ℝ)

def SourceCount (nodes : (n : ℕ) → Fin n → ℝ) (E : Set ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ volume.real E → SourceCountAt nodes E δ

end Jig133.SparseSourceRows
end
end

section
/- Exact definition scope from BandWindowExtraction. -/
noncomputable section
open Set MeasureTheory Polynomial Filter
open scoped Topology
namespace Jig133.BandWindowExtraction
open BandTargetMeasure BandTargetConstants FiniteSourceNets SparseSourceRows

def region (E : Set ℝ) (R : ℕ → ℕ) (Y : Finset ℝ) (P : ℝ[X])
    (η T A δ G : ℝ) (n : ℕ) : Set ℝ :=
  SourceGapWindows.windows Y (retained E R Y P η T A δ G n)
    (clearance δ) (density δ) (slope δ) n

end Jig133.BandWindowExtraction
end
end

noncomputable section
open Set MeasureTheory Polynomial Filter
open scoped Topology
open _root_.Statements.J5P133FixedBandWindowTarget.Jig133
open _root_.Statements.J5P133FixedBandWindowTarget.Jig133.BandTargetMeasure
open _root_.Statements.J5P133FixedBandWindowTarget.Jig133.BandTargetConstants
open _root_.Statements.J5P133FixedBandWindowTarget.Jig133.BandWindowExtraction
open _root_.Statements.J5P133FixedBandWindowTarget.Jig133.FiniteSourceNets
open _root_.Statements.J5P133FixedBandWindowTarget.Jig133.SparseSourceRows

def statement : Prop :=
  ∀
    (nodes : (n : ℕ) → Fin n → ℝ) (hsupp : ∀ n i, nodes n i ∈ Icc (-1 : ℝ) 1)
    (E : Set ℝ) (hE : MeasurableSet E) (hEI : E ⊆ Icc (-1 : ℝ) 1)
    (hSC : SourceCount nodes E) ,
    ∃ R : ℕ → ℕ, (∀ n, 0 < R n) ∧ Monotone R ∧ Tendsto R atTop atTop ∧
      Tendsto (fun n : ℕ => (R n : ℝ) / n) atTop (𝓝 0) ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 2 → ∃ G : ℝ, 0 < G ∧
        ∀ r : ℕ → ℕ, StrictMono r → ∀ Y : ℕ → Finset ℝ,
          (∀ j, IsSourceNet (rowNodes nodes (r j)) (Y j) (1 / (r j : ℝ))) →
          ∀ P : ℕ → ℝ[X], (∀ j, P j ≠ 0) → (∀ j i, (P j).eval (nodes (r j) i) = 0) →
          ∀ η T : ℝ, ∀ A : ℕ → ℝ,
          (∀ᶠ j in atTop, (P j).natDegree ≤ 2 * r j ∧
            δ ≤ volume.real (E ∩ band (P j) η T (A j))) →
          ∃ α : ℕ → ℕ, ∃ K : Set ℝ, StrictMono α ∧ IsCompact K ∧
            K ⊆ E ∩ Icc (-1 : ℝ) 1 ∧
            (FullProductBandScale.width (clearance δ) (density δ) (slope δ) * δ / G) / 8 < volume.real K ∧
            ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ a ∈ Icc (-1 : ℝ) 1, ∀ b ∈ Icc (-1 : ℝ) 1,
              ((FullProductBandScale.width (clearance δ) (density δ) (slope δ) * δ / G) / 8) *
                volume.real (K ∩ Icc a b) - ε ≤
                volume.real (region E R (Y (α j)) (P (α j)) η T (A (α j)) δ G (r (α j)) ∩ Icc a b)

end
end Statements.J5P133FixedBandWindowTarget
