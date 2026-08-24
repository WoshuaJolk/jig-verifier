import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

namespace Submissions.EllipticSeedK4N8Full.Exact

set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

structure QI2 where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
deriving DecidableEq

noncomputable def QI2.eval (z : QI2) : ℂ :=
  z.a + z.b * (Real.sqrt 2 : ℂ) +
    (z.c + z.d * (Real.sqrt 2 : ℂ)) * Complex.I

def pointQ : Fin 8 → Fin 4 → QI2 := ![
  ![⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩],
  ![⟨4, 0, 0, 0⟩, ⟨0, 1, 0, 1⟩, ⟨0, 0, 2, 0⟩, ⟨0, -1, 0, 1⟩],
  ![⟨0, 0, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨-1, 0, 0, 0⟩, ⟨0, 0, -1, 0⟩],
  ![⟨4, 0, 0, 0⟩, ⟨0, -1, 0, 1⟩, ⟨0, 0, -2, 0⟩, ⟨0, 1, 0, 1⟩],
  ![⟨0, 0, 0, 0⟩, ⟨-1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨-1, 0, 0, 0⟩],
  ![⟨4, 0, 0, 0⟩, ⟨0, -1, 0, -1⟩, ⟨0, 0, 2, 0⟩, ⟨0, 1, 0, -1⟩],
  ![⟨0, 0, 0, 0⟩, ⟨0, 0, -1, 0⟩, ⟨-1, 0, 0, 0⟩, ⟨0, 0, 1, 0⟩],
  ![⟨4, 0, 0, 0⟩, ⟨0, 1, 0, -1⟩, ⟨0, 0, -2, 0⟩, ⟨0, -1, 0, -1⟩]
]

def sectionQ : Fin 8 → Fin 4 → QI2 := ![
  ![⟨0, 0, 1, 0⟩, ⟨-1, 0, -1, 0⟩, ⟨2, 0, 0, 0⟩, ⟨-1, 0, 1, 0⟩],
  ![⟨1, 0, 0, 0⟩, ⟨0, -1, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩],
  ![⟨0, 0, -1, 0⟩, ⟨-1, 0, 1, 0⟩, ⟨2, 0, 0, 0⟩, ⟨-1, 0, -1, 0⟩],
  ![⟨-1, 0, 0, 0⟩, ⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 1⟩],
  ![⟨0, 0, 1, 0⟩, ⟨1, 0, 1, 0⟩, ⟨2, 0, 0, 0⟩, ⟨1, 0, -1, 0⟩],
  ![⟨1, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, -1, 0, 0⟩],
  ![⟨0, 0, -1, 0⟩, ⟨1, 0, -1, 0⟩, ⟨2, 0, 0, 0⟩, ⟨1, 0, 1, 0⟩],
  ![⟨-1, 0, 0, 0⟩, ⟨0, 0, 0, -1⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, -1⟩]
]

noncomputable def point (i : Fin 8) : Fin 4 → ℂ := fun r => (pointQ i r).eval
noncomputable def covector (i : Fin 8) : Fin 4 → ℂ := fun r => (sectionQ i r).eval
def seedQ : Fin 16 → Fin 4 → QI2 := Fin.append pointQ sectionQ
noncomputable def seed (i : Fin 16) : Fin 4 → ℂ := fun r => (seedQ i r).eval

def CrossAdj (i j : Fin 8) : Prop :=
  j.val = i.val ∨
  j.val = (i.val + 2) % 8 ∨
  j.val = (9 - i.val) % 8 ∨
  j.val = (13 - i.val) % 8

def pair (u v : Fin 4 → ℂ) : ℂ := ∑ r, star (u r) * v r

def EveryThreeIndependent (v : Fin 16 → Fin 4 → ℂ) : Prop :=
  ∀ f : Fin 3 → Fin 16, Function.Injective f →
    LinearIndependent ℂ (fun i => v (f i))

def EveryFiveSpanning (v : Fin 16 → Fin 4 → ℂ) : Prop :=
  ∀ f : Fin 5 → Fin 16, Function.Injective f →
    Submodule.span ℂ (Set.range fun i => v (f i)) = ⊤

abbrev statement : Prop :=
  (∀ i j, pair (point i) (covector j) = 0 ↔ CrossAdj i j) ∧
  EveryThreeIndependent seed ∧
  EveryFiveSpanning seed

noncomputable abbrev cval (a b c d : ℤ) : ℂ :=
  a + b * (Real.sqrt 2 : ℂ) + (c + d * (Real.sqrt 2 : ℂ)) * Complex.I

noncomputable abbrev pointD : Fin 8 → Fin 4 → ℂ := ![
  ![cval 0 0 0 0, cval 1 0 0 0, cval 1 0 0 0, cval 1 0 0 0],
  ![cval 4 0 0 0, cval 0 1 0 1, cval 0 0 2 0, cval 0 (-1) 0 1],
  ![cval 0 0 0 0, cval 0 0 1 0, cval (-1) 0 0 0, cval 0 0 (-1) 0],
  ![cval 4 0 0 0, cval 0 (-1) 0 1, cval 0 0 (-2) 0, cval 0 1 0 1],
  ![cval 0 0 0 0, cval (-1) 0 0 0, cval 1 0 0 0, cval (-1) 0 0 0],
  ![cval 4 0 0 0, cval 0 (-1) 0 (-1), cval 0 0 2 0, cval 0 1 0 (-1)],
  ![cval 0 0 0 0, cval 0 0 (-1) 0, cval (-1) 0 0 0, cval 0 0 1 0],
  ![cval 4 0 0 0, cval 0 1 0 (-1), cval 0 0 (-2) 0, cval 0 (-1) 0 (-1)]
]

noncomputable abbrev covectorD : Fin 8 → Fin 4 → ℂ := ![
  ![cval 0 0 1 0, cval (-1) 0 (-1) 0, cval 2 0 0 0, cval (-1) 0 1 0],
  ![cval 1 0 0 0, cval 0 (-1) 0 0, cval 0 0 0 0, cval 0 1 0 0],
  ![cval 0 0 (-1) 0, cval (-1) 0 1 0, cval 2 0 0 0, cval (-1) 0 (-1) 0],
  ![cval (-1) 0 0 0, cval 0 0 0 1, cval 0 0 0 0, cval 0 0 0 1],
  ![cval 0 0 1 0, cval 1 0 1 0, cval 2 0 0 0, cval 1 0 (-1) 0],
  ![cval 1 0 0 0, cval 0 1 0 0, cval 0 0 0 0, cval 0 (-1) 0 0],
  ![cval 0 0 (-1) 0, cval 1 0 (-1) 0, cval 2 0 0 0, cval 1 0 1 0],
  ![cval (-1) 0 0 0, cval 0 0 0 (-1), cval 0 0 0 0, cval 0 0 0 (-1)]
]

noncomputable abbrev seedD : Fin 16 → Fin 4 → ℂ := Fin.append pointD covectorD

abbrev directStatement : Prop :=
  (∀ i j, pair (pointD i) (covectorD j) = 0 ↔ CrossAdj i j) ∧
  EveryThreeIndependent seedD ∧
  EveryFiveSpanning seedD

instance crossAdjDecidable (i j : Fin 8) : Decidable (CrossAdj i j) := by
  unfold CrossAdj
  infer_instance

def qzero : QI2 := ⟨0, 0, 0, 0⟩
def qadd (x y : QI2) : QI2 :=
  ⟨x.a + y.a, x.b + y.b, x.c + y.c, x.d + y.d⟩
def qneg (x : QI2) : QI2 := ⟨-x.a, -x.b, -x.c, -x.d⟩
def qsub (x y : QI2) : QI2 := qadd x (qneg y)
def qmul (x y : QI2) : QI2 :=
  ⟨x.a * y.a + 2 * x.b * y.b - x.c * y.c - 2 * x.d * y.d,
   x.a * y.b + x.b * y.a - x.c * y.d - x.d * y.c,
   x.a * y.c + 2 * x.b * y.d + x.c * y.a + 2 * x.d * y.b,
   x.a * y.d + x.b * y.c + x.c * y.b + x.d * y.a⟩
def qstar (x : QI2) : QI2 := ⟨x.a, x.b, -x.c, -x.d⟩

local instance : Zero QI2 := ⟨qzero⟩
local instance : Add QI2 := ⟨qadd⟩
local instance : Neg QI2 := ⟨qneg⟩
local instance : Sub QI2 := ⟨qsub⟩
local instance : Mul QI2 := ⟨qmul⟩

def qdot (x y : Fin 4 → QI2) : QI2 :=
  qstar (x 0) * y 0 + qstar (x 1) * y 1 + qstar (x 2) * y 2 + qstar (x 3) * y 3

def det3Q (x y z : Fin 3 → QI2) : QI2 :=
  x 0 * y 1 * z 2 - x 0 * y 2 * z 1
    - x 1 * y 0 * z 2 + x 1 * y 2 * z 0
    + x 2 * y 0 * z 1 - x 2 * y 1 * z 0

def det3C (x y z : Fin 3 → ℂ) : ℂ :=
  x 0 * y 1 * z 2 - x 0 * y 2 * z 1
    - x 1 * y 0 * z 2 + x 1 * y 2 * z 0
    + x 2 * y 0 * z 1 - x 2 * y 1 * z 0

def det4Q (x y z t : Fin 4 → QI2) : QI2 :=
  x 0 * y 1 * z 2 * t 3
    - x 0 * y 1 * z 3 * t 2
    - x 0 * y 2 * z 1 * t 3
    + x 0 * y 2 * z 3 * t 1
    + x 0 * y 3 * z 1 * t 2
    - x 0 * y 3 * z 2 * t 1
    - x 1 * y 0 * z 2 * t 3
    + x 1 * y 0 * z 3 * t 2
    + x 1 * y 2 * z 0 * t 3
    - x 1 * y 2 * z 3 * t 0
    - x 1 * y 3 * z 0 * t 2
    + x 1 * y 3 * z 2 * t 0
    + x 2 * y 0 * z 1 * t 3
    - x 2 * y 0 * z 3 * t 1
    - x 2 * y 1 * z 0 * t 3
    + x 2 * y 1 * z 3 * t 0
    + x 2 * y 3 * z 0 * t 1
    - x 2 * y 3 * z 1 * t 0
    - x 3 * y 0 * z 1 * t 2
    + x 3 * y 0 * z 2 * t 1
    + x 3 * y 1 * z 0 * t 2
    - x 3 * y 1 * z 2 * t 0
    - x 3 * y 2 * z 0 * t 1
    + x 3 * y 2 * z 1 * t 0

def det4C (x y z t : Fin 4 → ℂ) : ℂ :=
  x 0 * y 1 * z 2 * t 3
    - x 0 * y 1 * z 3 * t 2
    - x 0 * y 2 * z 1 * t 3
    + x 0 * y 2 * z 3 * t 1
    + x 0 * y 3 * z 1 * t 2
    - x 0 * y 3 * z 2 * t 1
    - x 1 * y 0 * z 2 * t 3
    + x 1 * y 0 * z 3 * t 2
    + x 1 * y 2 * z 0 * t 3
    - x 1 * y 2 * z 3 * t 0
    - x 1 * y 3 * z 0 * t 2
    + x 1 * y 3 * z 2 * t 0
    + x 2 * y 0 * z 1 * t 3
    - x 2 * y 0 * z 3 * t 1
    - x 2 * y 1 * z 0 * t 3
    + x 2 * y 1 * z 3 * t 0
    + x 2 * y 3 * z 0 * t 1
    - x 2 * y 3 * z 1 * t 0
    - x 3 * y 0 * z 1 * t 2
    + x 3 * y 0 * z 2 * t 1
    + x 3 * y 1 * z 0 * t 2
    - x 3 * y 1 * z 2 * t 0
    - x 3 * y 2 * z 0 * t 1
    + x 3 * y 2 * z 1 * t 0

def delCol (c : Fin 4) (x : Fin 4 → QI2) : Fin 3 → QI2 := fun r => x (c.succAbove r)

theorem orthExact : ∀ i j : Fin 8,
    qdot (pointQ i) (sectionQ j) = 0 ↔ CrossAdj i j := by decide +kernel

theorem pointNzQ : ∀ i : Fin 8, ∃ r, pointQ i r ≠ 0 := by decide +kernel
theorem sectionNzQ : ∀ i : Fin 8, ∃ r, sectionQ i r ≠ 0 := by decide +kernel

theorem sameSideExact : ∀ i j : Fin 8, i ≠ j →
    qdot (pointQ i) (pointQ j) ≠ 0 ∧ qdot (sectionQ i) (sectionQ j) ≠ 0 := by
  decide +kernel

theorem triples :
    ∀ i1 i2 : Fin 16, i1 < i2 → ∀ i3 : Fin 16, i2 < i3 →
      det3Q (delCol 0 (seedQ i1)) (delCol 0 (seedQ i2)) (delCol 0 (seedQ i3)) ≠ 0 ∨
      det3Q (delCol 1 (seedQ i1)) (delCol 1 (seedQ i2)) (delCol 1 (seedQ i3)) ≠ 0 ∨
      det3Q (delCol 2 (seedQ i1)) (delCol 2 (seedQ i2)) (delCol 2 (seedQ i3)) ≠ 0 ∨
      det3Q (delCol 3 (seedQ i1)) (delCol 3 (seedQ i2)) (delCol 3 (seedQ i3)) ≠ 0 := by
  decide +kernel

theorem quintuples :
    ∀ i1 i2 : Fin 16, i1 < i2 → ∀ i3 : Fin 16, i2 < i3 →
    ∀ i4 : Fin 16, i3 < i4 → ∀ i5 : Fin 16, i4 < i5 →
      det4Q (seedQ i1) (seedQ i2) (seedQ i3) (seedQ i4) ≠ 0 ∨
      det4Q (seedQ i1) (seedQ i2) (seedQ i3) (seedQ i5) ≠ 0 ∨
      det4Q (seedQ i1) (seedQ i2) (seedQ i4) (seedQ i5) ≠ 0 ∨
      det4Q (seedQ i1) (seedQ i3) (seedQ i4) (seedQ i5) ≠ 0 ∨
      det4Q (seedQ i2) (seedQ i3) (seedQ i4) (seedQ i5) ≠ 0 := by
  decide +kernel

lemma sqrt2_sq_complex : ((Real.sqrt 2 : ℝ) : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
  rw [← Complex.ofReal_mul]
  norm_num [Real.mul_self_sqrt]

lemma eval_qadd (x y : QI2) : (x + y).eval = x.eval + y.eval := by
  rcases x with ⟨a,b,c,d⟩
  rcases y with ⟨e,f,g,h⟩
  change (qadd ⟨a,b,c,d⟩ ⟨e,f,g,h⟩).eval = _
  simp [QI2.eval, qadd]
  ring

lemma eval_qneg (x : QI2) : (-x).eval = -x.eval := by
  rcases x with ⟨a,b,c,d⟩
  change (qneg ⟨a,b,c,d⟩).eval = _
  simp [QI2.eval, qneg]
  ring

lemma eval_qsub (x y : QI2) : (x - y).eval = x.eval - y.eval := by
  change (qsub x y).eval = _
  change (qadd x (qneg y)).eval = _
  have ha := eval_qadd x (qneg y)
  have hn := eval_qneg y
  change (qadd x (qneg y)).eval = x.eval + (qneg y).eval at ha
  change (qneg y).eval = -y.eval at hn
  rw [ha, hn]
  ring

lemma eval_qmul (x y : QI2) : (x * y).eval = x.eval * y.eval := by
  rcases x with ⟨a,b,c,d⟩
  rcases y with ⟨e,f,g,h⟩
  change (qmul ⟨a,b,c,d⟩ ⟨e,f,g,h⟩).eval = _
  let s : ℂ := (Real.sqrt 2 : ℝ)
  have hs : s * s = 2 := sqrt2_sq_complex
  have hr :
      ((a * e + 2 * b * f - c * g - 2 * d * h : ℤ) : ℂ) +
          ((a * f + b * e - c * h - d * g : ℤ) : ℂ) * s =
        (((a : ℂ) + b * s) * ((e : ℂ) + f * s) -
          ((c : ℂ) + d * s) * ((g : ℂ) + h * s)) := by
    push_cast
    calc
      _ = (a : ℂ) * e + b * f * (s * s) - c * g - d * h * (s * s) +
          (a * f + b * e - c * h - d * g) * s := by rw [hs]; norm_num; ring
      _ = _ := by ring
  have hi :
      ((a * g + 2 * b * h + c * e + 2 * d * f : ℤ) : ℂ) +
          ((a * h + b * g + c * f + d * e : ℤ) : ℂ) * s =
        (((a : ℂ) + b * s) * ((g : ℂ) + h * s) +
          ((c : ℂ) + d * s) * ((e : ℂ) + f * s)) := by
    push_cast
    calc
      _ = (a : ℂ) * g + b * h * (s * s) + c * e + d * f * (s * s) +
          (a * h + b * g + c * f + d * e) * s := by rw [hs]; norm_num; ring
      _ = _ := by ring
  simp only [QI2.eval, qmul]
  change _ = ((a : ℂ) + b * s + ((c : ℂ) + d * s) * Complex.I) *
    ((e : ℂ) + f * s + ((g : ℂ) + h * s) * Complex.I)
  rw [hr, hi]
  symm
  calc
    _ = ((a : ℂ) + b * s) * ((e : ℂ) + f * s) +
        ((a : ℂ) + b * s) * ((g : ℂ) + h * s) * Complex.I +
        ((c : ℂ) + d * s) * ((e : ℂ) + f * s) * Complex.I +
        ((c : ℂ) + d * s) * ((g : ℂ) + h * s) * (Complex.I * Complex.I) := by ring
    _ = _ := by rw [Complex.I_mul_I]; ring

lemma eval_qstar (x : QI2) : (qstar x).eval = star x.eval := by
  rcases x with ⟨a,b,c,d⟩
  rw [Complex.star_def]
  simp [QI2.eval, qstar]
  ring

lemma int_sqrt2_eq_zero {a b : ℤ}
    (h : (a : ℝ) + (b : ℝ) * Real.sqrt 2 = 0) : a = 0 ∧ b = 0 := by
  by_cases hb : b = 0
  · subst b
    simp only [Int.cast_zero, zero_mul, add_zero] at h
    exact ⟨by exact_mod_cast h, rfl⟩
  · have hs : Real.sqrt 2 = (-(a : ℤ) : ℝ) / (b : ℤ) := by
      apply (eq_div_iff (by exact_mod_cast hb)).2
      linarith
    have hs' : Real.sqrt 2 = ((-a : ℤ) : ℝ) / (b : ℤ) := by simpa using hs
    exact (irrational_sqrt_two.ne_rational (-a) b hs').elim

lemma eval_injective : Function.Injective QI2.eval := by
  intro x y hxy
  have h : (x - y).eval = 0 := by rw [eval_qsub, hxy, sub_self]
  rcases x with ⟨a,b,c,d⟩
  rcases y with ⟨e,f,g,j⟩
  change (qsub ⟨a,b,c,d⟩ ⟨e,f,g,j⟩).eval = 0 at h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [QI2.eval, qsub, qadd, qneg] at hre him
  have hre' : ((a - e : ℤ) : ℝ) + ((b - f : ℤ) : ℝ) * Real.sqrt 2 = 0 := by
    push_cast
    simpa [sub_eq_add_neg] using hre
  have him' : ((c - g : ℤ) : ℝ) + ((d - j : ℤ) : ℝ) * Real.sqrt 2 = 0 := by
    push_cast
    simpa [sub_eq_add_neg] using him
  have hab := int_sqrt2_eq_zero hre'
  have hcd := int_sqrt2_eq_zero him'
  simp only [QI2.mk.injEq]
  omega

lemma eval_zero : QI2.eval 0 = 0 := by
  change QI2.eval qzero = 0
  simp [QI2.eval, qzero]

lemma eval_ne_zero {x : QI2} (hx : x ≠ 0) : x.eval ≠ 0 := by
  intro h
  apply hx
  apply eval_injective
  simpa [eval_zero] using h

lemma det3_cast (x y z : Fin 3 → QI2) :
    det3C (fun r => (x r).eval) (fun r => (y r).eval) (fun r => (z r).eval) =
      (det3Q x y z).eval := by
  simp only [det3C, det3Q, eval_qmul, eval_qadd, eval_qsub]

lemma det4_cast (x y z t : Fin 4 → QI2) :
    det4C (fun r => (x r).eval) (fun r => (y r).eval) (fun r => (z r).eval)
        (fun r => (t r).eval) = (det4Q x y z t).eval := by
  simp only [det4C, det4Q, eval_qmul, eval_qadd, eval_qsub]

lemma pair_eq (i j : Fin 8) :
    pair (point i) (covector j) = (qdot (pointQ i) (sectionQ j)).eval := by
  rw [pair, Fin.sum_univ_four]
  simp only [point, covector, qdot, eval_qstar, eval_qmul, eval_qadd]

lemma pair_evalQ (x y : Fin 4 → QI2) :
    pair (fun r => (x r).eval) (fun r => (y r).eval) = (qdot x y).eval := by
  rw [pair, Fin.sum_univ_four]
  simp only [qdot, eval_qstar, eval_qmul, eval_qadd]

lemma orthIff : ∀ i j : Fin 8, pair (point i) (covector j) = 0 ↔ CrossAdj i j := by
  intro i j
  rw [pair_eq]
  constructor
  · intro h
    apply (orthExact i j).mp
    apply eval_injective
    simpa [eval_zero] using h
  · intro h
    rw [(orthExact i j).mpr h, eval_zero]

def restrict3 (c : Fin 4) : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) where
  toFun g := fun r => g (c.succAbove r)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma linInd_of_det3 (c : Fin 4) {x y z : Fin 4 → QI2}
    (hd : det3Q (delCol c x) (delCol c y) (delCol c z) ≠ 0) :
    LinearIndependent ℂ ![
      (fun r : Fin 4 => (x r).eval),
      (fun r : Fin 4 => (y r).eval),
      (fun r : Fin 4 => (z r).eval)] := by
  let M : Matrix (Fin 3) (Fin 3) ℂ :=
    !![((delCol c x 0).eval), ((delCol c x 1).eval), ((delCol c x 2).eval);
       ((delCol c y 0).eval), ((delCol c y 1).eval), ((delCol c y 2).eval);
       ((delCol c z 0).eval), ((delCol c z 1).eval), ((delCol c z 2).eval)]
  have hdetC : M.det = det3C (fun r => (delCol c x r).eval)
      (fun r => (delCol c y r).eval) (fun r => (delCol c z r).eval) := by
    simp [M, Matrix.det_succ_row_zero, det3C, Fin.sum_univ_succ,
      Fin.val_succ, Fin.val_eq_zero, Fin.succAbove]
    ring
  have hdet0 : M.det ≠ 0 := by
    rw [hdetC, det3_cast]
    exact eval_ne_zero hd
  have hrows : LinearIndependent ℂ (fun s : Fin 3 => M s) :=
    Matrix.linearIndependent_rows_of_det_ne_zero hdet0
  have hfam :
      (fun s : Fin 3 => M s) =
        (⇑(restrict3 c)) ∘ ![(fun r : Fin 4 => (x r).eval),
          (fun r : Fin 4 => (y r).eval), (fun r : Fin 4 => (z r).eval)] := by
    ext s r
    fin_cases s <;> fin_cases r <;> simp [M, restrict3, delCol]
  rw [hfam] at hrows
  exact LinearIndependent.of_comp (restrict3 c) hrows

lemma linInd3 (i j k : Fin 16) (c : Fin 4)
    (hd : det3Q (delCol c (seedQ i)) (delCol c (seedQ j))
      (delCol c (seedQ k)) ≠ 0) :
    LinearIndependent ℂ ![seed i, seed j, seed k] := by
  have h := linInd_of_det3 c hd
  convert h using 1
  ext s r
  fin_cases s <;> simp [seed]

lemma tight_sorted (i j k : Fin 16) (hij : i < j) (hjk : j < k) :
    LinearIndependent ℂ ![seed i, seed j, seed k] := by
  rcases triples i j hij k hjk with h | h | h | h
  · exact linInd3 i j k 0 h
  · exact linInd3 i j k 1 h
  · exact linInd3 i j k 2 h
  · exact linInd3 i j k 3 h

lemma tightT (T : Finset (Fin 16)) (hT : T.card = 3) :
    LinearIndependent ℂ fun x : (T : Set (Fin 16)) => seed x := by
  let e := T.orderIsoOfFin hT
  have h01 : ((e 0 : T) : Fin 16) < ((e 1 : T) : Fin 16) :=
    Subtype.coe_lt_coe.mpr (e.strictMono (by decide : (0 : Fin 3) < 1))
  have h12 : ((e 1 : T) : Fin 16) < ((e 2 : T) : Fin 16) :=
    Subtype.coe_lt_coe.mpr (e.strictMono (by decide : (1 : Fin 3) < 2))
  have h3 : LinearIndependent ℂ ![seed (e 0), seed (e 1), seed (e 2)] :=
    tight_sorted _ _ _ h01 h12
  let g : ↥(T : Set (Fin 16)) → Fin 3 :=
    fun x => e.symm ⟨x.1, Finset.mem_coe.mp x.2⟩
  have hg : Function.Injective g := by
    intro x1 x2 h
    have h' := e.symm.injective h
    exact Subtype.ext (congrArg Subtype.val h')
  have hm : ∀ j : Fin 3,
      (![seed (e 0), seed (e 1), seed (e 2)] : Fin 3 → Fin 4 → ℂ) j = seed (e j) := by
    intro j
    fin_cases j <;> rfl
  have hfam : (fun x : ↥(T : Set (Fin 16)) => seed x) =
      (![seed (e 0), seed (e 1), seed (e 2)] : Fin 3 → Fin 4 → ℂ) ∘ g := by
    funext x
    have hx : e (g x) = ⟨x.1, Finset.mem_coe.mp x.2⟩ := e.apply_symm_apply _
    have hval : ((e (g x) : T) : Fin 16) = (x : Fin 16) := congrArg Subtype.val hx
    simp only [Function.comp_apply, hm (g x), hval]
  rw [hfam]
  exact h3.comp g hg

lemma everyThree : EveryThreeIndependent seed := by
  intro f hf
  let T : Finset (Fin 16) := Finset.univ.image f
  have hT : T.card = 3 := by
    simpa [T] using Finset.card_image_of_injective (Finset.univ : Finset (Fin 3)) hf
  have hLI := tightT T hT
  let g : Fin 3 → (T : Set (Fin 16)) := fun i => ⟨f i, by simp [T]⟩
  have hg : Function.Injective g := by
    intro i j h
    apply hf
    exact congrArg Subtype.val h
  have hc := hLI.comp g hg
  have heq : ((fun x : (T : Set (Fin 16)) => seed x) ∘ g) =
      (fun i => seed (f i)) := by
    funext i
    rfl
  rw [heq] at hc
  exact hc

lemma tightAll : ∀ S : Finset (Fin 16), S.card + 1 ≤ 4 →
    LinearIndependent ℂ fun i : (S : Set (Fin 16)) => seed i := by
  intro S hS
  have hcard : S.card ≤ 3 := by omega
  obtain ⟨T, hST, -, hT⟩ :=
    Finset.exists_subsuperset_card_eq (Finset.subset_univ S) hcard
      (by decide : 3 ≤ (Finset.univ : Finset (Fin 16)).card)
  have h : LinearIndepOn ℂ seed (T : Set (Fin 16)) := tightT T hT
  exact h.mono (Finset.coe_subset.mpr hST)

lemma linInd_of_det4 {x y z t : Fin 4 → QI2} (hd : det4Q x y z t ≠ 0) :
    LinearIndependent ℂ ![(fun r => (x r).eval), (fun r => (y r).eval),
      (fun r => (z r).eval), (fun r => (t r).eval)] := by
  let M : Matrix (Fin 4) (Fin 4) ℂ :=
    !![((x 0).eval), ((x 1).eval), ((x 2).eval), ((x 3).eval);
       ((y 0).eval), ((y 1).eval), ((y 2).eval), ((y 3).eval);
       ((z 0).eval), ((z 1).eval), ((z 2).eval), ((z 3).eval);
       ((t 0).eval), ((t 1).eval), ((t 2).eval), ((t 3).eval)]
  have hdetC : M.det = det4C (fun r => (x r).eval) (fun r => (y r).eval)
      (fun r => (z r).eval) (fun r => (t r).eval) := by
    simp [M, Matrix.det_succ_row_zero, det4C, Fin.sum_univ_succ,
      Fin.val_succ, Fin.val_eq_zero, Fin.succAbove]
    ring
  have hdet0 : M.det ≠ 0 := by
    rw [hdetC, det4_cast]
    exact eval_ne_zero hd
  have hrows : LinearIndependent ℂ (fun s : Fin 4 => M s) :=
    Matrix.linearIndependent_rows_of_det_ne_zero hdet0
  convert hrows using 1
  ext s r
  fin_cases s <;> fin_cases r <;> simp [M]

lemma span4_of_det (i j k l : Fin 16) (hd : det4Q (seedQ i) (seedQ j)
    (seedQ k) (seedQ l) ≠ 0) :
    Submodule.span ℂ (Set.range ![seed i, seed j, seed k, seed l]) = ⊤ := by
  have hLI := linInd_of_det4 hd
  have hLI' : LinearIndependent ℂ ![seed i, seed j, seed k, seed l] := by
    convert hLI using 1
    ext s r
    fin_cases s <;> simp [seed]
  apply hLI'.span_eq_top_of_card_eq_finrank
  simp

lemma span_sorted (i1 i2 i3 i4 i5 : Fin 16) (h12 : i1 < i2) (h23 : i2 < i3)
    (h34 : i3 < i4) (h45 : i4 < i5) :
    Submodule.span ℂ (Set.range ![seed i1, seed i2, seed i3, seed i4, seed i5]) = ⊤ := by
  rcases quintuples i1 i2 h12 i3 h23 i4 h34 i5 h45 with h | h | h | h | h
  · apply top_unique
    rw [← span4_of_det i1 i2 i3 i4 h]
    apply Submodule.span_mono
    rintro x ⟨r, rfl⟩
    fin_cases r <;> simp
  · apply top_unique
    rw [← span4_of_det i1 i2 i3 i5 h]
    apply Submodule.span_mono
    rintro x ⟨r, rfl⟩
    fin_cases r <;> simp
  · apply top_unique
    rw [← span4_of_det i1 i2 i4 i5 h]
    apply Submodule.span_mono
    rintro x ⟨r, rfl⟩
    fin_cases r <;> simp
  · apply top_unique
    rw [← span4_of_det i1 i3 i4 i5 h]
    apply Submodule.span_mono
    rintro x ⟨r, rfl⟩
    fin_cases r <;> simp
  · apply top_unique
    rw [← span4_of_det i2 i3 i4 i5 h]
    apply Submodule.span_mono
    rintro x ⟨r, rfl⟩
    fin_cases r <;> simp

lemma spanT (T : Finset (Fin 16)) (hT : T.card = 5) :
    Submodule.span ℂ (Set.range fun x : (T : Set (Fin 16)) => seed x) = ⊤ := by
  let e := T.orderIsoOfFin hT
  have h01 : ((e 0 : T) : Fin 16) < ((e 1 : T) : Fin 16) :=
    Subtype.coe_lt_coe.mpr (e.strictMono (by decide : (0 : Fin 5) < 1))
  have h12 : ((e 1 : T) : Fin 16) < ((e 2 : T) : Fin 16) :=
    Subtype.coe_lt_coe.mpr (e.strictMono (by decide : (1 : Fin 5) < 2))
  have h23 : ((e 2 : T) : Fin 16) < ((e 3 : T) : Fin 16) :=
    Subtype.coe_lt_coe.mpr (e.strictMono (by decide : (2 : Fin 5) < 3))
  have h34 : ((e 3 : T) : Fin 16) < ((e 4 : T) : Fin 16) :=
    Subtype.coe_lt_coe.mpr (e.strictMono (by decide : (3 : Fin 5) < 4))
  have hs := span_sorted (e 0) (e 1) (e 2) (e 3) (e 4) h01 h12 h23 h34
  apply top_unique
  rw [← hs]
  apply Submodule.span_mono
  rintro x ⟨i, rfl⟩
  refine ⟨e i, ?_⟩
  fin_cases i <;> rfl

lemma everyFive : EveryFiveSpanning seed := by
  intro f hf
  let T : Finset (Fin 16) := Finset.univ.image f
  have hT : T.card = 5 := by
    simpa [T] using Finset.card_image_of_injective (Finset.univ : Finset (Fin 5)) hf
  have hs := spanT T hT
  apply top_unique
  rw [← hs]
  apply Submodule.span_mono
  rintro x ⟨t, rfl⟩
  have ht : (t : Fin 16) ∈ Finset.univ.image f := by simpa [T] using t.property
  rcases Finset.mem_image.mp ht with ⟨i, -, hi⟩
  exact ⟨i, congrArg seed hi⟩

lemma spanAll : ∀ S : Finset (Fin 16), S.card = 5 →
    Submodule.span ℂ (Set.range fun i : (S : Set (Fin 16)) => seed i) = ⊤ :=
  spanT

lemma point_nonzero : ∀ i, point i ≠ 0 := by
  intro i h
  obtain ⟨r, hr⟩ := pointNzQ i
  apply hr
  apply eval_injective
  have hz := congrFun h r
  simpa [point, eval_zero] using hz

lemma covector_nonzero : ∀ i, covector i ≠ 0 := by
  intro i h
  obtain ⟨r, hr⟩ := sectionNzQ i
  apply hr
  apply eval_injective
  have hz := congrFun h r
  simpa [covector, eval_zero] using hz

lemma sameSide : ∀ i j, i ≠ j →
    pair (point i) (point j) ≠ 0 ∧ pair (covector i) (covector j) ≠ 0 := by
  intro i j hij
  obtain ⟨hp, hs⟩ := sameSideExact i j hij
  constructor
  · change pair (fun r => (pointQ i r).eval) (fun r => (pointQ j r).eval) ≠ 0
    rw [pair_evalQ]
    exact eval_ne_zero hp
  · change pair (fun r => (sectionQ i r).eval) (fun r => (sectionQ j r).eval) ≠ 0
    rw [pair_evalQ]
    exact eval_ne_zero hs

theorem proofLocal : statement :=
  ⟨orthIff, everyThree, everyFive⟩

lemma pointD_eq_point : pointD = point := by
  ext i r
  fin_cases i <;> fin_cases r <;> rfl

lemma covectorD_eq_covector : covectorD = covector := by
  ext i r
  fin_cases i <;> fin_cases r <;> rfl

lemma seedD_eq_seed : seedD = seed := by
  ext i r
  fin_cases i <;> fin_cases r <;> rfl

lemma seed_eq_append : seed = Fin.append point covector := by
  ext i r
  fin_cases i <;> fin_cases r <;> rfl

theorem proof : directStatement := by
  unfold directStatement
  rw [pointD_eq_point, covectorD_eq_covector, seedD_eq_seed]
  exact proofLocal

abbrev existsStatement : Prop :=
  ∃ point covector : Fin 8 → Fin 4 → ℂ,
    (∀ i j, pair (point i) (covector j) = 0 ↔ CrossAdj i j) ∧
    EveryThreeIndependent (Fin.append point covector) ∧
    EveryFiveSpanning (Fin.append point covector)

theorem existenceProof : existsStatement := by
  refine ⟨pointD, covectorD, ?_⟩
  exact proof

abbrev fullStatement : Prop :=
  ∃ point covector : Fin 8 → Fin 4 → ℂ,
    (∀ i, point i ≠ 0 ∧ covector i ≠ 0) ∧
    (∀ i j, pair (point i) (covector j) = 0 ↔ CrossAdj i j) ∧
    (∀ i j, i ≠ j → pair (point i) (point j) ≠ 0 ∧
      pair (covector i) (covector j) ≠ 0) ∧
    (∀ S : Finset (Fin 16), S.card + 1 ≤ 4 →
      LinearIndependent ℂ fun i : (S : Set (Fin 16)) =>
        Fin.append point covector i) ∧
    (∀ S : Finset (Fin 16), S.card = 5 →
      Submodule.span ℂ (Set.range fun i : (S : Set (Fin 16)) =>
        Fin.append point covector i) = ⊤)

theorem fullProof : fullStatement := by
  have htight : ∀ S : Finset (Fin 16), S.card + 1 ≤ 4 →
      LinearIndependent ℂ fun i : (S : Set (Fin 16)) => Fin.append point covector i := by
    simpa only [← seed_eq_append] using tightAll
  have hspan : ∀ S : Finset (Fin 16), S.card = 5 →
      Submodule.span ℂ (Set.range fun i : (S : Set (Fin 16)) =>
        Fin.append point covector i) = ⊤ := by
    simpa only [← seed_eq_append] using spanAll
  refine ⟨point, covector, ?_, orthIff, sameSide, htight, hspan⟩
  intro i
  exact ⟨point_nonzero i, covector_nonzero i⟩

end Submissions.EllipticSeedK4N8Full.Exact
