import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Induction
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Tuple.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Exp

namespace Submissions.Erdos529FiniteRepulsionTransfer.Main

-- BEGIN p289/RepeatArrivalEncoding.lean; source SHA-256 9560429abb8e6bc623e5d9bda05f358eb138180dc729c2fe0083b507d1a87d6a

/-!
An all-length repeat-arrival encoding for the canonical square-lattice direction
words of Jig #289. The canonical definitions below are copied literally, with a
new namespace. No admitted statement or project target is imported.
-/

namespace PlanarSAWRepeatArrival

abbrev Point := ℤ × ℤ
abbrev Direction := Fin 4

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

def trace (x : Point) (w : List Direction) : List Point :=
  w.scanl (fun y d => y + step d) x

def finish (x : Point) (w : List Direction) : Point :=
  w.foldl (fun y d => y + step d) x

def StrictBlock (w : List Direction) : Prop := (trace 0 w).Nodup

theorem finish_eq (x : Point) (w : List Direction) :
    finish x w = x + (w.map step).sum := by
  induction w generalizing x with
  | nil => simp [finish]
  | cons d w ih => simpa [finish, add_assoc] using ih (x + step d)

theorem finish_append (x : Point) (a b : List Direction) :
    finish x (a ++ b) = finish (finish x a) b := by
  simp [finish, List.foldl_append]

theorem trace_translate (x y : Point) (w : List Direction) :
    trace (x + y) w = (trace y w).map (fun z => x + z) := by
  induction w generalizing y with
  | nil => simp [trace]
  | cons d w ih =>
    simp only [trace, List.scanl_cons, List.map_cons]
    congr 1
    simpa only [trace, add_assoc] using ih (y + step d)

theorem strictBlock_iff_translate (x : Point) (w : List Direction) :
    (trace x w).Nodup ↔ StrictBlock w := by
  rw [show trace x w = (trace 0 w).map (fun z => x + z) by
    simpa using trace_translate x 0 w]
  exact List.nodup_map_iff (fun _ _ h => add_left_cancel h)

theorem trace_snoc (x : Point) (w : List Direction) (d : Direction) :
    trace x (w ++ [d]) = trace x w ++ [finish x w + step d] := by
  simp [trace, List.scanl_append, finish]

theorem trace_suffix_mem (x : Point) (a b : List Direction) (y : Point)
    (hy : y ∈ trace (finish x a) b) : y ∈ trace x (a ++ b) := by
  induction a generalizing x with
  | nil => simpa [finish] using hy
  | cons d a ih =>
    simp only [List.cons_append, trace, List.scanl_cons, List.mem_cons]
    right
    exact ih (x + step d) hy

theorem strictBlock_snoc_of_fresh (a b : List Direction) (d : Direction)
    (hb : StrictBlock b)
    (hfresh : finish 0 (a ++ b) + step d ∉ trace 0 (a ++ b)) :
    StrictBlock (b ++ [d]) := by
  apply (strictBlock_iff_translate (finish 0 a) _).mp
  rw [trace_snoc, List.nodup_append]
  refine ⟨(strictBlock_iff_translate _ _).mpr hb, by simp, ?_⟩
  intro y hy z hz
  simp only [List.mem_singleton] at hz
  subst z
  intro heq
  apply hfresh
  rw [finish_append]
  exact trace_suffix_mem 0 a b _ (heq ▸ hy)

theorem position_zero {n : ℕ} (s : Fin n → Fin 4) : position s 0 = 0 := by
  unfold position
  apply Finset.sum_eq_zero
  intro i _
  exact Fin.elim0 i

theorem position_succ {n : ℕ} (s : Fin n → Fin 4) (i : Fin n) :
    position s i.succ = position s i.castSucc + step (s i) := by
  simp only [position, Fin.val_succ, Fin.val_castSucc]
  rw [Fin.sum_univ_castSucc]
  congr 1

theorem trace_get_ofFn {n : ℕ} (s : Fin n → Fin 4) (i : Fin (n + 1)) :
    (trace 0 (List.ofFn s))[i.val]'(by
      simpa only [trace, List.length_scanl, List.length_ofFn] using i.isLt) = position s i := by
  induction i using Fin.induction with
  | zero => simp [trace, position_zero]
  | succ i ih =>
    rw [position_succ, ← ih]
    simpa [trace] using
      (List.getElem_succ_scanl (f := fun y d => y + step d)
        (b := (0 : Point)) (l := List.ofFn s) (i := i.val) (by simp))

theorem trace_ofFn {n : ℕ} (s : Fin n → Fin 4) :
    trace 0 (List.ofFn s) = List.ofFn (position s) := by
  apply List.ext_getElem
  · simp [trace]
  · intro i hi hj
    simpa only [List.getElem_ofFn] using
      trace_get_ofFn s ⟨i, by simpa only [List.length_ofFn] using hj⟩

theorem strictBlock_ofFn_iff {n : ℕ} (s : Fin n → Fin 4) :
    StrictBlock (List.ofFn s) ↔ IsSelfAvoidingWalk s := by
  rw [StrictBlock, trace_ofFn, List.nodup_ofFn]
  rfl

/-- Each unordered pair of equal entries is counted once: pair the head with
each equal entry in its tail, then recurse. Diagonal pairs are excluded. -/
def unorderedCollisions {α : Type*} [BEq α] : List α → ℕ
  | [] => 0
  | x :: xs => xs.count x + unorderedCollisions xs

theorem unorderedCollisions_snoc {α : Type*} [BEq α] [LawfulBEq α]
    (xs : List α) (x : α) :
    unorderedCollisions (xs ++ [x]) = unorderedCollisions xs + xs.count x := by
  induction xs with
  | nil => simp [unorderedCollisions]
  | cons y ys ih =>
    simp only [List.cons_append, unorderedCollisions, List.count_append, ih,
      List.count_cons, List.count_nil, Nat.zero_add]
    have hxy : (x == y) = (y == x) := by
      by_cases h : x = y <;> simp_all [eq_comm]
    rw [hxy]
    omega

theorem count_ofFn {α : Type*} [DecidableEq α] [BEq α] [LawfulBEq α]
    {m : ℕ} (f : Fin m → α) (x : α) :
    (List.ofFn f).count x = ∑ i : Fin m, if f i = x then 1 else 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.ofFn_succ, List.count_cons, Fin.sum_univ_succ, ih]
    simp [beq_iff_eq, Nat.add_comm]

theorem unorderedCollisions_ofFn {α : Type*} [DecidableEq α] [BEq α] [LawfulBEq α] {m : ℕ}
    (f : Fin m → α) :
    unorderedCollisions (List.ofFn f) =
      ∑ i : Fin m, ∑ j : Fin m, if i < j ∧ f i = f j then 1 else 0 := by
  induction m with
  | zero => simp [unorderedCollisions]
  | succ m ih =>
    rw [List.ofFn_succ, unorderedCollisions, count_ofFn, ih]
    simp only [Fin.sum_univ_succ, Fin.not_lt_zero, Fin.succ_pos,
      Fin.succ_lt_succ_iff, false_and, true_and, if_false, Nat.zero_add]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [eq_comm]

/-- The conventional finite set of pairs of distinct times i < j at which the
walk visits the same vertex. This is unordered-pair counting, with no factor 2. -/
def timeCollisionPairs {n : ℕ} (s : Fin n → Fin 4) :
    Finset (Fin (n + 1) × Fin (n + 1)) :=
  Finset.univ.filter (fun ij => ij.1 < ij.2 ∧ position s ij.1 = position s ij.2)

theorem unorderedCollisions_eq_pair_card {n : ℕ} (s : Fin n → Fin 4) :
    unorderedCollisions (List.ofFn (position s)) = (timeCollisionPairs s).card := by
  rw [unorderedCollisions_ofFn]
  simp only [timeCollisionPairs, Finset.card_eq_sum_ones, Finset.sum_filter,
    Fintype.sum_prod_type]

def collisionCount (w : List Direction) : ℕ := unorderedCollisions (trace 0 w)

theorem collisionCount_snoc (w : List Direction) (d : Direction) :
    collisionCount (w ++ [d]) = collisionCount w +
      (trace 0 w).count (finish 0 w + step d) := by
  exact (congrArg unorderedCollisions (trace_snoc 0 w d)).trans
    (unorderedCollisions_snoc _ _)

/-- A block followed by its removed arrival direction, repeated zero or more
times, and a final block. Empty blocks are retained. -/
structure Encoding where
  separated : List (List Direction × Direction)
  lastBlock : List Direction

def Encoding.prefix (e : Encoding) : List Direction :=
  e.separated.flatMap (fun bd => bd.1 ++ [bd.2])

def Encoding.decode (e : Encoding) : List Direction := e.prefix ++ e.lastBlock

def Encoding.blocks (e : Encoding) : List (List Direction) :=
  e.separated.map Prod.fst ++ [e.lastBlock]

def Encoding.marks (e : Encoding) : List Direction := e.separated.map Prod.snd

def Encoding.Good (e : Encoding) : Prop :=
  (∀ bd ∈ e.separated, StrictBlock bd.1) ∧ StrictBlock e.lastBlock

def Encoding.extend (e : Encoding) (d : Direction) : Encoding :=
  ⟨e.separated, e.lastBlock ++ [d]⟩

def Encoding.cut (e : Encoding) (d : Direction) : Encoding :=
  ⟨e.separated ++ [(e.lastBlock, d)], []⟩

@[simp] theorem Encoding.decode_extend (e : Encoding) (d : Direction) :
    (e.extend d).decode = e.decode ++ [d] := by
  simp [extend, decode, Encoding.prefix, List.append_assoc]

@[simp] theorem Encoding.decode_cut (e : Encoding) (d : Direction) :
    (e.cut d).decode = e.decode ++ [d] := by
  simp [cut, decode, Encoding.prefix, List.flatMap_append, List.append_assoc]

theorem Encoding.good_cut {e : Encoding} (h : e.Good) (d : Direction) :
    (e.cut d).Good := by
  rcases h with ⟨hpre, hlast⟩
  constructor
  · intro bd hbd
    simp only [cut, List.mem_append, List.mem_singleton] at hbd
    rcases hbd with hbd | rfl
    · exact hpre bd hbd
    · exact hlast
  · simp [cut, StrictBlock, trace]

theorem Encoding.good_extend {e : Encoding} (h : e.Good) (d : Direction)
    (hfresh : finish 0 e.decode + step d ∉ trace 0 e.decode) :
    (e.extend d).Good := by
  exact ⟨h.1, strictBlock_snoc_of_fresh e.prefix e.lastBlock d h.2 hfresh⟩

/-- The branch condition uses the entire previous trace, not just the current
block. Thus every globally repeated arrival, and no other step, is removed. -/
def encode : List Direction → Encoding :=
  List.reverseRec ⟨[], []⟩ fun w d e =>
    if finish 0 w + step d ∈ trace 0 w then e.cut d else e.extend d

@[simp] theorem encode_nil : encode [] = ⟨[], []⟩ := by
  simp [encode]

theorem encode_snoc (w : List Direction) (d : Direction) :
    encode (w ++ [d]) =
      if finish 0 w + step d ∈ trace 0 w then (encode w).cut d
      else (encode w).extend d := by
  simp [encode]

theorem decode_encode (w : List Direction) : (encode w).decode = w := by
  induction w using List.reverseRecOn with
  | nil => simp [Encoding.decode, Encoding.prefix]
  | append_singleton w d ih =>
    rw [encode_snoc]
    split <;> simp [ih]

theorem good_encode (w : List Direction) : (encode w).Good := by
  induction w using List.reverseRecOn with
  | nil => simp [Encoding.Good, StrictBlock, trace]
  | append_singleton w d ih =>
    rw [encode_snoc]
    split
    · exact Encoding.good_cut ih d
    · apply Encoding.good_extend ih d
      simpa [decode_encode] using ‹finish 0 w + step d ∉ trace 0 w›

theorem encode_injective : Function.Injective encode := by
  intro a b hab
  simpa only [decode_encode] using congrArg Encoding.decode hab

theorem marks_le_collisions (w : List Direction) :
    (encode w).marks.length ≤ collisionCount w := by
  induction w using List.reverseRecOn with
  | nil => simp [Encoding.marks, collisionCount, trace, unorderedCollisions]
  | append_singleton w d ih =>
    rw [encode_snoc, collisionCount_snoc]
    split
    · have hp := List.count_pos_iff.mpr ‹finish 0 w + step d ∈ trace 0 w›
      simp only [Encoding.marks, Encoding.cut, List.length_map, List.length_append,
        List.length_singleton]
      simp only [Encoding.marks, List.length_map] at ih
      omega
    · simpa [Encoding.marks, Encoding.extend] using
        le_trans ih (Nat.le_add_right (collisionCount w) _)

theorem trace_toFinset_snoc (w : List Direction) (d : Direction) :
    (trace 0 (w ++ [d])).toFinset =
      insert (finish 0 w + step d) (trace 0 w).toFinset := by
  ext y
  simp [trace_snoc]

/-- Exactly one arrival is unmarked for each newly visited vertex other than
the initial origin. Equivalently, the mark count is n+1 minus the range size. -/
theorem marks_add_range (w : List Direction) :
    (encode w).marks.length + (trace 0 w).toFinset.card = w.length + 1 := by
  induction w using List.reverseRecOn with
  | nil => simp [Encoding.marks, trace]
  | append_singleton w d ih =>
    rw [encode_snoc, trace_toFinset_snoc]
    split
    · rw [Finset.card_insert_of_mem (List.mem_toFinset.mpr
        ‹finish 0 w + step d ∈ trace 0 w›)]
      simp only [Encoding.marks, Encoding.cut, List.length_map,
        List.length_append, List.length_singleton] at *
      omega
    · rw [Finset.card_insert_of_notMem (by simpa using
        ‹finish 0 w + step d ∉ trace 0 w›)]
      simp only [Encoding.marks, Encoding.extend, List.length_map,
        List.length_append, List.length_singleton] at *
      omega

theorem Encoding.blocks_length (e : Encoding) :
    e.blocks.length = e.marks.length + 1 := by
  simp [blocks, marks]

theorem Encoding.good_blocks {e : Encoding} (h : e.Good) :
    ∀ b ∈ e.blocks, StrictBlock b := by
  intro b hb
  simp only [blocks, List.mem_append, List.mem_map, List.mem_singleton] at hb
  rcases hb with ⟨bd, hbd, rfl⟩ | rfl
  · exact h.1 bd hbd
  · exact h.2

theorem Encoding.length_decode (e : Encoding) :
    e.decode.length = (e.blocks.map List.length).sum + e.marks.length := by
  rcases e with ⟨ps, b⟩
  have hp : (ps.flatMap (fun bd => bd.1 ++ [bd.2])).length =
      (ps.map (fun bd => bd.1.length)).sum + ps.length := by
    induction ps with
    | nil => simp
    | cons bd ps ih =>
      simp only [List.flatMap_cons, List.length_append,
        List.map_cons, List.sum_cons, List.length_cons, List.length_nil, ih]
      omega
  simp only [decode, Encoding.prefix, blocks, marks, List.length_append, hp, List.map_append,
    List.map_map, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
    List.sum_nil, Nat.add_zero, List.length_map, Function.comp_def]
  omega

theorem strictBlock_get_iff (b : List Direction) :
    StrictBlock b ↔ IsSelfAvoidingWalk b.get := by
  simpa only [List.ofFn_get] using strictBlock_ofFn_iff b.get

/-- The all-length encoding theorem, including exact reconstruction, strict
canonical blocks, the r+1 block count, conservation of length, and r ≤ J. -/
theorem repeatArrivalEncoding {n : ℕ} (s : Fin n → Fin 4) :
    ∃ e : Encoding,
      e.decode = List.ofFn s ∧
      (∀ b ∈ e.blocks, IsSelfAvoidingWalk b.get) ∧
      e.blocks.length = e.marks.length + 1 ∧
      (e.blocks.map List.length).sum + e.marks.length = n ∧
      e.marks.length ≤ unorderedCollisions (List.ofFn (position s)) := by
  refine ⟨encode (List.ofFn s), decode_encode _, ?_, Encoding.blocks_length _, ?_, ?_⟩
  · intro b hb
    exact (strictBlock_get_iff b).mp (Encoding.good_blocks (good_encode _) b hb)
  · rw [← Encoding.length_decode, decode_encode, List.length_ofFn]
  · simpa only [collisionCount, trace_ofFn] using marks_le_collisions (List.ofFn s)

/-- A version using the conventional collision-pair cardinality and including
the exact repeated-arrival count. Length conservation also yields sum lengths
= n-r, without needing that subtraction as a hypothesis. -/
theorem repeatArrivalEncodingExact {n : ℕ} (s : Fin n → Fin 4) :
    ∃ e : Encoding,
      e.decode = List.ofFn s ∧
      (∀ b ∈ e.blocks, IsSelfAvoidingWalk b.get) ∧
      e.blocks.length = e.marks.length + 1 ∧
      (e.blocks.map List.length).sum = n - e.marks.length ∧
      e.marks.length + (List.ofFn (position s)).toFinset.card = n + 1 ∧
      e.marks.length ≤ (timeCollisionPairs s).card := by
  refine ⟨encode (List.ofFn s), decode_encode _, ?_, Encoding.blocks_length _, ?_, ?_, ?_⟩
  · intro b hb
    exact (strictBlock_get_iff b).mp (Encoding.good_blocks (good_encode _) b hb)
  · have h := Encoding.length_decode (encode (List.ofFn s))
    rw [decode_encode, List.length_ofFn] at h
    omega
  · simpa only [trace_ofFn, List.length_ofFn] using marks_add_range (List.ofFn s)
  · rw [← unorderedCollisions_eq_pair_card]
    simpa only [collisionCount, trace_ofFn] using marks_le_collisions (List.ofFn s)

theorem encode_canonical_injective {n : ℕ} :
    Function.Injective (fun s : Fin n → Fin 4 => encode (List.ofFn s)) :=
  encode_injective.comp List.ofFn_injective


end PlanarSAWRepeatArrival

-- END p289/RepeatArrivalEncoding.lean

-- BEGIN p289/RepeatArrivalCount.lean; source SHA-256 41ddd568601cf3b4dd2afc2cdd58bc01991da9e33a702ed496cc4ab37c82fe6e

/-! Finite counting for the canonical all-length repeat-arrival encoding.
The checked encoding source is imported unchanged. -/

namespace PlanarSAWRepeatArrival

deriving instance DecidableEq for Encoding

noncomputable def canonicalWalks (n : ℕ) : Finset (Fin n → Fin 4) := by
  classical
  exact Finset.univ.filter IsSelfAvoidingWalk

noncomputable def strictWordCount (n : ℕ) : ℕ := (canonicalWalks n).card

noncomputable def strictBlocks (n : ℕ) : Finset (List Direction) :=
  (canonicalWalks n).image List.ofFn

theorem mem_canonicalWalks {n : ℕ} (s : Fin n → Fin 4) :
    s ∈ canonicalWalks n ↔ IsSelfAvoidingWalk s := by
  classical
  simp [canonicalWalks]

theorem mem_strictBlocks {n : ℕ} (b : List Direction) :
    b ∈ strictBlocks n ↔ b.length = n ∧ StrictBlock b := by
  classical
  constructor
  · intro hb
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hb
    exact ⟨List.length_ofFn, (strictBlock_ofFn_iff s).mpr ((mem_canonicalWalks s).mp hs)⟩
  · rintro ⟨rfl, hb⟩
    exact Finset.mem_image.mpr ⟨b.get,
      (mem_canonicalWalks _).mpr ((strictBlock_get_iff b).mp hb), List.ofFn_get b⟩

theorem strictBlocks_card (n : ℕ) : (strictBlocks n).card = strictWordCount n :=
  Finset.card_image_of_injective _ List.ofFn_injective

def Encoding.prepend (b : List Direction) (d : Direction) (e : Encoding) : Encoding :=
  ⟨(b, d) :: e.separated, e.lastBlock⟩

theorem Encoding.decode_prepend (b : List Direction) (d : Direction) (e : Encoding) :
    (prepend b d e).decode = b ++ [d] ++ e.decode := by
  simp [prepend, decode, Encoding.prefix, List.append_assoc]

/-- An enlarged finite family: strict blocks and marked directions with total
word length n and r separators. Its separators need not be actual repeats. -/
noncomputable def encodingFamily (n r : ℕ) : Finset Encoding := by
  classical
  exact match r with
  | 0 => (strictBlocks n).image (fun b => ⟨[], b⟩)
  | r + 1 => (Finset.range n).biUnion fun l =>
      (((strictBlocks l) ×ˢ (Finset.univ : Finset Direction)) ×ˢ
        encodingFamily (n - l - 1) r).image
          (fun p => Encoding.prepend p.1.1 p.1.2 p.2)
termination_by r

theorem encodingFamily_zero (n : ℕ) :
    encodingFamily n 0 = (strictBlocks n).image (fun b => ⟨[], b⟩) := by
  simp [encodingFamily]

theorem encodingFamily_succ (n r : ℕ) :
    encodingFamily n (r + 1) = (Finset.range n).biUnion (fun l =>
      (((strictBlocks l) ×ˢ (Finset.univ : Finset Direction)) ×ˢ
        encodingFamily (n - l - 1) r).image
          (fun p => Encoding.prepend p.1.1 p.1.2 p.2)) := by
  simp [encodingFamily]

theorem mem_encodingFamily_of_good {n r : ℕ} (e : Encoding) (hg : e.Good)
    (hlen : e.decode.length = n) (hmarks : e.marks.length = r) :
    e ∈ encodingFamily n r := by
  classical
  induction r generalizing n e with
  | zero =>
    rcases e with ⟨ps, b⟩
    have hps : ps = [] := by simpa [Encoding.marks] using hmarks
    subst ps
    rw [encodingFamily_zero]
    apply Finset.mem_image.mpr
    refine ⟨b, (mem_strictBlocks b).mpr ⟨?_, hg.2⟩, rfl⟩
    simpa [Encoding.decode, Encoding.prefix] using hlen
  | succ r ih =>
    rcases e with ⟨ps, b⟩
    cases ps with
    | nil => simp [Encoding.marks] at hmarks
    | cons bd ps =>
      let rest : Encoding := ⟨ps, b⟩
      have hfirst : StrictBlock bd.1 := hg.1 bd (by simp)
      have hrest : rest.Good := ⟨fun c hc => hg.1 c (List.mem_cons_of_mem bd hc), hg.2⟩
      have hr : rest.marks.length = r := by
        simpa [rest, Encoding.marks] using hmarks
      have hn : bd.1.length + 1 + rest.decode.length = n := by
        change (Encoding.prepend bd.1 bd.2 rest).decode.length = n at hlen
        simpa only [Encoding.decode_prepend, List.length_append, List.length_singleton]
          using hlen
      have hlt : bd.1.length < n := by omega
      have hrem : rest.decode.length = n - bd.1.length - 1 := by omega
      rw [encodingFamily_succ]
      apply Finset.mem_biUnion.mpr
      refine ⟨bd.1.length, Finset.mem_range.mpr hlt, ?_⟩
      apply Finset.mem_image.mpr
      refine ⟨((bd.1, bd.2), rest), ?_, rfl⟩
      exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr
        ⟨(mem_strictBlocks _).mpr ⟨rfl, hfirst⟩, Finset.mem_univ _⟩,
        ih rest hrest hrem hr⟩

/-- c-weighted compositions whose total block length plus separator count is n.
For r ≤ n this is the sum over r+1 block lengths with sum n-r. -/
noncomputable def blockConvolution (n : ℕ) : ℕ → ℕ
  | 0 => strictWordCount n
  | r + 1 => ∑ l ∈ Finset.range n, strictWordCount l * blockConvolution (n - l - 1) r

theorem encodingFamily_card_le (n r : ℕ) :
    (encodingFamily n r).card ≤ 4 ^ r * blockConvolution n r := by
  classical
  induction r generalizing n with
  | zero =>
    rw [encodingFamily_zero]
    simpa [blockConvolution, strictBlocks_card] using
      (Finset.card_image_le (s := strictBlocks n) (f := fun b => (⟨[], b⟩ : Encoding)))
  | succ r ih =>
    rw [encodingFamily_succ]
    calc
      _ ≤ ∑ l ∈ Finset.range n,
          ((((strictBlocks l) ×ˢ (Finset.univ : Finset Direction)) ×ˢ
            encodingFamily (n - l - 1) r).image
              (fun p => Encoding.prepend p.1.1 p.1.2 p.2)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ l ∈ Finset.range n,
          strictWordCount l * 4 * (encodingFamily (n - l - 1) r).card := by
        apply Finset.sum_le_sum
        intro l _
        simpa [Finset.card_product, strictBlocks_card] using
          (Finset.card_image_le (s := ((strictBlocks l) ×ˢ
            (Finset.univ : Finset Direction)) ×ˢ encodingFamily (n - l - 1) r)
            (f := fun p => Encoding.prepend p.1.1 p.1.2 p.2))
      _ ≤ ∑ l ∈ Finset.range n,
          strictWordCount l * 4 * (4 ^ r * blockConvolution (n - l - 1) r) := by
        apply Finset.sum_le_sum
        intro l _
        exact Nat.mul_le_mul_left _ (ih _)
      _ = 4 ^ (r + 1) * blockConvolution n (r + 1) := by
        simp only [blockConvolution, pow_succ, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        ac_rfl

/-- N(n,r), counted in the full finite canonical direction-word space. -/
noncomputable def wordsWithRepeats (n r : ℕ) : Finset (Fin n → Fin 4) := by
  classical
  exact Finset.univ.filter (fun s => (encode (List.ofFn s)).marks.length = r)

noncomputable def repeatedWordCount (n r : ℕ) : ℕ := (wordsWithRepeats n r).card

theorem repeatedWordCount_le_encodingFamily (n r : ℕ) :
    repeatedWordCount n r ≤ (encodingFamily n r).card := by
  classical
  let f : (Fin n → Fin 4) → Encoding := fun s => encode (List.ofFn s)
  have hf : Function.Injective f := encode_canonical_injective
  have hs : (wordsWithRepeats n r).image f ⊆ encodingFamily n r := by
    intro e he
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp he
    apply mem_encodingFamily_of_good _ (good_encode _)
    · simp only [decode_encode, List.length_ofFn]
    · exact (Finset.mem_filter.mp hs).2
  have hc := Finset.card_le_card hs
  rw [Finset.card_image_of_injective _ hf] at hc
  exact hc

/-- The finite convolution majorant, valid for all lengths and all r. -/
theorem repeatArrival_count_bound (n r : ℕ) :
    repeatedWordCount n r ≤ 4 ^ r * blockConvolution n r :=
  (repeatedWordCount_le_encodingFamily n r).trans (encodingFamily_card_le n r)

/-- The conventional composition sum over r+1 nonnegative block lengths. -/
noncomputable def compositionWeight (m r : ℕ) : ℕ :=
  ∑ l ∈ Finset.Nat.antidiagonalTuple (r + 1) m, ∏ i, strictWordCount (l i)

theorem compositionWeight_zero (m : ℕ) :
    compositionWeight m 0 = strictWordCount m := by
  simp [compositionWeight]

theorem compositionWeight_succ (m r : ℕ) :
    compositionWeight m (r + 1) =
      ∑ l ∈ Finset.range (m + 1), strictWordCount l * compositionWeight (m - l) r := by
  change ((List.Nat.antidiagonalTuple (r + 2) m).map
    (fun l => ∏ i, strictWordCount (l i))).sum =
      ((List.range (m + 1)).map (fun l => strictWordCount l *
        ((List.Nat.antidiagonalTuple (r + 1) (m - l)).map
          (fun t => ∏ i, strictWordCount (t i))).sum)).sum
  rw [List.Nat.antidiagonalTuple]
  simp only [List.Nat.antidiagonal, List.flatMap, List.map_flatten,
    List.map_map, Function.comp_def, List.sum_flatten,
    Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, List.sum_map_mul_left]

theorem blockConvolution_zero_of_lt {n r : ℕ} (h : n < r) :
    blockConvolution n r = 0 := by
  induction r generalizing n with
  | zero => omega
  | succ r ih =>
    rw [blockConvolution]
    apply Finset.sum_eq_zero
    intro l hl
    have hl' := Finset.mem_range.mp hl
    rw [ih (by omega), Nat.mul_zero]

theorem blockConvolution_eq_compositionWeight {n r : ℕ} (h : r ≤ n) :
    blockConvolution n r = compositionWeight (n - r) r := by
  induction r generalizing n with
  | zero => simp [blockConvolution, compositionWeight_zero]
  | succ r ih =>
    rw [blockConvolution, compositionWeight_succ]
    have hsub : Finset.range (n - (r + 1) + 1) ⊆ Finset.range n :=
      Finset.range_mono (by omega)
    calc
      _ = ∑ l ∈ Finset.range (n - (r + 1) + 1),
          strictWordCount l * blockConvolution (n - l - 1) r := by
        symm
        apply Finset.sum_subset hsub
        intro l hln hlm
        have hln' := Finset.mem_range.mp hln
        have hlm' : n - (r + 1) + 1 ≤ l := by simpa using hlm
        rw [blockConvolution_zero_of_lt (by omega), Nat.mul_zero]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro l hl
        have hl' := Finset.mem_range.mp hl
        rw [ih (by omega)]
        congr 2
        omega

/-- The requested closed finite bound, including the trivial r>n case. -/
theorem repeatArrival_composition_bound (n r : ℕ) :
    repeatedWordCount n r ≤ 4 ^ r *
      ∑ l ∈ Finset.Nat.antidiagonalTuple (r + 1) (n - r),
        ∏ i, strictWordCount (l i) := by
  by_cases h : r ≤ n
  · simpa only [blockConvolution_eq_compositionWeight h, compositionWeight] using
      repeatArrival_count_bound n r
  · have hz := repeatArrival_count_bound n r
    rw [blockConvolution_zero_of_lt (by omega), Nat.mul_zero] at hz
    exact le_trans hz (Nat.zero_le _)


end PlanarSAWRepeatArrival

-- END p289/RepeatArrivalCount.lean

-- BEGIN p289/SoftHardEstimate.lean; source SHA-256 5cfbc3e9d0de7f9312b416de4ed4c46ce935b99953399da1faec52a5db1a6d70

/-!
Finite weighted-average comparison. These theorems do not establish any SAW
count, asymptotic estimate, or endpoint lower bound. The good set is nonempty;
the bad set and its total weight may be empty or zero.
-/

namespace PlanarSAWSoftHard

open scoped BigOperators

variable {α : Type*} [DecidableEq α]

noncomputable def weightedMean (Ω : Finset α) (w f : α → ℝ) : ℝ :=
  (∑ i ∈ Ω, w i * f i) / (∑ i ∈ Ω, w i)

noncomputable def uniformMean (A : Finset α) (f : α → ℝ) : ℝ :=
  (∑ i ∈ A, f i) / (A.card : ℝ)

noncomputable def badRatio (Ω A : Finset α) (w : α → ℝ) : ℝ :=
  (∑ i ∈ Ω \ A, w i) / (A.card : ℝ)

theorem sum_split (Ω A : Finset α) (hA : A ⊆ Ω) (g : α → ℝ) :
    (∑ i ∈ Ω, g i) = (∑ i ∈ A, g i) + (∑ i ∈ Ω \ A, g i) := by
  rw [← Finset.sum_sdiff hA]
  ring

theorem sum_weight_eq (Ω A : Finset α) (w : α → ℝ)
    (hA : A ⊆ Ω) (hone : ∀ i ∈ A, w i = 1) :
    (∑ i ∈ Ω, w i) = (A.card : ℝ) + (∑ i ∈ Ω \ A, w i) := by
  rw [sum_split Ω A hA]
  congr 1
  calc
    (∑ i ∈ A, w i) = ∑ _i ∈ A, (1 : ℝ) :=
      Finset.sum_congr rfl hone
    _ = (A.card : ℝ) := by simp

theorem sum_weight_pos (Ω A : Finset α) (w : α → ℝ)
    (hA : A ⊆ Ω) (hne : A.Nonempty)
    (hw : ∀ i ∈ Ω, 0 ≤ w i) (hone : ∀ i ∈ A, w i = 1) :
    0 < ∑ i ∈ Ω, w i := by
  rw [sum_weight_eq Ω A w hA hone]
  have ha : (0 : ℝ) < A.card := by
    exact_mod_cast Finset.card_pos.mpr hne
  have hb : 0 ≤ ∑ i ∈ Ω \ A, w i :=
    Finset.sum_nonneg fun i hi => hw i (Finset.mem_sdiff.mp hi).1
  linarith

theorem badRatio_nonneg (Ω A : Finset α) (w : α → ℝ)
    (hw : ∀ i ∈ Ω, 0 ≤ w i) :
    0 ≤ badRatio Ω A w := by
  exact div_nonneg
    (Finset.sum_nonneg fun i hi => hw i (Finset.mem_sdiff.mp hi).1)
    (Nat.cast_nonneg _)

theorem bad_fraction_eq (Ω A : Finset α) (w : α → ℝ)
    (hA : A ⊆ Ω) (hne : A.Nonempty)
    (hw : ∀ i ∈ Ω, 0 ≤ w i) (hone : ∀ i ∈ A, w i = 1) :
    (∑ i ∈ Ω \ A, w i) / (∑ i ∈ Ω, w i) =
      badRatio Ω A w / (1 + badRatio Ω A w) := by
  have ha : (0 : ℝ) < A.card := by
    exact_mod_cast Finset.card_pos.mpr hne
  have hz := sum_weight_pos Ω A w hA hne hw hone
  have hr : 0 < 1 + badRatio Ω A w := by
    have := badRatio_nonneg Ω A w hw
    linarith
  rw [sum_weight_eq Ω A w hA hone] at hz ⊢
  unfold badRatio at hr ⊢
  field_simp

/-- Scalar form of the mixture estimate, with no division by bad mass. -/
theorem bounded_mixture (a b g h n : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (hg0 : 0 ≤ g) (hgn : g ≤ n * a)
    (hh0 : 0 ≤ h) (hhn : h ≤ n * b) :
    |(g + h) / (a + b) - g / a| ≤ n * b / (a + b) := by
  have hab : 0 < a + b := by linarith
  have hu0 : 0 ≤ g / a := div_nonneg hg0 ha.le
  have hun : g / a ≤ n := (div_le_iff₀ ha).mpr hgn
  have hbu0 : 0 ≤ b * (g / a) := mul_nonneg hb hu0
  have hbun : b * (g / a) ≤ b * n :=
    mul_le_mul_of_nonneg_left hun hb
  have hbound : |h - b * (g / a)| ≤ n * b := by
    apply abs_le.mpr
    constructor <;> linarith
  have hid : (g + h) / (a + b) - g / a =
      (h - b * (g / a)) / (a + b) := by
    field_simp
    ring
  rw [hid, abs_div, abs_of_pos hab]
  exact div_le_div_of_nonneg_right hbound hab.le

/-- Any [0,n]-valued observable changes by at most n times the normalized
bad mass. The bound remains valid when the bad set is empty. -/
theorem weightedMean_sub_uniformMean_le (Ω A : Finset α) (w f : α → ℝ) (n : ℝ)
    (hA : A ⊆ Ω) (hne : A.Nonempty)
    (hw : ∀ i ∈ Ω, 0 ≤ w i) (hone : ∀ i ∈ A, w i = 1)
    (hf : ∀ i ∈ Ω, 0 ≤ f i ∧ f i ≤ n) :
    |weightedMean Ω w f - uniformMean A f| ≤
      n * badRatio Ω A w / (1 + badRatio Ω A w) := by
  have ha : (0 : ℝ) < A.card := by
    exact_mod_cast Finset.card_pos.mpr hne
  have hb : 0 ≤ ∑ i ∈ Ω \ A, w i :=
    Finset.sum_nonneg fun i hi => hw i (Finset.mem_sdiff.mp hi).1
  have hg0 : 0 ≤ ∑ i ∈ A, f i :=
    Finset.sum_nonneg fun i hi => (hf i (hA hi)).1
  have hgn : (∑ i ∈ A, f i) ≤ n * (A.card : ℝ) := by
    calc
      (∑ i ∈ A, f i) ≤ ∑ _i ∈ A, n :=
        Finset.sum_le_sum fun i hi => (hf i (hA hi)).2
      _ = n * (A.card : ℝ) := by simp [mul_comm]
  have hh0 : 0 ≤ ∑ i ∈ Ω \ A, w i * f i := by
    apply Finset.sum_nonneg
    intro i hi
    have hiΩ := (Finset.mem_sdiff.mp hi).1
    exact mul_nonneg (hw i hiΩ) (hf i hiΩ).1
  have hhn : (∑ i ∈ Ω \ A, w i * f i) ≤ n * (∑ i ∈ Ω \ A, w i) := by
    calc
      (∑ i ∈ Ω \ A, w i * f i) ≤ ∑ i ∈ Ω \ A, w i * n := by
        apply Finset.sum_le_sum
        intro i hi
        have hiΩ := (Finset.mem_sdiff.mp hi).1
        exact mul_le_mul_of_nonneg_left (hf i hiΩ).2 (hw i hiΩ)
      _ = n * (∑ i ∈ Ω \ A, w i) := by rw [← Finset.sum_mul]; ring
  have hg : (∑ i ∈ A, w i * f i) = ∑ i ∈ A, f i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hone i hi, one_mul]
  have hmix := bounded_mixture (A.card : ℝ) (∑ i ∈ Ω \ A, w i)
    (∑ i ∈ A, f i) (∑ i ∈ Ω \ A, w i * f i) n ha hb hg0 hgn hh0 hhn
  unfold weightedMean uniformMean
  rw [sum_split Ω A hA (fun i => w i * f i), hg,
    sum_weight_eq Ω A w hA hone]
  calc
    _ ≤ n * (∑ i ∈ Ω \ A, w i) /
        ((A.card : ℝ) + ∑ i ∈ Ω \ A, w i) := hmix
    _ = n * badRatio Ω A w / (1 + badRatio Ω A w) := by
      have hfrac := bad_fraction_eq Ω A w hA hne hw hone
      rw [sum_weight_eq Ω A w hA hone] at hfrac
      simpa only [mul_div_assoc] using congrArg (n * ·) hfrac

/-- Zero bad mass, including an empty bad set, makes the means equal. -/
theorem weightedMean_eq_of_zero_bad_mass (Ω A : Finset α) (w f : α → ℝ) (n : ℝ)
    (hA : A ⊆ Ω) (hne : A.Nonempty)
    (hw : ∀ i ∈ Ω, 0 ≤ w i) (hone : ∀ i ∈ A, w i = 1)
    (hf : ∀ i ∈ Ω, 0 ≤ f i ∧ f i ≤ n)
    (hbad : (∑ i ∈ Ω \ A, w i) = 0) :
    weightedMean Ω w f = uniformMean A f := by
  have h := weightedMean_sub_uniformMean_le Ω A w f n hA hne hw hone hf
  simp only [badRatio, hbad, zero_div, mul_zero, add_zero, zero_div] at h
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))

/-- An algebraic bound; no exponential function or binomial coefficients occur. -/
theorem pow_mul_one_sub_mul_le_one (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    (1 + x) ^ n * (1 - (n : ℝ) * x) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp : 0 ≤ (1 + x) ^ n := pow_nonneg (by linarith) _
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hs : 0 ≤ ((n : ℝ) + 1) * x ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg x)
    calc
      (1 + x) ^ (n + 1) * (1 - ((n + 1 : ℕ) : ℝ) * x)
          ≤ (1 + x) ^ n * (1 - (n : ℝ) * x) := by
        simp only [pow_succ, Nat.cast_add, Nat.cast_one]
        nlinarith [mul_nonneg hp hs]
      _ ≤ 1 := ih

theorem pow_sub_one_le_two_mul (n : ℕ) (x : ℝ)
    (hx : 0 ≤ x) (hnx : (n : ℝ) * x ≤ 1 / 2) :
    (1 + x) ^ n - 1 ≤ 2 * (n : ℝ) * x := by
  have h := pow_mul_one_sub_mul_le_one n x hx
  have hp : 0 ≤ (1 + x) ^ n := pow_nonneg (by linarith) _
  have ht : 0 ≤ (n : ℝ) * x := mul_nonneg (Nat.cast_nonneg n) hx
  have hp2 : (1 + x) ^ n ≤ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hnx hp]
  nlinarith [mul_le_mul_of_nonneg_left hp2 ht]

/-- The scalar remainder bound used after the finite-count estimate.
For the intended application, a = exp H and x ≤ exp(-H)/(n+1)^3.
Those substitutions and the SAW count estimate remain separate premises. -/
theorem scalar_majorant_le (n : ℕ) (a x R : ℝ)
    (ha : 1 ≤ a) (hx0 : 0 ≤ x)
    (hx : x ≤ 1 / (a * ((n : ℝ) + 1) ^ 3))
    (hR : R ≤ a * ((1 + x) ^ n - 1)) :
    R ≤ 2 * (n : ℝ) / ((n : ℝ) + 1) ^ 3 := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have ha0 : 0 < a := by linarith
  have hd : 0 < ((n : ℝ) + 1) ^ 3 := pow_pos (by linarith) _
  have hdge : 2 * (n : ℝ) ≤ ((n : ℝ) + 1) ^ 3 := by
    nlinarith [sq_nonneg (n : ℝ), pow_nonneg hn 3]
  have hprod : a * x * ((n : ℝ) + 1) ^ 3 ≤ 1 := by
    have h := (le_div_iff₀ (mul_pos ha0 hd)).mp hx
    nlinarith [h]
  have hax : a * x ≤ 1 / ((n : ℝ) + 1) ^ 3 :=
    (le_div_iff₀ hd).mpr hprod
  have hxd : x * ((n : ℝ) + 1) ^ 3 ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right ha (mul_nonneg hx0 hd.le)
    nlinarith
  have hnx : (n : ℝ) * x ≤ 1 / 2 := by
    have h := mul_le_mul_of_nonneg_right hdge hx0
    nlinarith
  calc
    R ≤ a * ((1 + x) ^ n - 1) := hR
    _ ≤ a * (2 * (n : ℝ) * x) :=
      mul_le_mul_of_nonneg_left (pow_sub_one_le_two_mul n x hx0 hnx) ha0.le
    _ = (2 * (n : ℝ)) * (a * x) := by ring
    _ ≤ (2 * (n : ℝ)) * (1 / ((n : ℝ) + 1) ^ 3) :=
      mul_le_mul_of_nonneg_left hax (by linarith)
    _ = 2 * (n : ℝ) / ((n : ℝ) + 1) ^ 3 := by ring

theorem ratio_fraction_le_self (R : ℝ) (hR : 0 ≤ R) :
    R / (1 + R) ≤ R := by
  apply (div_le_iff₀ (by linarith : 0 < 1 + R)).mpr
  nlinarith [sq_nonneg R]

/-- A supplied bad-ratio upper bound gives a finite observable error bound. -/
theorem weightedMean_sub_uniformMean_le_of_ratio_le
    (Ω A : Finset α) (w f : α → ℝ) (n : ℕ) (r : ℝ)
    (hA : A ⊆ Ω) (hne : A.Nonempty)
    (hw : ∀ i ∈ Ω, 0 ≤ w i) (hone : ∀ i ∈ A, w i = 1)
    (hf : ∀ i ∈ Ω, 0 ≤ f i ∧ f i ≤ (n : ℝ))
    (hr : badRatio Ω A w ≤ r) :
    |weightedMean Ω w f - uniformMean A f| ≤ (n : ℝ) * r := by
  calc
    _ ≤ (n : ℝ) * badRatio Ω A w / (1 + badRatio Ω A w) :=
      weightedMean_sub_uniformMean_le Ω A w f n hA hne hw hone hf
    _ = (n : ℝ) * (badRatio Ω A w / (1 + badRatio Ω A w)) := by ring
    _ ≤ (n : ℝ) * badRatio Ω A w :=
      mul_le_mul_of_nonneg_left
        (ratio_fraction_le_self _ (badRatio_nonneg Ω A w hw)) (Nat.cast_nonneg n)
    _ ≤ (n : ℝ) * r := mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg n)

theorem weightedMean_sub_uniformMean_le_of_scalar_majorant
    (Ω A : Finset α) (w f : α → ℝ) (n : ℕ) (a x : ℝ)
    (hA : A ⊆ Ω) (hne : A.Nonempty)
    (hw : ∀ i ∈ Ω, 0 ≤ w i) (hone : ∀ i ∈ A, w i = 1)
    (hf : ∀ i ∈ Ω, 0 ≤ f i ∧ f i ≤ (n : ℝ))
    (ha : 1 ≤ a) (hx0 : 0 ≤ x)
    (hx : x ≤ 1 / (a * ((n : ℝ) + 1) ^ 3))
    (hR : badRatio Ω A w ≤ a * ((1 + x) ^ n - 1)) :
    |weightedMean Ω w f - uniformMean A f| ≤
      2 * (n : ℝ) ^ 2 / ((n : ℝ) + 1) ^ 3 := by
  have h := weightedMean_sub_uniformMean_le_of_ratio_le Ω A w f n
    (2 * (n : ℝ) / ((n : ℝ) + 1) ^ 3) hA hne hw hone hf
    (scalar_majorant_le n a x _ ha hx0 hx hR)
  convert h using 1
  ring

end PlanarSAWSoftHard


-- END p289/SoftHardEstimate.lean

-- BEGIN p289/WalkAverages.lean; source SHA-256 5ec53d4c3888f9a47b961de1294f9bda9ca975576ed7b8e4f5352fc3635231c1

/-!
The direction-word and vertex-path descriptions of a finite square-lattice walk
are equivalent. Point, step, position, and IsSelfAvoidingWalk are copied exactly
from the canonical definitions for Jig #289; only the namespace differs.
-/

namespace PlanarSAWDirectionBridge

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

def GridAdjacent (x y : Point) : Prop :=
  (y.1 = x.1 + 1 ∧ y.2 = x.2) ∨
  (y.1 = x.1 - 1 ∧ y.2 = x.2) ∨
  (y.1 = x.1 ∧ y.2 = x.2 + 1) ∨
  (y.1 = x.1 ∧ y.2 = x.2 - 1)

def HasUnitSteps {n : ℕ} (p : Fin (n + 1) → Point) : Prop :=
  ∀ i : Fin n, GridAdjacent (p i.castSucc) (p i.succ)

theorem step_injective : Function.Injective step := by
  unfold Function.Injective
  decide

theorem position_zero {n : ℕ} (s : Fin n → Fin 4) :
    position s 0 = (0, 0) := by
  unfold position
  apply Finset.sum_eq_zero
  intro i _
  exact Fin.elim0 i

theorem position_succ {n : ℕ} (s : Fin n → Fin 4) (i : Fin n) :
    position s i.succ = position s i.castSucc + step (s i) := by
  simp only [position, Fin.val_succ, Fin.val_castSucc]
  rw [Fin.sum_univ_castSucc]
  congr 1

theorem position_injective {n : ℕ} :
    Function.Injective (@position n) := by
  intro s t h
  funext i
  apply step_injective
  have hnext := congrFun h i.succ
  have hcurrent := congrFun h i.castSucc
  rw [position_succ, position_succ, hcurrent] at hnext
  exact add_left_cancel hnext

theorem gridAdjacent_iff_exists_step (x y : Point) :
    GridAdjacent x y ↔ ∃ d : Fin 4, y = x + step d := by
  constructor
  · intro h
    rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · refine ⟨0, ?_⟩
      apply Prod.ext
      · simpa [step] using h₁
      · simpa [step] using h₂
    · refine ⟨1, ?_⟩
      apply Prod.ext
      · simpa [step, sub_eq_add_neg] using h₁
      · simpa [step] using h₂
    · refine ⟨2, ?_⟩
      apply Prod.ext
      · simpa [step] using h₁
      · simpa [step] using h₂
    · refine ⟨3, ?_⟩
      apply Prod.ext
      · simpa [step] using h₁
      · simpa [step, sub_eq_add_neg] using h₂
  · rintro ⟨d, rfl⟩
    by_cases h₀ : d = 0
    · left
      simp [step, h₀]
    · by_cases h₁ : d = 1
      · right; left
        simp [step, h₁, sub_eq_add_neg]
      · by_cases h₂ : d = 2
        · right; right; left
          simp [step, h₂]
        · right; right; right
          simp [step, h₀, h₁, h₂, sub_eq_add_neg]

theorem position_hasUnitSteps {n : ℕ} (s : Fin n → Fin 4) :
    HasUnitSteps (position s) := by
  intro i
  exact (gridAdjacent_iff_exists_step _ _).mpr ⟨s i, position_succ s i⟩

/-- Every rooted unit-step vertex path is the partial-sum path of a direction
word. No self-avoidance assumption is needed for this representation theorem. -/
theorem exists_directionWord {n : ℕ} (p : Fin (n + 1) → Point)
    (hzero : p 0 = (0, 0)) (hsteps : HasUnitSteps p) :
    ∃ s : Fin n → Fin 4, position s = p := by
  classical
  have hd : ∀ i : Fin n, ∃ d : Fin 4, p i.succ = p i.castSucc + step d :=
    fun i => (gridAdjacent_iff_exists_step _ _).mp (hsteps i)
  let s : Fin n → Fin 4 := fun i => Classical.choose (hd i)
  have hs : ∀ i : Fin n, p i.succ = p i.castSucc + step (s i) :=
    fun i => Classical.choose_spec (hd i)
  refine ⟨s, ?_⟩
  funext t
  refine Fin.induction ?_ ?_ t
  · exact (position_zero s).trans hzero.symm
  · intro i hi
    rw [position_succ, hi, ← hs i]

theorem existsUnique_directionWord {n : ℕ} (p : Fin (n + 1) → Point)
    (hzero : p 0 = (0, 0)) (hsteps : HasUnitSteps p) :
    ∃! s : Fin n → Fin 4, position s = p := by
  obtain ⟨s, hs⟩ := exists_directionWord p hzero hsteps
  refine ⟨s, hs, ?_⟩
  intro t ht
  exact position_injective (ht.trans hs.symm)

theorem exists_selfAvoidingWord {n : ℕ} (p : Fin (n + 1) → Point)
    (hzero : p 0 = (0, 0)) (hsteps : HasUnitSteps p)
    (hp : Function.Injective p) :
    ∃ s : Fin n → Fin 4, IsSelfAvoidingWalk s ∧ position s = p := by
  obtain ⟨s, hs⟩ := exists_directionWord p hzero hsteps
  refine ⟨s, ?_, hs⟩
  unfold IsSelfAvoidingWalk
  rw [hs]
  exact hp

theorem exists_directionWord_iff {n : ℕ} (p : Fin (n + 1) → Point) :
    (∃ s : Fin n → Fin 4, position s = p) ↔
      p 0 = (0, 0) ∧ HasUnitSteps p := by
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨position_zero s, position_hasUnitSteps s⟩
  · rintro ⟨hzero, hsteps⟩
    exact exists_directionWord p hzero hsteps

theorem exists_selfAvoidingWord_iff {n : ℕ} (p : Fin (n + 1) → Point) :
    (∃ s : Fin n → Fin 4, IsSelfAvoidingWalk s ∧ position s = p) ↔
      p 0 = (0, 0) ∧ HasUnitSteps p ∧ Function.Injective p := by
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨position_zero s, position_hasUnitSteps s, hs⟩
  · rintro ⟨hzero, hsteps, hp⟩
    exact exists_selfAvoidingWord p hzero hsteps hp

end PlanarSAWDirectionBridge


namespace PlanarSAWTailBound

theorem max_natAbs_le_euclidean (z : ℤ × ℤ) :
    ((max z.1.natAbs z.2.natAbs : ℕ) : ℝ) ≤
      Real.sqrt ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) := by
  rw [Nat.cast_max]
  apply max_le
  · rw [Nat.cast_natAbs, Int.cast_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg _))
  · rw [Nat.cast_natAbs, Int.cast_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (le_add_of_nonneg_left (sq_nonneg _))

/-- The reflection counting inequality forces a lower bound for the first moment.
The high-endpoint set contributes both its baseline m and its excess above m. -/
theorem mean_sum_bound {α : Type*} (s : Finset α) (R : α → ℝ) (m : ℝ)
    (hm : 0 ≤ m) (hR : ∀ x ∈ s, 0 ≤ R x)
    (hcount : ((s.filter (fun x => R x ≤ m)).card : ℝ) ≤
      (m + 1) * ((s.filter (fun x => m * (m + 2) ≤ R x)).card : ℝ)) :
    m * s.card ≤ ∑ x ∈ s, R x := by
  classical
  have hpoint (x : α) (hx : x ∈ s) :
      m ≤ R x + (if R x ≤ m then m else 0) -
        (if m * (m + 2) ≤ R x then m * (m + 1) else 0) := by
    have hnonneg := hR x hx
    split_ifs <;> nlinarith [sq_nonneg m]
  have hsum := Finset.sum_le_sum (s := s) hpoint
  have hlow : (∑ x ∈ s, if R x ≤ m then m else 0) =
      ((s.filter (fun x => R x ≤ m)).card : ℝ) * m := by
    rw [← Finset.sum_filter]
    simp
  have hhigh : (∑ x ∈ s, if m * (m + 2) ≤ R x then m * (m + 1) else 0) =
      ((s.filter (fun x => m * (m + 2) ≤ R x)).card : ℝ) * (m * (m + 1)) := by
    rw [← Finset.sum_filter]
    simp
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, hlow, hhigh,
    Finset.sum_const, nsmul_eq_mul] at hsum
  have hweighted := mul_le_mul_of_nonneg_left hcount hm
  nlinarith [hsum, hweighted]

theorem mean_bound {α : Type*} (s : Finset α) (R : α → ℝ) (m : ℝ)
    (hne : s.Nonempty) (hm : 0 ≤ m) (hR : ∀ x ∈ s, 0 ≤ R x)
    (hcount : ((s.filter (fun x => R x ≤ m)).card : ℝ) ≤
      (m + 1) * ((s.filter (fun x => m * (m + 2) ≤ R x)).card : ℝ)) :
    m ≤ (∑ x ∈ s, R x) / s.card := by
  have hc : (0 : ℝ) < s.card := by exact_mod_cast Finset.card_pos.mpr hne
  exact (le_div_iff₀ hc).mpr (mean_sum_bound s R m hm hR hcount)

end PlanarSAWTailBound

namespace PlanarSAWDirectionBridge

noncomputable def walks (n : ℕ) : Finset (Fin n → Fin 4) := by
  classical
  exact Finset.univ.filter IsSelfAvoidingWalk

noncomputable def endpointDistance {n : ℕ} (s : Fin n → Fin 4) : ℝ :=
  Real.sqrt (((position s (Fin.last n)).1 : ℝ)^2 +
             ((position s (Fin.last n)).2 : ℝ)^2)

noncomputable def expectedDistance (n : ℕ) : ℝ :=
  ((walks n).sum endpointDistance) / (walks n).card

def endpointNorm {n : ℕ} (s : Fin n → Fin 4) : ℕ :=
  max (position s (Fin.last n)).1.natAbs (position s (Fin.last n)).2.natAbs

theorem position_allEast {n : ℕ} (t : Fin (n + 1)) :
    position (fun _ : Fin n => (0 : Fin 4)) t = ((t.val : ℤ), 0) := by
  simp [position, step]

theorem walks_nonempty (n : ℕ) : (walks n).Nonempty := by
  classical
  refine ⟨fun _ => 0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  intro a b h
  simp only [position_allEast, Prod.mk.injEq] at h
  apply Fin.ext
  exact_mod_cast h.1

theorem endpointNorm_le_distance {n : ℕ} (s : Fin n → Fin 4) :
    (endpointNorm s : ℝ) ≤ endpointDistance s :=
  PlanarSAWTailBound.max_natAbs_le_euclidean (position s (Fin.last n))


theorem expectedDistance_ge_of_counts (n m : ℕ)
    (hcount : ((walks n).filter (fun s => endpointNorm s ≤ m)).card ≤
      ((walks n).filter (fun s => m * (m + 2) ≤ endpointNorm s)).card * (m + 1)) :
    (m : ℝ) ≤ expectedDistance n := by
  classical
  let R : (Fin n → Fin 4) → ℝ := fun s => endpointNorm s
  have hlow : (walks n).filter (fun s => R s ≤ (m : ℝ)) =
      (walks n).filter (fun s => endpointNorm s ≤ m) := by
    ext s
    simp [R]
  have hhigh : (walks n).filter (fun s => (m : ℝ) * ((m : ℝ) + 2) ≤ R s) =
      (walks n).filter (fun s => m * (m + 2) ≤ endpointNorm s) := by
    ext s
    simp only [Finset.mem_filter, R]
    norm_cast
  have hcountReal : (((walks n).filter (fun s => R s ≤ (m : ℝ))).card : ℝ) ≤
      ((m : ℝ) + 1) * (((walks n).filter
        (fun s => (m : ℝ) * ((m : ℝ) + 2) ≤ R s)).card : ℝ) := by
    rw [hlow, hhigh]
    have hcast := (Nat.cast_le (α := ℝ)).mpr hcount
    push_cast at hcast
    nlinarith [hcast]
  have hm := PlanarSAWTailBound.mean_bound (walks n) R (m : ℝ)
    (walks_nonempty n) (Nat.cast_nonneg m)
    (fun s _ => Nat.cast_nonneg (endpointNorm s)) hcountReal
  have hsum : (∑ s ∈ walks n, R s) ≤ (walks n).sum endpointDistance := by
    apply Finset.sum_le_sum
    intro s _
    exact endpointNorm_le_distance s
  exact hm.trans (div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _))

end PlanarSAWDirectionBridge

-- END p289/WalkAverages.lean

-- BEGIN p289/SoftHardCanonical.lean; source SHA-256 be64efec5b43e131e689d2ea94eda2caa31eeddcea850d04be2d146a163774a8

/-!
The actual canonical planar finite walk law with Gibbs collision weights.
The observable and strict expectation are the definitions from WalkAverages.
No count estimate, growing-penalty conclusion, or endpoint lower bound is assumed.
-/

namespace PlanarSAWSoftHardCanonical

open scoped BigOperators
open PlanarSAWDirectionBridge

abbrev Word (n : ℕ) := Fin n → Fin 4

def allWords (n : ℕ) : Finset (Word n) := Finset.univ

theorem position_bridge {n : ℕ} (s : Word n) :
    PlanarSAWRepeatArrival.position s = position s := rfl

theorem selfAvoiding_bridge {n : ℕ} (s : Word n) :
    PlanarSAWRepeatArrival.IsSelfAvoidingWalk s ↔ IsSelfAvoidingWalk s := Iff.rfl

/-- Conventional unordered collision pairs, with i<j and no diagonal terms. -/
def J {n : ℕ} (s : Word n) : ℕ :=
  (PlanarSAWRepeatArrival.timeCollisionPairs s).card

theorem J_eq_unorderedCollisions {n : ℕ} (s : Word n) :
    J s = PlanarSAWRepeatArrival.unorderedCollisions
      (List.ofFn (position s)) :=
  (PlanarSAWRepeatArrival.unorderedCollisions_eq_pair_card s).symm

theorem J_eq_zero_iff {n : ℕ} (s : Word n) :
    J s = 0 ↔ IsSelfAvoidingWalk s := by
  classical
  rw [J, Finset.card_eq_zero]
  constructor
  · intro h i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hm : (i, j) ∈ PlanarSAWRepeatArrival.timeCollisionPairs s :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, hij⟩
      rw [h] at hm
      exact Finset.notMem_empty _ hm
    · have hm : (j, i) ∈ PlanarSAWRepeatArrival.timeCollisionPairs s :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt, hij.symm⟩
      rw [h] at hm
      exact Finset.notMem_empty _ hm
  · intro hs
    apply Finset.eq_empty_of_forall_notMem
    intro ij hij
    have h := (Finset.mem_filter.mp hij).2
    exact (ne_of_lt h.1) (hs h.2)

theorem walks_eq_zero_energy (n : ℕ) :
    walks n = (allWords n).filter (fun s => J s = 0) := by
  classical
  ext s
  simp [walks, allWords, J_eq_zero_iff]

theorem strict_walks_nonempty (n : ℕ) : (walks n).Nonempty :=
  walks_nonempty n

theorem walks_subset_allWords (n : ℕ) : walks n ⊆ allWords n := by
  intro s _
  exact Finset.mem_univ _

noncomputable def badWords (n : ℕ) : Finset (Word n) :=
  (allWords n).filter (fun s => 0 < J s)

theorem badWords_eq_sdiff (n : ℕ) :
    badWords n = allWords n \ walks n := by
  classical
  ext s
  simp [badWords, allWords, walks, Nat.pos_iff_ne_zero, J_eq_zero_iff]

noncomputable def gibbsWeight {n : ℕ} (β : ℝ) (s : Word n) : ℝ :=
  Real.exp (-β * (J s : ℝ))

noncomputable def gibbsPartition (n : ℕ) (β : ℝ) : ℝ :=
  ∑ s ∈ allWords n, gibbsWeight β s

noncomputable def gibbsExpectedDistance (n : ℕ) (β : ℝ) : ℝ :=
  (∑ s ∈ allWords n, gibbsWeight β s * endpointDistance s) /
    gibbsPartition n β

noncomputable def gibbsBadRatio (n : ℕ) (β : ℝ) : ℝ :=
  (∑ s ∈ badWords n, gibbsWeight β s) / ((walks n).card : ℝ)

theorem gibbsWeight_pos {n : ℕ} (β : ℝ) (s : Word n) :
    0 < gibbsWeight β s := Real.exp_pos _

theorem gibbsWeight_eq_one {n : ℕ} (β : ℝ) (s : Word n)
    (hs : s ∈ walks n) : gibbsWeight β s = 1 := by
  classical
  have hj : J s = 0 := (J_eq_zero_iff s).mpr (Finset.mem_filter.mp hs).2
  simp [gibbsWeight, hj]

theorem gibbsPartition_pos (n : ℕ) (β : ℝ) :
    0 < gibbsPartition n β :=
  PlanarSAWSoftHard.sum_weight_pos (allWords n) (walks n) (gibbsWeight β)
    (walks_subset_allWords n) (strict_walks_nonempty n)
    (fun s _ => (gibbsWeight_pos β s).le) (gibbsWeight_eq_one β)

theorem gibbsBadRatio_eq_generic (n : ℕ) (β : ℝ) :
    gibbsBadRatio n β =
      PlanarSAWSoftHard.badRatio (allWords n) (walks n) (gibbsWeight β) := by
  simp only [gibbsBadRatio, badWords_eq_sdiff, PlanarSAWSoftHard.badRatio]

theorem gibbsBadRatio_nonneg (n : ℕ) (β : ℝ) :
    0 ≤ gibbsBadRatio n β := by
  rw [gibbsBadRatio_eq_generic]
  exact PlanarSAWSoftHard.badRatio_nonneg _ _ _
    (fun s _ => (gibbsWeight_pos β s).le)

theorem gibbsPartition_eq (n : ℕ) (β : ℝ) :
    gibbsPartition n β =
      ((walks n).card : ℝ) + ∑ s ∈ badWords n, gibbsWeight β s := by
  rw [badWords_eq_sdiff]
  exact PlanarSAWSoftHard.sum_weight_eq _ _ _
    (walks_subset_allWords n) (gibbsWeight_eq_one β)

theorem gibbs_bad_fraction (n : ℕ) (β : ℝ) :
    (∑ s ∈ badWords n, gibbsWeight β s) / gibbsPartition n β =
      gibbsBadRatio n β / (1 + gibbsBadRatio n β) := by
  rw [badWords_eq_sdiff, gibbsBadRatio_eq_generic]
  exact PlanarSAWSoftHard.bad_fraction_eq _ _ _
    (walks_subset_allWords n) (strict_walks_nonempty n)
    (fun s _ => (gibbsWeight_pos β s).le) (gibbsWeight_eq_one β)

theorem step_l1 (d : Fin 4) :
    |(step d).1| + |(step d).2| = (1 : ℤ) := by
  unfold step
  split_ifs <;> norm_num

/-- The lattice l1 displacement is at most the number of elapsed steps. -/
theorem position_l1_le {n : ℕ} (s : Word n) (t : Fin (n + 1)) :
    |(position s t).1| + |(position s t).2| ≤ (t.val : ℤ) := by
  induction t using Fin.induction with
  | zero => simp [position_zero]
  | succ t ih =>
    rw [position_succ]
    simp only [Prod.fst_add, Prod.snd_add, Fin.val_succ, Nat.cast_add, Nat.cast_one]
    have h₁ := abs_add_le (position s t.castSucc).1 (step (s t)).1
    have h₂ := abs_add_le (position s t.castSucc).2 (step (s t)).2
    have hstep := step_l1 (s t)
    simp only [Fin.val_castSucc] at ih
    linarith

theorem endpointDistance_nonneg {n : ℕ} (s : Word n) :
    0 ≤ endpointDistance s := Real.sqrt_nonneg _

/-- The exact Euclidean observable is bounded by n for every direction word,
including words with collisions. -/
theorem endpointDistance_le {n : ℕ} (s : Word n) :
    endpointDistance s ≤ (n : ℝ) := by
  have hl1 := position_l1_le s (Fin.last n)
  let x : ℝ := ((position s (Fin.last n)).1 : ℝ)
  let y : ℝ := ((position s (Fin.last n)).2 : ℝ)
  have hr : |x| + |y| ≤ (n : ℝ) := by
    dsimp [x, y]
    exact_mod_cast hl1
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hsum : 0 ≤ (n : ℝ) + (|x| + |y|) := by
    linarith [abs_nonneg x, abs_nonneg y]
  apply Real.sqrt_le_iff.mpr
  refine ⟨hn, ?_⟩
  change x ^ 2 + y ^ 2 ≤ (n : ℝ) ^ 2
  nlinarith [sq_abs x, sq_abs y,
    mul_nonneg (abs_nonneg x) (abs_nonneg y),
    mul_nonneg (sub_nonneg.mpr hr) hsum]

/-- Concrete canonical soft-to-strict endpoint comparison.
The theorem holds for all real beta; the repulsive case is beta >= 0. -/
theorem gibbs_endpoint_error (n : ℕ) (β : ℝ) :
    |gibbsExpectedDistance n β - expectedDistance n| ≤
      (n : ℝ) * gibbsBadRatio n β / (1 + gibbsBadRatio n β) := by
  rw [gibbsBadRatio_eq_generic]
  exact PlanarSAWSoftHard.weightedMean_sub_uniformMean_le
    (allWords n) (walks n) (gibbsWeight β) endpointDistance n
    (walks_subset_allWords n) (strict_walks_nonempty n)
    (fun s _ => (gibbsWeight_pos β s).le) (gibbsWeight_eq_one β)
    (fun s _ => ⟨endpointDistance_nonneg s, endpointDistance_le s⟩)

/-- A supplied remainder bound can be used directly for the canonical mean. -/
theorem gibbs_endpoint_error_of_ratio_le (n : ℕ) (β r : ℝ)
    (hr : gibbsBadRatio n β ≤ r) :
    |gibbsExpectedDistance n β - expectedDistance n| ≤ (n : ℝ) * r := by
  rw [gibbsBadRatio_eq_generic] at hr
  exact PlanarSAWSoftHard.weightedMean_sub_uniformMean_le_of_ratio_le
    (allWords n) (walks n) (gibbsWeight β) endpointDistance n r
    (walks_subset_allWords n) (strict_walks_nonempty n)
    (fun s _ => (gibbsWeight_pos β s).le) (gibbsWeight_eq_one β)
    (fun s _ => ⟨endpointDistance_nonneg s, endpointDistance_le s⟩) hr

theorem gibbs_endpoint_error_of_scalar_majorant (n : ℕ) (β a x : ℝ)
    (ha : 1 ≤ a) (hx0 : 0 ≤ x)
    (hx : x ≤ 1 / (a * ((n : ℝ) + 1) ^ 3))
    (hR : gibbsBadRatio n β ≤ a * ((1 + x) ^ n - 1)) :
    |gibbsExpectedDistance n β - expectedDistance n| ≤
      2 * (n : ℝ) ^ 2 / ((n : ℝ) + 1) ^ 3 := by
  rw [gibbsBadRatio_eq_generic] at hR
  exact PlanarSAWSoftHard.weightedMean_sub_uniformMean_le_of_scalar_majorant
    (allWords n) (walks n) (gibbsWeight β) endpointDistance n a x
    (walks_subset_allWords n) (strict_walks_nonempty n)
    (fun s _ => (gibbsWeight_pos β s).le) (gibbsWeight_eq_one β)
    (fun s _ => ⟨endpointDistance_nonneg s, endpointDistance_le s⟩)
    ha hx0 hx hR

end PlanarSAWSoftHardCanonical


-- END p289/SoftHardCanonical.lean

-- BEGIN p289/RepeatArrivalPartition.lean; source SHA-256 8851abe7b2570d0a484e6e7058b803d143958e8adca57f431e0b01c783b65175

/-! Finite partition bounds from the checked repeat-arrival count. No count
asymptotic or endpoint estimate is imported or assumed. -/

namespace PlanarSAWRepeatArrival

def repeatCount {n : ℕ} (s : Fin n → Fin 4) : ℕ :=
  (encode (List.ofFn s)).marks.length

def collisionEnergy {n : ℕ} (s : Fin n → Fin 4) : ℕ := (timeCollisionPairs s).card

theorem repeatCount_le_length {n : ℕ} (s : Fin n → Fin 4) : repeatCount s ≤ n := by
  have h := Encoding.length_decode (encode (List.ofFn s))
  rw [decode_encode, List.length_ofFn] at h
  unfold repeatCount
  omega

theorem repeatCount_le_energy {n : ℕ} (s : Fin n → Fin 4) :
    repeatCount s ≤ collisionEnergy s := by
  rw [collisionEnergy, ← unorderedCollisions_eq_pair_card]
  simpa only [repeatCount, collisionCount, trace_ofFn] using marks_le_collisions (List.ofFn s)

theorem collisionEnergy_eq_zero_iff {n : ℕ} (s : Fin n → Fin 4) :
    collisionEnergy s = 0 ↔ IsSelfAvoidingWalk s := by
  classical
  rw [collisionEnergy, Finset.card_eq_zero]
  constructor
  · intro h i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hm : (i, j) ∈ timeCollisionPairs s :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, hij⟩
      rw [h] at hm
      exact Finset.notMem_empty _ hm
    · have hm : (j, i) ∈ timeCollisionPairs s :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt, hij.symm⟩
      rw [h] at hm
      exact Finset.notMem_empty _ hm
  · intro hs
    apply Finset.eq_empty_of_forall_notMem
    intro ij hij
    have h := (Finset.mem_filter.mp hij).2
    exact (ne_of_lt h.1) (hs h.2)

theorem selfAvoiding_of_repeatCount_zero {n : ℕ} (s : Fin n → Fin 4)
    (h : repeatCount s = 0) : IsSelfAvoidingWalk s := by
  have hps : (encode (List.ofFn s)).separated = [] := by
    simpa [repeatCount, Encoding.marks] using h
  have hb := (good_encode (List.ofFn s)).2
  have hd := decode_encode (List.ofFn s)
  simp only [Encoding.decode, Encoding.prefix, hps, List.flatMap_nil, List.nil_append] at hd
  rw [hd] at hb
  exact (strictBlock_ofFn_iff s).mp hb

theorem repeatCount_pos_of_energy_pos {n : ℕ} (s : Fin n → Fin 4)
    (h : 0 < collisionEnergy s) : 0 < repeatCount s := by
  by_contra hn
  have hz : repeatCount s = 0 := by omega
  have he := (collisionEnergy_eq_zero_iff s).mpr (selfAvoiding_of_repeatCount_zero s hz)
  omega

noncomputable def collisionBadWords (n : ℕ) : Finset (Fin n → Fin 4) := by
  classical
  exact Finset.univ.filter (fun s => 0 < collisionEnergy s)

theorem mem_collisionBadWords {n : ℕ} (s : Fin n → Fin 4) :
    s ∈ collisionBadWords n ↔ ¬ IsSelfAvoidingWalk s := by
  classical
  simp [collisionBadWords, Nat.pos_iff_ne_zero, collisionEnergy_eq_zero_iff]

noncomputable def qBadMass (n : ℕ) (q : ℝ) : ℝ :=
  ∑ s ∈ collisionBadWords n, q ^ collisionEnergy s

noncomputable def qBadRatio (n : ℕ) (q : ℝ) : ℝ :=
  qBadMass n q / (strictWordCount n : ℝ)

theorem compositionWeight_power_bound (m r : ℕ) (lam a : ℝ)
    (hlam : 0 ≤ lam) (ha : 0 ≤ a)
    (hc : ∀ k ≤ m, (strictWordCount k : ℝ) ≤ lam ^ k * a) :
    (compositionWeight m r : ℝ) ≤ ((m + r).choose r : ℝ) * lam ^ m * a ^ (r + 1) := by
  induction r generalizing m with
  | zero => simpa [compositionWeight_zero] using hc m le_rfl
  | succ r ih =>
    rw [compositionWeight_succ]
    push_cast
    have hs : (∑ l ∈ Finset.range (m + 1), ((m - l + r).choose r : ℝ)) =
        ((m + r + 1).choose (r + 1) : ℝ) := by
      exact_mod_cast (Finset.sum_flip (n := m) (fun i => (i + r).choose r)).trans
        (Nat.sum_range_add_choose m r)
    calc
      _ ≤ ∑ l ∈ Finset.range (m + 1),
          ((m - l + r).choose r : ℝ) * lam ^ m * a ^ (r + 2) := by
        apply Finset.sum_le_sum
        intro l hl
        have hlm : l ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hl)
        have hi := ih (m - l) (fun k hk => hc k (by omega))
        have hp : lam ^ l * lam ^ (m - l) = lam ^ m := by
          rw [← pow_add, Nat.add_sub_of_le hlm]
        calc
          _ ≤ (lam ^ l * a) *
              (((m - l + r).choose r : ℝ) * lam ^ (m - l) * a ^ (r + 1)) :=
            mul_le_mul (hc l hlm) hi (Nat.cast_nonneg _) (mul_nonneg (pow_nonneg hlam _) ha)
          _ = ((m - l + r).choose r : ℝ) *
              (lam ^ l * lam ^ (m - l)) * (a * a ^ (r + 1)) := by ring
          _ = _ := by rw [hp, ← pow_succ']
      _ = _ := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, hs]
        rfl

theorem repeatedWordCount_power_bound (n r : ℕ) (lam a : ℝ)
    (hlam : 0 ≤ lam) (ha : 0 ≤ a)
    (hc : ∀ k ≤ n, (strictWordCount k : ℝ) ≤ lam ^ k * a) :
    (repeatedWordCount n r : ℝ) ≤
      4 ^ r * (n.choose r : ℝ) * lam ^ (n - r) * a ^ (r + 1) := by
  by_cases hr : r ≤ n
  · have hcount : (repeatedWordCount n r : ℝ) ≤ 4 ^ r * (compositionWeight (n-r) r : ℝ) := by
      exact_mod_cast repeatArrival_composition_bound n r
    have hcomp := compositionWeight_power_bound (n-r) r lam a hlam ha
      (fun k hk => hc k (by omega))
    rw [Nat.sub_add_cancel hr] at hcomp
    calc
      _ ≤ 4 ^ r * (compositionWeight (n-r) r : ℝ) := hcount
      _ ≤ 4 ^ r * ((n.choose r : ℝ) * lam ^ (n-r) * a ^ (r+1)) :=
        mul_le_mul_of_nonneg_left hcomp (pow_nonneg (by norm_num) _)
      _ = _ := by ring
  · have hz := repeatArrival_count_bound n r
    rw [blockConvolution_zero_of_lt (by omega), Nat.mul_zero] at hz
    have hzero : repeatedWordCount n r = 0 := Nat.eq_zero_of_le_zero hz
    simp [hzero, Nat.choose_eq_zero_of_lt (by omega : n < r)]

theorem qBadMass_le_repeat_sum (n : ℕ) (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    qBadMass n q ≤ ∑ r ∈ (Finset.range (n + 1)).erase 0,
      (repeatedWordCount n r : ℝ) * q ^ r := by
  classical
  have hm : ∀ s ∈ collisionBadWords n,
      repeatCount s ∈ (Finset.range (n + 1)).erase 0 := by
    intro s hs
    have hp := repeatCount_pos_of_energy_pos s (Finset.mem_filter.mp hs).2
    exact Finset.mem_erase.mpr ⟨Nat.ne_of_gt hp,
      Finset.mem_range.mpr (Nat.lt_succ_of_le (repeatCount_le_length s))⟩
  calc
    _ ≤ ∑ s ∈ collisionBadWords n, q ^ repeatCount s := by
      apply Finset.sum_le_sum
      intro s _
      exact pow_le_pow_of_le_one hq hq1 (repeatCount_le_energy s)
    _ = ∑ r ∈ (Finset.range (n + 1)).erase 0,
        ∑ s ∈ (collisionBadWords n).filter (fun s => repeatCount s = r), q ^ repeatCount s :=
      (Finset.sum_fiberwise_of_maps_to hm _).symm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro r _
      have hsub : (collisionBadWords n).filter (fun s => repeatCount s = r) ⊆
          wordsWithRepeats n r := by
        intro s hs
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hs).2⟩
      have hcard : (((collisionBadWords n).filter (fun s => repeatCount s = r)).card : ℝ) ≤
          (repeatedWordCount n r : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      calc
        _ = (((collisionBadWords n).filter (fun s => repeatCount s = r)).card : ℝ) * q ^ r := by
          calc
            _ = ∑ s ∈ (collisionBadWords n).filter (fun s => repeatCount s = r), q ^ r := by
              apply Finset.sum_congr rfl
              intro s hs
              rw [(Finset.mem_filter.mp hs).2]
            _ = _ := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right hcard (pow_nonneg hq _)

theorem positive_binomial_sum (n : ℕ) (x y : ℝ) :
    (∑ r ∈ (Finset.range (n + 1)).erase 0,
      x ^ r * y ^ (n-r) * (n.choose r : ℝ)) = (x+y)^n - y^n := by
  have h := Finset.sum_erase_add (Finset.range (n+1))
    (fun r => x^r * y^(n-r) * (n.choose r : ℝ)) (a := 0) (by simp)
  rw [← add_pow] at h
  simp only [pow_zero, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one,
    one_mul, mul_one] at h
  linarith

theorem qBadMass_binomial_bound (n : ℕ) (q lam a : ℝ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hlam : 0 ≤ lam) (ha : 0 ≤ a)
    (hc : ∀ k ≤ n, (strictWordCount k : ℝ) ≤ lam^k * a) :
    qBadMass n q ≤ a * ((lam + 4*a*q)^n - lam^n) := by
  calc
    _ ≤ ∑ r ∈ (Finset.range (n+1)).erase 0, (repeatedWordCount n r : ℝ) * q^r :=
      qBadMass_le_repeat_sum n q hq hq1
    _ ≤ ∑ r ∈ (Finset.range (n+1)).erase 0,
        (4^r * (n.choose r : ℝ) * lam^(n-r) * a^(r+1)) * q^r := by
      apply Finset.sum_le_sum
      intro r _
      exact mul_le_mul_of_nonneg_right
        (repeatedWordCount_power_bound n r lam a hlam ha hc) (pow_nonneg hq _)
    _ = a * ∑ r ∈ (Finset.range (n+1)).erase 0,
        (4*a*q)^r * lam^(n-r) * (n.choose r : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      simp only [mul_pow, pow_succ]
      ring
    _ = _ := by rw [positive_binomial_sum]; congr 2; ring

/-- The finite algebraic comparison; the exact denominator identity and all
shorter-length count hypotheses are explicit, including k=0 and n=0. -/
theorem qBadRatio_binomial_bound (n : ℕ) (q lam a : ℝ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hlam : 0 < lam) (ha : 1 ≤ a)
    (hc : ∀ k ≤ n, (strictWordCount k : ℝ) ≤ lam^k * a)
    (hcn : (strictWordCount n : ℝ) = lam^n) :
    qBadRatio n q ≤ a * ((1 + (4/lam)*a*q)^n - 1) := by
  rw [qBadRatio, hcn]
  apply (div_le_iff₀ (pow_pos hlam n)).mpr
  have hbase : lam + 4*a*q = lam * (1 + (4/lam)*a*q) := by
    field_simp
  calc
    _ ≤ a * ((lam + 4*a*q)^n - lam^n) :=
      qBadMass_binomial_bound n q lam a hq hq1 hlam.le (le_trans (by norm_num) ha) hc
    _ = _ := by rw [hbase, mul_pow]; ring

/-- Exact energy, rather than repeat count, is used in the exponential weight. -/
theorem repeatArrival_exp_badRatio_bound (n : ℕ) (beta lam a : ℝ)
    (hbeta : 0 ≤ beta) (hlam : 0 < lam) (ha : 1 ≤ a)
    (hc : ∀ k ≤ n, (strictWordCount k : ℝ) ≤ lam^k * a)
    (hcn : (strictWordCount n : ℝ) = lam^n) :
    (∑ s ∈ collisionBadWords n,
      Real.exp (-beta * ((timeCollisionPairs s).card : ℝ))) / (strictWordCount n : ℝ)
      ≤ a * ((1 + (4/lam)*a*Real.exp (-beta))^n - 1) := by
  have h := qBadRatio_binomial_bound n (Real.exp (-beta)) lam a
    (Real.exp_nonneg _) ((Real.exp_le_one_iff).mpr (by linarith)) hlam ha hc hcn
  convert h using 1
  unfold qBadRatio qBadMass
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  rw [← Real.exp_nat_mul]
  unfold collisionEnergy
  congr 1
  ring


end PlanarSAWRepeatArrival

-- END p289/RepeatArrivalPartition.lean

-- BEGIN p289/SoftHardCombined.lean; source SHA-256 3a7b4add1147058f9958429cdda4843dcc4c61dece36e0a2941e3ca54f37a1df

/-!
The finite repeat-arrival partition estimate applied to the exact canonical
Euclidean endpoint mean. All count caps remain explicit finite hypotheses.
-/

namespace PlanarSAWSoftHardCanonical

open PlanarSAWDirectionBridge

theorem strictWordCount_eq_card_walks (n : ℕ) :
    PlanarSAWRepeatArrival.strictWordCount n = (walks n).card := rfl

theorem collisionBadWords_eq_badWords (n : ℕ) :
    PlanarSAWRepeatArrival.collisionBadWords n = badWords n := rfl

theorem gibbsBadRatio_le_binomial (n : ℕ) (β lam a : ℝ)
    (hβ : 0 ≤ β) (hlam : 0 < lam) (ha : 1 ≤ a)
    (hc : ∀ k ≤ n, ((walks k).card : ℝ) ≤ lam ^ k * a)
    (hcn : ((walks n).card : ℝ) = lam ^ n) :
    gibbsBadRatio n β ≤ a * ((1 + (4 / lam) * a * Real.exp (-β)) ^ n - 1) :=
  PlanarSAWRepeatArrival.repeatArrival_exp_badRatio_bound n β lam a
    hβ hlam ha hc hcn

/-- Finite canonical endpoint transfer, including n=0. No count asymptotic
or weak-law endpoint lower bound is assumed by the conclusion. -/
theorem gibbs_endpoint_error_of_finite_count_caps (n : ℕ) (β lam a : ℝ)
    (hβ : 0 ≤ β) (hlam : 2 ≤ lam) (ha : 1 ≤ a)
    (hc : ∀ k ≤ n, ((walks k).card : ℝ) ≤ lam ^ k * a)
    (hcn : ((walks n).card : ℝ) = lam ^ n)
    (hq : Real.exp (-β) ≤ 1 / (2 * a ^ 2 * ((n : ℝ) + 1) ^ 3)) :
    |gibbsExpectedDistance n β - expectedDistance n| ≤
      2 * (n : ℝ) ^ 2 / ((n : ℝ) + 1) ^ 3 := by
  have hlam0 : 0 < lam := by linarith
  have ha0 : 0 < a := by linarith
  have hn0 : 0 < (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hcoef : 4 / lam ≤ (2 : ℝ) := (div_le_iff₀ hlam0).mpr (by linarith)
  have hx0 : 0 ≤ (4 / lam) * a * Real.exp (-β) :=
    mul_nonneg (mul_nonneg (div_nonneg (by norm_num) hlam0.le) ha0.le)
      (Real.exp_nonneg _)
  have hx : (4 / lam) * a * Real.exp (-β) ≤
      1 / (a * ((n : ℝ) + 1) ^ 3) := by
    calc
      _ ≤ 2 * a * Real.exp (-β) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef ha0.le)
          (Real.exp_nonneg _)
      _ ≤ 2 * a * (1 / (2 * a ^ 2 * ((n : ℝ) + 1) ^ 3)) :=
        mul_le_mul_of_nonneg_left hq (mul_nonneg (by norm_num) ha0.le)
      _ = _ := by field_simp [ha0.ne', hn0.ne']
  exact gibbs_endpoint_error_of_scalar_majorant n β a
    ((4 / lam) * a * Real.exp (-β)) ha hx0 hx
    (gibbsBadRatio_le_binomial n β lam a hβ hlam0 ha hc hcn)

noncomputable def finiteCountPenalty (n : ℕ) (a : ℝ) : ℝ :=
  2 * Real.log a + 3 * Real.log ((n : ℝ) + 1) + Real.log 2

theorem finiteCountPenalty_nonneg (n : ℕ) (a : ℝ) (ha : 1 ≤ a) :
    0 ≤ finiteCountPenalty n a := by
  have hn : 1 ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  dsimp [finiteCountPenalty]
  linarith [Real.log_nonneg ha, Real.log_nonneg hn,
    Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)]

theorem exp_neg_finiteCountPenalty (n : ℕ) (a : ℝ) (ha : 1 ≤ a) :
    Real.exp (-finiteCountPenalty n a) =
      1 / (2 * a ^ 2 * ((n : ℝ) + 1) ^ 3) := by
  have ha0 : 0 < a := by linarith
  have hn0 : 0 < (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have h₂ : Real.exp (2 * Real.log a) = a ^ 2 := by
    simpa only [Nat.cast_ofNat, Real.exp_log ha0] using Real.exp_nat_mul (Real.log a) 2
  have h₃ : Real.exp (3 * Real.log ((n : ℝ) + 1)) = ((n : ℝ) + 1) ^ 3 := by
    simpa only [Nat.cast_ofNat, Real.exp_log hn0] using
      Real.exp_nat_mul (Real.log ((n : ℝ) + 1)) 3
  rw [Real.exp_neg, finiteCountPenalty, Real.exp_add, Real.exp_add, h₂, h₃,
    Real.exp_log (show (0 : ℝ) < 2 by norm_num), one_div]
  congr 1
  ring

/-- The explicit nonnegative logarithmic penalty meets the finite smallness
condition exactly. The shorter-length caps and c_n=lam^n are still hypotheses. -/
theorem gibbs_endpoint_error_at_finiteCountPenalty (n : ℕ) (lam a : ℝ)
    (hlam : 2 ≤ lam) (ha : 1 ≤ a)
    (hc : ∀ k ≤ n, ((walks k).card : ℝ) ≤ lam ^ k * a)
    (hcn : ((walks n).card : ℝ) = lam ^ n) :
    |gibbsExpectedDistance n (finiteCountPenalty n a) - expectedDistance n| ≤
      2 * (n : ℝ) ^ 2 / ((n : ℝ) + 1) ^ 3 :=
  gibbs_endpoint_error_of_finite_count_caps n (finiteCountPenalty n a) lam a
    (finiteCountPenalty_nonneg n a ha) hlam ha hc hcn
    (exp_neg_finiteCountPenalty n a ha).le

end PlanarSAWSoftHardCanonical


-- END p289/SoftHardCombined.lean

/-- Finite endpoint comparison at the explicit penalty, retaining every count cap. -/
theorem proof (n : ℕ) (lam a : ℝ)
    (hlam : 2 ≤ lam) (ha : 1 ≤ a)
    (hc : ∀ k ≤ n, ((PlanarSAWDirectionBridge.walks k).card : ℝ) ≤ lam ^ k * a)
    (hcn : ((PlanarSAWDirectionBridge.walks n).card : ℝ) = lam ^ n) :
    |PlanarSAWSoftHardCanonical.gibbsExpectedDistance n
        (PlanarSAWSoftHardCanonical.finiteCountPenalty n a) -
      PlanarSAWDirectionBridge.expectedDistance n| ≤
      2 * (n : ℝ) ^ 2 / ((n : ℝ) + 1) ^ 3 :=
  PlanarSAWSoftHardCanonical.gibbs_endpoint_error_at_finiteCountPenalty
    n lam a hlam ha hc hcn

end Submissions.Erdos529FiniteRepulsionTransfer.Main
