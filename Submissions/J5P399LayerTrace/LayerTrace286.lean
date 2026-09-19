/- Exact abstract layer-transfer theorem for the51 classified signatures.
   No graph extraction or series-parallel representation theorem is asserted here. -/
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace Submissions.J5P399LayerTrace.LayerTrace286.Kernel

structure Profile where
  entering : List Nat
  leaving : List Nat
  linkage : List Nat
  deriving DecidableEq
structure Cell where
  mask : Nat
  rank : Nat
  deriving DecidableEq

def profile0 : Profile := ⟨[1], [1], [0]⟩
def profile1 : Profile := ⟨[2, 3], [2, 3], [1, 2]⟩
def profile2 : Profile := ⟨[4, 5, 6, 7], [3, 4, 5, 6, 7], [2, 3, 4, 5, 6]⟩
def profile3 : Profile := ⟨[3, 4, 5, 6, 7], [3, 4, 5, 6, 7], [3, 4, 5, 6]⟩
def profile4 : Profile := ⟨[3, 4, 5, 6, 7], [4, 5, 6, 7], [2, 3, 4, 5, 6]⟩
def profile5 : Profile := ⟨[2, 3, 4], [2, 3, 4], [2, 3]⟩
def profile6 : Profile := ⟨[3, 4, 5], [3, 4, 5], [2, 3, 4]⟩
def profile7 : Profile := ⟨[4, 5, 6, 7, 8], [3, 4, 5, 6, 7, 8], [3, 4, 5, 6, 7]⟩
def profile8 : Profile := ⟨[5, 6, 7, 8, 9], [4, 5, 6, 7, 8, 9], [3, 4, 5, 6, 7, 8]⟩
def profile9 : Profile := ⟨[3, 4, 5, 6, 7, 8], [3, 4, 5, 6, 7, 8], [4, 5, 6, 7]⟩
def profile10 : Profile := ⟨[4, 5, 6, 7, 8, 9], [4, 5, 6, 7, 8, 9], [4, 5, 6, 7, 8]⟩
def profile11 : Profile := ⟨[3, 4, 5, 6, 7, 8], [4, 5, 6, 7, 8], [3, 4, 5, 6, 7]⟩
def profile12 : Profile := ⟨[4, 5, 6, 7, 8, 9], [5, 6, 7, 8, 9], [3, 4, 5, 6, 7, 8]⟩
def profile13 : Profile := ⟨[6, 7, 8, 9, 10, 11, 12], [4, 5, 6, 7, 8, 9, 10, 11, 12], [4, 5, 6, 7, 8, 9, 10, 11]⟩
def profile14 : Profile := ⟨[7, 8, 9, 10, 11, 12, 13], [5, 6, 7, 8, 9, 10, 11, 12, 13], [4, 5, 6, 7, 8, 9, 10, 11, 12]⟩
def profile15 : Profile := ⟨[5, 6, 7, 8, 9, 10, 11, 12], [4, 5, 6, 7, 8, 9, 10, 11, 12], [5, 6, 7, 8, 9, 10, 11]⟩
def profile16 : Profile := ⟨[6, 7, 8, 9, 10, 11, 12, 13], [5, 6, 7, 8, 9, 10, 11, 12, 13], [5, 6, 7, 8, 9, 10, 11, 12]⟩
def profile17 : Profile := ⟨[5, 6, 7, 8, 9, 10, 11, 12], [5, 6, 7, 8, 9, 10, 11, 12], [4, 5, 6, 7, 8, 9, 10, 11]⟩
def profile18 : Profile := ⟨[6, 7, 8, 9, 10, 11, 12, 13], [6, 7, 8, 9, 10, 11, 12, 13], [4, 5, 6, 7, 8, 9, 10, 11, 12]⟩
def profile19 : Profile := ⟨[4, 5, 6, 7, 8, 9, 10, 11, 12], [4, 5, 6, 7, 8, 9, 10, 11, 12], [6, 7, 8, 9, 10, 11]⟩
def profile20 : Profile := ⟨[5, 6, 7, 8, 9, 10, 11, 12, 13], [5, 6, 7, 8, 9, 10, 11, 12, 13], [6, 7, 8, 9, 10, 11, 12]⟩
def profile21 : Profile := ⟨[4, 5, 6, 7, 8, 9, 10, 11, 12], [5, 6, 7, 8, 9, 10, 11, 12], [5, 6, 7, 8, 9, 10, 11]⟩
def profile22 : Profile := ⟨[5, 6, 7, 8, 9, 10, 11, 12, 13], [6, 7, 8, 9, 10, 11, 12, 13], [5, 6, 7, 8, 9, 10, 11, 12]⟩
def profile23 : Profile := ⟨[4, 5, 6, 7, 8, 9, 10, 11, 12], [6, 7, 8, 9, 10, 11, 12], [4, 5, 6, 7, 8, 9, 10, 11]⟩
def profile24 : Profile := ⟨[5, 6, 7, 8, 9, 10, 11, 12, 13], [7, 8, 9, 10, 11, 12, 13], [4, 5, 6, 7, 8, 9, 10, 11, 12]⟩
def profile25 : Profile := ⟨[2, 3, 4, 5], [1, 4, 5], [3, 4]⟩
def profile26 : Profile := ⟨[3, 4], [2, 3, 4], [3, 4]⟩
def profile27 : Profile := ⟨[1, 4, 5], [2, 3, 4, 5], [3, 4]⟩
def profile28 : Profile := ⟨[2, 3, 4], [3, 4], [3, 4]⟩
def profile29 : Profile := ⟨[2, 3, 5, 6, 7], [3, 4, 5, 6, 7], [4, 5, 6]⟩
def profile30 : Profile := ⟨[3, 4, 6, 7], [1, 4, 5, 6], [5, 6]⟩
def profile31 : Profile := ⟨[1, 4, 5, 6], [3, 4, 6, 7], [5, 6]⟩
def profile32 : Profile := ⟨[3, 4, 5, 6, 7], [2, 3, 5, 6, 7], [4, 5, 6]⟩
def profile33 : Profile := ⟨[2, 3, 4, 5, 6], [2, 3, 4, 5, 6], [3, 4, 5]⟩
def profile34 : Profile := ⟨[3, 4, 5], [3, 4, 5], [3, 4, 5]⟩
def profile35 : Profile := ⟨[2, 3, 4, 5, 6], [1, 4, 5, 6], [4, 5]⟩
def profile36 : Profile := ⟨[1, 4, 5, 6], [2, 3, 4, 5, 6], [4, 5]⟩
def profile37 : Profile := ⟨[2, 3, 4, 5, 6, 8, 9, 10], [2, 3, 4, 5, 6, 8, 9, 10], [7, 8, 9]⟩
def profile38 : Profile := ⟨[4, 5, 6, 7, 8, 9, 10], [4, 5, 6, 7, 8, 9, 10], [4, 5, 6, 7, 8, 9]⟩
def profile39 : Profile := ⟨[4, 5, 6, 7, 8, 9, 10], [3, 4, 5, 6, 7, 8], [4, 5, 6, 7, 8, 9]⟩
def profile40 : Profile := ⟨[3, 4, 5, 6, 7, 8], [4, 5, 6, 7, 8, 9, 10], [4, 5, 6, 7, 8, 9]⟩
def profile41 : Profile := ⟨[5, 6, 7, 8, 9, 10], [3, 4, 5, 6, 7, 8, 9, 10], [4, 5, 6, 7, 8, 9]⟩
def profile42 : Profile := ⟨[3, 4, 5, 6, 7, 8, 9, 10], [4, 5, 6, 7, 8, 9], [4, 5, 6, 7, 8, 9]⟩
def profile43 : Profile := ⟨[4, 5, 6, 7, 8, 9], [3, 4, 5, 6, 7, 8, 9, 10], [4, 5, 6, 7, 8, 9]⟩
def profile44 : Profile := ⟨[3, 4, 5, 6, 7, 8, 9, 10], [5, 6, 7, 8, 9, 10], [4, 5, 6, 7, 8, 9]⟩
def profile45 : Profile := ⟨[5, 6, 7, 8, 9], [2, 5, 6, 7, 8, 9, 10], [4, 5, 6, 7, 8, 9]⟩
def profile46 : Profile := ⟨[2, 5, 6, 7, 8, 9, 10], [5, 6, 7, 8, 9], [4, 5, 6, 7, 8, 9]⟩
def profile47 : Profile := ⟨[3, 4, 5, 6, 7, 8], [2, 3, 4, 5, 6, 7, 8], [4, 5, 6, 7]⟩
def profile48 : Profile := ⟨[3, 4, 5, 6, 7, 8], [1, 4, 5, 6], [5, 6, 7]⟩
def profile49 : Profile := ⟨[1, 4, 5, 6], [3, 4, 5, 6, 7, 8], [5, 6, 7]⟩
def profile50 : Profile := ⟨[2, 3, 4, 5, 6, 7, 8], [3, 4, 5, 6, 7, 8], [4, 5, 6, 7]⟩
def profiles : List Profile := [profile0, profile1, profile2, profile3, profile4, profile5, profile6, profile7, profile8, profile9, profile10, profile11, profile12, profile13, profile14, profile15, profile16, profile17, profile18, profile19, profile20, profile21, profile22, profile23, profile24, profile25, profile26, profile27, profile28, profile29, profile30, profile31, profile32, profile33, profile34, profile35, profile36, profile37, profile38, profile39, profile40, profile41, profile42, profile43, profile44, profile45, profile46, profile47, profile48, profile49, profile50]
def closedCells : List Cell := [⟨1, 0⟩, ⟨6, 1⟩, ⟨120, 1⟩, ⟨32736, 1⟩, ⟨124, 2⟩, ⟨248, 1⟩, ⟨32760, 2⟩]
def openBlock0 : List Cell := [⟨0, 0⟩, ⟨2, 1⟩, ⟨12, 1⟩, ⟨248, 1⟩, ⟨240, 1⟩, ⟨28, 1⟩, ⟨56, 1⟩, ⟨504, 1⟩, ⟨1008, 1⟩, ⟨496, 1⟩, ⟨992, 1⟩]
def openBlock1 : List Cell := [⟨8176, 1⟩, ⟨16352, 1⟩, ⟨8160, 1⟩, ⟨16320, 1⟩, ⟨8128, 1⟩, ⟨16256, 1⟩, ⟨50, 2⟩, ⟨60, 2⟩, ⟨24, 1⟩, ⟨114, 2⟩, ⟨216, 2⟩]
def openBlock2 : List Cell := [⟨236, 1⟩, ⟨124, 2⟩, ⟨1916, 1⟩, ⟨2032, 1⟩, ⟨2040, 1⟩, ⟨2016, 1⟩, ⟨2020, 1⟩, ⟨508, 1⟩, ⟨32752, 2⟩, ⟨220, 2⟩, ⟨882, 3⟩]
def openBlock3 : List Cell := [⟨16368, 2⟩, ⟨32760, 2⟩, ⟨32740, 2⟩, ⟨32736, 2⟩, ⟨16184, 2⟩, ⟨15900, 2⟩, ⟨32312, 2⟩, ⟨65508, 2⟩, ⟨16376, 2⟩, ⟨65052, 2⟩, ⟨32568, 2⟩]
def openBlock4 : List Cell := [⟨32284, 2⟩, ⟨65080, 2⟩, ⟨16140, 2⟩, ⟨64540, 2⟩, ⟨64536, 2⟩, ⟨32514, 2⟩, ⟨3804, 3⟩, ⟨15218, 4⟩, ⟨98, 2⟩, ⟨8184, 2⟩, ⟨1852, 3⟩]
def openBlock5 : List Cell := [⟨7384, 3⟩, ⟨3708, 3⟩, ⟨65528, 2⟩, ⟨15864, 2⟩, ⟨7900, 3⟩, ⟨31602, 4⟩, ⟨866, 3⟩, ⟨16188, 4⟩, ⟨64728, 4⟩, ⟨32380, 4⟩, ⟨130552, 3⟩]
def openBlock6 : List Cell := [⟨32524, 2⟩, ⟨32620, 2⟩, ⟨65244, 4⟩, ⟨67108848, 3⟩, ⟨134217700, 3⟩, ⟨7388, 3⟩, ⟨29554, 4⟩, ⟨29538, 4⟩, ⟨64732, 4⟩, ⟨2031324, 5⟩, ⟨2030812, 5⟩]
def openCells : List Cell := openBlock0 ++ openBlock1 ++ openBlock2 ++ openBlock3 ++ openBlock4 ++ openBlock5 ++ openBlock6

def bits (xs : List Nat) : Nat := xs.foldl (fun m k => m ||| (1 <<< k)) 0
def hit (m : Nat) (p : Profile) : Bool :=
  p.entering.any (fun a => [4,8,16].any (fun d =>
    decide (a+2 ≤ d) && m.testBit (d-(a+2))))
def advance (m : Nat) (p : Profile) : Nat :=
  (p.linkage.foldl (fun z t => z ||| (m <<< (t+2))) (bits p.leaving)) &&& 2147483647
def cap (m : Nat) : Bool := m.testBit 2 || m.testBit 6 || m.testBit 14

def findCell : List Cell → Nat → Option Cell
  | [], _ => none
  | c::cs, m => if c.mask = m then some c else findCell cs m
theorem findCell_sound (cs : List Cell) : ∀ m c,
    findCell cs m = some c → c ∈ cs ∧ c.mask = m := by
  induction cs with
  | nil => intro m c h; simp [findCell] at h
  | cons a cs ih =>
    intro m c h
    by_cases ha : a.mask = m
    · simp only [findCell, ha, if_pos] at h
      cases h
      exact ⟨by simp, ha⟩
    · have hc := ih m c (by simpa [findCell, ha] using h)
      exact ⟨by simp [hc.1], hc.2⟩
def checked (cs : List Cell) (m k : Nat) : Bool :=
  match findCell cs m with
  | none => false
  | some c => decide (k ≤ c.rank)
def pairCheck (cs : List Cell) (c : Cell) (p : Profile) : Bool :=
  if hit c.mask p then true else checked cs (advance c.mask p) (c.rank+1)
def rowCheck (cs : List Cell) (limit : Nat) (c : Cell) : Bool :=
  decide (c.rank ≤ limit) && profiles.all (pairCheck cs c)

theorem counts : profiles.length = 51 ∧ openCells.length = 77 ∧ closedCells.length = 7 := by decide +kernel
theorem closed_certificate : closedCells.all (rowCheck closedCells 2) = true := by decide +kernel
theorem open_block0 : openBlock0.all (rowCheck openCells 5) = true := by decide +kernel
theorem open_block1 : openBlock1.all (rowCheck openCells 5) = true := by decide +kernel
theorem open_block2 : openBlock2.all (rowCheck openCells 5) = true := by decide +kernel
theorem open_block3 : openBlock3.all (rowCheck openCells 5) = true := by decide +kernel
theorem open_block4 : openBlock4.all (rowCheck openCells 5) = true := by decide +kernel
theorem open_block5 : openBlock5.all (rowCheck openCells 5) = true := by decide +kernel
theorem open_block6 : openBlock6.all (rowCheck openCells 5) = true := by decide +kernel
theorem open_certificate : openCells.all (rowCheck openCells 5) = true := by
  simp only [openCells, List.all_append, open_block0, open_block1, open_block2, open_block3, open_block4, open_block5, open_block6]
  rfl
theorem open_base : checked openCells 0 0 = true := by decide +kernel
theorem closed_base : checked closedCells 1 0 = true := by decide +kernel
theorem cap_certificate : closedCells.all (fun c => if cap c.mask then true else decide (c.rank=0)) = true := by decide +kernel

theorem checked_sound {cs : List Cell} {m k : Nat} (h : checked cs m k = true) :
    ∃ c, c ∈ cs ∧ c.mask = m ∧ k ≤ c.rank := by
  unfold checked at h
  cases he : findCell cs m with
  | none => simp [he] at h
  | some c =>
    have hc := findCell_sound cs m c he
    have hk : k ≤ c.rank := of_decide_eq_true (by simpa [he] using h)
    exact ⟨c, hc.1, hc.2, hk⟩

inductive Avoiding (initial : Nat) : Nat → Nat → Prop where
  | base : Avoiding initial initial 0
  | step {m n : Nat} {p : Profile} : Avoiding initial m n → p ∈ profiles →
      hit m p = false → Avoiding initial (advance m p) (n+1)

theorem avoiding_certificate {cs : List Cell} {limit initial m n : Nat}
    (cert : cs.all (rowCheck cs limit) = true)
    (base : checked cs initial 0 = true)
    (h : Avoiding initial m n) :
    ∃ c, c ∈ cs ∧ c.mask = m ∧ n ≤ c.rank := by
  induction h with
  | base => exact checked_sound base
  | @step m n p _ hp free ih =>
    obtain ⟨c, hc, rfl, hn⟩ := ih
    have row := (List.all_eq_true.mp cert) c hc
    have allpairs := (Bool.and_eq_true_iff.mp row).2
    have pair := (List.all_eq_true.mp allpairs) p hp
    have next : checked cs (advance c.mask p) (c.rank+1) = true := by
      simpa [pairCheck, free] using pair
    obtain ⟨d, hd, hm, hinc⟩ := checked_sound next
    exact ⟨d, hd, hm, Nat.le_trans (Nat.add_le_add_right hn 1) hinc⟩

theorem length_bound {cs : List Cell} {limit initial m n : Nat}
    (cert : cs.all (rowCheck cs limit) = true)
    (base : checked cs initial 0 = true)
    (h : Avoiding initial m n) : n ≤ limit := by
  obtain ⟨c, hc, _, hn⟩ := avoiding_certificate cert base h
  have row := (List.all_eq_true.mp cert) c hc
  have hb : c.rank ≤ limit := of_decide_eq_true (Bool.and_eq_true_iff.mp row).1
  exact Nat.le_trans hn hb

theorem open_length_bound {m n : Nat} (h : Avoiding 0 m n) : n ≤ 5 :=
  length_bound open_certificate open_base h
theorem terminal_length_bound {m n : Nat} (h : Avoiding 1 m n) : n ≤ 2 :=
  length_bound closed_certificate closed_base h
theorem six_open_impossible (m : Nat) : ¬ Avoiding 0 m 6 := by
  intro h
  exact (by decide : ¬ (6 ≤ 5)) (open_length_bound h)
theorem three_terminal_impossible (m : Nat) : ¬ Avoiding 1 m 3 := by
  intro h
  exact (by decide : ¬ (3 ≤ 2)) (terminal_length_bound h)
theorem capped_nonempty_impossible {m n : Nat} (h : Avoiding 1 m n)
    (free : cap m = false) : n = 0 := by
  obtain ⟨c, hc, rfl, hn⟩ := avoiding_certificate closed_certificate closed_base h
  have row := (List.all_eq_true.mp cap_certificate) c hc
  have hz : c.rank = 0 := of_decide_eq_true (by simpa [free] using row)
  exact Nat.eq_zero_of_le_zero (by simpa [hz] using hn)

theorem five_open_witness : Avoiding 0 2031324 5 := (Avoiding.step (p := profile26) (Avoiding.step (p := profile0) (Avoiding.step (p := profile26) (Avoiding.step (p := profile0) (Avoiding.step (p := profile28) Avoiding.base (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel))
theorem two_terminal_witness : Avoiding 1 124 2 := (Avoiding.step (p := profile1) (Avoiding.step (p := profile0) Avoiding.base (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel))

end Submissions.J5P399LayerTrace.LayerTrace286.Kernel

namespace Submissions.J5P399LayerTrace.LayerTrace286
namespace Semantics
def data : Nat → List Nat × List Nat × List Nat
  | 0 => ([1], [1], [0])
  | 1 => ([2, 3], [2, 3], [1, 2])
  | 2 => ([4, 5, 6, 7], [3, 4, 5, 6, 7], [2, 3, 4, 5, 6])
  | 3 => ([3, 4, 5, 6, 7], [3, 4, 5, 6, 7], [3, 4, 5, 6])
  | 4 => ([3, 4, 5, 6, 7], [4, 5, 6, 7], [2, 3, 4, 5, 6])
  | 5 => ([2, 3, 4], [2, 3, 4], [2, 3])
  | 6 => ([3, 4, 5], [3, 4, 5], [2, 3, 4])
  | 7 => ([4, 5, 6, 7, 8], [3, 4, 5, 6, 7, 8], [3, 4, 5, 6, 7])
  | 8 => ([5, 6, 7, 8, 9], [4, 5, 6, 7, 8, 9], [3, 4, 5, 6, 7, 8])
  | 9 => ([3, 4, 5, 6, 7, 8], [3, 4, 5, 6, 7, 8], [4, 5, 6, 7])
  | 10 => ([4, 5, 6, 7, 8, 9], [4, 5, 6, 7, 8, 9], [4, 5, 6, 7, 8])
  | 11 => ([3, 4, 5, 6, 7, 8], [4, 5, 6, 7, 8], [3, 4, 5, 6, 7])
  | 12 => ([4, 5, 6, 7, 8, 9], [5, 6, 7, 8, 9], [3, 4, 5, 6, 7, 8])
  | 13 => ([6, 7, 8, 9, 10, 11, 12], [4, 5, 6, 7, 8, 9, 10, 11, 12], [4, 5, 6, 7, 8, 9, 10, 11])
  | 14 => ([7, 8, 9, 10, 11, 12, 13], [5, 6, 7, 8, 9, 10, 11, 12, 13], [4, 5, 6, 7, 8, 9, 10, 11, 12])
  | 15 => ([5, 6, 7, 8, 9, 10, 11, 12], [4, 5, 6, 7, 8, 9, 10, 11, 12], [5, 6, 7, 8, 9, 10, 11])
  | 16 => ([6, 7, 8, 9, 10, 11, 12, 13], [5, 6, 7, 8, 9, 10, 11, 12, 13], [5, 6, 7, 8, 9, 10, 11, 12])
  | 17 => ([5, 6, 7, 8, 9, 10, 11, 12], [5, 6, 7, 8, 9, 10, 11, 12], [4, 5, 6, 7, 8, 9, 10, 11])
  | 18 => ([6, 7, 8, 9, 10, 11, 12, 13], [6, 7, 8, 9, 10, 11, 12, 13], [4, 5, 6, 7, 8, 9, 10, 11, 12])
  | 19 => ([4, 5, 6, 7, 8, 9, 10, 11, 12], [4, 5, 6, 7, 8, 9, 10, 11, 12], [6, 7, 8, 9, 10, 11])
  | 20 => ([5, 6, 7, 8, 9, 10, 11, 12, 13], [5, 6, 7, 8, 9, 10, 11, 12, 13], [6, 7, 8, 9, 10, 11, 12])
  | 21 => ([4, 5, 6, 7, 8, 9, 10, 11, 12], [5, 6, 7, 8, 9, 10, 11, 12], [5, 6, 7, 8, 9, 10, 11])
  | 22 => ([5, 6, 7, 8, 9, 10, 11, 12, 13], [6, 7, 8, 9, 10, 11, 12, 13], [5, 6, 7, 8, 9, 10, 11, 12])
  | 23 => ([4, 5, 6, 7, 8, 9, 10, 11, 12], [6, 7, 8, 9, 10, 11, 12], [4, 5, 6, 7, 8, 9, 10, 11])
  | 24 => ([5, 6, 7, 8, 9, 10, 11, 12, 13], [7, 8, 9, 10, 11, 12, 13], [4, 5, 6, 7, 8, 9, 10, 11, 12])
  | 25 => ([2, 3, 4, 5], [1, 4, 5], [3, 4])
  | 26 => ([3, 4], [2, 3, 4], [3, 4])
  | 27 => ([1, 4, 5], [2, 3, 4, 5], [3, 4])
  | 28 => ([2, 3, 4], [3, 4], [3, 4])
  | 29 => ([2, 3, 5, 6, 7], [3, 4, 5, 6, 7], [4, 5, 6])
  | 30 => ([3, 4, 6, 7], [1, 4, 5, 6], [5, 6])
  | 31 => ([1, 4, 5, 6], [3, 4, 6, 7], [5, 6])
  | 32 => ([3, 4, 5, 6, 7], [2, 3, 5, 6, 7], [4, 5, 6])
  | 33 => ([2, 3, 4, 5, 6], [2, 3, 4, 5, 6], [3, 4, 5])
  | 34 => ([3, 4, 5], [3, 4, 5], [3, 4, 5])
  | 35 => ([2, 3, 4, 5, 6], [1, 4, 5, 6], [4, 5])
  | 36 => ([1, 4, 5, 6], [2, 3, 4, 5, 6], [4, 5])
  | 37 => ([2, 3, 4, 5, 6, 8, 9, 10], [2, 3, 4, 5, 6, 8, 9, 10], [7, 8, 9])
  | 38 => ([4, 5, 6, 7, 8, 9, 10], [4, 5, 6, 7, 8, 9, 10], [4, 5, 6, 7, 8, 9])
  | 39 => ([4, 5, 6, 7, 8, 9, 10], [3, 4, 5, 6, 7, 8], [4, 5, 6, 7, 8, 9])
  | 40 => ([3, 4, 5, 6, 7, 8], [4, 5, 6, 7, 8, 9, 10], [4, 5, 6, 7, 8, 9])
  | 41 => ([5, 6, 7, 8, 9, 10], [3, 4, 5, 6, 7, 8, 9, 10], [4, 5, 6, 7, 8, 9])
  | 42 => ([3, 4, 5, 6, 7, 8, 9, 10], [4, 5, 6, 7, 8, 9], [4, 5, 6, 7, 8, 9])
  | 43 => ([4, 5, 6, 7, 8, 9], [3, 4, 5, 6, 7, 8, 9, 10], [4, 5, 6, 7, 8, 9])
  | 44 => ([3, 4, 5, 6, 7, 8, 9, 10], [5, 6, 7, 8, 9, 10], [4, 5, 6, 7, 8, 9])
  | 45 => ([5, 6, 7, 8, 9], [2, 5, 6, 7, 8, 9, 10], [4, 5, 6, 7, 8, 9])
  | 46 => ([2, 5, 6, 7, 8, 9, 10], [5, 6, 7, 8, 9], [4, 5, 6, 7, 8, 9])
  | 47 => ([3, 4, 5, 6, 7, 8], [2, 3, 4, 5, 6, 7, 8], [4, 5, 6, 7])
  | 48 => ([3, 4, 5, 6, 7, 8], [1, 4, 5, 6], [5, 6, 7])
  | 49 => ([1, 4, 5, 6], [3, 4, 5, 6, 7, 8], [5, 6, 7])
  | 50 => ([2, 3, 4, 5, 6, 7, 8], [3, 4, 5, 6, 7, 8], [4, 5, 6, 7])
  | _ => ([], [], [])
def bits (xs : List Nat) : Nat := xs.foldl (fun m k => m ||| (1 <<< k)) 0
def hit (m i : Nat) : Bool :=
  (data i).1.any (fun a => [4,8,16].any (fun d =>
    decide (a+2 ≤ d) && m.testBit (d-(a+2))))
def advance (m i : Nat) : Nat :=
  ((data i).2.2.foldl (fun z t => z ||| (m <<< (t+2))) (bits (data i).2.1)) &&& 2147483647
def cap (m : Nat) : Bool := m.testBit 2 || m.testBit 6 || m.testBit 14
def Trace (initial n : Nat) (states choices : Nat → Nat) : Prop :=
  states 0 = initial ∧ ∀ j, j < n →
    choices j < 51 ∧ hit (states j) (choices j) = false ∧
      states (j+1) = advance (states j) (choices j)

end Semantics

def selected (i : Nat) : Kernel.Profile :=
  let p := Semantics.data i
  ⟨p.1, p.2.1, p.2.2⟩

theorem selected_mem : ∀ i : Fin 51, selected i.val ∈ Kernel.profiles := by
  decide +kernel

theorem trace_lift (n : Nat) : ∀ (initial : Nat) (states choices : Nat → Nat),
    Semantics.Trace initial n states choices → Kernel.Avoiding initial (states n) n := by
  induction n with
  | zero =>
    intro initial states choices h
    rw [h.1]
    exact Kernel.Avoiding.base
  | succ n ih =>
    intro initial states choices h
    have hn : Semantics.Trace initial n states choices :=
      ⟨h.1, fun j hj => h.2 j (Nat.lt_trans hj (Nat.lt_succ_self n))⟩
    have step := h.2 n (Nat.lt_succ_self n)
    have hm := selected_mem ⟨choices n, step.1⟩
    have hh : Kernel.hit (states n) (selected (choices n)) = false := by
      simpa [Kernel.hit, selected, Semantics.hit] using step.2.1
    have lifted := Kernel.Avoiding.step (ih initial states choices hn) hm hh
    rw [step.2.2]
    simpa [Kernel.advance, Kernel.bits, selected, Semantics.advance, Semantics.bits] using lifted

theorem proof :
    (∀ (n : Nat) (states choices : Nat → Nat), Semantics.Trace 0 n states choices → n ≤ 5) ∧
    (∀ (n : Nat) (states choices : Nat → Nat), Semantics.Trace 1 n states choices → n ≤ 2) ∧
    (∀ (n : Nat) (states choices : Nat → Nat), Semantics.Trace 1 n states choices →
      Semantics.cap (states n) = false → n = 0) := by
  constructor
  · intro n states choices h
    exact Kernel.open_length_bound (trace_lift n 0 states choices h)
  · constructor
    · intro n states choices h
      exact Kernel.terminal_length_bound (trace_lift n 1 states choices h)
    · intro n states choices h hc
      exact Kernel.capped_nonempty_impossible (trace_lift n 1 states choices h) hc

end Submissions.J5P399LayerTrace.LayerTrace286
