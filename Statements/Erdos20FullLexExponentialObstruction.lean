import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic


namespace Statements.Erdos20FullLexExponentialObstruction

variable {α : Type*} [DecidableEq α]

def shiftMember (i j : α) (F : Finset (Finset α)) (A : Finset α) : Finset α :=
  if i ∉ A ∧ j ∈ A ∧ insert i (A.erase j) ∉ F then insert i (A.erase j) else A

def shift (i j : α) (F : Finset (Finset α)) : Finset (Finset α) :=
  F.image (shiftMember i j F)

def tagged (B : α → Finset ℕ) (w : α) : Finset (ℕ ⊕ α) :=
  ((B w).image Sum.inl) ∪ {Sum.inr w}

def taggedFamily [Fintype α] (B : α → Finset ℕ) : Finset (Finset (ℕ ⊕ α)) :=
  Finset.univ.image (tagged B)

def bodySources (m i : ℕ) : List ℕ := (List.range m).filter (i < ·)

def perform (L : List (α × α)) (F : Finset (Finset α)) :=
  L.foldl (fun F p => shift p.1 p.2 F) F

def bodySchedule (m : ℕ) (tags : List α) (targets : List ℕ) : List ((ℕ ⊕ α) × (ℕ ⊕ α)) :=
  targets.flatMap fun i =>
    (((bodySources m i).map Sum.inl ++ tags.map Sum.inr).map fun j => (Sum.inl i, j))

def tagSchedule (tags : List α) : List ((ℕ ⊕ α) × (ℕ ⊕ α)) :=
  tags.rec [] (fun a L ih => L.map (fun b => (Sum.inr a, Sum.inr b)) ++ ih)

/-- All ordered-ground-set pairs, first by ascending target and then ascending source.
The body vertices are 0,...,2k−1, followed by the supplied tag enumeration. -/
def fullSchedule (k : ℕ) (tags : List α) : List ((ℕ ⊕ α) × (ℕ ⊕ α)) :=
  bodySchedule (2*k) tags (List.range k) ++
  bodySchedule (2*k) tags (List.range' k k) ++ tagSchedule tags

def core (k : ℕ) : Finset (ℕ ⊕ α) := (Finset.range k).image Sum.inl

abbrev Word (k : ℕ) := Fin k → Bool

def coordinate {k : ℕ} (i : Fin k) (b : Bool) : ℕ := 2*i.val + if b then 1 else 0

def binaryBody {k : ℕ} (w : Word k) : Finset ℕ :=
  Finset.univ.image (fun i => coordinate i (w i))

def initialFamily (k : ℕ) := taggedFamily (binaryBody (k := k))

/-- A fixed enumeration of all binary words; its order defines the order of the private tags. -/
noncomputable def allTags (k : ℕ) : List (Word k) :=
  List.ofFn ((Fintype.equivFin (Word k)).symm)

def IsSunflower (F : Finset (Finset α)) : Prop :=
  ∃ K, ∀ A ∈ F, ∀ B ∈ F, A ≠ B → A ∩ B = K

noncomputable def finalFamily (k : ℕ) := perform (fullSchedule k (allTags k)) (initialFamily k)

abbrev statement : Prop :=
  ∀ k : ℕ,
    (initialFamily k).card = 2^k ∧
    (∀ A ∈ initialFamily k, A.card = k+1) ∧
    (∀ G ⊆ initialFamily k, 3 ≤ G.card → ¬ IsSunflower G) ∧
    (allTags k).Nodup ∧ (∀ w : Word k, w ∈ allTags k) ∧
    (finalFamily k).card = 2^k ∧
    (∀ A ∈ finalFamily k, A.card = k+1) ∧
    (∀ A ∈ finalFamily k, ∀ B ∈ finalFamily k, A ≠ B → A ∩ B = core k)

theorem target : statement := sorry

end Statements.Erdos20FullLexExponentialObstruction
