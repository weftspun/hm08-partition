/-
  hm08 vertex groups: what they actually cover.

  ## The claim this file was written to check

  Through a whole design discussion one sentence went unchecked:

    "hm08 partitions the mesh, so layer masks have no gaps by construction."

  That sentence is why the 3D layer route was believed not to need a segmentation model.
  Half of it is true and half is false, and writing it down formally is what separated them.

  Disjointness holds. Nothing is claimed by two groups, so no vertex ends up in two layers.

  Coverage does not. **992 vertices belong to no group at all.** They sit in one contiguous
  block between `helper-tongue` and `helper-l-eye`, and 992 = 124 * 8: one eight-vertex cube
  per joint helper. `select_groups` names them (`HELPERS` -> `HelperGeometry`) and
  `groups_by_range` gives them no range, which is why counting the ranges misses them.

  They are not junk. MakeHuman uses those cubes to place skeleton joints. They are simply
  not a renderable part, so the corrected claim is narrower and true: the groups partition
  the *renderable* vertices, and the remainder is exactly the helper block.

  Left unstated, those 124 cubes would have fallen through every mask and either vanished
  from the corpus or turned up as small floating boxes inside whichever layer caught the
  remainder.

  Ranges are read from `anny/data/mpfb2/mesh_metadata/hm08_config.json`.
-/
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.Disjoint
import Mathlib.Data.Set.Lattice
import Mathlib.Data.List.Pairwise
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

namespace Hm08

/-- A named inclusive vertex range, as `groups_by_range` stores it. -/
structure Range where
  name : String
  lo   : Nat
  hi   : Nat
  deriving Repr, DecidableEq

/-- The vertices a range covers. Inclusive at both ends in the file, so the upper bound is
    `hi + 1` here. Using `Set.Ico` rather than `Finset` on purpose: every statement below is
    about membership and disjointness, and a `Finset` over 19,150 elements would invite
    `decide` to enumerate the mesh. -/
def Range.seg (r : Range) : Set Nat := Set.Ico r.lo (r.hi + 1)

/-- `groups_by_range`, verbatim, sorted by `lo`. The JSON is not sorted. -/
def groups : List Range :=
  [ ⟨"body",               0,     13379⟩
  , ⟨"helper-tongue",      13380, 13605⟩
  , ⟨"helper-l-eye",       14598, 14669⟩
  , ⟨"helper-r-eye",       14670, 14741⟩
  , ⟨"helper-l-eyelashes", 14742, 14866⟩
  , ⟨"helper-r-eyelashes", 14867, 14991⟩
  , ⟨"helper-lower-teeth", 14992, 15059⟩
  , ⟨"helper-upper-teeth", 15060, 15127⟩
  , ⟨"helper-genital",     15128, 15327⟩
  , ⟨"helper-tights",      15328, 18001⟩
  , ⟨"helper-skirt",       18002, 18721⟩
  , ⟨"helper-hair",        18722, 19149⟩ ]

/-- Every vertex any group names, as one set. -/
def coveredSet : Set Nat := ⋃ r ∈ groups, r.seg

/-- The mesh: 19,150 vertices, indices `0 .. 19149`. -/
def meshSet : Set Nat := Set.Ico 0 19150

/-! ## Disjointness holds -/

/-- Ranges are ordered and non-overlapping: each starts after the previous one ends. Stated
    over the list rather than checked pairwise by hand, so inserting a group in the wrong
    place fails here rather than silently later. -/
theorem groups_sorted : groups.Pairwise (fun a b => a.hi < b.lo) := by
  simp [groups]

/-- Therefore no vertex is claimed by two groups. This is the half of the original claim that
    was correct, and it is what stops a vertex landing in two layers. -/
theorem segs_disjoint :
    groups.Pairwise (fun a b => Disjoint a.seg b.seg) := by
  refine groups_sorted.imp ?_
  intro a b hab
  rw [Set.disjoint_left]
  intro x hx hx'
  have h₁ : x ≤ a.hi := Nat.lt_succ_iff.mp hx.2
  have h₂ : b.lo ≤ x := hx'.1
  omega

/-! ## Coverage does not

    The counterexample is a single vertex. Exhibiting one is enough to falsify the claim, and
    it costs nothing to check -- no enumeration, no card arithmetic over 19,150 elements. -/

/-- Vertex 13606 is in the mesh. -/
theorem gap_witness_in_mesh : 13606 ∈ meshSet := by
  constructor <;> norm_num

/-- **And it belongs to no group.** This is the sentence that was wrong. -/
theorem gap_witness_uncovered : 13606 ∉ coveredSet := by
  simp only [coveredSet, Set.mem_iUnion, not_exists]
  intro r hr
  fin_cases hr <;> (simp [Range.seg, Set.mem_Ico]; try omega)

/-- Stated as the negation directly, so the failure cannot be lost by someone reading only
    the disjointness result above and assuming the rest. -/
theorem not_a_partition : coveredSet ≠ meshSet := by
  intro h
  exact gap_witness_uncovered (h ▸ gap_witness_in_mesh)

/-! ## The gap, exactly

    One contiguous block. Not scattered holes, which would be a different and worse problem:
    a single named block can be excluded by name, while scattered holes could not. -/

/-- The unassigned block. -/
def helperBlock : Set Nat := Set.Ico 13606 14598

/-- Every vertex in the block is outside every group. -/
theorem helperBlock_uncovered : ∀ x ∈ helperBlock, x ∉ coveredSet := by
  intro x hx
  simp only [coveredSet, Set.mem_iUnion, not_exists]
  intro r hr
  obtain ⟨hlo, hhi⟩ := hx
  fin_cases hr <;> (simp [Range.seg, Set.mem_Ico]; try omega)

/-- And the block is 992 vertices: 124 joint-helper cubes of 8. Arithmetic rather than a
    comment, so the reading of what those vertices *are* is tied to the count. -/
theorem helperBlock_card : 14598 - 13606 = 124 * 8 := by norm_num

/-! ## The corrected claim

    Narrower, and true. A mask built from these groups is gapless over the parts it names,
    provided the helper block is excluded by name rather than assumed not to exist. -/

/-- Nothing in the mesh is missed except the helper block: every vertex is in some group, or
    in the block. This is the statement a caller actually needs before trusting the masks. -/
theorem covered_or_helper : ∀ x ∈ meshSet, x ∈ coveredSet ∨ x ∈ helperBlock := by
  intro x hx
  obtain ⟨-, hlt⟩ := hx
  by_cases hb : x ∈ helperBlock
  · exact Or.inr hb
  · refine Or.inl ?_
    simp only [helperBlock, Set.mem_Ico, not_and, not_lt] at hb
    simp only [coveredSet, Set.mem_iUnion]
    rcases Nat.lt_or_ge x 13606 with h | h
    · rcases Nat.lt_or_ge x 13380 with h' | h'
      · exact ⟨⟨"body", 0, 13379⟩, by simp [groups], by simp [Range.seg, Set.mem_Ico]; try omega⟩
      · exact ⟨⟨"helper-tongue", 13380, 13605⟩, by simp [groups],
               by simp [Range.seg, Set.mem_Ico]; try omega⟩
    · have h14598 : 14598 ≤ x := hb h
      -- Above the block the groups run contiguously to the end of the mesh, so one of them
      -- contains x. Split on the boundaries in order.
      rcases Nat.lt_or_ge x 14670 with h1 | h1
      · exact ⟨⟨"helper-l-eye", 14598, 14669⟩, by simp [groups],
               by simp [Range.seg, Set.mem_Ico]; try omega⟩
      rcases Nat.lt_or_ge x 14742 with h2 | h2
      · exact ⟨⟨"helper-r-eye", 14670, 14741⟩, by simp [groups],
               by simp [Range.seg, Set.mem_Ico]; try omega⟩
      rcases Nat.lt_or_ge x 14867 with h3 | h3
      · exact ⟨⟨"helper-l-eyelashes", 14742, 14866⟩, by simp [groups],
               by simp [Range.seg, Set.mem_Ico]; try omega⟩
      rcases Nat.lt_or_ge x 14992 with h4 | h4
      · exact ⟨⟨"helper-r-eyelashes", 14867, 14991⟩, by simp [groups],
               by simp [Range.seg, Set.mem_Ico]; try omega⟩
      rcases Nat.lt_or_ge x 15060 with h5 | h5
      · exact ⟨⟨"helper-lower-teeth", 14992, 15059⟩, by simp [groups],
               by simp [Range.seg, Set.mem_Ico]; try omega⟩
      rcases Nat.lt_or_ge x 15128 with h6 | h6
      · exact ⟨⟨"helper-upper-teeth", 15060, 15127⟩, by simp [groups],
               by simp [Range.seg, Set.mem_Ico]; try omega⟩
      rcases Nat.lt_or_ge x 15328 with h7 | h7
      · exact ⟨⟨"helper-genital", 15128, 15327⟩, by simp [groups],
               by simp [Range.seg, Set.mem_Ico]; try omega⟩
      rcases Nat.lt_or_ge x 18002 with h8 | h8
      · exact ⟨⟨"helper-tights", 15328, 18001⟩, by simp [groups],
               by simp [Range.seg, Set.mem_Ico]; try omega⟩
      rcases Nat.lt_or_ge x 18722 with h9 | h9
      · exact ⟨⟨"helper-skirt", 18002, 18721⟩, by simp [groups],
               by simp [Range.seg, Set.mem_Ico]; try omega⟩
      · exact ⟨⟨"helper-hair", 18722, 19149⟩, by simp [groups],
               by simp [Range.seg, Set.mem_Ico]; try omega⟩

end Hm08
