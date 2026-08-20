/-
  hm08 vertex groups: what they actually cover.

  ## The claim this file was written to check

  Through a whole design discussion one sentence went unchecked:

    "hm08 partitions the mesh, so layer masks have no gaps by construction."

  That sentence is why the 3D layer route was believed not to need a segmentation model.
  It is **true**, and the first version of this file concluded it was half false, because it
  read one JSON field and took that field for the mesh.

  Disjointness holds. Nothing is claimed by two groups, so no vertex ends up in two layers.

  Coverage holds too, via `basemesh_vertex_groups.json`'s three top-level groups:

      body ⊔ HelperGeometry ⊔ JointCubes  =  0 .. 19157
      13380 +      4778     +   1000      =  19158        no overlap, no gap

  It does **not** hold via `hm08_config.json`'s `groups_by_range`, which names twelve ranges
  and stops at 19149. A mask built from those twelve has gaps. That is the real finding, and
  it is narrower than what this file used to say.

  ## Retracted, and kept in place

  Two sentences from the first version are withdrawn. They stay written down, because a reader
  who knows which roads are dead ends is better off than one who only knows the answer.

  **Retracted: "992 vertices belong to no group at all."** They belong to `JointCubes`. What is
  true is narrower: they belong to no group in `groups_by_range`. There are also 1000 of them,
  not 992, in **two** ranges rather than one:

      "JointCubes": [[13606, 14597], [19150, 19157]]

  **Retracted: "`select_groups` names them (`HELPERS` -> `HelperGeometry`)."** It does not.
  `HelperGeometry` is `[[13380, 13605], [14598, 19149]]`, which excludes the joint cubes
  exactly. `select_groups` never mentions `JointCubes` at all, so the group that names them is
  the one that mapping cannot reach.

  ## Why the error survived

  Worth recording, because it is the same error twice at two levels.

  The original claim counted the ranges in `groups_by_range` and missed the helper block. The
  correction counted the same twelve ranges, stopped at 19149, and missed the second
  `JointCubes` range. Both times, counting one field stood in for measuring the mesh.

  And `992 = 124 * 8` divides evenly. A number that resolves neatly invites no further
  question, so nobody asked whether 992 was all of them. It was not. 1000 = 125 * 8 divides
  just as neatly, which is the warning: the arithmetic working is not evidence.

  ## The mesh is 19,158 vertices

  Not 19,150. The highest index in any of the 144 groups is 19157. ANNY agrees when asked for
  a topology that keeps unattached vertices:

      Anny(topology=TopologyConfig(base_mesh="makehuman", remove_unattached_vertices=False))
        -> 19158 vertices
      Anny()  -> 13718 vertices, because the default drops every unattached vertex

  The eight vertices at 19150..19157 are the ones a mask built from `groups_by_range` loses.
  They have a name: **`joint-ground`**, MakeHuman's ground joint. It is a group of its own,
  and it sits at the end of the mesh rather than in the contiguous block, which is exactly
  how reading one range lost it.

  That also settles what "125 cubes" means, rather than leaving it as a division that came
  out even. There are 125 groups named `joint-*`. Every one is 8 vertices. Their union is
  `JointCubes` exactly. So the count is read off the data three independent ways.

  Left unstated, `joint-ground` would either vanish from the corpus or turn up as one small
  floating box inside whichever layer caught the remainder. RFD 0121 records the measurement
  and its consequence for the layer route.

  `check_hm08_claims.py` asserts every number above against the installed ANNY data, so drift
  fails a command rather than surviving another design discussion.

  Ranges are read from `anny/data/mpfb2/mesh_metadata/hm08_config.json` and
  `basemesh_vertex_groups.json`.
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

/-- The mesh: 19,158 vertices, indices `0 .. 19157`.

    The first version of this file said 19,150, which is where `groups_by_range` stops rather
    than where the mesh does. `basemesh_vertex_groups.json` reaches 19157, and ANNY returns
    19158 vertices for a topology that keeps unattached vertices. -/
def meshSet : Set Nat := Set.Ico 0 19158

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

/-! ## Coverage does not hold via `groups_by_range`

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

/-- `JointCubes`, verbatim: **two** ranges, not one.

    The first version of this file had only the first range and called it "the unassigned
    block". Both halves of that name were wrong. The vertices are assigned, to this group, and
    they do not form one block. The second range is `joint-ground`. -/
def jointCubes : Set Nat := Set.Ico 13606 14598 ∪ Set.Ico 19150 19158

/-- Every joint-cube vertex is outside every `groups_by_range` group. This is what a mask
    built from those twelve ranges loses. -/
theorem jointCubes_uncovered : ∀ x ∈ jointCubes, x ∉ coveredSet := by
  intro x hx
  simp only [coveredSet, Set.mem_iUnion, not_exists]
  intro r hr
  simp only [jointCubes, Set.mem_union, Set.mem_Ico] at hx
  fin_cases hr <;> (simp [Range.seg, Set.mem_Ico]; try omega)

/-- And there are 1000 of them: 125 joint-helper cubes of 8, not 124. Arithmetic rather than a
    comment, so the reading of what those vertices *are* stays tied to the count.

    Both `992 = 124 * 8` and `1000 = 125 * 8` divide evenly. The first was believed partly
    because it did. That the arithmetic works is not evidence that the input was complete. -/
theorem jointCubes_card : (14598 - 13606) + (19158 - 19150) = 125 * 8 := by norm_num

/-! ## Coverage does hold, via the three top-level groups

    This is the section the first version of the file did not have, and it is the one that
    settles the original sentence. `basemesh_vertex_groups.json` carries 144 groups. Three of
    them sit above the rest and tile the mesh exactly. -/

/-- `body`, verbatim. -/
def bodyBlock : Set Nat := Set.Ico 0 13380

/-- `HelperGeometry`, verbatim: two ranges, and neither reaches the joint cubes. That gap in
    the middle is exactly `jointCubes`' first range, which is why `HELPERS -> HelperGeometry`
    cannot name what the first version of this file said it named. -/
def helperGeometry : Set Nat := Set.Ico 13380 13606 ∪ Set.Ico 14598 19150

/-- The three cover the mesh with nothing left over. **This is the original claim, and it is
    true.** A mask built from these three has no gaps by construction. -/
theorem three_groups_cover : bodyBlock ∪ helperGeometry ∪ jointCubes = meshSet := by
  ext x
  simp only [bodyBlock, helperGeometry, jointCubes, meshSet, Set.mem_union, Set.mem_Ico]
  omega

/-- And no vertex is in two of them, so the cover is a partition. Stated as three separate
    disjointness facts rather than one `Pairwise`, because each is the thing a caller checks
    before trusting one particular pair of layers not to overlap. -/
theorem three_groups_disjoint :
    Disjoint bodyBlock helperGeometry ∧ Disjoint bodyBlock jointCubes ∧
      Disjoint helperGeometry jointCubes := by
  refine ⟨?_, ?_, ?_⟩ <;>
    · rw [Set.disjoint_left]
      intro x hx hx'
      simp only [bodyBlock, helperGeometry, jointCubes, Set.mem_union, Set.mem_Ico] at hx hx'
      omega

/-- The counts, tied to the definitions rather than to a comment. -/
theorem three_groups_card :
    13380 + ((13606 - 13380) + (19150 - 14598)) + ((14598 - 13606) + (19158 - 19150))
      = 19158 := by norm_num

/-! ## The corrected claim

    Narrower, and true. A mask built from these groups is gapless over the parts it names,
    provided the helper block is excluded by name rather than assumed not to exist. -/

/-- Nothing in the mesh is missed except the joint cubes: every vertex is in some
    `groups_by_range` group, or in `jointCubes`. This is the statement a caller actually needs
    before trusting the masks. -/
theorem covered_or_jointCubes : ∀ x ∈ meshSet, x ∈ coveredSet ∨ x ∈ jointCubes := by
  intro x hx
  obtain ⟨-, hlt⟩ := hx
  by_cases hb : x ∈ jointCubes
  · exact Or.inr hb
  · refine Or.inl ?_
    simp only [jointCubes, Set.mem_union, Set.mem_Ico, not_or, not_and, not_lt] at hb
    obtain ⟨hb, hb2⟩ := hb
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
      -- Above 19149 the twelve ranges stop, so anything left is the second `JointCubes`
      -- range, which `hb2` has already excluded. This branch is the one the first version of
      -- the proof did not have, because its `meshSet` ended at 19149.
      · have h19150 : x < 19150 := by
          by_contra hcon
          exact absurd (hb2 (Nat.le_of_not_lt hcon)) (by omega)
        exact ⟨⟨"helper-hair", 18722, 19149⟩, by simp [groups],
               by simp [Range.seg, Set.mem_Ico]; try omega⟩

end Hm08
