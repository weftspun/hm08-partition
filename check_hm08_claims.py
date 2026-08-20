"""Re-measure every constant `Hm08Partition.lean` states, and fail if the data has moved.

WHY THIS EXISTS. This file's Lean proofs are only as good as the numbers hand-copied into
them, and that copying has already gone wrong once, in a way a proof assistant could not
catch. The first version of `Hm08Partition.lean` proved every theorem it stated. It was
still wrong, because `meshSet` was defined as `Set.Ico 0 19150` and the mesh has 19,158
vertices. Lean cannot notice that a definition disagrees with a JSON file it never reads.

So the constants are re-derived here from the installed ANNY package and compared. Drift
fails a command instead of surviving another design discussion.

The specific defect this would have caught: `JointCubes` carries **two** ranges,
`[[13606, 14597], [19150, 19157]]`. Reading only the first gives 992 vertices, which is
124 cubes of 8, which divides evenly and therefore invites no further question. The real
count is 1000, in 125 cubes. `check_joint_cubes` asserts the range *count*, not just the
total, so truncation fails loudly rather than reading as a smaller tidy answer.

Not checked here, on purpose: this script does not instantiate `anny.Anny`. That pulls in
Warp and a CUDA context to settle a claim about a JSON file. The instantiation result is
recorded instead, measured once for RFD 0121:

    Anny(topology=TopologyConfig(base_mesh="makehuman", remove_unattached_vertices=False))
      -> 19158 vertices, matching the group data below
    Anny()
      -> 13718 vertices, because the default drops every unattached vertex

Usage:
    python check_hm08_claims.py              re-measure against the installed ANNY data
    python check_hm08_claims.py --self-test  run the negative controls, then the above

Exit code is non-zero if any claim has drifted, so it can gate CI.

A claim whose source data is missing is reported as UNVERIFIED and counted as a failure. A
silent skip reads exactly like a pass, which is the failure mode this repository's own
subject matter is about.
"""

import copy
import json
import pathlib
import sys

# Every number below appears in Hm08Partition.lean. The Lean name is given so a reader can
# find the definition a failure refers to.

MESH_VERTICES = 19158  # meshSet
BODY_VERTICES = 13380  # bodyBlock
HELPER_GEOMETRY_VERTICES = 4778  # helperGeometry
JOINT_CUBES_VERTICES = 1000  # jointCubes
JOINT_CUBES_RANGES = 2  # jointCubes, the count the first version got wrong
CUBE_SIZE = 8

# groups_by_range, verbatim, sorted by lo. This is the `groups` list in the Lean file.
GROUPS_BY_RANGE = [
    ("body", 0, 13379),
    ("helper-tongue", 13380, 13605),
    ("helper-l-eye", 14598, 14669),
    ("helper-r-eye", 14670, 14741),
    ("helper-l-eyelashes", 14742, 14866),
    ("helper-r-eyelashes", 14867, 14991),
    ("helper-lower-teeth", 14992, 15059),
    ("helper-upper-teeth", 15060, 15127),
    ("helper-genital", 15128, 15327),
    ("helper-tights", 15328, 18001),
    ("helper-skirt", 18002, 18721),
    ("helper-hair", 18722, 19149),
]

# The witness `gap_witness_uncovered` names. It must be in the mesh and in no
# groups_by_range group.
GAP_WITNESS = 13606

# The 125th cube, and the one the first version of the Lean file missed. It sits at the end
# of the mesh rather than in the contiguous block, which is why reading one range lost it.
GROUND_JOINT = "joint-ground"
GROUND_JOINT_RANGE = [19150, 19157]
JOINT_GROUP_COUNT = 125


def anny_metadata_dir():
    import anny

    return pathlib.Path(anny.__file__).parent / "data" / "mpfb2" / "mesh_metadata"


def load_data():
    d = anny_metadata_dir()
    groups = json.loads((d / "basemesh_vertex_groups.json").read_text())
    config = json.loads((d / "hm08_config.json").read_text())
    return groups, config


def total(ranges):
    return sum(hi - lo + 1 for lo, hi in ranges)


def members(ranges):
    out = set()
    for lo, hi in ranges:
        out.update(range(lo, hi + 1))
    return out


# --- the claims -----------------------------------------------------------------------


def check_joint_cubes(groups, config, fail):
    ranges = groups["JointCubes"]
    if len(ranges) != JOINT_CUBES_RANGES:
        fail(
            f"jointCubes: JointCubes has {len(ranges)} range(s), expected "
            f"{JOINT_CUBES_RANGES}. Reading only the first is the original defect."
        )
        return
    n = total(ranges)
    if n != JOINT_CUBES_VERTICES:
        fail(f"jointCubes: {n} vertices, expected {JOINT_CUBES_VERTICES}")
    if n % CUBE_SIZE:
        fail(f"jointCubes_card: {n} is not a whole number of {CUBE_SIZE}-vertex cubes")
    elif n // CUBE_SIZE != 125:
        fail(f"jointCubes_card: {n // CUBE_SIZE} cubes, expected 125")


def check_helper_geometry(groups, config, fail):
    ranges = groups["HelperGeometry"]
    n = total(ranges)
    if n != HELPER_GEOMETRY_VERTICES:
        fail(f"helperGeometry: {n} vertices, expected {HELPER_GEOMETRY_VERTICES}")
    # The retracted claim: HELPERS -> HelperGeometry was said to name the joint cubes.
    # It does not, and this asserts the exclusion rather than trusting the docstring.
    if GAP_WITNESS in members(ranges):
        fail(
            f"helperGeometry: contains vertex {GAP_WITNESS}. The docstring's retraction "
            f"says it does not, so either the data or the retraction is wrong."
        )
    if "JointCubes" in config["select_groups"].get("HELPERS", []):
        fail("select_groups: HELPERS now names JointCubes, so the retraction is stale")


def check_body(groups, config, fail):
    n = total(groups["body"])
    if n != BODY_VERTICES:
        fail(f"bodyBlock: {n} vertices, expected {BODY_VERTICES}")


def check_partition(groups, config, fail):
    """three_groups_cover and three_groups_disjoint, re-derived."""
    seen = {}
    for name in ("body", "HelperGeometry", "JointCubes"):
        for v in members(groups[name]):
            if v in seen:
                fail(f"three_groups_disjoint: vertex {v} in {seen[v]} and {name}")
                return
            seen[v] = name
    if len(seen) != MESH_VERTICES:
        fail(f"three_groups_cover: union is {len(seen)}, expected {MESH_VERTICES}")
        return
    if set(seen) != set(range(MESH_VERTICES)):
        fail("three_groups_cover: union is not exactly 0..%d" % (MESH_VERTICES - 1))


def check_mesh_extent(groups, config, fail):
    """meshSet. The highest index in ANY of the 144 groups decides the mesh size, which is
    the measurement the first version replaced with a count of twelve ranges."""
    top = -1
    for ranges in groups.values():
        for r in ranges:
            if isinstance(r, list) and len(r) == 2 and all(isinstance(x, int) for x in r):
                top = max(top, r[1])
    if top + 1 != MESH_VERTICES:
        fail(f"meshSet: highest index {top}, so {top + 1} vertices, expected {MESH_VERTICES}")


def check_groups_by_range(groups, config, fail):
    """The `groups` list in the Lean file, verbatim, and `groups_sorted`."""
    live = config["groups_by_range"]
    for name, lo, hi in GROUPS_BY_RANGE:
        if name not in live:
            fail(f"groups: {name} is gone from groups_by_range")
            continue
        got = live[name]
        if [lo, hi] != list(got):
            fail(f"groups: {name} is {got}, expected [{lo}, {hi}]")
    extra = set(live) - {n for n, _, _ in GROUPS_BY_RANGE}
    if extra:
        fail(f"groups: groups_by_range gained {sorted(extra)}, not in the Lean list")
    ordered = sorted(GROUPS_BY_RANGE, key=lambda g: g[1])
    for (an, _, ahi), (bn, blo, _) in zip(ordered, ordered[1:]):
        if ahi >= blo:
            fail(f"groups_sorted: {an} ends at {ahi}, {bn} starts at {blo}")


def check_joint_groups(groups, config, fail):
    """The 125 individually named joint helpers tile JointCubes exactly, 8 vertices each.

    This is what makes "125 cubes" a reading of the data rather than a division that came
    out even. It also names the cube the first version lost: joint-ground."""
    named = [k for k in groups if k.startswith("joint-")]
    if len(named) != JOINT_GROUP_COUNT:
        fail(f"jointCubes_card: {len(named)} joint-* groups, expected {JOINT_GROUP_COUNT}")
    odd = {k: total(groups[k]) for k in named if total(groups[k]) != CUBE_SIZE}
    if odd:
        fail(f"jointCubes_card: joint groups not {CUBE_SIZE} vertices: {odd}")
    union = set()
    for k in named:
        union |= members(groups[k])
    if union != members(groups["JointCubes"]):
        fail("jointCubes: the joint-* groups do not tile JointCubes exactly")
    if GROUND_JOINT not in groups:
        fail(f"jointCubes: {GROUND_JOINT} is gone, so the 125th cube has no name")
    elif [list(r) for r in groups[GROUND_JOINT]] != [GROUND_JOINT_RANGE]:
        fail(
            f"jointCubes: {GROUND_JOINT} is {groups[GROUND_JOINT]}, expected "
            f"[{GROUND_JOINT_RANGE}]. The docstring names it as the missed cube."
        )


def check_gap_witness(groups, config, fail):
    """gap_witness_in_mesh and gap_witness_uncovered."""
    if not 0 <= GAP_WITNESS < MESH_VERTICES:
        fail(f"gap_witness_in_mesh: {GAP_WITNESS} is outside the mesh")
    for name, lo, hi in GROUPS_BY_RANGE:
        if lo <= GAP_WITNESS <= hi:
            fail(f"gap_witness_uncovered: {GAP_WITNESS} is in {name}, so it is covered")


CHECKS = [
    check_mesh_extent,
    check_groups_by_range,
    check_body,
    check_helper_geometry,
    check_joint_cubes,
    check_partition,
    check_joint_groups,
    check_gap_witness,
]


def run(groups, config, quiet=False):
    """Returns the list of failures. Empty means every claim still holds."""
    failures = []
    for check in CHECKS:
        before = len(failures)
        try:
            check(groups, config, failures.append)
        except Exception as exc:  # a check that cannot run has not passed
            failures.append(f"UNVERIFIED {check.__name__}: {type(exc).__name__}: {exc}")
        if not quiet:
            added = failures[before:]
            mark = "FAIL" if added else "ok  "
            print(f"  {mark} {check.__name__}")
            for f in added:
                print(f"       {f}")
    return failures


# --- the negative controls ------------------------------------------------------------
#
# A check that passes on known-broken input certifies the defect. Each control below is a
# distinct way the data could be wrong, and each must be caught. One control would only
# prove the script is not uniformly permissive.


def _truncate_joint_cubes(groups, config):
    """The original defect: read only the first JointCubes range."""
    groups["JointCubes"] = groups["JointCubes"][:1]


def _shrink_mesh(groups, config):
    """The original meshSet: stop where groups_by_range stops, at 19149.

    Note this must trim `Left`, `Right` and `joint-ground` as well, not only `JointCubes`.
    `Right` runs [19122, 19151] straight across the boundary, because the mirror-side
    groups are an orthogonal partition of the mesh and do not respect part edges."""
    for name, ranges in list(groups.items()):
        trimmed = []
        for r in ranges:
            if not (isinstance(r, list) and len(r) == 2 and all(isinstance(x, int) for x in r)):
                trimmed.append(r)
            elif r[0] > 19149:
                continue
            else:
                trimmed.append([r[0], min(r[1], 19149)])
        groups[name] = trimmed


def _overlap_groups(groups, config):
    """Break disjointness: let HelperGeometry reach into the joint cubes."""
    groups["HelperGeometry"] = [[13380, 13700]] + groups["HelperGeometry"][1:]


def _drop_ground_joint(groups, config):
    """Remove the 125th cube's name while leaving the vertices in JointCubes."""
    del groups[GROUND_JOINT]


def _rename_group(groups, config):
    """Break the groups_by_range list the Lean file copies verbatim."""
    config["groups_by_range"]["helper-hair"] = [18722, 19148]


def _helpers_names_cubes(groups, config):
    """Make the retracted docstring claim true again, which must be reported."""
    config["select_groups"]["HELPERS"] = ["HelperGeometry", "JointCubes"]


CONTROLS = [
    ("JointCubes truncated to one range", _truncate_joint_cubes),
    ("mesh shortened to 19150", _shrink_mesh),
    ("HelperGeometry overlaps JointCubes", _overlap_groups),
    ("helper-hair range changed", _rename_group),
    ("joint-ground removed", _drop_ground_joint),
    ("HELPERS names JointCubes", _helpers_names_cubes),
]


def self_test(groups, config):
    print("negative controls (each must FAIL):")
    bad = []
    for label, mutate in CONTROLS:
        g, c = copy.deepcopy(groups), copy.deepcopy(config)
        mutate(g, c)
        failures = run(g, c, quiet=True)
        if failures:
            print(f"  ok   {label} -> caught: {failures[0]}")
        else:
            print(f"  FAIL {label} -> passed, so the check is decoration")
            bad.append(label)
    return bad


def main(argv):
    try:
        groups, config = load_data()
    except Exception as exc:
        print(f"UNVERIFIED: cannot read the ANNY mesh metadata: {exc}")
        return 2

    rc = 0
    if "--self-test" in argv:
        bad = self_test(groups, config)
        if bad:
            print(f"\n{len(bad)} negative control(s) did not fail. The checks are not gating.")
            rc = 1
        print()

    print("claims, against the installed ANNY data:")
    failures = run(groups, config)
    if failures:
        print(f"\n{len(failures)} claim(s) drifted. Hm08Partition.lean states numbers that")
        print("the data no longer supports. Fix the Lean file, not this script.")
        return 1
    print("\nEvery constant in Hm08Partition.lean still matches the data.")
    return rc


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
