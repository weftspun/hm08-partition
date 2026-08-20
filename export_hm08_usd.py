"""Write the hm08 topology and its vertex groups to an OpenUSD layer.

WHY THIS EXISTS. RFD 0053 makes OpenUSD the internal format, and this is the entry point for
the body. Downstream stages compose against the layer this writes rather than importing
`anny` and re-deriving the topology, so nobody has to know which loader path ships in which
release.

That question is not hypothetical. `TopologyConfig(base_mesh=...)` and the `topology=` spec
string take different vocabularies. `AlternativeTopology` is `smplx`, `smpl`, `soma`,
`anny_from_soma`, `notoes` and three collapse variants. `"anny"` is not in it. Passing
`base_mesh="anny"` therefore falls through to `data/topology/anny.obj`, a file that was never
meant to exist, and the error names a missing asset rather than a bad argument. Reading it as
a packaging fault is easy and wrong. A USD layer removes the question, because a layer has one
way to be opened.

WHAT THE PARTITION BUYS. `UsdGeomSubset` has a `partition` family type, and USD validates it.
That is the same property `Hm08Partition.lean` proves, now enforced by the data format rather
than argued in a comment. A malformed export fails `ValidateSubsets` here instead of producing
a mask with holes six stages later.

THE TWO INDEX SPACES, which is where this would otherwise go wrong.

`Anny.faces` is the **body submodel**: 27,420 triangles reaching vertex index 14741, and no
higher under any of the eight combinations of `eyes`, `tongue` and `nudity_edits`. Read it as
the mesh and you conclude that `helper-hair`, `helper-tights` and `helper-skirt` have no faces
and cannot be rendered. That conclusion is wrong, and this file was written with it in it once.

The real table is `basemesh_face_to_vertex_table.json.gz`: **18,486 quads** reaching **19,157**,
referencing **all 19,158 vertices with none left over**. Every group has faces, the helper
meshes included. The helpers are proxy surfaces with no appearance, which is a different claim
from having no geometry.

So the layer carries both prims, and says which is which.

    /Hm08/Basemesh   19,158 points, 18,486 quads, every group, partition over the whole mesh
    /Hm08/Body       13,718 points, 27,420 triangles, the submodel that carries UVs

The map between them is measured, not assumed:

    ref = unique(Anny.faces)                     -> 13,718 indices, ascending
    max |basemesh_vertices[ref] - body|          -> 0.0 exactly
    body_index = searchsorted(ref, basemesh_index)

UVs exist for the body submodel only. `texture_coordinates` is (21334, 2) under
`topology="anny"` and `None` under `"soma"`. No UV table ships for the helper geometry, so the
basemesh prim carries none and this file does not invent any.

Usage:
    python export_hm08_usd.py [out.usda]
    python export_hm08_usd.py --check out.usda      re-open and validate, no ANNY import

Exit code is non-zero if the partition does not validate.
"""

import gzip
import hashlib
import json
import pathlib
import sys

import numpy as np

# Groups that survive into the renderable mesh are written as point subsets. The rest are
# recorded as metadata, because a subset of no elements is a lie about what is there.
GROUPS_BY_RANGE = "groups_by_range"
TOP_LEVEL = ("body", "HelperGeometry", "JointCubes")

DEFAULT_OUT = "hm08.usda"


def anny_metadata_dir():
    import anny

    return pathlib.Path(anny.__file__).parent / "data" / "mpfb2" / "mesh_metadata"


def members(ranges):
    out = []
    for lo, hi in ranges:
        out.extend(range(lo, hi + 1))
    return np.asarray(out, dtype=np.int64)


def load_source():
    """Everything read from ANNY, in one place, so the rest of this file is pure data work."""
    import anny
    import torch  # noqa: F401  (anny needs it loaded)
    from anny.models.model_data import TopologyConfig

    full = anny.Anny(
        topology=TopologyConfig(base_mesh="makehuman", remove_unattached_vertices=False)
    )
    faces_base = full.faces.cpu().numpy().astype(np.int64)
    verts_base = full()["vertices"][0].detach().cpu().numpy().astype(np.float32)

    # The spec string, not base_mesh. This is the call that carries UVs.
    render = anny.Anny(topology="anny")
    verts_render = render()["vertices"][0].detach().cpu().numpy().astype(np.float32)
    st = render.texture_coordinates
    st = None if st is None else st.cpu().numpy().astype(np.float32)
    faces_render_uv = render.face_texture_coordinate_indices.cpu().numpy().astype(np.int64)

    md = anny_metadata_dir()
    groups = json.loads((md / "basemesh_vertex_groups.json").read_text())
    config = json.loads((md / "hm08_config.json").read_text())
    # The whole basemesh, helper geometry included. Anny.faces is the body submodel only.
    quads = np.asarray(
        json.loads(gzip.open(md / "basemesh_face_to_vertex_table.json.gz").read()),
        dtype=np.int64,
    )
    return dict(
        quads=quads,
        faces_base=faces_base,
        verts_base=verts_base,
        verts_render=verts_render,
        st=st,
        faces_render_uv=faces_render_uv,
        groups=groups,
        config=config,
    )


def build_index_map(faces_base, verts_base, verts_render):
    """basemesh index -> renderable index, proved rather than trusted."""
    ref = np.unique(faces_base)
    if ref.size != verts_render.shape[0]:
        raise SystemExit(
            f"index map: faces reference {ref.size} vertices, renderable mesh has "
            f"{verts_render.shape[0]}. The two topologies have diverged."
        )
    drift = float(np.abs(verts_base[ref] - verts_render).max())
    if drift != 0.0:
        raise SystemExit(
            f"index map: max positional drift {drift} is not zero, so removing unattached "
            f"vertices is not order preserving and searchsorted is the wrong map."
        )
    return ref


def export(out_path):
    from pxr import Gf, Sdf, Usd, UsdGeom, Vt

    src = load_source()
    ref = build_index_map(src["faces_base"], src["verts_base"], src["verts_render"])
    n_base = src["verts_base"].shape[0]
    n_render = src["verts_render"].shape[0]

    # Faces, renumbered into renderable space.
    faces = np.searchsorted(ref, src["faces_base"])

    stage = Usd.Stage.CreateNew(str(out_path))
    UsdGeom.SetStageUpAxis(stage, UsdGeom.Tokens.z)
    UsdGeom.SetStageMetersPerUnit(stage, 1.0)
    root = UsdGeom.Xform.Define(stage, "/Hm08")
    stage.SetDefaultPrim(root.GetPrim())

    # --- the whole basemesh, every group, partition over all 19,158 --------------------
    quads = src["quads"]
    covered = np.unique(quads)
    if covered.size != n_base:
        raise SystemExit(
            f"basemesh: the face table references {covered.size} of {n_base} vertices. "
            f"An unreferenced vertex would fall through every mask."
        )
    base = UsdGeom.Mesh.Define(stage, "/Hm08/Basemesh")
    base.CreatePointsAttr(Vt.Vec3fArray.FromNumpy(src["verts_base"]))
    base.CreateFaceVertexIndicesAttr(Vt.IntArray.FromNumpy(quads.ravel().astype(np.int32)))
    base.CreateFaceVertexCountsAttr(
        Vt.IntArray.FromNumpy(np.full(quads.shape[0], 4, dtype=np.int32))
    )
    base.CreateSubdivisionSchemeAttr(UsdGeom.Tokens.none)
    base.CreatePurposeAttr(UsdGeom.Tokens.guide)

    bfam = "hm08_toplevel"
    for name in TOP_LEVEL:
        sub = UsdGeom.Subset.Define(stage, f"/Hm08/Basemesh/{name}")
        sub.CreateElementTypeAttr(UsdGeom.Tokens.point)
        sub.CreateFamilyNameAttr(bfam)
        sub.CreateIndicesAttr(
            Vt.IntArray.FromNumpy(members(src["groups"][name]).astype(np.int32))
        )
    UsdGeom.Subset.SetFamilyType(base, bfam, UsdGeom.Tokens.partition)

    gfam = "hm08_groups_by_range"
    for name, (lo, hi) in sorted(src["config"][GROUPS_BY_RANGE].items(), key=lambda kv: kv[1][0]):
        sub = UsdGeom.Subset.Define(stage, f"/Hm08/Basemesh/gbr_{name.replace('-', '_')}")
        sub.CreateElementTypeAttr(UsdGeom.Tokens.point)
        sub.CreateFamilyNameAttr(gfam)
        sub.CreateIndicesAttr(
            Vt.IntArray.FromNumpy(np.arange(lo, hi + 1, dtype=np.int32))
        )
    UsdGeom.Subset.SetFamilyType(base, gfam, UsdGeom.Tokens.nonOverlapping)

    mesh = UsdGeom.Mesh.Define(stage, "/Hm08/Body")
    mesh.CreatePointsAttr(Vt.Vec3fArray.FromNumpy(src["verts_render"]))
    mesh.CreateFaceVertexIndicesAttr(Vt.IntArray.FromNumpy(faces.ravel().astype(np.int32)))
    mesh.CreateFaceVertexCountsAttr(
        Vt.IntArray.FromNumpy(np.full(faces.shape[0], faces.shape[1], dtype=np.int32))
    )
    mesh.CreateSubdivisionSchemeAttr(UsdGeom.Tokens.none)

    if src["st"] is not None:
        api = UsdGeom.PrimvarsAPI(mesh)
        st = api.CreatePrimvar(
            "st", Sdf.ValueTypeNames.TexCoord2fArray, UsdGeom.Tokens.faceVarying
        )
        st.Set(Vt.Vec2fArray.FromNumpy(src["st"]))
        st.SetIndices(Vt.IntArray.FromNumpy(src["faces_render_uv"].ravel().astype(np.int32)))

    # --- the groups, as a validated partition -----------------------------------------
    #
    # Only groups with surviving vertices become subsets. A group whose vertices are all
    # unattached is recorded by name in metadata instead, because an empty subset would claim
    # the group is present and empty rather than absent.

    keep = np.zeros(n_base, dtype=bool)
    keep[ref] = True
    survivors, dropped, thinned = {}, {}, {}

    def account(name, m):
        """Record what a group lost. A partial loss is reported, not only a total one.

        The first version of this file recorded only groups that vanished entirely, so
        `body` losing 32 vertices did not appear anywhere. A silent partial loss reads
        exactly like a clean survival, which is the defect this repository is about."""
        alive = m[keep[m]]
        lost = int(m.size - alive.size)
        if alive.size == 0:
            dropped[name] = int(m.size)
        elif lost:
            thinned[name] = {"total": int(m.size), "lost": lost}
        return alive

    for name in TOP_LEVEL:
        alive = account(name, members(src["groups"][name]))
        if alive.size:
            survivors[name] = np.searchsorted(ref, alive)

    family = "hm08_toplevel"
    for name, idx in survivors.items():
        sub = UsdGeom.Subset.Define(stage, f"/Hm08/Body/{name}")
        sub.CreateElementTypeAttr(UsdGeom.Tokens.point)
        sub.CreateFamilyNameAttr(family)
        sub.CreateIndicesAttr(Vt.IntArray.FromNumpy(idx.astype(np.int32)))
    UsdGeom.Subset.SetFamilyType(mesh, family, UsdGeom.Tokens.partition)

    # groups_by_range, the twelve. Written as their own family, which is deliberately NOT a
    # partition, because Hm08Partition.lean proves it is not one.
    gbr = "hm08_groups_by_range"
    for name, (lo, hi) in sorted(src["config"][GROUPS_BY_RANGE].items(), key=lambda kv: kv[1][0]):
        alive = account(name, np.arange(lo, hi + 1, dtype=np.int64))
        if not alive.size:
            continue
        sub = UsdGeom.Subset.Define(stage, f"/Hm08/Body/gbr_{name.replace('-', '_')}")
        sub.CreateElementTypeAttr(UsdGeom.Tokens.point)
        sub.CreateFamilyNameAttr(gbr)
        sub.CreateIndicesAttr(Vt.IntArray.FromNumpy(np.searchsorted(ref, alive).astype(np.int32)))
    UsdGeom.Subset.SetFamilyType(mesh, gbr, UsdGeom.Tokens.nonOverlapping)

    # --- provenance, so a consumer can prove which topology this is --------------------
    prim = root.GetPrim()
    face_hash = hashlib.sha256(np.ascontiguousarray(src["faces_base"]).tobytes()).hexdigest()
    prim.SetCustomDataByKey("hm08:basemeshVertexCount", n_base)
    prim.SetCustomDataByKey("hm08:renderableVertexCount", n_render)
    prim.SetCustomDataByKey("hm08:basemeshFaceSha256", face_hash)
    prim.SetCustomDataByKey("hm08:basemeshQuadCount", int(quads.shape[0]))
    # Named for the prim they describe. The basemesh loses nothing, so an unqualified
    # "dropped" would read as a claim about the topology rather than about the submodel.
    prim.SetCustomDataByKey("hm08:bodySubmodelDroppedGroups", json.dumps(dropped, sort_keys=True))
    prim.SetCustomDataByKey("hm08:bodySubmodelThinnedGroups", json.dumps(thinned, sort_keys=True))
    prim.SetCustomDataByKey(
        "hm08:note",
        "Vertex order is frozen. coco.pth weights are per-index and hm08 groups are ranges, "
        "so a permutation keeps the count and moves every keypoint. See RFD 0121.",
    )

    stage.GetRootLayer().Save()
    return dict(
        out=str(out_path),
        base=n_base,
        render=n_render,
        faces=int(faces.shape[0]),
        subsets=len(survivors),
        dropped=dropped,
        thinned=thinned,
        face_hash=face_hash,
        uv=None if src["st"] is None else list(src["st"].shape),
        quads=int(quads.shape[0]),
    )


def check(path):
    """Re-open and validate. Imports no ANNY, so it runs anywhere the layer goes."""
    from pxr import Usd, UsdGeom

    stage = Usd.Stage.Open(str(path))
    mesh = UsdGeom.Mesh(stage.GetPrimAtPath("/Hm08/Body"))
    if not mesh:
        print("FAIL no mesh at /Hm08/Body")
        return 1

    n = len(mesh.GetPointsAttr().Get())
    failures = []
    basemesh = UsdGeom.Mesh(stage.GetPrimAtPath("/Hm08/Basemesh"))
    nb = len(basemesh.GetPointsAttr().Get())
    for prim_, count, family, expected in (
        (basemesh, nb, "hm08_toplevel", UsdGeom.Tokens.partition),
        (basemesh, nb, "hm08_groups_by_range", UsdGeom.Tokens.nonOverlapping),
        (mesh, n, "hm08_toplevel", UsdGeom.Tokens.partition),
        (mesh, n, "hm08_groups_by_range", UsdGeom.Tokens.nonOverlapping),
    ):
        subsets = UsdGeom.Subset.GetGeomSubsets(prim_, UsdGeom.Tokens.point, family)
        # Read the family type off the prim under test. The first version read it off
        # `mesh` every time, so relaxing Basemesh's family type was invisible and the
        # layer validated while making no partition claim at all. The negative control
        # for exactly that case is what found it.
        got = UsdGeom.Subset.GetFamilyType(prim_, family)
        ok, reason = UsdGeom.Subset.ValidateSubsets(subsets, elementCount=count, familyType=got)
        mark = "ok  " if ok else "FAIL"
        where = prim_.GetPath().name
        print(f"  {mark} {where}/{family}: {len(subsets)} subsets, "
              f"familyType={got}, {reason or 'valid'}")
        if got != expected:
            failures.append(f"{where}/{family}: familyType is {got}, expected {expected}")
        if not ok:
            failures.append(f"{where}/{family}: {reason}")

    prim = stage.GetPrimAtPath("/Hm08")
    for key in ("hm08:basemeshVertexCount", "hm08:basemeshFaceSha256"):
        if prim.GetCustomDataByKey(key) is None:
            failures.append(f"provenance: {key} is missing")
    print(f"  ok   provenance: basemesh {prim.GetCustomDataByKey('hm08:basemeshVertexCount')} "
          f"verts, faces {str(prim.GetCustomDataByKey('hm08:basemeshFaceSha256'))[:16]}...")

    if failures:
        for f in failures:
            print(f"  FAIL {f}")
        return 1
    print("\nThe layer validates. The top-level family is a partition, as Lean proves.")
    return 0


# --- negative controls ----------------------------------------------------------------
#
# `check` calls USD's own ValidateSubsets, so a passing run proves USD agrees with itself.
# It does not prove that a broken layer would be caught here. Each control below breaks the
# layer a different way, and each must make `check` fail.


def self_test(path):
    from pxr import Usd, UsdGeom, Vt
    import numpy as np

    def _drop_group(stage):
        """Remove JointCubes from the partition. 1,000 vertices then belong to nothing."""
        stage.RemovePrim("/Hm08/Basemesh/JointCubes")

    def _overlap(stage):
        """Make body claim a vertex HelperGeometry already owns."""
        sub = UsdGeom.Subset(stage.GetPrimAtPath("/Hm08/Basemesh/body"))
        idx = np.asarray(sub.GetIndicesAttr().Get())
        sub.GetIndicesAttr().Set(Vt.IntArray.FromNumpy(np.append(idx, 13380).astype(np.int32)))

    def _relax_family(stage):
        """Downgrade the family type. The partition claim quietly stops being made."""
        base = UsdGeom.Mesh(stage.GetPrimAtPath("/Hm08/Basemesh"))
        UsdGeom.Subset.SetFamilyType(base, "hm08_toplevel", UsdGeom.Tokens.unrestricted)

    def _strip_provenance(stage):
        """Remove the face hash. The layer no longer says which topology it holds."""
        stage.GetPrimAtPath("/Hm08").ClearCustomDataByKey("hm08:basemeshFaceSha256")

    controls = [
        ("JointCubes removed from the partition", _drop_group),
        ("body overlaps HelperGeometry", _overlap),
        ("family type relaxed to unrestricted", _relax_family),
        ("provenance hash stripped", _strip_provenance),
    ]

    print("negative controls (each must FAIL):")
    bad = []
    for i, (label, mutate) in enumerate(controls):
        # A unique path per control, deliberately. USD caches stages by identifier, so
        # reusing one filename hands the next control the previous one's mutated stage.
        # The first version of this did that. Every control still reported FAIL, so it
        # looked correct, and three of the four were reporting the second one's defect.
        # A control that fires for the wrong reason proves nothing.
        tmp = pathlib.Path(f"{path}.control{i}.usda")
        tmp.unlink(missing_ok=True)
        Usd.Stage.Open(str(path)).Export(str(tmp))
        st = Usd.Stage.Open(str(tmp))
        mutate(st)
        st.GetRootLayer().Save()
        import contextlib, io as _io
        buf = _io.StringIO()
        with contextlib.redirect_stdout(buf):
            rc = check(tmp)
        tmp.unlink(missing_ok=True)
        if rc:
            first = next((ln.strip() for ln in buf.getvalue().splitlines() if "FAIL" in ln), "")
            print(f"  ok   {label} -> caught: {first}")
        else:
            print(f"  FAIL {label} -> passed, so the check is decoration")
            bad.append(label)
    return bad


def main(argv):
    if argv and argv[0] == "--self-test":
        target = pathlib.Path(argv[1] if len(argv) > 1 else DEFAULT_OUT)
        bad = self_test(target)
        print()
        if bad:
            print(f"{len(bad)} control(s) did not fail. The validator is not gating.")
            return 1
        return check(target)
    if argv and argv[0] == "--check":
        return check(argv[1] if len(argv) > 1 else DEFAULT_OUT)
    out = pathlib.Path(argv[0] if argv else DEFAULT_OUT)
    if out.exists():
        out.unlink()
    info = export(out)
    print(f"wrote {info['out']}")
    print(f"  basemesh    {info['base']} vertices, faces sha256 {info['face_hash'][:16]}...")
    print(f"  basemesh    {info['quads']} quads, all {info['base']} vertices referenced")
    print(f"  body        {info['render']} vertices, {info['faces']} triangles")
    print(f"  uv          {info['uv']}")
    print(f"  subsets     {info['subsets']} in the partition family")
    print(f"  body drops  {info['dropped']}")
    print(f"  body thins  {info['thinned']}")
    print("              (both are about /Hm08/Body only. The basemesh keeps every group.)")
    print()
    return check(out)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
