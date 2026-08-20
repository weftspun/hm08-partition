# hm08-partition

What the hm08 vertex groups cover, stated in Lean 4 and checked against the data.

`Hm08Partition.lean` proves that `body`, `HelperGeometry` and `JointCubes` partition all
19,158 vertices with no overlap and no gap, and that `hm08_config.json`'s twelve
`groups_by_range` entries do not. A mask built from the three has no holes. A mask built from
the twelve does.

`check_hm08_claims.py` re-derives every constant in the Lean file from the installed ANNY
package, with six negative controls that each must fail. A proof assistant cannot notice that
a definition disagrees with a JSON file it never reads, which is how the first version of this
file came to prove every theorem it stated while being wrong about the size of the mesh.

`export_hm08_usd.py` writes the topology and its groups to an OpenUSD layer, per RFD 0053.
`UsdGeomSubset` carries a `partition` family type that USD validates, so the property the Lean
file proves is enforced by the data format rather than argued in a comment.

## Build and check

```sh
lake build                                  # 847 jobs, no sorry
python check_hm08_claims.py                 # every constant against live ANNY data
python check_hm08_claims.py --self-test     # six negative controls, each must fail
python export_hm08_usd.py out.usda          # export, then validate the partition
python export_hm08_usd.py --self-test f     # four negative controls, each must fail
```

## Licence

Licensed under either of

* Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE))
* MIT License ([LICENSE-MIT](LICENSE-MIT))

at your option.

`SPDX-License-Identifier: Apache-2.0 OR MIT`

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion
in this work by you shall be dual licensed as above, without any additional terms or
conditions.
