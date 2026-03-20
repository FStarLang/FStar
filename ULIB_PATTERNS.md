# ulib {:nopattern} Tightening Plan

Goal: Replace `{:nopattern}` with explicit `{:pattern}` wherever possible in ulib `.fsti` files (highest impact) and `.fst` files. After each change, verify ulib (349 files) and `make test-3` pass.

## Priority 1: High-impact .fsti files

These are interfaces used by many downstream clients. Explicit patterns here benefit the entire ecosystem.

- [x] `FStar.Seq.Properties.fsti` (34 → 5) — done
- [x] `FStar.List.Tot.Properties.fsti` (42 → 14) — largest, many `mem`/`count`/`index` quantifiers
- [ ] `FStar.Classical.fsti` (19) — `forall_intro`, `exists_elim`, `move_requires` lemmas
- [ ] `FStar.Pervasives.fsti` (15) — WP definitions (st/ex/all effects)
- [ ] `FStar.Matrix.fsti` (8) — matrix indexing quantifiers
- [ ] `FStar.FiniteMap.Base.fsti` (5) — map membership/equality
- [ ] `FStar.FiniteSet.Base.fsti` (3) — set membership
- [ ] `FStar.Set.fsti` (4) — set subset/equality  
- [ ] `FStar.TSet.fsti` (4) — same as Set
- [ ] `FStar.GSet.fsti` (4) — same
- [ ] `FStar.GhostSet.fsti` (4) — same
- [ ] `FStar.Map.fsti` (2) — map domain/equality
- [ ] `FStar.Math.Euclid.fsti` (2) — divides, is_gcd
- [ ] `FStar.Monotonic.Witnessed.fsti` (3) — witnessed/stable
- [ ] `FStar.PartialMap.fsti` (1)
- [ ] `FStar.DependentMap.fsti` (1)
- [ ] `FStar.UInt.fsti` (1)
- [ ] `FStar.Int.fsti` (1)

## Priority 2: .fst implementation files

Less impactful (patterns only affect the module itself and its checked file), but still valuable.

- [x] `FStar.Seq.Properties.fst` (9 → 4) — done
- [x] `FStar.Seq.Base.fst` (4 → 0) — done
- [ ] SKIP THIS TOO LOW IMPACT FOR THE RISK `FStar.Monotonic.Witnessed.fst` (30) — many witnessed/stable quantifiers
- [ ] `FStar.OrdSet.fst` (24) — ordered set operations
- [ ] SKIP THIS TOO LOW IMPACT FOR THE RISK `FStar.Monotonic.Heap.fst` (16) — heap axiom quantifiers
- [ ] SKIP THIS HIGH PROBABILITY OF BREAKAGE `Prims.fst` (9) — core WP definitions
- [ ] `FStar.Classical.fst` (8)
- [ ] HIGH IMPACT `FStar.PCM.fst` (5) — composable/compatible
- [ ] `FStar.ST.fst` (3) — heap_rel, stable
- [ ] `FStar.OrdMap.fst` (2)
- [ ] `FStar.OrdSetProps.fst` (1)
- [ ] `FStar.Int.fst` (1)
- [ ] `FStar.DependentMap.fst` (1)

## Verification protocol

After each file change:
1. Rebuild ulib: `rm -rf stage2/ulib.checked && mkdir -p stage2/ulib.checked && env SRC=ulib/ FSTAR_EXE=stage3/out/bin/fstar.exe CACHE_DIR=stage2/ulib.checked/ OUTPUT_DIR=stage2/ulib.ml/ CODEGEN=OCaml TAG=lib OTHERFLAGS="--warn_error -271" TOUCH=.alib.src.touch make -f mk/lib.mk verify -j16 -sk`
2. Check 349/349 pass
3. Spot-check key downstream targets
4. If regression found, revert the specific pattern and keep as `{:nopattern}`
5. Eventually get the whole repo to build with make test