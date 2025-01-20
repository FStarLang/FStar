# fstardoc

A tool for nicely extract documentation for F* files

## How to Run

```
python3 fstardoc.py {path to fst/fsti file}
```

## Running regression tests

```
make
```

## Getting latest version of the tool

```
make update-to-latest
```

## Makefile

The snippet below used to be in ulib/Makefile

        DOC_FILES=Prims.fst FStar.Pervasives.Native.fst FStar.Pervasives.fst \
              FStar.Squash.fsti FStar.Classical.fsti FStar.BigOps.fsti \
              FStar.BitVector.fst FStar.BV.fsti \
              FStar.Char.fsti FStar.Date.fsti FStar.DependentMap.fsti \
              FStar.Dyn.fsti FStar.Exn.fst FStar.Fin.fst FStar.Float.fsti \
              FStar.FunctionalExtensionality.fsti FStar.Float.fsti \
              FStar.Ghost.fsti FStar.IFC.fsti FStar.IndefiniteDescription.fst \
              FStar.UInt8.fst FStar.UInt16.fst FStar.UInt32.fst FStar.UInt64.fst

        DOC_DIR=./doc

        fstardoc: $(DOC_DIR) $(addprefix $(DOC_DIR)/, $(addsuffix .md, $(DOC_FILES)))

        $(DOC_DIR):
            mkdir -p $@

        $(DOC_DIR)/%.md: %
            ../bin/fstar --print_in_place $^
            python3 ../.scripts/fstardoc/fstardoc.py $^ > $@
