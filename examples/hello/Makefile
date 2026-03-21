# This Makefile exists only to set FSTAR_EXE for dune, so it uses our
# locally-built F* binary instead of whatever is in the environment.
# Dune's env-vars mechanism does not support variable expansion, so we
# must set FSTAR_EXE externally.

FSTAR_ROOT ?= ../..
FSTAR_EXE ?= $(FSTAR_ROOT)/out/bin/fstar.exe
FSTAR_EXE := $(abspath $(FSTAR_EXE))
export FSTAR_EXE

.PHONY: all clean

all:
	FSTAR_EXE=$(FSTAR_EXE) $(FSTAR_EXE) --ocamlenv dune build

clean:
	dune clean
