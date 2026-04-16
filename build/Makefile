# ============================================================================
# build/Makefile — Thin portable orchestrator for F* staged dune build
# ============================================================================
#
# Entry point for building F*. Works on Linux, macOS, and Windows.
#
# Usage:
#   opam install .              # installs deps + builds + installs F*
#   make -C build               # just build (assumes deps installed)
#   make -C build ADMIT=1       # skip SMT verification
#   make -C build install PREFIX=/usr/local
#
# Chain: opam deps → make → dune build (staged)

FSROOT := $(abspath ..)

EXE := .exe
DUNE := dune
DUNE_FLAGS := --root=.

# Pass ADMIT=1 to skip verification (admit all SMT queries)
ifeq ($(ADMIT),1)
export FSTAR_ADMIT := --admit_smt_queries true
endif

# Stage 0: pre-built compiler
FSTAR0 := $(FSROOT)/stage0/out/bin/fstar$(EXE)

# Stage 1 outputs (inside _build)
FSTARC1_BARE := $(abspath _build/default/stage1-ocaml/fstarc1_bare$(EXE))
FSTARC1_FULL := $(abspath _build/default/stage1-plugins-ocaml/fstarc1_full$(EXE))

# Stage 2 outputs
FSTARC2_BARE := $(abspath _build/default/stage2-ocaml/fstarc2_bare$(EXE))
FSTARC2_FULL := $(abspath _build/default/stage2-plugins-ocaml/fstarc2_full$(EXE))

.PHONY: all stage0 stage1-bare stage1-full stage2-bare stage2-full install clean

.DEFAULT_GOAL := stage2-full

# === Stage 0 ===
stage0: $(FSTAR0)

$(FSTAR0):
	$(DUNE) build --root=$(FSROOT)/stage0/dune
	$(DUNE) install --root=$(FSROOT)/stage0/dune --prefix=$(FSROOT)/stage0/out

# === Stage 1: bare compiler ===
stage1-bare: $(FSTARC1_BARE)

$(FSTARC1_BARE): $(FSTAR0)
	@echo "  EXTRACT  stage1 FStarC (using fstar0)"
	FSTAR0_EXE=$(FSTAR0) FSTAR1_EXE=$(FSTAR0) FSTAR1F_EXE=$(FSTAR0) FSTAR2_EXE=$(FSTAR0) \
	  $(DUNE) build $(DUNE_FLAGS) @stage1 stage1-ocaml/fstarc1_bare$(EXE)

# === Stage 1: plugins + full compiler ===
stage1-full: $(FSTARC1_FULL)

$(FSTARC1_FULL): $(FSTARC1_BARE)
	@echo "  EXTRACT  stage1 plugins + BUILD fstarc1_full"
	FSTAR0_EXE=$(FSTAR0) FSTAR1_EXE=$(FSTARC1_BARE) FSTAR1F_EXE=$(FSTARC1_BARE) FSTAR2_EXE=$(FSTARC1_BARE) \
	  $(DUNE) build $(DUNE_FLAGS) @stage1-plugins stage1-plugins-ocaml/fstarc1_full$(EXE)

# === Stage 2: bare compiler ===
stage2-bare: $(FSTARC2_BARE)

$(FSTARC2_BARE): $(FSTARC1_FULL)
	@echo "  EXTRACT  stage2 FStarC + BUILD fstarc2_bare"
	FSTAR0_EXE=$(FSTAR0) FSTAR1_EXE=$(FSTARC1_BARE) \
	FSTAR1F_EXE=$(FSTARC1_FULL) FSTAR2_EXE=$(FSTARC1_FULL) \
	  $(DUNE) build $(DUNE_FLAGS) @stage2 stage2-ocaml/fstarc2_bare$(EXE)

# === Stage 2: plugins + full compiler ===
stage2-full: $(FSTARC2_FULL)

$(FSTARC2_FULL): $(FSTARC2_BARE)
	@echo "  EXTRACT  stage2 plugins + BUILD fstarc2_full"
	FSTAR0_EXE=$(FSTAR0) FSTAR1_EXE=$(FSTARC1_BARE) \
	FSTAR1F_EXE=$(FSTARC1_FULL) FSTAR2_EXE=$(FSTARC2_BARE) \
	  $(DUNE) build $(DUNE_FLAGS) @stage2-plugins stage2-plugins-ocaml/fstarc2_full$(EXE)

# === Install ===
PREFIX ?= /usr/local
install: stage2-full
	mkdir -p $(PREFIX)/bin
	cp $(FSTARC2_FULL) $(PREFIX)/bin/fstar$(EXE)
	mkdir -p $(PREFIX)/lib/fstar
	cp -r $(FSROOT)/ulib $(PREFIX)/lib/fstar/ulib

# === Convenience ===
all: stage2-full

clean:
	$(DUNE) clean $(DUNE_FLAGS)
	rm -f .opam-deps.stamp
