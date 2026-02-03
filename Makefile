# F* Makefile - Build system using dune
#
# Prerequisites:
#   - OCaml 4.14+ with opam
#   - Run 'make install-deps' once to install OCaml dependencies
#   - Python 3 (for version generation)
#   - Z3 theorem prover in PATH
#
# Quick start:
#   make install-deps   # install OCaml dependencies (once)
#   make                # build F* compiler

.PHONY: all build test clean distclean install install-deps help
.PHONY: stage0 stage1 stage2 extract 0 1 2
.PHONY: package package-src save bump-stage0 unit-tests

# Default goal
FSTAR_DEFAULT_GOAL ?= build
.DEFAULT_GOAL := $(FSTAR_DEFAULT_GOAL)

# Number of parallel jobs (default: number of CPUs)
JOBS ?= $(shell nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 4)

# Platform-specific commands
ifeq ($(OS),Windows_NT)
  RM = powershell -Command "Remove-Item -Recurse -Force -ErrorAction SilentlyContinue"
  MKDIR = powershell -Command "New-Item -ItemType Directory -Force"
  ECHO = echo
else
  RM = rm -rf
  MKDIR = mkdir -p
  ECHO = echo
endif

# =============================================================================
# Dependency Installation
# =============================================================================

install-deps:
	opam install --deps-only ./fstar.opam

# =============================================================================
# Main Build Rules
# =============================================================================

all: build

# Build dependencies: stage0 -> extract -> stage1 -> stage2
# These must be sequential, not parallel
build: stage2

# Explicit dependencies for parallel-safe builds
extract: stage0
stage1: extract
stage2: stage1

test:
	dune runtest

clean:
	dune clean
	-dune clean --root=stage0
	-$(RM) stage0/out
	-$(RM) _deps.txt

distclean: clean
	-$(RM) _build
	-$(RM) stage0/_build

# =============================================================================
# Stage Rules
# =============================================================================

# Path to stage0 fstar executable (absolute path for dune)
FSTAR_STAGE0 := $(CURDIR)/stage0/out/bin/fstar.exe
export FSTAR_EXE := $(FSTAR_STAGE0)

# Stage 0: Bootstrap compiler from OCaml snapshot
stage0 0:
	dune build --root=stage0 @install
	dune install --root=stage0 --prefix=$(CURDIR)/stage0/out

# Extract: Generate stage1 ML files from F* sources
extract:
	dune build @extract-stage1

# Stage 1: Build stage1 compiler library
stage1 1:
	dune build @stage1

# Stage 2: Build final compiler with plugins
stage2 2:
	dune build @stage2

# =============================================================================
# Packaging Rules
# =============================================================================

package: build
	dune build @packaging/package

package-src: build
	dune build @packaging/package-src

install: build
	dune build @packaging/install-fstar

# =============================================================================
# Maintenance Rules
# =============================================================================

save:
	dune build @packaging/save

bump-stage0:
	dune build @packaging/bump-stage0

unit-tests:
	dune runtest tests/micro-benchmarks

# =============================================================================
# Help
# =============================================================================

help:
	@$(ECHO) "F* Build System (dune)"
	@$(ECHO) ""
	@$(ECHO) "Setup:"
	@$(ECHO) "  install-deps       install OCaml dependencies via opam"
	@$(ECHO) ""
	@$(ECHO) "Main rules:"
	@$(ECHO) "  build              build the compiler (default)"
	@$(ECHO) "  test               run tests"
	@$(ECHO) "  clean              clean build artifacts"
	@$(ECHO) "  distclean          remove all generated files"
	@$(ECHO) "  install            install F* to system"
	@$(ECHO) ""
	@$(ECHO) "Stage rules (for F* hackers):"
	@$(ECHO) "  stage0 / 0         build stage0 (bootstrap) compiler"
	@$(ECHO) "  extract            extract stage1 ML from F* sources"
	@$(ECHO) "  stage1 / 1         build stage1 compiler library"
	@$(ECHO) "  stage2 / 2         build stage2 (final) compiler"
	@$(ECHO) ""
	@$(ECHO) "Packaging rules:"
	@$(ECHO) "  package            create binary distribution"
	@$(ECHO) "  package-src        create source distribution"
	@$(ECHO) ""
	@$(ECHO) "Maintenance rules:"
	@$(ECHO) "  save               snapshot stage2 to stage0_new"
	@$(ECHO) "  bump-stage0        replace stage0 with snapshot"
	@$(ECHO) "  unit-tests         run unit tests only"
	@$(ECHO) ""
	@$(ECHO) "Prerequisites:"
	@$(ECHO) "  - OCaml 4.14+ with opam"
	@$(ECHO) "  - Python 3"
	@$(ECHO) "  - Z3 theorem prover"
