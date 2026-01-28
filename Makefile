# F* Makefile - Wrapper for esy/dune build system
#
# This Makefile provides backward compatibility with the legacy build commands.
# All commands delegate to esy, which uses dune for the actual build.
#
# Prerequisites:
#   - esy (install via: npm install -g esy)
#   - Run 'esy install' once to set up dependencies
#
# For direct dune usage, see package.json for available esy scripts.

.PHONY: all build test clean distclean install help
.PHONY: stage0 stage1 stage2 0 1 2
.PHONY: package package-src save bump-stage0 unit-tests

# Default goal
FSTAR_DEFAULT_GOAL ?= build
.DEFAULT_GOAL := $(FSTAR_DEFAULT_GOAL)

# =============================================================================
# Main Rules
# =============================================================================

build:
	esy build

test:
	esy test

clean:
	esy clean

distclean:
	esy distclean

install:
	esy install-fstar

# =============================================================================
# Stage Rules (for F* hackers)
# =============================================================================

stage0 0:
	esy stage0

stage1 1:
	esy stage1

stage2 2:
	esy stage2

# =============================================================================
# Packaging Rules
# =============================================================================

package:
	esy package

package-src:
	esy package-src

# =============================================================================
# Maintenance Rules
# =============================================================================

save:
	esy save

bump-stage0:
	esy bump-stage0

unit-tests:
	esy unit-tests

# =============================================================================
# Help
# =============================================================================

help:
	@echo "F* Build System (esy/dune)"
	@echo ""
	@echo "Main rules:"
	@echo "  build              build the compiler and libraries (default)"
	@echo "  test               run tests"
	@echo "  clean              clean build artifacts"
	@echo "  distclean          remove all generated files"
	@echo "  install            install F* to out/"
	@echo ""
	@echo "Stage rules (for F* hackers):"
	@echo "  stage0 / 0         build stage0 compiler"
	@echo "  stage1 / 1         build stage1 compiler"
	@echo "  stage2 / 2         build stage2 compiler (= build)"
	@echo ""
	@echo "Packaging rules:"
	@echo "  package            create binary distribution"
	@echo "  package-src        create source distribution"
	@echo ""
	@echo "Maintenance rules:"
	@echo "  save               snapshot stage2 to stage0_new"
	@echo "  bump-stage0        replace stage0 with snapshot"
	@echo "  unit-tests         run unit tests only"
	@echo ""
	@echo "Prerequisites:"
	@echo "  npm install -g esy   # install esy"
	@echo "  esy install          # install dependencies (run once)"
