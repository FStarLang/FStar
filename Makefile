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
.PHONY: stage0 stage1 stage2 extract 0 1 2 verify-ulib
.PHONY: package package-src save bump-stage0 unit-tests

# Default goal
FSTAR_DEFAULT_GOAL ?= all
.DEFAULT_GOAL := $(FSTAR_DEFAULT_GOAL)

# Number of parallel jobs (default: number of CPUs)
JOBS ?= $(shell nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 4)

# Platform-specific commands
ifeq ($(OS),Windows_NT)
  RM = powershell -Command "Remove-Item -Recurse -Force -ErrorAction SilentlyContinue"
  MKDIR = powershell -Command "New-Item -ItemType Directory -Force -Path"
  CP = powershell -Command "Copy-Item -Recurse -Force"
  ECHO = echo
  # Windows uses .exe suffix
  FSTAR_EXE_ABS = $(CURDIR)/stage0/out/bin/fstar.exe
else
  RM = rm -rf
  MKDIR = mkdir -p
  CP = cp -r
  ECHO = echo
  # Unix: binary is just 'fstar' (no .exe suffix)
  FSTAR_EXE_ABS = $(shell pwd)/stage0/out/bin/fstar
endif

# Export FSTAR_EXE for dune (used in fstarc.dune.inc for .checked file generation)
export FSTAR_EXE := $(FSTAR_EXE_ABS)

# =============================================================================
# Dependency Installation
# =============================================================================

install-deps:
	opam install --deps-only ./fstar.opam

# =============================================================================
# Main Build Rules
# =============================================================================

all: build setlink-2

# Build depends on stage2, which chains to stage1 -> extract -> stage0
build: stage2

test:
	dune runtest --root=.

clean:
	dune clean --root=.
	-dune clean --root=stage0
	-$(RM) stage0/out
	-$(RM) _deps.txt
	-$(RM) src/extracted/fstarc.dune.inc

distclean: clean
	-$(RM) _build
	-$(RM) stage0/_build

# =============================================================================
# Stage Rules
# =============================================================================

# Stage 0: Bootstrap compiler from OCaml snapshot
# Note: dune install runs from stage0/, so prefix is relative to that
stage0 0:
	dune build --root=stage0
	dune install --root=stage0 --prefix=out

# Extract: Generate stage1 ML files from F* sources
# First generate fstarc.dune.inc (dune needs it to parse src/extracted/dune)
# Depends on stage0 for fstar.exe
# FSTAR_EXE is exported at top with platform-specific path
# Use --root=. to prevent dune from finding parent dune-project (e.g., in opam build)
extract: stage0
	$(FSTAR_EXE) --lax --MLish --MLish_effect FStarC.Effect --dep dune \
		--include ulib --include src/basic --include src/class \
		--include src/data --include src/extraction --include src/fstar \
		--include src/interactive --include src/parser --include src/prettyprint \
		--include src/reflection --include src/smtencoding --include src/syntax \
		--include src/syntax/print --include src/tactics --include src/tosyntax \
		--include src/typechecker --include src/tests \
		--extract FStarC --extract +FStar.Pervasives \
		--extract -FStar.Pervasives.Native --extract "krml:-*" \
		src/fstar/FStarC.Main.fst > src/extracted/fstarc.dune.inc
	dune build --root=. @extract-stage1

# Stage 1: Build stage1 compiler library
# Depends on extract for generated ML files
# Also copies plugin files from stage0 to src/plugins for stage2
stage1 1: extract
	$(MKDIR) src/plugins/app
	$(MKDIR) src/plugins/plugin
	$(MKDIR) src/plugins/plugins.ml
	$(CP) stage0/fstar-plugins/app/* src/plugins/app/
	$(CP) stage0/fstar-plugins/plugin/* src/plugins/plugin/
	$(CP) stage0/fstar-plugins/plugins.ml/* src/plugins/plugins.ml/
	dune build --root=. @stage1

# Stage 2: Build final compiler with plugins
# Depends on stage1 for compiler library
stage2 2: stage1
	dune build --root=. @stage2

# Verify ulib using stage2 compiler
# Uses --dep dune directory support to enumerate all ulib files
# The .checked files are cached in ulib/ for use by downstream projects
FSTAR2_EXE = _build/default/src/stage2/fstar.exe
verify-ulib: stage2 setlink-2
	@echo "=== Verifying ulib ==="
	$(FSTAR2_EXE) \
		--warn_error -241 --warn_error -318 --warn_error -328 \
		--cache_dir ulib \
		--include ulib --include ulib/experimental --include ulib/legacy \
		--already_cached "*," \
		ulib
	@echo "=== ulib verification complete ==="

# Set up symlinks/directories for compatibility with CI and tests
# Creates out/bin/fstar and out/lib/fstar/ulib for the smoke test
setlink-%:
ifeq ($(OS),Windows_NT)
	@if exist out if not exist out\NUL (echo ERROR: out/ exists and is not a directory, please remove it && exit 1)
	-@$(RM) out
	@$(MKDIR) out/bin
	@$(CP) _build/default/src/stage2/fstar.exe out/bin/
	@$(MKDIR) out/lib/fstar
	@if exist ulib (mklink /D out\lib\fstar\ulib "$(CURDIR)\ulib" 2>nul || xcopy /E /I /Q ulib out\lib\fstar\ulib)
	@$(MKDIR) bin
	@$(CP) out/bin/fstar.exe bin/
else
	@if [ -e out ] && ! [ -h out ]; then echo "ERROR: out/ exists and is not a symbolic link, please remove it"; false; fi
	rm -rf out && mkdir -p out/bin out/lib/fstar
	@# dune always produces .exe suffix for native executables, link to that
	ln -sf $(CURDIR)/_build/default/src/stage2/fstar.exe out/bin/fstar
	ln -sf $(CURDIR)/ulib out/lib/fstar/ulib
	mkdir -p bin
	ln -sf $(CURDIR)/out/bin/fstar bin/fstar
endif

# =============================================================================
# Packaging Rules
# =============================================================================

# PREFIX for install (default: out/)
PREFIX ?= out

# FSTAR_TAG: suffix for package name (e.g., -Linux-x86_64). If empty, creates fstar.tar.gz
# Used by CI to create a simpler package name.
FSTAR_TAG ?= auto

# Binary package - creates fstar{FSTAR_TAG}.tar.gz or .zip
package: build
ifeq ($(OS),Windows_NT)
	-@powershell -Command "Remove-Item -Recurse -Force _package -ErrorAction SilentlyContinue"
	@powershell -Command "New-Item -ItemType Directory -Force _package/fstar/bin | Out-Null"
	@powershell -Command "New-Item -ItemType Directory -Force _package/fstar/lib/fstar | Out-Null"
	@powershell -Command "Copy-Item _build/default/src/stage2/fstar.exe _package/fstar/bin/"
	@powershell -Command "Copy-Item -Recurse ulib _package/fstar/lib/fstar/"
	@powershell -Command "'ulib' | Out-File -FilePath '_package/fstar/lib/fstar/fstar.include' -Encoding utf8"
	@powershell -Command "Copy-Item LICENSE,README.md,INSTALL.md,version.txt _package/fstar/"
	@powershell -Command "$$v = (Get-Content version.txt -Raw).Trim(); Compress-Archive -Path _package/fstar -DestinationPath \"fstar-v$$v-Windows_x64.zip\" -Force; Write-Host \"Created: fstar-v$$v-Windows_x64.zip\""
	@powershell -Command "Remove-Item -Recurse -Force _package"
else
	@rm -rf _package
	@mkdir -p _package/fstar/bin _package/fstar/lib/fstar
	@cp _build/default/src/stage2/fstar.exe _package/fstar/bin/fstar 2>/dev/null || \
		cp _build/default/src/stage2/fstar _package/fstar/bin/fstar
	@cp -r ulib _package/fstar/lib/fstar/
	@echo 'ulib' > _package/fstar/lib/fstar/fstar.include
	@cp LICENSE README.md INSTALL.md version.txt _package/fstar/
ifeq ($(FSTAR_TAG),)
	@cd _package && tar czf ../fstar.tar.gz fstar && echo "Created: fstar.tar.gz"
else ifeq ($(FSTAR_TAG),auto)
	@VERSION=$$(cat version.txt | tr -d '\n\r'); \
		ARCH=$$(uname -m); \
		OS=$$(uname -s); \
		case "$$OS" in Darwin) OS=macOS ;; esac; \
		cd _package && tar czf ../fstar-v$${VERSION}-$${OS}_$${ARCH}.tar.gz fstar && \
		echo "Created: fstar-v$${VERSION}-$${OS}_$${ARCH}.tar.gz"
else
	@cd _package && tar czf ../fstar$(FSTAR_TAG).tar.gz fstar && echo "Created: fstar$(FSTAR_TAG).tar.gz"
endif
	@rm -rf _package
endif

# Source package - creates fstar-src.tar.gz (if FSTAR_TAG=) or fstar-v{VERSION}-src.tar.gz
package-src: build
ifeq ($(OS),Windows_NT)
	-@powershell -Command "Remove-Item -Recurse -Force _srcpackage -ErrorAction SilentlyContinue"
	@powershell -Command "New-Item -ItemType Directory -Force _srcpackage/fstar | Out-Null"
	@powershell -Command "Copy-Item -Recurse stage0,src,ulib,.scripts _srcpackage/fstar/"
	@powershell -Command "Copy-Item dune,dune-project,dune-workspace,fstar.opam,Makefile _srcpackage/fstar/"
	@powershell -Command "Copy-Item LICENSE,README.md,INSTALL.md,version.txt _srcpackage/fstar/"
	-@powershell -Command "Get-ChildItem -Path _srcpackage -Recurse -Directory -Filter '_build' | Remove-Item -Recurse -Force"
	-@powershell -Command "Get-ChildItem -Path _srcpackage -Recurse -Filter '*.checked*' | Remove-Item -Force"
	@powershell -Command "$$v = (Get-Content version.txt -Raw).Trim(); Compress-Archive -Path _srcpackage/fstar -DestinationPath \"fstar-v$$v-src.zip\" -Force; Write-Host \"Created: fstar-v$$v-src.zip\""
	@powershell -Command "Remove-Item -Recurse -Force _srcpackage"
else
	@rm -rf _srcpackage
	@mkdir -p _srcpackage/fstar
	@cp -r stage0 src ulib .scripts _srcpackage/fstar/
	@cp dune dune-project dune-workspace fstar.opam Makefile _srcpackage/fstar/
	@cp LICENSE README.md INSTALL.md version.txt _srcpackage/fstar/
	@find _srcpackage -name '_build' -type d -exec rm -rf {} + 2>/dev/null || true
	@find _srcpackage -name '*.checked*' -delete 2>/dev/null || true
ifeq ($(FSTAR_TAG),)
	@cd _srcpackage && tar czf ../fstar-src.tar.gz fstar && echo "Created: fstar-src.tar.gz"
else
	@VERSION=$$(cat version.txt | tr -d '\n\r'); \
		cd _srcpackage && tar czf ../fstar-v$${VERSION}-src.tar.gz fstar && \
		echo "Created: fstar-v$${VERSION}-src.tar.gz"
endif
	@rm -rf _srcpackage
endif

# Install F* to PREFIX (used by opam install)
install: build
ifeq ($(OS),Windows_NT)
	powershell -Command "New-Item -ItemType Directory -Force -Path '$(PREFIX)/bin' | Out-Null"
	powershell -Command "New-Item -ItemType Directory -Force -Path '$(PREFIX)/lib/fstar' | Out-Null"
	powershell -Command "Copy-Item -Force '_build/default/src/stage2/fstar.exe' '$(PREFIX)/bin/'"
	powershell -Command "Copy-Item -Recurse -Force 'ulib' '$(PREFIX)/lib/fstar/'"
	powershell -Command "'ulib' | Out-File -FilePath '$(PREFIX)/lib/fstar/fstar.include' -Encoding utf8"
	powershell -Command "Copy-Item -Force 'LICENSE','README.md','INSTALL.md','version.txt' '$(PREFIX)/'"
else
	$(MKDIR) $(PREFIX)/bin $(PREFIX)/lib/fstar
	cp _build/default/src/stage2/fstar.exe $(PREFIX)/bin/fstar 2>/dev/null || \
		cp _build/default/src/stage2/fstar $(PREFIX)/bin/fstar
	$(CP) ulib $(PREFIX)/lib/fstar/
	echo 'ulib' > $(PREFIX)/lib/fstar/fstar.include
	cp LICENSE README.md INSTALL.md version.txt $(PREFIX)/
endif

# =============================================================================
# Test Rules (for CI compatibility)
# =============================================================================

# Stage 2 unit tests (micro-benchmarks)
stage2-unit-tests: stage2
	dune runtest tests/micro-benchmarks --root=.

# Test with bare compiler (no plugins) - uses dune
test-2-bare: stage2
	dune runtest bare-tests --root=.

# Full test suite
_test test: stage2
	dune runtest --root=.
.PHONY: _test test

# Stage 3 diff check (verify extraction is stable)
stage3-diff: stage2
	@echo "Stage 3 diff check not yet implemented in simplified build"
	@true

# F# library build
lib-fsharp: stage2
	@echo "F# library build not yet implemented in simplified build"
	@true

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
