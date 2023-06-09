include .common.mk

.PHONY: all
all: build-and-verify-ulib

DUNE_SNAPSHOT ?= $(call maybe_cygwin_path,$(CURDIR)/ocaml)

# The directory where we install files when doing "make install".
# Overridden via the command-line by the OPAM invocation.
PREFIX ?= /usr/local

# On Cygwin, the `--prefix` option to dune only
# supports Windows paths.
FSTAR_CURDIR=$(call maybe_cygwin_path,$(CURDIR))

FSTAR_BUILD_PROFILE ?= release

.PHONY: fstar
fstar:
	$(Q)cp version.txt $(DUNE_SNAPSHOT)/
	@# Call Dune to build the snapshot.
	@echo "  DUNE BUILD"
	$(Q)cd $(DUNE_SNAPSHOT) && dune build --profile=$(FSTAR_BUILD_PROFILE)
	@echo "  DUNE INSTALL"
	$(Q)cd $(DUNE_SNAPSHOT) && dune install --profile=$(FSTAR_BUILD_PROFILE) --prefix=$(FSTAR_CURDIR)

.PHONY: verify-ulib
verify-ulib:
	+$(Q)$(MAKE) -C ulib

.PHONY: build-and-verify-ulib
build-and-verify-ulib: fstar
	+$(Q)$(MAKE) verify-ulib

# Removes all generated files (including the whole generated snapshot,
# and .checked files), except the object files, so that the snapshot
# can be rebuilt with an existing fstar.exe
.PHONY: clean-snapshot
clean-snapshot: clean-intermediate
	$(call msg, "CLEAN SNAPSHOT")
	$(Q)cd $(DUNE_SNAPSHOT) && { dune clean || true ; }
	$(Q)rm -rf $(DUNE_SNAPSHOT)/fstar-lib/generated/*

.PHONY: extract-all
extract-all:
	+$(Q)$(MAKE) -C src/ocaml-output dune-snapshot

# This rule is not incremental, by design.
.PHONY: full-bootstrap
full-bootstrap:
	+$(Q)$(MAKE) fstar
	+$(Q)$(MAKE) clean-snapshot
	+$(Q)$(MAKE) bootstrap

.PHONY: bootstrap
bootstrap:
	+$(Q)$(MAKE) extract-all
	+$(Q)$(MAKE) fstar

.PHONY: boot
boot:
	+$(Q)$(MAKE) extract-all
	$(Q)cp version.txt $(DUNE_SNAPSHOT)/
	@# Call Dune to build the snapshot.
	$(call msg, "DUNE BUILD")
	$(Q)cd $(DUNE_SNAPSHOT) && dune build --profile release
	$(call msg, "RAW INSTALL")
	$(Q)cp ocaml/_build/default/fstar/main.exe $(FSTAR_CURDIR)/bin/fstar.exe

.PHONY: install
install:
	+$(Q)$(MAKE) -C src/ocaml-output install

# The `uninstall` rule is only necessary for users who manually ran
# `make install`. It is not needed if F* was installed with opam,
# since `opam remove` can uninstall packages automatically with its
# own way.

.PHONY: uninstall
uninstall:
	rm -rf \
	  $(PREFIX)/lib/fstar \
	  $(PREFIX)/bin/fstar_tests.exe \
	  $(PREFIX)/bin/fstar.exe \
	  $(PREFIX)/share/fstar

.PHONY: package
package: all
	+$(Q)$(MAKE) -C src/ocaml-output package

# Removes everything created by `make all`. MUST NOT be used when
# bootstrapping.
.PHONY: clean
clean: clean-intermediate clean-buildfiles
	$(call msg, "CLEAN")
	$(Q)cd $(DUNE_SNAPSHOT) && { dune uninstall --prefix=$(FSTAR_CURDIR) || true ; }

# Clean temporary dune build files, while retaining all checked files
# and installed files. Used to save space after building, particularly
# after CI. Note we have to keep fstar.install or otherwise `dune
# uninstall` cannot work.
.PHONY: clean-buildfiles
clean-buildfiles:
	$(call msg, "CLEAN BUILDFILES")
	$(Q)cp -f $(DUNE_SNAPSHOT)/_build/default/fstar.install ._fstar.install
	$(Q)cd $(DUNE_SNAPSHOT) && { dune clean || true ; }
	$(Q)mkdir -p $(DUNE_SNAPSHOT)/_build/default/
	$(Q)cp -f ._fstar.install $(DUNE_SNAPSHOT)/_build/default/fstar.install

# Removes all .checked files and other intermediate files
# Does not remove the object files from the dune snapshot.
.PHONY: clean-intermediate
clean-intermediate:
	+$(Q)$(MAKE) -C ulib clean
	+$(Q)$(MAKE) -C src clean

# Regenerate all hints for the standard library and regression test suite
.PHONY: hints
hints:
	+$(Q)OTHERFLAGS=--record_hints $(MAKE) -C ulib/
	+$(Q)OTHERFLAGS=--record_hints $(MAKE) ci-uregressions

.PHONY: bench
bench:
	./bin/run_benchmark.sh

# Regenerate and accept expected output tests. Should be manually
# reviewed before checking in.
.PHONY: output
output:
	+$(Q)$(MAKE) -C tests/error-messages accept
	+$(Q)$(MAKE) -C tests/ide/emacs accept
	+$(Q)$(MAKE) -C tests/bug-reports output-accept

# This rule is meant to mimic what the docker based CI does, but it
# is not perfect. In particular it will not look for a diff on the
# snapshot, nor run the build-standalone script.
.PHONY: ci
ci:
	+$(Q)OTHERFLAGS="--use_hints" FSTAR_HOME=$(CURDIR)$(MAKE) ci-pre
	+$(Q)OTHERFLAGS="--use_hints" FSTAR_HOME=$(CURDIR)$(MAKE) ci-post

# This rule runs a CI job in a local container, exactly like is done for
# CI.
.PHONY: docker-ci
docker-ci:
	docker build -f .docker/standalone.Dockerfile --build-arg CI_THREADS=$(shell nproc) .

.PHONY: ci-pre
ci-pre: ci-rebootstrap ci-ocaml-test ci-ulib-in-fsharp

.PHONY: ci-rebootstrap
ci-rebootstrap:
	+$(Q)$(MAKE) full-bootstrap FSTAR_BUILD_PROFILE=test

.PHONY: ci-ocaml-test
ci-ocaml-test: ci-rebootstrap
	+$(Q)$(MAKE) -C src ocaml-unit-tests

.PHONY: ci-ulib-in-fsharp
ci-ulib-in-fsharp: ci-rebootstrap
	+$(Q)$(MAKE) -C ulib ulib-in-fsharp

.PHONY: ci-post
ci-post: ci-uregressions

.PHONY: ci-uregressions
ci-uregressions:
	+$(Q)$(MAKE) -C src uregressions

.PHONY: ci-uregressions-ulong
ci-uregressions-ulong:
	+$(Q)$(MAKE) -C src uregressions-ulong

# Shortcuts:

.PHONY: 1 2 3

1: fstar

2:
	+$(Q)$(MAKE) -C src ocaml
	+$(Q)$(MAKE) fstar

3:
	+$(Q)$(MAKE) 1
	+$(Q)$(MAKE) 2
