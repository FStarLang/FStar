.PHONY: all package clean boot 1 2 3 hints bench output install uninstall package_unknown_platform

include .common.mk

all: dune

DUNE_SNAPSHOT ?= $(CURDIR)/ocaml

# The directory where we install files when doing "make install".
# Overridden via the command-line by the OPAM invocation.
PREFIX ?= /usr/local

ifeq ($(OS),Windows_NT)
  # On Cygwin, the `--prefix` option to dune only
  # supports Windows paths.
  FSTAR_CURDIR=$(shell cygpath -m $(CURDIR))
else
  FSTAR_CURDIR=$(CURDIR)
endif

.PHONY: dune dune-fstar verify-ulib
dune-fstar:
	$(Q)cp version.txt $(DUNE_SNAPSHOT)/
	@# Call Dune to build the snapshot.
	@echo "  DUNE BUILD"
	$(Q)cd $(DUNE_SNAPSHOT) && dune build --profile release
	@echo "  DUNE INSTALL"
	$(Q)cd $(DUNE_SNAPSHOT) && dune install --prefix=$(FSTAR_CURDIR)

verify-ulib:
	+$(MAKE) -C ulib

dune: dune-fstar
	+$(MAKE) verify-ulib

.PHONY: clean-dune-snapshot

# Removes all generated files (including the whole generated snapshot,
# and .checked files), except the object files, so that the snapshot
# can be rebuilt with an existing fstar.exe
clean-dune-snapshot: clean-intermediate
	cd $(DUNE_SNAPSHOT) && { dune clean || true ; }
	rm -rf $(DUNE_SNAPSHOT)/fstar-lib/generated/*
	rm -rf $(DUNE_SNAPSHOT)/fstar-lib/dynamic/*

.PHONY: dune-extract-all

dune-extract-all:
	+$(MAKE) -C src/ocaml-output dune-snapshot

# This rule is not incremental, by design.
dune-full-bootstrap:
	+$(MAKE) dune-fstar
	+$(MAKE) clean-dune-snapshot
	+$(MAKE) dune-bootstrap

.PHONY: dune-bootstrap
dune-bootstrap:
	+$(MAKE) dune-extract-all
	+$(MAKE) dune

.PHONY: boot

boot:
	+$(MAKE) dune-extract-all
	$(Q)cp version.txt $(DUNE_SNAPSHOT)/
	@# Call Dune to build the snapshot.
	@echo "  DUNE BUILD"
	$(Q)cd $(DUNE_SNAPSHOT) && dune build --profile release
	@echo "  RAW INSTALL"
	$(Q)cp ocaml/_build/default/fstar/main.exe $(FSTAR_CURDIR)/bin/fstar.exe

install:
	$(Q)+$(MAKE) -C src/ocaml-output install

# The `uninstall` rule is only necessary for users who manually ran
# `make install`. It is not needed if F* was installed with opam,
# since `opam remove` can uninstall packages automatically with its
# own way.

uninstall:
	rm -rf \
	  $(PREFIX)/lib/fstar \
	  $(PREFIX)/bin/fstar_tests.exe \
	  $(PREFIX)/bin/fstar.exe \
	  $(PREFIX)/share/fstar

package: all
	$(Q)+$(MAKE) -C src/ocaml-output package

package_unknown_platform: all
	$(Q)+$(MAKE) -C src/ocaml-output package_unknown_platform

.PHONY: clean-intermediate

# Removes everything created by `make all`. MUST NOT be used when
# bootstrapping.
clean: clean-intermediate
	cd $(DUNE_SNAPSHOT) && { dune uninstall --prefix=$(FSTAR_CURDIR) || true ; } && { dune clean || true ; }

# Removes all .checked files and other intermediate files
# Does not remove the object files from the dune snapshot,
# because otherwise dune can't uninstall properly
clean-intermediate:
	$(Q)+$(MAKE) -C ulib clean
	$(Q)+$(MAKE) -C src clean

# Regenerate all hints for the standard library and regression test suite
hints:
	+$(Q)OTHERFLAGS=--record_hints $(MAKE) -C ulib/
	+$(Q)OTHERFLAGS=--record_hints $(MAKE) ci-uregressions

bench:
	./bin/run_benchmark.sh

# Regenerate and accept expected output tests. Should be manually
# reviewed before checking in.
output:
	$(Q)+$(MAKE) -C tests/error-messages accept
	$(Q)+$(MAKE) -C tests/interactive accept
	$(Q)+$(MAKE) -C tests/bug-reports output-accept

.PHONY: ci-utest-prelude

ci-utest-prelude: dune
	$(Q)+$(MAKE) dune-bootstrap
	$(Q)+$(MAKE) -C src ocaml-unit-tests
	$(Q)+$(MAKE) -C ulib ulib-in-fsharp    #build ulibfs

.PHONY: ci-uregressions ci-uregressions-ulong

ci-uregressions:
	$(Q)+$(MAKE) -C src uregressions

ci-uregressions-ulong:
	$(Q)+$(MAKE) -C src uregressions-ulong

# Shortcuts:

1: dune-fstar

2:
	+$(MAKE) -C src ocaml
	+$(MAKE) dune-fstar

3:
	+$(MAKE) dune-fstar
	+$(MAKE) -C src ocaml
	+$(MAKE) dune-fstar
