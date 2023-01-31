.PHONY: all package clean boot 0 1 2 3 hints bench libs output install uninstall package_unknown_platform no-ulib-checked

include .common.mk

all: dune

.PHONY: dune dune-fstar
dune-fstar:
	cd ocaml && dune build --profile release && dune install --prefix=$(PWD)

dune: dune-fstar
	+$(MAKE) -C ulib

.PHONY: clean-dune-snapshot

DUNE_SNAPSHOT ?= $(PWD)/ocaml

clean-dune-snapshot:
	rm -rf $(DUNE_SNAPSHOT)/fstar-lib/generated/*

.PHONY: dune-extract-all

dune-extract-all:
	+$(MAKE) -C src/ocaml-output dune-snapshot

dune-full-bootstrap:
	+$(MAKE) dune
	+$(MAKE) clean-dune-snapshot
	rm -rf ulib/.depend*
	+$(MAKE) -C src/ocaml-output clean
	+$(MAKE) dune-extract-all
	rm -rf ulib/.depend*
	+$(MAKE) dune

.PHONY: dune-bootstrap
dune-bootstrap:
	+$(MAKE) dune-extract-all
	+$(MAKE) dune

install:
	$(Q)+$(MAKE) -C src/ocaml-output install

# The directory where we install files when doing "make install".
# Overridden via the command-line by the OPAM invocation.
PREFIX ?= $(PWD)

uninstall:
	ocamlfind remove fstar
	ocamlfind remove fstar.lib
	rm -rf \
	  $(PREFIX)/lib/fstar \
	  $(PREFIX)/doc/fstar \
	  $(PREFIX)/etc/fstar \
	  $(PREFIX)/bin/fstar.exe \
	  $(PREFIX)/share/fstar

package: all
	$(Q)+$(MAKE) -C src/ocaml-output package

package_unknown_platform: all
	$(Q)+$(MAKE) -C src/ocaml-output package_unknown_platform

clean:
	$(Q)+$(MAKE) -C ulib clean
	$(Q)+$(MAKE) -C src/ocaml-output clean

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
	$(Q)+$(MAKE) -C ulib ulib-in-fsharp    #build ulibfs

.PHONY: ci-uregressions ci-uregressions-ulong

ci-uregressions:
	$(Q)+$(MAKE) -C src uregressions

ci-uregressions-ulong:
	$(Q)+$(MAKE) -C src uregressions-ulong
