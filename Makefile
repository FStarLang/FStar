.PHONY: all package clean boot 0 1 2 3 hints bench libs output install uninstall package_unknown_platform no-ulib-checked

include .common.mk

all:
	$(Q)+$(MAKE) -C src/ocaml-output
	$(Q)+$(MAKE) -C ulib/ml
	$(Q)+$(MAKE) -C ulib

.PHONY: dune
dune:
	cd ocaml && dune build --profile release && dune install --prefix=$(PWD)

.PHONY: dune-staged-bootstrap dune-bootstrap-stage
dune-bootstrap-stage:
	rm -rf ulib/.depend*
	+$(MAKE) -C src/ocaml-output dune-snapshot # verifies everything
	+$(MAKE) dune

dune-staged-bootstrap:
	+$(MAKE) STAGE_EXPERIMENTAL=0 dune-bootstrap-stage
	+$(MAKE) STAGE_EXPERIMENTAL=0 dune-bootstrap-stage # need to do stage 0 twice if fstar.exe was not present for the first time
	+$(MAKE) STAGE_EXPERIMENTAL=1 dune-bootstrap-stage # generates Steel.Effect.Common
	+$(MAKE) STAGE_EXPERIMENTAL=2 dune-bootstrap-stage # generates Steel.ST.GenElim.Base
	+$(MAKE) dune-bootstrap-stage # verifies the rest of ulib/experimental

.PHONY: clean-full-dune-snapshot clean-dune-snapshot

clean-dune-snapshot:
	rm -rf ocaml/*/generated

clean-full-dune-snapshot: clean-dune-snapshot
	find ocaml -name *.ml | xargs rm -rf

install:
	$(Q)+$(MAKE) -C src/ocaml-output install

# The directory where we install files when doing "make install".
# Overridden via the command-line by the OPAM invocation.
PREFIX=$(shell pwd)/fstar

uninstall:
	ocamlfind remove fstarlib
	ocamlfind remove fstar-compiler-lib
	ocamlfind remove fstar-tactics-lib
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

# Shortcuts for developers

# Build the OCaml snapshot. NOTE: This will not build the standard library,
# nor tests, and native tactics will not run
1:
	$(Q)+$(MAKE) -C src/ocaml-output ../../bin/fstar.exe

# Bootstrap just the compiler, not the library and tests;
# fastest way to incrementally build a patch to the compiler
boot:
	$(Q)+$(MAKE) -C src/ ocaml
	$(Q)+$(MAKE) -C src/ocaml-output ../../bin/fstar.exe

boot_tests:
	$(Q)+$(MAKE) -C src/ ocaml
	$(Q)+$(MAKE) -C src/ocaml-output ../../bin/tests.exe

boot_libs: boot
	$(Q)+$(MAKE) libs

boot.ocaml:
	$(Q)+$(MAKE) -C src/ ocaml
	$(Q)+$(MAKE) -C src/ocaml-output ../../bin/fstar.ocaml

# Alias for boot
2: boot

# Build the snapshot and then regen, i.e. 1 + 2
3:
	$(Q)+$(MAKE) -C src/ocaml-output ../../bin/fstar.exe
	$(Q)+$(MAKE) -C src/ ocaml
	$(Q)+$(MAKE) -C src/ocaml-output ../../bin/fstar.exe

# Build the binary libraries: fstar-compiler-lib, fstarlib, fstartaclib
# Removes the .mgen files to trigger rebuild of the libraries if needed.
# This does NOT verify the library modules.
libs:
	$(Q)+$(MAKE) -C src/ocaml-output
	$(Q)rm -f ulib/*.mgen
	$(Q)+$(MAKE) -C ulib/ml

# Regenerate all hints for the standard library and regression test suite
hints:
	+$(Q)OTHERFLAGS=--record_hints $(MAKE) -C ulib/
	+$(Q)OTHERFLAGS=--record_hints $(MAKE) -C ulib/ml
	+$(Q)OTHERFLAGS=--record_hints $(MAKE) -C src/ uregressions

bench:
	./bin/run_benchmark.sh

# Regenerate and accept expected output tests. Should be manually
# reviewed before checking in.
output:
	$(Q)+$(MAKE) -C tests/error-messages accept
	$(Q)+$(MAKE) -C tests/interactive accept
	$(Q)+$(MAKE) -C tests/bug-reports output-accept
