.PHONY: all package clean boot 0 1 2 3 hints bench libs output install uninstall package_unknown_platform no-ulib-checked

include .common.mk

all:
	$(Q)+$(MAKE) -C src/ocaml-output
	$(Q)+$(MAKE) -C ulib/ml
	$(Q)+$(MAKE) -C ulib

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

# Build the F# version
0:
	$(Q)+$(MAKE) -C src/

# Build the OCaml snapshot. NOTE: This will not build the standard library,
# nor tests, and native tactics will not run
1:
	$(Q)+$(MAKE) -C src/ocaml-output ../../bin/fstar.exe

# Bootstrap just the compiler, not the library and tests;
# fastest way to incrementally build a patch to the compiler
boot:
	$(Q)+$(MAKE) -C src/ ocaml
	$(Q)+$(MAKE) -C src/ocaml-output ../../bin/fstar.exe

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
