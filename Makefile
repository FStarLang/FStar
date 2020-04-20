.PHONY: all package clean boot 0 1 2 3 hints bench

include .common.mk

all:
	$(Q)+$(MAKE) -C src/ocaml-output
	$(Q)+$(MAKE) -C ulib
	$(Q)+$(MAKE) -C ulib/ml

package:
	$(Q)+$(MAKE) -C src/ocaml-output package

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

# Build the libraries: fstar-compiler-lib, fstarlib, fstartaclib
libs:
	$(Q)+$(MAKE) -C src/ocaml-output
	$(Q)+$(MAKE) -C ulib/ml

# Regenerate all hints for the standard library and regression test suite
hints:
	+$(Q)OTHERFLAGS=--record_hints $(MAKE) -C ulib/
	+$(Q)OTHERFLAGS=--record_hints $(MAKE) -C ulib/ml
	+$(Q)OTHERFLAGS=--record_hints $(MAKE) -C src/ uregressions

bench:
	./bin/run_benchmark.sh
