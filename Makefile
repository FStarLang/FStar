.PHONY: all package clean 0 1 2 3 hints

all:
	$(MAKE) -C src/ocaml-output

package:
	git clean -ffdx .
	$(MAKE) -C src/ocaml-output package

clean:
	$(MAKE) -C ulib clean
	$(MAKE) -C src/ocaml-output clean

# Shortcuts

# Build the F# version
0:
	$(MAKE) -C src/

# Build the OCaml snapshot
1:
	$(MAKE) -C src/ocaml-output

# Generate a new OCaml snapshot
2:
	$(MAKE) -C src fstar-ocaml

# Build the snapshot and then regen, i.e. 1 + 2
3:
	$(MAKE) -C src ocaml-fstar-ocaml

# Regenerate all hints for the regression test suite
hints:
	OTHERFLAGS=--record_hints $(MAKE) -C src/ uregressions
