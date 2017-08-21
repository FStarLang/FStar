.PHONY: all

all:
	$(MAKE) -C src/ocaml-output

package:
	$(MAKE) -C src ocaml
	git diff --exit-code HEAD
	$(MAKE) -C src/ocaml-output package
