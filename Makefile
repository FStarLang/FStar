.PHONY: all

all:
	$(MAKE) -C src/ocaml-output

package:
	git clean -ffdx .
	$(MAKE) all
	$(MAKE) -C src ocaml
	git diff --exit-code HEAD
	$(MAKE) -C src/ocaml-output package
