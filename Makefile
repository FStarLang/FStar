.PHONY: all

all:
	$(MAKE) -C src/ocaml-output
	$(MAKE) -C ulib

package:
	git clean -ffdx .
	$(MAKE) -C src/ocaml-output package

clean:
	$(MAKE) -C ulib clean
	$(MAKE) -C src/ocaml-output clean
