all: build
	+$(MAKE) test

build: extract
	export OCAMLPATH=$(FSTAR_HOME)/lib && cd src/ocaml && dune build
	cp -f src/_build/default/ocaml/main.exe .

extract:
	+$(MAKE) -C src extract

test:
	+$(MAKE) -C tests/
