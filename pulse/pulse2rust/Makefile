all: extract
	export OCAMLPATH=$(FSTAR_HOME)/lib && cd src/ocaml && dune build
	cp -f src/_build/default/ocaml/main.exe .

extract:
	make -C src extract
