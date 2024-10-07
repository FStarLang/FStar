.PHONY: all
all: build
	+$(MAKE) test

.PHONY: build
build: rustlib extract
	export OCAMLPATH=$(FSTAR_HOME)/lib && cd src/ocaml && dune build
	cp -f src/_build/default/ocaml/main.exe .

.PHONY: rustlib
rustlib:
	cd src/ocaml && cargo build && cp target/debug/librustast_bindings.a ./librustast_bindings.a

.PHONY: extract
extract:
	+$(MAKE) -C src extract

.PHONY: test
test:
	+$(MAKE) -C tests/
