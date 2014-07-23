# -*- Makefile -*-

# --------------------------------------------------------------------
.PHONY: all ocaml-% __force__

all: ocaml-asn1-combinators ocaml-nocrypto ocaml-x509

ocaml-%: __force__
	cd ocaml-$* && ( ocamlfind remove $* || true )
	make -C ocaml-$*
	make -C ocaml-$* install
