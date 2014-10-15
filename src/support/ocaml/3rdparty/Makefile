# -*- Makefile -*-

# --------------------------------------------------------------------
PACKAGES := asn1-combinators nocrypto x509

# --------------------------------------------------------------------
.PHONY: all update ocaml-% update-% __force__

all: $(PACKAGES:%=ocaml-%)

update: $(PACKAGES:%=update-%)

ocaml-%: __force__
	cd ocaml-$* && ( ocamlfind remove $* || true )
	make -C ocaml-$*
	make -C ocaml-$* install

update-%: __force__
	cd ocaml-$* && ( set -e; \
	  git clean -fdx; \
	  git reset --hard HEAD; \
	  git pull --all --prune \
	)
