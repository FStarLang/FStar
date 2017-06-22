FSTAR_HOME=../..
include $(FSTAR_HOME)/src/gmake/z3.mk
include $(FSTAR_HOME)/src/gmake/fstar.mk

all: fstarlib.cmxa


ULIB_GEN_DIR=extracted

FIND=$(shell which gfind > /dev/null 2>&1 && echo gfind || echo find)
SED=$(shell which gsed > /dev/null 2>&1 && echo gsed || echo sed)
OCAMLBUILD=cd ../../ && ocamlbuild -use-ocamlfind -I ulib/ml -I ulib/ml/$(ULIB_GEN_DIR) -build-dir ulib/ml/_build

.PHONY:clean

all: .mgen fstarlib.cmxa

fstarlib.mllib: .mgen *.ml $(wildcard extracted/*.ml)
	$(FIND) . extracted -maxdepth 1 -name "*.ml" -printf '%f\n' \
		| $(SED) -e 's/\.ml//g' -e 's/\./_/g' -e 's/\<./\u&/g' \
		| sort | uniq > $@

FSTARLIB_DIR=../../bin/fstarlib/

fstarlib.cmxa:fstarlib.mllib
	$(OCAMLBUILD) fstarlib.cmxa
	$(MAKE) install

fstarlib.cma:fstarlib.mllib
	$(OCAMLBUILD) fstarlib.cma
	$(MAKE) install

install:
	cp _build/ulib/ml/fstarlib.{cmxa,cma,a} $(FSTARLIB_DIR) 2>/dev/null || :
	cp _build/ulib/ml/*.cmi $(FSTARLIB_DIR)
	cp _build/ulib/ml/extracted/*.cmi $(FSTARLIB_DIR)

.mgen:
	$(MAKE) -C .. .mgen


# Common rules
clean:
	rm -f fstarlib.mllib || :
	rm -f $(ULIB_GEN_DIR)/*
	rm -f ../.mgen || :
	rm -rf _build # ← ocamlbuild -clean does not work on Cygwin
