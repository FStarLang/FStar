FSTAR_HOME=../..
include $(FSTAR_HOME)/src/gmake/z3.mk
include $(FSTAR_HOME)/src/gmake/fstar.mk

all: fstarlib.cmxa


ULIB_GEN_DIR=extracted

FIND=$(shell which gfind > /dev/null 2>&1 && echo gfind || echo find)
SED=$(shell which gsed > /dev/null 2>&1 && echo gsed || echo sed)
OCAMLBUILD=cd ../../ && ocamlbuild -use-ocamlfind -I ulib/ml -I ulib/ml/$(ULIB_GEN_DIR) -build-dir ulib/ml/_build

.PHONY:clean

all: .mgen install

fstarlib.mllib: .mgen *.ml $(wildcard extracted/*.ml)
	$(FIND) . extracted -maxdepth 1 -name "*.ml" -printf '%f\n' \
		| $(SED) -e 's/\.ml//g' -e 's/\./_/g' -e 's/\<./\u&/g' \
		| sort | uniq > $@
	touch fstarlib.ml

FSTARLIB_DIR=../../bin/fstarlib/

fstarlib.cma:fstarlib.mllib
	$(OCAMLBUILD) $@
	cp _build/ulib/ml/$@ $(FSTARLIB_DIR)

fstarlib.cmxa:fstarlib.mllib | fstarlib.cma
	$(OCAMLBUILD) $@
	cp _build/ulib/ml/$@ $(FSTARLIB_DIR)

install: fstarlib.cmxa fstarlib.cma
	cp _build/ulib/ml/fstarlib.a $(FSTARLIB_DIR)
	cp _build/ulib/ml/*.cmi $(FSTARLIB_DIR)
	cp _build/ulib/ml/extracted/*.cmi $(FSTARLIB_DIR)

.mgen:
	$(MAKE) -C .. .mgen


# Common rules
clean:
	rm -f fstarlib.mllib *~
	rm -fr $(ULIB_GEN_DIR) compiler-extracted
	rm -f $(FSTARLIB_DIR)/*.cm[aiox]a?
	rm -f ../.mgen
	rm -rf _build # ← ocamlbuild -clean does not work on Cygwin
