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
	$(FIND) . extracted -maxdepth 1 -name "*.ml" -print \
		| xargs -n 1 basename \
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

# Rewrote recipe to make it work on Alpine Linux 3.6
# (_build/ulib/ml/extracted/*.cmi glob was empty)
install: fstarlib.cmxa fstarlib.cma
	for f in \
	  _build/ulib/ml/fstarlib.a \
	  $(wildcard _build/ulib/ml/*.cmi) \
	  $(wildcard _build/ulib/ml/extracted/*.cmi) \
        ; do cp $$f $(FSTARLIB_DIR) ; done

.mgen:
	$(MAKE) -C .. .mgen


# Common rules
clean:
	rm -f fstarlib.mllib *~
	rm -fr $(ULIB_GEN_DIR) compiler-extracted
	rm -f $(FSTARLIB_DIR)/*.cm[aiox]a?
	rm -f ../.mgen
	rm -rf _build # ← ocamlbuild -clean does not work on Cygwin
