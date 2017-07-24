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
	cp ../../src/ocaml-output/FStar_*.ml extracted/
	cp ../../src/basic/ml/*.ml extracted/
	cp ../../src/prettyprint/ml/*.ml extracted/
	cp ../../src/extraction/ml/FStar_Extraction_ML_PrintML.ml extracted/
	cp ../../src/parser/ml/FStar_Parser_LexFStar.mll extracted/
	cp ../../src/parser/ml/FStar_Parser_ParseIt.ml   extracted/
	cp ../../src/parser/ml/FStar_Parser_Util.ml      extracted/
	cp ../../src/tactics/ml/FStar_Tactics_Native.ml extracted/
	cp ../../src/tactics/ml/FStar_Tactics_Load.ml extracted/
	cp ../../src/tactics/ml/FStar_Tactics_Builtins.ml extracted/
	$(FIND) . extracted -maxdepth 1 -name "*.ml" -printf '%f\n' \
		| $(SED) -e 's/\.ml//g' -e 's/\./_/g' -e 's/\<./\u&/g' \
		| sort | uniq > $@
	echo 'FStar_Parser_LexFStar' >> $@
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
	rm -f fstarlib.mllib
	rm -f $(ULIB_GEN_DIR)/*
	rm -f ../.mgen
	rm -rf _build # ← ocamlbuild -clean does not work on Cygwin
