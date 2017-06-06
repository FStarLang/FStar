ULIB_GEN_DIR=./extracted

SED=$(shell which gsed > /dev/null 2>&1 && echo gsed || echo sed)
OCAMLBUILD=cd ../../ && ocamlbuild -use-ocamlfind -I ulib/ml -I ulib/ml/$(ULIB_GEN_DIR) -build-dir ulib/ml/_build

.PHONY:clean

all: .mgen fstarlib.cmxa

fstarlib.mllib: .mgen *.ml $(wildcard extracted/*.ml)
	echo $^ | $(SED) -e 's;\(.mgen \|\w*/\);;g' \
	                 -e 's/\.ml//g' \
	                 -e 's/\./_/g' \
	                 -e 's/\<./\u&/g' \
	                 -e 's/ /\n/g' | sort | uniq > $@

FSTARLIB_DIR=../../bin/fstarlib/

fstarlib.cmxa:fstarlib.mllib
	$(OCAMLBUILD) -I ulib/ml/heap fstarlib.cmxa
	make install

fstarlib.cma:fstarlib.mllib
	$(OCAMLBUILD) -I ulib/ml/heap fstarlib.cma
	make install

install:
	cp _build/ulib/ml/fstarlib.{cmxa,cma,a} $(FSTARLIB_DIR) 2>/dev/null || :
	cp _build/ulib/ml/*.cmi $(FSTARLIB_DIR)
	cp _build/ulib/ml/extracted/*.cmi $(FSTARLIB_DIR)

.mgen:
	make -C .. .mgen


# Common rules
clean:
	rm -f fstarlib.mllib || :
	rm -f $(ULIB_GEN_DIR)/*
	rm -f ../.mgen || :
	ocamlbuild -clean
