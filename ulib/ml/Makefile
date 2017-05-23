ULIB_GEN_DIR=./extracted

SED=$(shell which gsed > /dev/null 2>&1 && echo gsed || echo sed)
OCAMLBUILD=cd ../../ && ocamlbuild -use-ocamlfind -I ulib/ml -I ulib/ml/$(ULIB_GEN_DIR) -build-dir ulib/ml/_build

.PHONY:clean

all: .mgen fstarlib.cmxa

fstarlib.mllib: .mgen *.ml $(wildcard extracted/*.ml)
	echo $^ | $(SED) -e 's/.mgen //' \
	                 -e 's;extracted/;;g' \
	                 -e 's/\.ml//g' \
	                 -e 's/\./_/g' \
	                 -e 's/\<./\u&/g' \
	                 -e 's/ /\n/g' > $@

fstarlib.cmxa:fstarlib.mllib
	$(OCAMLBUILD) fstarlib.cmxa
	cp _build/ulib/ml/fstarlib.cmxa ../../bin/

.mgen:
	make -C .. mgen


# Common rules
clean:
	rm fstarlib.mllib
	rm -f $(ULIB_GEN_DIR)/*
	ocamlbuild -clean
