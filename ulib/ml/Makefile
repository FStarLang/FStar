ULIB_GEN_DIR=./extracted

SED=$(shell which gsed > /dev/null 2>&1 && echo gsed || echo sed)
OCAMLBUILD=cd ../../ && ocamlbuild -use-ocamlfind -I ulib/ml -I ulib/ml/$(ULIB_GEN_DIR) -build-dir ulib/ml/_build

.PHONY:clean

all: .mgen fstarlib.cmxa

# TODO : Remove this terrible hack with directories heap/hyperheap ASAP
# heap and hyperstack contains files with the same name :
# we depend on both directories but we actually put the name
# of the file only once in the mllib
fstarlib.mllib: .mgen *.ml $(wildcard heap/*.ml) $(wildcard hyperstack/*.ml) $(wildcard extracted/*.ml)
	echo $^ | $(SED) -e 's;\(.mgen \|\w*/\);;g' \
	                 -e 's/\.ml//g' \
	                 -e 's/\./_/g' \
	                 -e 's/\<./\u&/g' \
	                 -e 's/ /\n/g' | sort | uniq > $@

FSTARLIB_DIR=../../bin/fstarlib/

fstarlib.cmxa:fstarlib.mllib
	$(OCAMLBUILD) -I ulib/ml/heap fstarlib.cmxa
	@# the mllib for hyperstack is the same as the one for normal heaps,
	@# only the include path changes
	@cp fstarlib.mllib fstarlib_hyperstack.mllib
	$(OCAMLBUILD) -I ulib/ml/hyperstack fstarlib_hyperstack.cmxa
	@rm fstarlib_hyperstack.mllib
	make install

fstarlib.cma:fstarlib.mllib
	$(OCAMLBUILD) -I ulib/ml/heap fstarlib.cma
	@cp fstarlib.mllib fstarlib_hyperstack.mllib
	$(OCAMLBUILD) -I ulib/ml/hyperstack fstarlib_hyperstack.cma
	@rm fstarlib_hyperstack.mllib
	make install

install:
	cp _build/ulib/ml/fstarlib.{cmxa,cma,a} $(FSTARLIB_DIR) 2>/dev/null || :
	cp _build/ulib/ml/fstarlib_hyperstack.{cmxa,cma,a} $(FSTARLIB_DIR) 2>/dev/null || :
	cp _build/ulib/ml/*.cmi $(FSTARLIB_DIR)
	cp _build/ulib/ml/extracted/*.cmi $(FSTARLIB_DIR)
	cp _build/ulib/ml/heap/*.cmi $(FSTARLIB_DIR)
	cp _build/ulib/ml/hyperstack/*.cmi $(FSTARLIB_DIR)

.mgen:
	make -C .. .mgen


# Common rules
clean:
	rm -f fstarlib.mllib || :
	rm -f $(ULIB_GEN_DIR)/*
	rm -f ../.mgen || :
	ocamlbuild -clean
