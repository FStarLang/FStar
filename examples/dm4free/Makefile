FSTAR_HOME=../..
include ../Makefile.include

all: uall
uall:	FStar.DM4F.MonadLaws.uver \
	Effects.Def.uver \
	FStar.DM4F.IntST.uver \
	FStar.DM4F.Exceptions.uver \
	FStar.DM4F.ExnSt.uver \
	FStar.DM4F.StExn.uver \
	FStar.DM4F.ST.uver \
	FStar.DM4F.Heap.uver \
	FStar.DM4F.Heap.ST.uver \
	FStar.DM4F.StExnC.uver \
	FStar.DM4F.IFC.uver \
	FStar.DM4F.Continuations.uver \
	delimcc.uver \
	FStar.DM4F.IntStore.uver \
	FStar.DM4F.IntStoreFixedReader.uver \
	FStar.DM4F.IntStoreFixed.uver \
	FStar.DM4F.IntStoreExcFixed.uver \
	FStar.DM4F.Heap.Random.uver \
	FStar.DM4F.Random.uver

old:
	$(MAKE) -C old

%.uver-explicit: %.fst
	$(FSTAR) $^ --explicit_deps

%.uver: %.fst
	$(FSTAR) $^

include $(FSTAR_HOME)/ulib/ml/Makefile.include

FIND=$(shell which gfind > /dev/null 2>&1 && echo gfind || echo find)
SED=$(shell which gsed > /dev/null 2>&1 && echo gsed || echo sed)
REALIZED_FILES=$(shell $(FIND) ml -maxdepth 1 -type f -name "*.ml" -printf "%f " | $(SED) -e 's/\.ml//g' -e 's/_/./g')

NOEXTRACT=$(addprefix --no_extract , $(REALIZED_FILES))

extract_erase: $(wildcard FStar.Erase.*.fst)
	mkdir -p ml/extracted
	$(FSTAR) --codegen OCaml --odir ml/extracted --extract_namespace FStar.DM4F --extract_namespace FStar.Erase $(NOEXTRACT) $^
	$(SED) -i -e 's/let rec for_all_prop /type (_,_,_) for_all_prop = unit\n&/' ml/extracted/FStar_Erase_Test.ml

OCAML_PATH=$(realpath $(FSTAR_HOME)/bin)

ml/bin/dm4f.cma: extract_erase
	OCAMLPATH=$(OCAML_PATH) ocamlbuild -build-dir ml/_build -use-ocamlfind -pkg fstarlib -I ml -I ml/extracted dm4f.cma
	mkdir -p ml/bin
	cp ml/_build/dm4f.cma ml/bin/
	$(FIND) ml/_build -name "*.cmi" -exec cp {} ml/bin/ \;

