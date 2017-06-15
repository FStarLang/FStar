FSTAR_HOME=../..
include $(FSTAR_HOME)/src/gmake/z3.mk
include $(FSTAR_HOME)/src/gmake/fstar.mk

all: fstarlib.cmxa


ULIB_GEN_DIR=extracted

EXTRACT_MOD=FStar.Pervasives FStar.TSet FStar.Map FStar.HyperHeap FStar.HyperStack
EXTRACT_FLS=$(addsuffix .ml,$(addprefix $(ULIB_GEN_DIR)/,$(subst .,_,$(EXTRACT_MOD))))

.SECONDEXPANSION:
$(EXTRACT_FLS): ../$$(subst _,.,$$(subst $(ULIB_GEN_DIR)/,,$$*)).fst
	$(FSTAR) --lax --codegen OCaml --odir $(ULIB_GEN_DIR) --extract_module $(subst _,.,$(subst $(ULIB_GEN_DIR)/,,$*)) $<


FILES=prims.ml FStar_Mul.ml FStar_Float.ml FStar_Char.ml FStar_Int8.ml		\
	FStar_UInt8.ml FStar_Int16.ml FStar_UInt16.ml FStar_Int32.ml			\
	FStar_UInt32.ml FStar_Int64.ml FStar_UInt64.ml FStar_UInt128.ml			\
	FStar_Int_Cast.ml FStar_BaseTypes.ml FStar_IO.ml FStar_Heap.ml			\
	FStar_List_Tot_Base.ml FStar_List.ml FStar_Option.ml FStar_String.ml	\
	FStar_Set.ml FStar_Buffer.ml FStar_CommonST.ml							\
	$(ULIB_GEN_DIR)/FStar_Pervasives.ml

FIND=$(shell which gfind && echo gfind || echo find)
SED=$(shell which gsed > /dev/null 2>&1 && echo gsed || echo sed)
OCAMLBUILD=cd ../../ && ocamlbuild -use-ocamlfind -I ulib/ml -I ulib/ml/$(ULIB_GEN_DIR) -build-dir ulib/ml/_build

.PHONY:clean

all: .mgen fstarlib.cmxa

fstarlib.mllib: .mgen *.ml $(wildcard extracted/*.ml)
	find . extracted -maxdepth 1 -name "*.ml" -printf '%f\n' \
		| $(SED) -e 's/\.ml//g' -e 's/\./_/g' -e 's/\<./\u&/g' \
		| sort | uniq > $@

FSTARLIB_DIR=../../bin/fstarlib/

fstarlib.cmxa:fstarlib.mllib
	$(OCAMLBUILD) fstarlib.cmxa
	make install

fstarlib.cma:fstarlib.mllib
	$(OCAMLBUILD) fstarlib.cma
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
