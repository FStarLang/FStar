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

ifeq ($(MEM),HST)
  FILES+=$(ULIB_GEN_DIR)/FStar_TSet.ml $(ULIB_GEN_DIR)/FStar_Map.ml $(ULIB_GEN_DIR)/FStar_HyperHeap.ml $(ULIB_GEN_DIR)/FStar_HyperStack.ml hyperstack/FStar_ST.ml hyperstack/FStar_All.ml
else
  FILES+=FStar_ST.ml FStar_All.ml
endif


OCAMLOPT=ocamlfind opt -thread -package batteries,zarith,stdint -linkpkg -g $(INCLUDES)
OCAMLDEP=ocamlfind dep
OCAMLMKLIB=ocamlfind mklib

fstarlib.cmxa: $(FILES:.ml=.cmx)
	ocamlopt -a $? -o $@

.SUFFIXES: .ml .mli .cmo .cmi .cmx

%.cmx: %.ml
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -c -I $(ULIB_GEN_DIR) -linkpkg $<

.depend: $(FILES)
	$(OCAMLDEP) -I $(ULIB_GEN_DIR) $(FILES) > .depend

depend: .depend

clean:
	rm -f fstarlib.cmxa fstarlib.a 
	rm -f $(subst .ml,.cmx,$(FILES)) $(subst .ml,.cmi,$(FILES)) $(subst .ml,.o,$(FILES))
	rm -rf $(ULIB_GEN_DIR)
	rm -rf .depend

-include .depend
