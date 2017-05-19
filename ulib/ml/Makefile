ULIB_GEN_DIR=./extracted

ifeq ($(MEM),HST)
	ST=$(ULIB_GEN_DIR)/FStar_TSet.ml $(ULIB_GEN_DIR)/FStar_Map.ml $(ULIB_GEN_DIR)/FStar_HyperHeap.ml $(ULIB_GEN_DIR)/FStar_HyperStack.ml hyperstack/FStar_ST.ml hyperstack/FStar_All.ml
else
	ST=FStar_ST.ml FStar_All.ml
endif

FILES=prims.ml $(ULIB_GEN_DIR)/FStar_Pervasives.ml FStar_Mul.ml FStar_Float.ml FStar_Char.ml \
      FStar_Int8.ml FStar_UInt8.ml FStar_Int16.ml FStar_UInt16.ml \
      FStar_Int32.ml FStar_UInt32.ml FStar_Int64.ml FStar_UInt64.ml FStar_UInt128.ml \
      FStar_Int_Cast.ml \
      FStar_BaseTypes.ml \
      FStar_IO.ml FStar_Heap.ml FStar_List_Tot_Base.ml FStar_List.ml \
      FStar_Option.ml FStar_String.ml FStar_Set.ml \
      FStar_Buffer.ml FStar_CommonST.ml $(ST)

OCAMLOPT=ocamlfind opt -thread -package batteries,zarith,stdint -linkpkg -g $(INCLUDES)
OCAMLDEP=ocamlfind dep
OCAMLMKLIB=ocamlfind mklib

OBJS=$(FILES:.ml=.o)
CMX=$(FILES:.ml=.cmx)

.mgen:
	make -C .. mgen

all: .mgen
	make $(OBJS)
	ocamlopt -a $(CMX) -o fstarlib.cmxa

# Common rules
.SUFFIXES: .ml .mli .cmo .cmi .cmx

%.o: %.ml
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -c -I $(PRIMS_DIR) $(ULIB_GEN_DIR) -linkpkg $<

depend:
	$(OCAMLDEP) $(FILES) > .depend

CLEAN=*.cmi *.cmo *.cmx *.exe *.o *.a *.cmxa *~ $(subst .ml,.cmx,$(ST)) $(subst .ml,.cmi,$(ST)) $(subst .ml,.o,$(ST))

clean:
	rm -f $(CLEAN)
	rm -f $(ULIB_GEN_DIR)/*
	rm -f hyperstack/*.o hyperstack/*.cm*

-include .depend
