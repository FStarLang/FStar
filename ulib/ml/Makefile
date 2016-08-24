# The variable below can be configured from the outside. For instance:
# $(MAKE) -C $(FSTAR_HOME)/lib/ml PRIMS_DIR=native_int
PRIMS_DIR=.

PRIMS=MkPrims.ml $(PRIMS_DIR)/prims.ml
FILES=$(PRIMS) FStar_ST.ml FStar_HyperHeap.ml FStar_Mul.ml FStar_Float.ml FStar_Char.ml \
	FStar_Int8.ml FStar_UInt8.ml FStar_Int16.ml FStar_UInt16.ml \
	FStar_Int32.ml FStar_UInt32.ml FStar_Int64.ml FStar_UInt64.ml FStar_UInt128.ml \
	FStar_Int_Cast.ml \
	FStar_BaseTypes.ml \
	FStar_All.ml FStar_IO.ml FStar_Heap.ml FStar_List.ml \
	FStar_Option.ml FStar_String.ml FStar_Set.ml \
	FStar_Buffer.ml

OCAMLOPT=ocamlfind opt -thread -package batteries,zarith,stdint -linkpkg -g $(INCLUDES)
OCAMLDEP=ocamlfind dep
OCAMLMKLIB=ocamlfind mklib

OBJS=$(FILES:.ml=.o)
CMX=$(FILES:.ml=.cmx)

# Note: because of the way we either prepend the regular ST or the hyperheap ST,
# you must always clean before running either "make" or "make hyperheap".
all: $(OBJS)
	ocamlopt -a $(CMX) -o $(PRIMS_DIR)/fstarlib.cmxa

# Common rules
.SUFFIXES: .ml .mli .cmo .cmi .cmx

%.o: %.ml
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -c -I $(PRIMS_DIR) -linkpkg $<

depend:
	$(OCAMLDEP) -I native_int $(FILES) > .depend

CLEAN=*.cmi *.cmo *.cmx *.exe *.o *.a *.cmxa *~

clean:
	rm -f $(CLEAN) $(addprefix native_int/,$(CLEAN))

-include .depend
