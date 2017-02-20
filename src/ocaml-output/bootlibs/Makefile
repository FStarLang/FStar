# The variable below can be configured from the outside. For instance:
# $(MAKE) -C $(FSTAR_HOME)/lib/ml hyperheap PRIMS_DIR=native_int
PRIMS_DIR=.

PRIMS=MkPrims.ml $(PRIMS_DIR)/prims.ml
COMMON=FStar_Float.ml FStar_Char.ml FStar_Int8.ml FStar_UInt8.ml FStar_Int16.ml FStar_UInt16.ml \
	FStar_Int32.ml FStar_Int64.ml FStar_BaseTypes.ml \
	FStar_All.ml FStar_IO.ml FStar_Heap.ml FStar_List.ml \
	FStar_Option.ml FStar_String.ml FStar_Set.ml
FILES=$(PRIMS) FStar_ST.ml $(COMMON)
HYPERHEAP=$(PRIMS) ./hyperheap/FStar_ST.ml $(COMMON) ./hyperheap/FStar_HyperHeap.ml

OCAMLOPT=ocamlfind opt -thread -package zarith,batteries -linkpkg -g $(INCLUDES)
OCAMLDEP=ocamlfind dep
OCAMLMKLIB=ocamlfind mklib

OBJS=$(FILES:.ml=.o)
CMX=$(FILES:.ml=.cmx)
HH_OBJS=$(HYPERHEAP:.ml=.o)
HH_CMX=$(HYPERHEAP:.ml=.cmx)

# Note: because of the way we either prepend the regular ST or the hyperheap ST,
# you must always clean before running either "make" or "make hyperheap".
all: $(OBJS)
	ocamlfind ocamlopt -a $(CMX) -o fstarlib.cmxa

hyperheap: $(HH_OBJS)
	ocamlfind ocamlopt -a $(HH_CMX) -o fstarlib-hyperheap.cmxa

# Common rules
.SUFFIXES: .ml .mli .cmo .cmi .cmx

%.o: %.ml
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -c $<

depend:
	$(OCAMLDEP) -I native_int -I hyperheap $(FILES) $(HYPERHEAP) > .depend

CLEAN=*.cmi *.cmo *.cmx *.exe *.o *.a *.cmxa *~

clean:
	rm -f $(CLEAN) $(addprefix hyperheap/,$(CLEAN)) $(addprefix native_int/,$(CLEAN))

-include .depend
