# The two variables below can be configured from the outside. For instance:
# $(MAKE) -C $(FSTAR_HOME)/lib/ml hyperheap PRIMS=native_int/prims.ml INCLUDES="-I native_int/"
PRIMS=prims.ml
INCLUDES=

COMMON=FStar_All.ml FStar_IO.ml FStar_Heap.ml FStar_List.ml FStar_Option.ml FStar_Char.ml FStar_String.ml FStar_Set.ml
FILES=$(PRIMS) FStar_ST.ml $(COMMON)
HYPERHEAP=$(PRIMS) ./hyperheap/FStar_ST.ml $(COMMON) ./hyperheap/FStar_HyperHeap.ml

OCAMLOPT=ocamlfind opt -thread -package batteries -linkpkg -g $(INCLUDES)
OCAMLDEP=ocamlfind dep
OCAMLMKLIB=ocamlfind mklib

OBJS=$(FILES:.ml=.o)
CMX=$(FILES:.ml=.cmx)
HH_OBJS=$(HYPERHEAP:.ml=.o)
HH_CMX=$(HYPERHEAP:.ml=.cmx)

# Note: because of the way we either prepend the regular ST or the hyperheap ST,
# you must always clean before running either "make" or "make hyperheap".
all: $(OBJS)
	ocamlopt -a $(CMX) -o fstarlib.cmxa

hyperheap: $(HH_OBJS)
	ocamlopt -a $(HH_CMX) -o fstarlib-hyperheap.cmxa

# Common rules
.SUFFIXES: .ml .mli .cmo .cmi .cmx

%.o: %.ml
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -c $<

depend:
	$(OCAMLDEP) $(INCLUDES) $(FILES) > .depend

CLEAN=*.cmi *.cmo *.cmx *.exe *.o *.cmxa *~

clean:
	rm -f $(CLEAN) $(addprefix hyperheap/,$(CLEAN))

-include .depend
