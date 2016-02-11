# The two variables below can be configured from the outside. For instance:
# $(MAKE) -C $(FSTAR_HOME)/lib/ml hyperheap PRIMS=native_int/prims.ml INCLUDES="-I native_int/"
PRIMS=prims.ml
INCLUDES=
FILES=$(PRIMS) FStar_ST.ml FStar_All.ml FStar_IO.ml FStar_List.ml FStar_Option.ml FStar_Char.ml FStar_String.ml FStar_Set.ml
HYPERHEAP=$(PRIMS) ./hyperheap/FStar_ST.ml FStar_All.ml FStar_IO.ml FStar_List.ml FStar_Option.ml FStar_Char.ml FStar_String.ml FStar_Set.ml ./hyperheap/FStar_HyperHeap.ml

OCAMLOPT=ocamlfind ocamlopt -thread -package batteries -linkpkg -g $(INCLUDES)
OCAMLDEP=ocamldep
OBJS=$(FILES:.ml=.o)
HH_OBJS=$(HYPERHEAP:.ml=.o)

all_objs: $(OBJS)

hyperheap: $(HH_OBJS)
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -c $<

# Common rules
.SUFFIXES: .ml .mli .cmo .cmi .cmx

%.o: %.ml
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -c $<

depend:
	$(OCAMLDEP) $(INCLUDES) $(FILES) > .depend

clean:
	rm -f *.cmi *.cmo *.cmx *.exe *.o *~ ./hyperheap/*.cmi ./hyperheap/*.cmo ./hyperheap/*.cmx ./hyperheap/*.o ./hyperheap/*~

-include .depend
