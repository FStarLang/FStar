FILES=prims.ml st.ml all.ml list.ml option.ml Microsoft_FStar_Char.ml Microsoft_FStar_String.ml Microsoft_FStar_Util.ml Microsoft_FStar_Unionfind.ml Microsoft_FStar_Platform.ml Microsoft_FStar_Getopt.ml Microsoft_FStar_Range.ml Microsoft_FStar_Bytes.ml Microsoft_FStar_Parser_Util.ml set.ml map.ml heap.ml
OCAMLOPT=ocamlfind ocamlopt -thread -package batteries -linkpkg -g
OCAMLDEP=ocamldep
OBJS=$(FILES:.ml=.o)

all_objs: $(OBJS)

# Common rules
.SUFFIXES: .ml .mli .cmo .cmi .cmx

%.o: %.ml
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -c $<

depend:
	$(OCAMLDEP) $(INCLUDES) $(FILES) > .depend

clean:
	rm -f *.cmi *.cmo *.cmx *.exe *.o *~

-include .depend
