FILES=prims.ml FStar_ST.ml FStar_All.ml FStar_List.ml FStar_Option.ml FStar_Char.ml FStar_String.ml FStar_Util.ml FStar_Unionfind.ml FStar_Platform.ml FStar_Getopt.ml FStar_Range.ml FStar_Bytes.ml FStar_Parser_Util.ml FStar_Set.ml FStar_Set.ml FStar_Set.ml
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
