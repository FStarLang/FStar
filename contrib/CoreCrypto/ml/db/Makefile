OCAMLC=ocamlfind ocamlc -thread -package batteries -linkpkg -g
OCAMLOPT=ocamlfind ocamlopt -thread -package batteries,fileutils,sqlite3 -linkpkg -g
OCAMLDEP=ocamldep
INCLUDES=-I +fileutils # all relevant -I options here
OCAMLFLAGS=$(INCLUDES)    # add other options for ocamlc here
OCAMLOPTFLAGS=$(INCLUDES) # add other options for ocamlopt here

.SUFFIXES: .ml .mli .cmo .cmi .cmx

all: DB.cmi # DB.cmx

clean:
	rm -fr *~ *.cm* *.o

.mli.cmi:
	$(OCAMLC) $(OCAMLFLAGS) -c $<

.ml.cmo:
	$(OCAMLC) $(OCAMLFLAGS) -c $<

.ml.cmx:
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -c $<

depend:
	$(OCAMLDEP) *.ml* > .depend

-include .depend

