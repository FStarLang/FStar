OCAMLC=ocamlfind ocamlc -thread -package batteries,zarith -linkpkg -g -I ../
OCAMLOPT=ocamlfind ocamlopt -thread -package batteries,zarith -linkpkg -g -I ../
OCAMLDEP=ocamldep
INCLUDES=                 # all relevant -I options here
OCAMLFLAGS=$(INCLUDES)    # add other options for ocamlc here
OCAMLOPTFLAGS=$(INCLUDES) # add other options for ocamlopt here

.SUFFIXES: .ml .mli .cmo .cmi .cmx .exe

all: platform.cmx

clean:
	rm -fr *~ *.cm* *.o *.annot

.ml.cmo:
	$(OCAMLC) $(OCAMLFLAGS) -c $<

.mli.cmi:
	$(OCAMLC) $(OCAMLFLAGS) -c $<

.ml.cmx:
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -c $<

.ml.exe:
	$(OCAMLOPT) $(OCAMLOPTFLAGS) platform.cmx $< -o $@

test: Tests.exe
		@./Tests.exe


depend:
	$(OCAMLDEP) Bytes.ml* Error.ml* > .depend

-include .depend
