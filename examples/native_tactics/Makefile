FSTAR_HOME=../..
OCAML_OUTPUT=$(FSTAR_HOME)/src/ocaml-output
INCLUDES=$(addprefix -I $(OCAML_OUTPUT)/_build/, src/tactics/ml ulib/ml src/ocaml-output/ src/basic/ml)

.PRECIOUS: %.ml

%.ml: %.fst
	fstar $(OTHERFLAGS) --codegen OCaml $< --extract_module $(patsubst %.fst,%,$<)
	cat $(patsubst %.fst,%,$<).fixup >> $@

%.cmxs: %.ml
	ocamlfind ocamlopt -shared $(INCLUDES) -linkpkg -package zarith -o $@ $<

.PHONY: test

%.test: %.cmxs %.Test.fst 
	fstar --load $^

clean:
	rm -f *.ml *.cm*
