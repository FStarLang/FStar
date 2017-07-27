FSTAR_HOME=../..
OCAML_OUTPUT=$(FSTAR_HOME)/src/ocaml-output
INCLUDES=$(addprefix -I $(OCAML_OUTPUT)/_build/, src/tactics/ml ulib/ml src/ocaml-output/ src/basic/ml)
FSTAR=$(FSTAR_HOME)/bin/fstar.exe

.PRECIOUS: %.ml %.cmxs

MODULES=Print Split Canon

all: $(patsubst %,%.test,$(MODULES))

%.ml: %.fst
	$(FSTAR) $(OTHERFLAGS) --lax --codegen OCaml $< --extract_module $(patsubst %.fst,%,$<)
	@# Sneaky fix...
	sed -i 's/Reflection_Syntax\.\(Tv\|C_\)/Reflection_Data.\1/g' *.ml

%.cmxs: %.ml
	ocamlfind ocamlopt -shared $(INCLUDES) -linkpkg -package zarith -o $@ $<

.PHONY: test

%.test: %.cmxs %.Test.fst 
	$(FSTAR) --load $^ --admit_smt_queries true

clean:
	rm -f *.ml *.cm*
