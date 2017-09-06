FSTAR_HOME=../..

include $(FSTAR_HOME)/ulib/ml/Makefile.include

OCAML_OUTPUT=$(FSTAR_HOME)/src/ocaml-output
INCLUDES=$(addprefix -I $(OCAML_OUTPUT)/_build/, src/tactics/ml ulib/ml src/ocaml-output/ src/basic/ml)
FSTAR=$(FSTAR_HOME)/bin/fstar.exe

.PRECIOUS: %.ml %.cmxs
.PHONY: %.test

MODULES=Print Split Canon

all: $(patsubst %,%.test,$(MODULES))

.ulib: ../../bin/fstarlib/fstarlib.cmxa
	touch $@

../../bin/fstarlib/fstarlib.cmxa:
	$(MAKE) -C $(ULIB_ML)

%.ml: %.fst .ulib
	$(FSTAR) $(OTHERFLAGS) --lax --codegen OCaml $< --extract_module $(patsubst %.fst,%,$<)

%.cmxs: %.ml
	ocamlfind ocamlopt -shared $(INCLUDES) -linkpkg -package zarith -o $@ $<

%.test: %.cmxs %.Test.fst 
	$(FSTAR) --load $^ --admit_smt_queries true

clean:
	rm -f *.ml *.cm*
