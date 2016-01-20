# Change whatever is necessary
CPP=cpp -ffreestanding

FSTAR_HOME=../..
FSTAR=$(FSTAR_HOME)/bin/fstar.exe
FSTAR_OPTIONS=--z3timeout 30

OCAMLC=ocamlfind ocamlc -thread -package batteries -linkpkg -g
OCAMLOPT=ocamlfind ocamlopt -thread -package batteries -linkpkg -g
OCAMLDEP=ocamldep
SUPPORTDIR=$(FSTAR_HOME)/src/ocaml-output
INCLUDES=$(addprefix -I $(SUPPORTDIR)/, Support)
OCAMLFLAGS=$(INCLUDES)    # add other options for ocamlc here
OCAMLOPTFLAGS=$(INCLUDES) # add other options for ocamlopt here

STDLIB=$(addprefix $(FSTAR_HOME)/lib/, FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst seq.fsi FStar.SeqProperties.fst FStar.Array.fst)
ADMITS=FStar.Set FStar.Seq

FSTAR_FILES=axiomatic.p.fst intlib.p.fst limb.fst eval.p.fst addition.p.fst scalar_multiplication.p.fst shift_array.p.fst multiplication.p.fst

LAX_FILES=carry.p.fst resize.p.fst

OOCAML_FILES=support.ml Axiomatic.ml IntLib.ml Limb.ml Seq.ml Eval.ml Addition.ml ScalarMultiplication.ml ShiftArray.ml Multiplication.ml Carry.ml Resize.ml

OCAML_FILES=support.cmx Axiomatic.cmx IntLib.cmx Limb.cmx Seq.cmx Eval.cmx Addition.cmx ScalarMultiplication.cmx ShiftArray.cmx Resize.cmx Multiplication.cmx Carry.cmx

.PHONY: preproc-verify verify preproc-codegen codegen all ml compile

all: preproc-verify verify

verify: $(STDLIB) $(FSTAR_FILES)
	$(FSTAR) $(FSTAR_OPTIONS) $(addprefix --admit_fsi , $(ADMITS)) $^

addition:$(STDLIB) axiomatic.p.fst intlib.p.fst limb.fst eval_st.fst # addition_st.p.fst
	$(FSTAR) $(FSTAR_OPTIONS) $(addprefix --admit_fsi , $(ADMITS)) $^ --verify_module Eval

preproc-verify:
#	rm -f *.p.fst || true
	@echo "#define VERIFY" > preproc.h
	@echo "#define RESET #reset-options" >> preproc.h
	@echo "#define SET #set-options" >> preproc.h

preproc-codegen:
#	rm -f *.p.fst || true
	@echo "#define COMPILE" > preproc.h
	@echo "#define RESET #reset-options" >> preproc.h
	@echo "#define SET #set-options" >> preproc.h

OCAML_LIB_FILES=./ml/Seq.ml
codeg: $(STDLIB) $(FSTAR_FILES) $(LAX_FILES)
	$(FSTAR) $(FSTAR_OPTIONS) $(addprefix --admit_fsi , $(ADMITS)) $^ --codegen OCaml
	cp $(OCAML_LIB_FILES) .

codegen: preproc-codegen codeg

lax: $(STDLIB) $(FSTAR_FILES) $(LAX_FILES)
	$(FSTAR) $(FSTAR_OPTIONS) $(addprefix --admit_fsi , $(ADMITS)) $^ --lax

clean:
	rm -f *.p.fst *~  preproc.h || true
	rm -f *.cmo *.cmx *.cmi *.o *.out ml/*.cmx ml/*.o ml/*.cmi ml/*.cmo || true
	rm -f *.ml || true

ml: $(OCAML_FILES) 

compile: ml

test: ml
	ocamlfind ocamlopt -thread -package batteries,zarith -linkpkg -g -p -I +zarith -I /home/jkz/fstar/FStar/src/ocaml-output/Support $(OCAML_FILES)  ./ml/unit_test.ml -o a.out
	./a.out

debug: ml
	ocamlfind ocamlc -thread -package batteries,zarith -linkpkg -g -I +zarith -I /home/jkz/fstar/FStar/src/ocaml-output/Support $(OOCAML_FILES)  ./ml/unit_test.ml -o a.out
	./a.out

%.p.fsi: %.fsi
	$(CPP)  -C $^ 2>/dev/null | sed '/^[#] 1 "<.*/d' > $@

%.p.fsti: %.fsti
	$(CPP)  -C $^ 2>/dev/null | sed '/^[#] 1 "<.*/d' > $@

%.p.fst: %.fst
	$(CPP) -P -C $^ 2>/dev/null | sed '/^[#] 1 "<.*/d' > $@

.SUFFIXES: .ml .mli .cmo .cmi .cmx

support.ml:
	cp $(SUPPORTDIR)/support.ml .

.ml.cmo:
	$(OCAMLC) $(OCAMLFLAGS) -c $<

.mli.cmi:
	$(OCAMLC) $(OCAMLFLAGS) -c $<

.ml.cmx:
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -c $<

# Dependencies
depend:
	$(OCAMLDEP) ../../libs/ml/*.ml* *.ml > .depend

-include .depend
