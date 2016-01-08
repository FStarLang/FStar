# Change whatever is necessary
CPP=cpp -ffreestanding

FSTAR_HOME=../..
FSTAR=$(FSTAR_HOME)/bin/fstar.exe
FSTAR_OPTIONS=--z3timeout 50 --prims prims.fst --max_fuel 10 --max_ifuel 10 --initial_ifuel 2 --initial_fuel 2

OCAMLC=ocamlfind ocamlc -thread -package batteries -linkpkg -g
OCAMLOPT=ocamlfind ocamlopt -thread -package batteries -linkpkg -g
OCAMLDEP=ocamldep
SUPPORTDIR=$(FSTAR_HOME)/src/ocaml-output
INCLUDES=$(addprefix -I $(SUPPORTDIR)/, Support)
OCAMLFLAGS=$(INCLUDES)    # add other options for ocamlc here
OCAMLOPTFLAGS=$(INCLUDES) # add other options for ocamlopt here

STDLIB=$(addprefix $(FSTAR_HOME)/lib/, FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst seq.fsi FStar.SeqProperties.fst FStar.Array.fst)
ADMITS=FStar.Set FStar.Seq

FSTAR_ST_FILES=axiomatic.p.fst intlib.p.fst limb.fst bigint_st.fst eval_st.fst addition_st.fst substraction_st.fst scalar_multiplication_st.fst multiplication_st.fst

LAX_ST_FILES=carry_st.fst retemplate_st.fst compare_st.fst shift_st.fst neg_st.fst modulo_st.fst division_st.fst

OCAML_FILES=support.cmx IntLib.cmx Seq.cmx Limb.cmx Bigint.cmx Eval.cmx Addition.cmx Substraction.cmx ScalarMultiplication.cmx Retemplate.cmx Multiplication.cmx Carry.cmx Compare.cmx Neg.cmx Shift.cmx Modulo.cmx Division.cmx

.PHONY: preproc-verify wo work

all: preproc-verify verify

verify: $(STDLIB) $(FSTAR_ST_FILES)
	$(FSTAR) $(FSTAR_OPTIONS) $(addprefix --admit_fsi , $(ADMITS)) $^

work: preproc-verify wo

wo: $(STDLIB) axiomatic.p.fst intlib.p.fst limb.fst bigint_st.fst eval_st.fst addition_st.fst substraction_st.fst scalar_multiplication_st.fst multiplication_st.fst compare_st.fst
	$(FSTAR) $(FSTAR_OPTIONS) $(addprefix --admit_fsi , $(ADMITS)) $^ --verify_module Compare

carry: preproc-verify carr

carr: $(STDLIB) axiomatic.p.fst intlib.p.fst limb.fst bigint_st.fst eval_st.fst carry_st.fst
	$(FSTAR) $(FSTAR_OPTIONS) $(addprefix --admit_fsi , $(ADMITS)) $^ --lax #--verify_module Carry

retemplate: preproc-verify retemplat

retemplat: $(STDLIB) axiomatic.p.fst intlib.p.fst limb.fst bigint_st.fst eval_st.fst retemplate_st.fst
	$(FSTAR) $(FSTAR_OPTIONS) $(addprefix --admit_fsi , $(ADMITS)) $^ --lax #--verify_module Retemplate

neg: preproc-verify ne

ne: $(STDLIB) axiomatic.p.fst intlib.p.fst limb.fst bigint_st.fst eval_st.fst neg_st.fst
	$(FSTAR) $(FSTAR_OPTIONS) $(addprefix --admit_fsi , $(ADMITS)) $^ --verify_module Neg

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

OCAML_LIB_FILES=./ml/Seq.ml ./ml/Bigint.ml ./ml/IntLib.ml
codeg: $(STDLIB) $(FSTAR_ST_FILES) $(LAX_ST_FILES)
	$(FSTAR) $(FSTAR_OPTIONS) $(addprefix --admit_fsi , $(ADMITS)) $^ --codegen OCaml
	cp $(OCAML_LIB_FILES) .

codegen: preproc-codegen codeg

auxlax: $(STDLIB) $(FSTAR_ST_FILES) $(LAX_ST_FILES)
	$(FSTAR) $(FSTAR_OPTIONS) $(addprefix --admit_fsi , $(ADMITS)) $^ --lax

lax: preproc-verify auxlax

clean:
	rm -f *.p.fst *~  preproc.h || true
	rm -f *.cmo *.cmx *.cmi *.o *.out ml/*.cmx ml/*.o ml/*.cmi ml/*.cmo || true
	rm -f *.ml || true

ml: $(OCAML_FILES) 

compile: ml

test: ml
	ocamlfind ocamlopt -thread -package batteries,zarith -linkpkg -g -p -I +zarith -I /home/jkz/fs#tar/FStar/src/ocaml-output/Support $(OCAML_FILES)  ./ml/unit_test.ml -o a.out
	./a.out

debug : support.ml IntLib.ml Seq.ml Limb.ml Bigint.ml Eval.ml Addition.ml Substraction.ml ScalarMultiplication.ml Retemplate.ml Multiplication.ml Carry.ml Compare.ml Neg.ml Shift.ml Modulo.ml Division.ml
	ocamlfind ocamlc -thread -package batteries,zarith -linkpkg -g -I +zarith $^ ./ml/unit_test.ml -o a.out
	ocamldebug a.out

%.p.fsi: %.fsi
	$(CPP)  -C $^ 2>/dev/null | sed '/^[#] 1 "<.*/d' > $@

%.p.fsti: %.fsti
	$(CPP)  -C $^ 2>/dev/null | sed '/^[#] 1 "<.*/d' > $@

%.p.fst: %.fst
	$(CPP) -P -C $^ 2>/dev/null | sed '/^[#] 1 "<.*/d' > $@

.SUFFIXES: .ml .mli .cmo .cmi .cmx

support.ml:
	cp ./ml/support.ml .

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
