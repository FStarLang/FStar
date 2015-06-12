CPP=cpp -ffreestanding

FSTAR=$(FSTAR_HOME)/bin/fstar.exe
FSTAR_OPTIONS=--z3timeout 20

OCAMLC=ocamlfind ocamlc -thread -package batteries -linkpkg -g
OCAMLOPT=ocamlfind ocamlopt -thread -package batteries -linkpkg -g
OCAMLDEP=ocamldep
SUPPORTDIR=$(FSTAR_HOME)/src/ocaml-output
INCLUDES=$(addprefix -I $(SUPPORTDIR)/, Support)
OCAMLFLAGS=$(INCLUDES)    # add other options for ocamlc here
OCAMLOPTFLAGS=$(INCLUDES) # add other options for ocamlopt here

STDLIB=$(addprefix $(FSTAR_HOME)/lib/, seq.fsi)
ADMITS=Seq

FSTAR_FILES=axiomatic.p.fst intlib.p.fst limb.fst eval.fst addition.fst scalar_multiplication.fst shift_array.fst multiplication.fst

OOCAML_FILES=support.ml IntLib.ml Axiomatic.ml Limb.ml Seq.ml Eval.ml Addition.ml ScalarMultiplication.ml ShiftArray.ml Multiplication.ml Carry.ml Resize.ml

OCAML_FILES=support.cmx IntLib.cmx Axiomatic.cmx Limb.cmx Seq.cmx Eval.cmx Addition.cmx ScalarMultiplication.cmx ShiftArray.cmx Resize.cmx Multiplication.cmx Carry.cmx

all: $(STDLIB) $(FSTAR_FILES)
	$(FSTAR) $(FSTAR_OPTIONS) $(addprefix --admit_fsi , $(ADMITS)) $^

# OCAML_LIB_FILES=./ml/Seq.ml
# codegen: $(STDLIB) $(FSTAR_FILES)
# 	$(FSTAR) $(FSTAR_OPTIONS) $(addprefix --admit_fsi , $(ADMITS)) $^ --codegen OCaml
# 	cp $(OCAML_LIB_FILES) .

lax: $(STDLIB) $(FSTAR_FILES)
	$(FSTAR) $(FSTAR_OPTIONS) $(addprefix --admit_fsi , $(ADMITS)) $^ --lax

clean:
	rm -f *.p.fst *~ || true
	rm -f *.cmo *.cmx *.cmi *.o *.out ml/*.cmx ml/*.o ml/*.cmi ml/*.cmo || true
	rm -f *.ml || true

ml: $(OCAML_FILES) 

test: ml
	ocamlfind ocamlopt -thread -package batteries -linkpkg -g -I /home/jkz/fstar/FStar/src/ocaml-output/Support $(OCAML_FILES)  ./ml/unit_test.ml -o a.out
	./a.out

debug: ml
	ocamlfind ocamlc -thread -package batteries -linkpkg -g -I /home/jkz/fstar/FStar/src/ocaml-output/Support $(OOCAML_FILES)  ./ml/unit_test.ml -o a.out
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
