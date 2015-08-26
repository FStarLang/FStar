include ../Makefile.include

all: api theory codegen clean

api:
	$(FSTAR) wysteria.fst
	$(FSTAR) mill1.fst
	$(FSTAR) mill2.fst
	$(FSTAR) mill3.fst
	$(FSTAR) mill4.fst
	$(FSTAR) mill5.fst
	$(FSTAR) gps.fst
	$(FSTAR) median.fst

theory:
	$(FSTAR) theory.fst

OCAMLOPT=ocamlfind ocamlopt -thread -package batteries -linkpkg -g -w -8

codegen:
	$(FSTAR) --admit_fsi FStar.OrdSet --admit_fsi FStar.OrdMap --admit_fsi FFI --codegen OCaml ../../lib/ordset.fsi ../../lib/ordmap.fsi ../../lib/classical.fst ast.fst ffi.fsi sem.fst sinterpreter.fst

ocaml: 
	cp $(FSTAR_HOME)/lib/ml/prims.ml .
	cp $(FSTAR_HOME)/lib/ml/FStar_All.ml .
	$(OCAMLOPT) prims.ml FStar_All.ml FStar_OrdSet.ml FStar_OrdMap.ml AST.ml FFI.ml Semantics.ml SourceInterpreter.ml -o a.out

clean:
	rm -f Classical.ml AST.ml Semantics.ml SourceInterpreter.ml *.cmi *.cmx *.o *.exe a.out support.ml
