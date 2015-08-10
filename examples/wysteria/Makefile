include ../Makefile.include
all:
	$(FSTAR) wysteria.fst
	$(FSTAR) mill1.fst
	$(FSTAR) mill2.fst
	$(FSTAR) mill3.fst
	$(FSTAR) mill4.fst
	$(FSTAR) mill5.fst
	$(FSTAR) lib.fst    # remove once some example uses it
	$(FSTAR) theory.fst
	$(FSTAR) sinterpreter.fst


OCAMLOPT=ocamlfind ocamlopt -thread -package batteries -linkpkg -g

codegen:
	$(FSTAR) --admit_fsi OrdSet --admit_fsi OrdMap --codegen OCaml-experimental ../../lib/ordset.fsi ../../lib/ordmap.fsi ../../lib/classical.fst ast.fst sem.fst sinterpreter.fst
	$(OCAMLOPT) support.ml ordSet.ml ordMap.ml AST.ml Semantics.ml SourceInterpreter.ml -o a.out

clean:
	rm -f Classical.ml AST.ml Semantics.ml SourceInterpreter.ml *.cmi *.cmx *.o *.exe a.out
