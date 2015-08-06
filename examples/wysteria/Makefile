include ../Makefile.include
all:
	$(FSTAR) examples.fst
	$(FSTAR) wysteria.fst
	#$(FSTAR) ast.fst
	#$(FSTAR) sem.fst
	$(FSTAR) theory.fst
	$(FSTAR) sinterpreter.fst


OCAMLOPT=ocamlfind ocamlopt -thread -package batteries -linkpkg -g

interpreter:
	$(FSTAR) --admit_fsi OrdSet --admit_fsi OrdMap --codegen OCaml-experimental ../../lib/ordset.fsi ../../lib/ordmap.fsi ../../lib/classical.fst ast.fst sem.fst sinterpreter.fst
	$(OCAMLOPT) support.ml ordSet.ml ordMap.ml AST.ml Semantics.ml SourceInterpreter.ml -o interpreter.exe

parser: interpreter
	ocamlyacc -v wparser.mly
	ocamllex wlexer.mll
	$(OCAMLOPT) wparser.mli
	$(OCAMLOPT) wlexer.ml
	$(OCAMLOPT) wparser.ml 

clean:
	rm -f Classical.ml AST.ml Semantics.ml SourceInterpreter.ml *.cmi *.cmx *.o *.exe a.out wlexer.ml wparser.ml wparser.mli wparser.output 
