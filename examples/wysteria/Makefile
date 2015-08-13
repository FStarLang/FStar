include ../Makefile.include
all:
	$(FSTAR) wysteria.fst
	$(FSTAR) mill1.fst
	$(FSTAR) mill2.fst
	$(FSTAR) mill3.fst
	$(FSTAR) mill4.fst
	$(FSTAR) mill5.fst
	$(FSTAR) gps.fst
	$(FSTAR) theory.fst
	$(FSTAR) sinterpreter.fst


OCAMLC=ocamlfind ocamlc -thread -package batteries -linkpkg -g
OCAMLOPT=ocamlfind ocamlopt -thread -package batteries -linkpkg -g

gen: ast.fst ffi.fsi sem.fst sinterpreter.fst support.ml ordSet.ml ordMap.ml wparser.mly wlexer.mll
	$(FSTAR) --admit_fsi OrdSet --admit_fsi OrdMap --admit_fsi FFI --codegen OCaml-experimental --z3timeout 15 ../../lib/ordset.fsi ../../lib/ordmap.fsi ../../lib/classical.fst ast.fst ffi.fsi sem.fst sinterpreter.fst
	ocamlyacc -v wparser.mly
	ocamllex wlexer.mll

INTERPRETER_OBJS=support.cmx ordSet.cmx ordMap.cmx AST.cmx FFI.cmx Semantics.cmx SourceInterpreter.cmx

PARSER_OBJS=wparser.cmi wparser.cmx wlexer.cmx main.cmx

a.out: $(INTERPRETER_OBJS) $(PARSER_OBJS)
	$(OCAMLOPT) -o a.out $(INTERPRETER_OBJS) wparser.cmx wlexer.cmx main.cmx

# Common rules
.SUFFIXES: .ml .mli .cmo .cmi .cmx

.ml.cmo:
	$(OCAMLC) $(OCAMLFLAGS) -c $<

.mli.cmi:
	$(OCAMLC) $(OCAMLFLAGS) -c $<

.ml.cmx:
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -c $<

clean:
	rm -f *.cmi *.cmx *.o *.exe a.out

distclean: clean
	rm -f Classical.ml AST.ml Semantics.ml SourceInterpreter.ml wlexer.ml wparser.ml wparser.mli wparser.output
