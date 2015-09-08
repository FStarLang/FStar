include ../Makefile.include

all: api sinterpreter tinterpreter theory codegen distclean

api:
	$(FSTAR) wysteria.fst
	$(FSTAR) mill1.fst
	$(FSTAR) mill2.fst
	$(FSTAR) mill3.fst
	$(FSTAR) mill4.fst
	$(FSTAR) mill5.fst
	$(FSTAR) gps.fst
	$(FSTAR) median.fst

sinterpreter:
	$(FSTAR) sinterpreter.fst

tinterpreter:
	$(FSTAR) tinterpreter.fst

theory:
	$(FSTAR) theory.fst

OCAMLOPT=ocamlfind ocamlopt -thread -package batteries -linkpkg -g -w -8

LIB = $(FSTAR_HOME)/lib

codegen:
	$(FSTAR) --admit_fsi FStar.OrdSet --admit_fsi FStar.OrdMap --admit_fsi FStar.Set\
	         --admit_fsi FFI --admit_fsi Runtime --codegen OCaml $(LIB)/ordset.fsi\
					 $(LIB)/ordmap.fsi $(LIB)/classical.fst $(LIB)/set.fsi $(LIB)/heap.fst $(LIB)/st.fst\
					 $(LIB)/all.fst ast.fst ffi.fsi sem.fst sinterpreter.fst runtime.fsi tinterpreter.fst\
					 sec_server.fst main.fst

a.out: codegen
	cp $(FSTAR_HOME)/lib/ml/prims.ml .
	cp $(FSTAR_HOME)/lib/ml/FStar_All.ml .
	cp $(FSTAR_HOME)/lib/ml/FStar_ST.ml .
	$(OCAMLOPT) prims.ml FStar_ST.ml FStar_All.ml FStar_OrdSet.ml FStar_OrdMap.ml \
	            AST.ml FFI.ml Semantics.ml SourceInterpreter.ml Runtime.ml TargetInterpreter.ml SecServer.ml Main.ml -o a.out
clean:
	rm -f *.cmi *.cmx *.o *.exe a.out 

distclean:
	rm -f AST.ml prims.ml FStar_All.ml FStar_Classical.ml FStar_Heap.ml FStar_ST.ml SecServer.ml TargetInterpreter.ml Semantics.ml SourceInterpreter.ml Main.ml *.cmi *.cmx *.o *.exe a.out 
