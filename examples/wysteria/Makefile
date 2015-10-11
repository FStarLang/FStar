include ../Makefile.include

all: api interpreter theory codegen distclean

api:
	$(FSTAR) wysteria.fst
	$(FSTAR) mill1.fst
	$(FSTAR) mill2.fst
	$(FSTAR) mill3.fst
	$(FSTAR) mill4.fst
	$(FSTAR) mill5.fst
	$(FSTAR) gps.fst
	$(FSTAR) median.fst

interpreter:
	$(FSTAR) interpreter.fst

theory:
	$(FSTAR) theory.fst

OCAMLOPT=ocamlfind ocamlopt -thread -package batteries -linkpkg -g -w -8

codegen:
	$(FSTAR) --admit_fsi FStar.OrdSet --admit_fsi FStar.OrdMap --admit_fsi FStar.Set\
	         --admit_fsi Ffibridge --admit_fsi Runtime --admit_fsi Prog --codegen OCaml --admit_fsi FStar.IO\
                 ghost.fst listTot.fst ordset.fsi ordmap.fsi classical.fst set.fsi heap.fst st.fst\
                 all.fst io.fsti string.fsi prins.fst ast.fst ffibridge.fsi sem.fst runtime.fsi print.fst interpreter.fst sec_server.fst prog.fsi main.fst ffi.fst

a.out: codegen
	cp $(FSTAR_HOME)/lib/ml/prims.ml .
	cp $(FSTAR_HOME)/lib/ml/FStar_ST.ml .
	cp $(FSTAR_HOME)/lib/ml/FStar_All.ml .
	cp $(FSTAR_HOME)/lib/ml/FStar_IO.ml .
	cp $(FSTAR_HOME)/lib/ml/FStar_List.ml .
	cp $(FSTAR_HOME)/lib/ml/FStar_String.ml .
	$(OCAMLOPT) prims.ml FStar_Ghost.ml FStar_List_Tot.ml FStar_OrdSet.ml FStar_OrdMap.ml FStar_ST.ml FStar_All.ml FStar_IO.ml FStar_List.ml FStar_String.ml  \
	            Prins.ml AST.ml ffibridge.ml Semantics.ml runtime.ml Print.ml Interpreter.ml SecServer.ml FFI.ml prog.ml Main.ml -o a.out
clean:
	rm -f *.cmi *.cmx *.o *.exe a.out 

distclean:
	rm -f prims.ml FStar_Ghost.ml FStar_List_Tot.ml FStar_ST.ml FStar_All.ml FStar_IO.ml FStar_List.ml FStar_String.ml Prins.ml AST.ml Semantics.ml Print.ml Interpreter.ml SecServer.ml FFI.ml Main.ml FStar_Classical.ml FStar_Heap.ml  *.cmi *.cmx *.o *.exe a.out
