include ../Makefile.include

verify-ex8a-acls:  ex8a-acls.fst 
	$(FSTAR) $(addprefix $(FSTAR_HOME)/lib/, string.fst partialmap.fst st.fst list.fst ) $^

verify-ex9a-acls-cap: ../solutions/ex9a-mac.fst ../solutions/ex9a-acls2.fst ex9a-acls-cap.fst
	$(FSTAR) $(addprefix $(FSTAR_HOME)/lib/, string.fst partialmap.fst st.fst array-realized.fst ) ../../../examples/unit-tests/list.fst $^

verify-ex9b-format: ex9b-format.fst
	$(FSTAR) $(SECLIB) $^

verify-ex9c-format: ex9c-format.fst
	$(FSTAR) $(SECLIB) $^

verify-ex9d-padding: ex9d-padding.fst
	$(FSTAR) $(SECLIB) $^

verify-ex9e-padding: ex9e-padding.fst
	$(FSTAR) $(SECLIB) $^

verify-ex9f-padding: ex9f-padding.fst
	$(FSTAR) $(SECLIB) $^

verify-ex9g-padding: ex9g-padding.fst
	$(FSTAR) $(SECLIB) $^



verify-%: __force__
	$(FSTAR) $*.fst

verify-security: verify-ex9b-format verify-ex9c-format verify-ex9d-padding verify-ex9e-padding verify-ex9f-padding verify-ex9g-padding

extract-acl:
	fstar.exe --codegen OCaml-experimental ex1a-safe-read-write.fst
	sed -i "s/Support\\.System\\.IO/System.IO/" UntrustedClientCode.ml

ML_FILES = FileName.ml ACLs.ml UntrustedClientCode.ml

STUFF = All.ml Heap.ml ST.ml System_IO.ml

ocaml-acl:
	ocamlfind ocamlopt -o acl -package batteries -linkpkg -thread -I $(FSTAR_HOME)/src/ocaml-output/ $(FSTAR_HOME)/src/ocaml-output/support.ml system.ml $(ML_FILES) main.ml

clean-acl:
	rm -f $(ML_FILES) $(STUFF) *.cmi *.cmx *.o *~ acl
