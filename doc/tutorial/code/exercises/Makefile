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

extract-acl: clean-acl
	fstar.exe --codegen OCaml ex1a-safe-read-write.fst
	make ocaml-acl-deps

ML_FILES = FileName.ml ACLs.ml UntrustedClientCode.ml
ALL_FILES= prims.ml FStar_Set.ml FStar_ST.ml FStar_All.ml FileName.ml System_IO.ml ACLs.ml UntrustedClientCode.ml main.ml
STUFF = FStar_All.ml FStar_ST.ml System_IO.ml

SUPPORT_DIR = $(FSTAR_HOME)/src/support/ocaml/fstar-lib/src

ocaml-acl: deps
	ocamlfind ocamlopt -o acl -package batteries -linkpkg -thread $(SUPPORT_DIR)/prims.ml $(SUPPORT_DIR)/FStar_ST.ml $(SUPPORT_DIR)/FStar_All.ml system.ml $(ML_FILES) main.ml

OCAMLDEP=ocamldep
OCAMLOPT=ocamlfind ocamlopt -thread -package batteries -linkpkg -g

ocaml-acl-deps: $(addprefix $(SUPPORT_DIR)/, prims.ml FStar_Set.ml FStar_ST.ml FStar_All.ml) 
	cp $^ .
	cp system.io.ml System_IO.ml
	$(OCAMLDEP) *.ml > .depend

acls.exe: $(ALL_FILES:.ml=.cmx)
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -o acls.exe $^

%.cmx: %.ml
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -c $<

clean-acl:
	rm -f $(ML_FILES) $(STUFF) *.cmi *.cmx *.o *~ acl acls.exe

-include .depend
