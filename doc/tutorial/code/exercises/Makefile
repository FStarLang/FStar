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

## Extracting and compiling the ACL example using OCaml -- the simple way ##

SUPPORT_FILES=prims.ml FStar_Set.ml FStar_ST.ml FStar_All.ml

SUPPORT=$(addprefix $(FSTAR_HOME)/lib/ml/, $(SUPPORT_FILES))

extract-acl:
	fstar.exe --codegen OCaml ex1a-safe-read-write.fst
	cp system.io.ml System_IO.ml
	cp $(SUPPORT) .    # copying these things just to make ocamlfind happy

ML_FILES = System_IO.ml FileName.ml ACLs.ml UntrustedClientCode.ml

OCAMLOPT=ocamlfind ocamlopt -thread -package batteries -linkpkg -g

simple-acl:
	make clean-acl
	make extract-acl
	$(OCAMLOPT) -o acls.exe $(SUPPORT_FILES) $(ML_FILES) main.ml

## Extracting and compiling the ACL example using OCaml -- the hard/better way ##

OCAMLDEP=ocamldep

deps-acl:
	$(OCAMLDEP) *.ml > .depend

acls.exe: $(SUPPORT_FILES:.ml=.cmx) $(ML_FILES:.ml=.cmx) main.ml
	$(OCAMLOPT) -o acls.exe $^

.SUFFIXES: .ml .cmx

%.cmx: %.ml
	$(OCAMLOPT) -c $<

hard-acl:
	make clean-acl
	make extract-acl
	make deps-acl
	make acls.exe

STUFF = FStar_All.ml FStar_ST.ml System_IO.ml

clean-acl:
	rm -f $(ML_FILES) $(STUFF) *.cmi *.cmx *.o *~ acl acls.exe

-include .depend
