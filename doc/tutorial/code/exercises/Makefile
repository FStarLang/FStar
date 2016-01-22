include ../Makefile.include

verify-ex8a-acls:  ex8a-acls.fst 
	$(FSTAR) $(addprefix $(FSTAR_HOME)/lib/, FStar.String.fst partialmap.fst FStar.ST.fst FStar.List.fst ) $^

verify-ex9a-acls-cap: ../solutions/ex9a-mac.fst ../solutions/ex9a-acls2.fst ex9a-acls-cap.fst
	$(FSTAR) $(addprefix $(FSTAR_HOME)/lib/, FStar.String.fst partialmap.fst FStar.ST.fst array-realized.fst ) ../../../examples/unit-tests/FStar.List.fst $^

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

verify-ex10a-acls: ex10a-acls.fst
	$(FSTAR) $(addprefix $(FSTAR_HOME)/lib/, FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.List.fst) --admit_fsi FStar.Set $^

verify-%: __force__
	$(FSTAR) $*.fst

verify-security: verify-ex9b-format verify-ex9c-format verify-ex9d-padding verify-ex9e-padding verify-ex9f-padding verify-ex9g-padding

## Extracting and compiling the ACL example using OCaml -- the simple way ##

SUPPORT_FILES=prims.ml FStar_All.ml

SUPPORT=$(addprefix $(FSTAR_HOME)/lib/ml/, $(SUPPORT_FILES))

extract-acl:
	fstar.exe --admit_fsi FileIO --codegen OCaml ex1a-safe-read-write.fst
	cp $(SUPPORT) .    # copying these things just to make ocamlfind happy

GEN_ML_FILES = FileName.ml ACLs.ml UntrustedClientCode.ml
ML_FILES = FileIO.ml $(GEN_ML_FILES)

OCAMLOPT=ocamlfind ocamlopt -thread -package batteries -linkpkg -g -w -26

acls-ocaml.exe: demo
	make clean-acl
	make extract-acl
	$(OCAMLOPT) -o acls-ocaml.exe $(SUPPORT_FILES) $(ML_FILES) main.ml

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
	make demo
	make acls.exe

## Extracting and compiling the ACL example using F#
SUPPORT_FS_FILES=prims.fs all.fs
LIB=$(FSTAR_HOME)/lib
BIN=$(FSTAR_HOME)/bin

ifeq ($(OS),Windows_NT)
FSC     = fsc --mlcompatibility $(addprefix -r , $(FS_LIBS))
else
FSC     = fsharpc --mlcompatibility $(addprefix -r , $(FS_LIBS))
endif

FS_LIBS=$(BIN)/FSharp.PowerPack.dll
SUPPORT_FS=$(addprefix $(FSTAR_HOME)/lib/fs/, $(SUPPORT_FS_FILES))
GEN_FS_FILES = FileName.fs ACLs.fs UntrustedClientCode.fs
FS_FILES=FileIO.fs $(GEN_FS_FILES)

acls-fs.exe: demo ex1a-safe-read-write.fst
	fstar.exe --codegen FSharp --admit_fsi FileIO ex1a-safe-read-write.fst
	$(FSC) -o $@ $(SUPPORT_FS) $(FS_FILES) main.fs

clean-acl:
	rm -f $(GEN_FS_FILES) $(GEN_ML_FILES) *.cmi *.cmx *.o *~ acl acls-fs.exe acls-ocaml.exe acls.exe
	rm -rf demo

demo:__force__
	mkdir -p demo
	echo "demo tempfile" > demo/tempfile
	echo "demo secret" > demo/passwd
	echo "demo readme" > demo/README

-include .depend
