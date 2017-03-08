VERFILES=bug015.fst bug019.fst\
  bug021.fst bug022.fst bug023.fst bug024.fst bug025.fst\
  bug029.fst bug026.fst bug028.fst bug034.fst\
  bug052.fst bug056.fst bug058.fst bug062.fst bug067.fst bug077.fst\
  bug092.fst bug096.fst bug097b.fst bug101.fst bug103.fst\
  bug111.fst bug116.fst bug117.fst bug122.fst bug124.fst bug139.fst\
  bug148.fst bug155.fst bug161.fst bug162.fst bug170.fst bug175.fst bug178.fst\
  bug179.fst bug181.fst bug184.fst bug184Eta.fst bug184b.fst\
  bug186.fst bug189.fst bug190.fst bug192.fst bug195.fst\
  bug203.fst bug212.fst bug213.fst bug-295.fst bug316.fst\
  bug331.fst bug331Iso.fst bug331Index.fst bugWildcardTelescopes.fst

# CH: bug060.fst started failing somewhere before 2016-09-07

FSTAR_HOME=../..
include ../Makefile.include

all:

uall: $(subst .fst,.uver,$(VERFILES))

bug194: bug194.fst
	$(FSTAR) --explicit_deps ../../lib/FStar.Classical.fst ../../lib/FStar.FunctionalExtensionality.fst ../../lib/FStar.Constructive.fst ../metatheory/stlc_strong_db_parsubst.fst bug194.fst

bug244: bug244.fst
	$(FSTAR)  --explicit_deps ../../lib/FStar.String.fsti bug244.fst

insertionsortcmp: insertionsortcmp.fst
	$(FSTAR) insertionsortcmp.fst

insertionsortcmpfails: insertionsortcmpfails.fst
	$(FSTAR) insertionsortcmpfails.fst

insertionsortcmpfails2: insertionsortcmpfails2.fst
	$(FSTAR) insertionsortcmpfails2.fst


extraction-error1:
	$(FSTAR) extraction-error1.fst
	ocamlfind ocamlopt -cc "$(CC)" -cclib -L$(LIB) -o Bug.exe -package batteries -linkpkg -g -thread -I \
	        $(FSTAR_HOME)/src/ocaml-output/ \
					$(FSTAR_HOME)/src/ocaml-output/support.ml \
			    Bug.ml

ExtractionBug.ver:
	$(FSTAR) --explicit_deps  FStar.FunctionalExtensionality.fst FStar.Set.fst FStar.Heap.fst FStar.Map.fst FStar.List.Tot.fst FStar.HyperHeap.fsi stHyperHeap.fst ExtractionBug.fst --dump_module ExtractionBug --print_implicits --codegen OCaml

ExtractionBug.out:
	cp ../../lib/ml/native_int/prims.ml .
	cp ../../lib/ml/hyperheap/*ml .
	ocamlc prims.ml FStar_HyperHeap.ml FStar_ST.ml ExtractionBug.ml

extraction-error2: ExtractionBug.ver 
	cp ../../lib/ml/native_int/prims.ml .
	cp ../../lib/ml/hyperheap/*ml .
	ocamlc prims.ml FStar_HyperHeap.ml FStar_ST.ml ExtractionBug.ml

FSTAR_HOME=../..
include $(FSTAR_HOME)/ulib/ml/Makefile.include

extraction-bug734: bug734.fst
	mkdir -p out
	$(MAKE) -C $(ULIB_ML)
	$(FSTAR) --explicit_deps $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml bug734.fst
	$(OCAMLOPT) out/Bug734.ml -o bug734.exe
	./bug734.exe

all-cver:

export CFSTAR=$(subst CURRENT_DIR,examples/bug-reports,$(CVERFSTAR))
uall-cver: $(subst .fst,.ucver,$(VERFILES))
