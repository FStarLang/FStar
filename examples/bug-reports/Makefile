VERFILES=bug015.fst bug019.fst\
  bug021.fst bug022.fst bug023.fst bug024.fst bug025.fst\
  bug029.fst bug026.fst bug028.fst bug034.fst\
  bug052.fst bug056.fst bug058.fst bug060.fst bug062.fst bug067.fst bug077.fst\
  bug092.fst bug096.fst bug097b.fst bug101.fst bug103.fst\
  bug111.fst bug116.fst bug117.fst bug122.fst bug124.fst bug139.fst\
  bug148.fst bug155.fst bug161.fst bug162.fst bug170.fst bug175.fst bug178.fst\
  bug179.fst bug181.fst bug184.fst bug184b.fst\
  bug186.fst bug189.fst bug190.fst bug192.fst bug195.fst\
  bug203.fst bug212.fst bug213.fst bug-295.fst bug316.fst bug331.fst\
  bugWildcardTelescopes.fst

include ../Makefile.include
all: .all.ver

bug194: bug194.fst
	../../bin/fstar.exe ../../lib/FStar.Classical.fst ../../lib/FStar.FunctionalExtensionality.fst ../../lib/FStar.Constructive.fst ../metatheory/stlc_strong_db_parsubst.fst bug194.fst

bug244: bug244.fst
	../../bin/fstar.exe  ../../lib/FStar.String.fst bug244.fst

insertionsortcmp: insertionsortcmp.fst
	../../bin/fstar.exe insertionsortcmp.fst

insertionsortcmpfails: insertionsortcmpfails.fst
	../../bin/fstar.exe insertionsortcmpfails.fst

insertionsortcmpfails2: insertionsortcmpfails2.fst
	../../bin/fstar.exe insertionsortcmpfails2.fst


extraction-error1:
	fstar extraction-error1.fst
	ocamlfind ocamlopt -cc "$(CC)" -cclib -L$(LIB) -o Bug.exe -package batteries -linkpkg -g -thread -I \
	        $(FSTAR_HOME)/src/ocaml-output/ \
					$(FSTAR_HOME)/src/ocaml-output/support.ml \
			    Bug.ml
