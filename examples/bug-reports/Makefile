VERFILES=bug22.fst bug19.fst bug29.fst bug26.fst bug15.fst bug25.fst bug24.fst\
  bug28.fst bug52.fst bug23.fst bug21.fst bug96.fst bug77.fst bug92.fst bug62.fst\
  bug67.fst bug56.fst bug103.fst bug96.fst bug60.fst bug97b.fst bug101.fst\
  bug111.fst bug116.fst bug117.fst bug122.fst bug124.fst \
  bug148.fst bug161.fst bug162.fst bug170.fst bug175.fst bug178.fst\
  bug179.fst bug181.fst bug186.fst bug189.fst bug190.fst bug192.fst bug195.fst\
  bug212.fst bug213.fst\
  bugWildcardTelescopes.fst

include ../Makefile.include
all: .all.ver

bug194: bug194.fst
	../../bin/fstar.exe ../../lib/classical.fst ../../lib/ext.fst ../../lib/constr.fst ../metatheory/stlc_strong_db_parsubst.fst bug194.fst

insertionsortcmp: insertionsortcmp.fst
	../../bin/fstar.exe ../../lib/list.fst insertionsortcmp.fst

insertionsortcmpfails: insertionsortcmpfails.fst
	../../bin/fstar.exe ../../lib/list.fst insertionsortcmpfails.fst

insertionsortcmpfails2: insertionsortcmpfails2.fst
	../../bin/fstar.exe ../../lib/list.fst insertionsortcmpfails2.fst
