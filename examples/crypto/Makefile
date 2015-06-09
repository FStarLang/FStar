VERFILES=cca2.fst mac.fst format.fst rpc.fst sig.fst padding.fst mac3.fst #encrypt3.fst wysteria.fst millionaires.fst
include ../Makefile.include
all: .all.oldlib.ver millionaires acls-cap

millionaires:
	$(FSTAR) --admit_fsi Set --admit_fsi Map $(STDLIB) $(FSTAR_HOME)/lib/map.fsi wysteria.fst millionaires.fst

mac:
	$(FSTAR) $(FSTAR_HOME)/lib/partialmap.fst $(FSTAR_HOME)/lib/st.fst mac.fst

merkle_tree:
	$(FSTAR) $(FSTAR_HOME)/lib/list.fst $(FSTAR_HOME)/lib/constr.fst merkle_tree.fst

acls-cap: mac.fst ../security/acls2.fst acls-cap.fst
	$(FSTAR) $(addprefix $(FSTAR_HOME)/lib/, string.fst partialmap.fst st.fst list.fst ) $^
