VERFILES=cca2.fst mac.fst format.fst rpc.fst sig.fst padding.fst mac3.fst #encrypt3.fst wysteria.fst millionaires.fst
include ../Makefile.include
all: .all.oldlib.ver acls-cap merkle_tree

# millionaires:
# 	$(FSTAR) --admit_fsi Set --admit_fsi Map $(STDLIB) $(FSTAR_HOME)/lib/map.fsi wysteria.fst millionaires.fst


mac:
	$(FSTAR) $(FSTAR_HOME)/lib/partialmap.fst $(FSTAR_HOME)/lib/st.fst mac.fst

merkle_tree:
	$(FSTAR) $(FSTAR_HOME)/lib/list.fst $(FSTAR_HOME)/lib/constr.fst merkle_tree.fst

acls-cap: mac.fst ../security/acls2.fst acls-cap.fst
	$(FSTAR) $(addprefix $(FSTAR_HOME)/lib/, string.fst partialmap.fst st.fst list.fst ) $^

cnt-protocol: cnt-format.fst cnt-format.fsi cnt-mac.fst cnt-protocol.fst
	$(FSTAR) --admit_fsi Set $(addprefix $(FSTAR_HOME)/lib/, list.fst string.fst partialmap.fst ) cnt-format-deprecated.fst
	$(FSTAR) --z3timeout 10 --prims ../../lib/prims.fst --admit_fsi Seq --max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1 \
          $(addprefix $(FSTAR_HOME)/lib/, string.fst list.fst ext.fst classical.fst \
					set.fsi set.fst \
					heap.fst st.fst \
					seq.fsi seqproperties.fst ) cnt-format.fst cnt-mac.fst cnt-protocol.fst
