VERFILES=stlc_cbv_db_pntsubst_nolists.fst stlc_cbv_named.fst 
include ../Makefile.include
all: .all.ver tinyfstar.vv pars stlc_strong_db_parsubst #stlc_cbv_db_pntsubst_lists 

pars:
	$(FSTAR) ../../lib/ext.fst pars.fst --max_fuel 1 --max_ifuel 1

lo:
	$(FSTAR) ../../lib/constr.fst ../../lib/classical.fst ../../lib/ext.fst lo.fst --max_fuel 1 --max_ifuel 1 

stlc_strong_db_parsubst:
	$(FSTAR) ../../lib/constr.fst ../../lib/classical.fst ../../lib/ext.fst stlc_strong_db_parsubst.fst --max_fuel 1 --max_ifuel 1

stlc_cbv_db_pntsubst_lists:
	make stlc_cbv_db_pntsubst_lists.fulllib.ver OTHERFLAGS='--z3timeout 20'
