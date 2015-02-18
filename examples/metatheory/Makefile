VERFILES=stlc_cbv_db_pntsubst_nolists.fst stlc_cbv_named.fst pars.fst
include ../Makefile.include
all: .all.ver tinyfstar.vv stlc_cbv_db_pntsubst_lists stlc_strong_db_parsubst

stlc_strong_db_parsubst:
	make stlc_strong_db_parsubst.vv OTHERFLAGS='--max_fuel 2 --max_ifuel 1'

stlc_cbv_db_pntsubst_lists:
	make stlc_cbv_db_pntsubst_lists.fulllib.ver OTHERFLAGS='--z3timeout 20'
