VERFILES=stlc_cbv_db_pntsubst_nolists.fst stlc_cbv_named.fst db_subst.fst
include ../Makefile.include
all: .all.ver tinyfstar pars stlc_cbv_db_parsubst lo-reduced f-omega hoare_wp
# tinyfstar-new

pars:
	$(FSTAR) ../../lib/ext.fst pars.fst --max_fuel 1 --max_ifuel 1

tinyfstar: ../../lib/constr.fst tinyfstar.fst
	$(FSTAR) $^

tinyfstar-new: tinyfstar-new.fst
	$(FSTAR) $^

lo:
	$(FSTAR) ../../lib/constr.fst ../../lib/classical.fst ../../lib/ext.fst lambda_omega.fst --max_fuel 1 --max_ifuel 1 --initial_fuel 1

lo-reduced:
	$(FSTAR) ../../lib/constr.fst ../../lib/classical.fst ../../lib/ext.fst lambda_omega_reduced.fst

f-omega:
	$(FSTAR) ../../lib/constr.fst ../../lib/classical.fst ../../lib/ext.fst f-omega.fst --max_fuel 1 --max_ifuel 1 --initial_fuel 1 --z3timeout 15

stlc_strong_db_parsubst:
	$(FSTAR) ../../lib/constr.fst ../../lib/classical.fst ../../lib/ext.fst stlc_strong_db_parsubst.fst --max_fuel 1 --max_ifuel 1

stlc_cbv_db_parsubst:
	$(FSTAR) ../../lib/constr.fst ../../lib/classical.fst ../../lib/ext.fst stlc_strong_db_parsubst.fst stlc_cbv_db_parsubst.fst --max_fuel 1 --max_ifuel 1

norm-take2:
	$(FSTAR) ../../lib/constr.fst ../../lib/classical.fst ../../lib/ext.fst stlc_strong_db_parsubst.fst norm-take2.fst --max_fuel 1 --max_ifuel 1

norm-take3:
	$(FSTAR) ../../lib/constr.fst ../../lib/classical.fst ../../lib/ext.fst stlc_strong_db_parsubst.fst norm-take3.fst --max_fuel 1 --max_ifuel 1

stlc_cbv_db_pntsubst_lists:
	make stlc_cbv_db_pntsubst_lists.fulllib.ver OTHERFLAGS='--z3timeout 20'

hoare_wp:
	$(FSTAR) ../../lib/classical.fst hoare_wp.fst --max_fuel 1 --max_ifuel 1
