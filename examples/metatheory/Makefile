VERFILES=stlc_cbv_db_pntsubst_nolists.fst stlc_cbv_named.fst db_subst.fst
include ../Makefile.include
all: .all.ver pars stlc_cbv_db_parsubst lo-reduced f-omega micro-fstar hoare_wp

_STDLIB_=constr.fst classical.fst ext.fst set.fsi heap.fst st.fst all.fst --admit_fsi Set

pars:
	$(FSTAR) $(_STDLIB_) pars.fst --max_fuel 1 --max_ifuel 1

stlc_cbv_db_parsubst:
	$(FSTAR) $(_STDLIB_) stlc_strong_db_parsubst.fst stlc_cbv_db_parsubst.fst --max_fuel 1 --max_ifuel 1

lo:
	$(FSTAR) $(_STDLIB_) lambda_omega.fst --max_fuel 1 --max_ifuel 1 --initial_fuel 1

lo-reduced:
	$(FSTAR) $(_STDLIB_) lambda_omega_reduced.fst

f-omega:
	$(FSTAR) $(_STDLIB_) f-omega.fst --max_fuel 1 --max_ifuel 1 --initial_fuel 1 --z3timeout 15

micro-fstar: micro-fstar.fst
	$(FSTAR) $^

hoare_wp:
	$(FSTAR) $(_STDLIB_) hoare_wp.fst --max_fuel 1 --max_ifuel 1

###################################
#old
###################################
stlc_strong_db_parsubst:
	$(FSTAR) $(_STDLIB_) stlc_strong_db_parsubst.fst --max_fuel 1 --max_ifuel 1

norm-take2:
	$(FSTAR) ../../lib/constr.fst ../../lib/classical.fst ../../lib/ext.fst stlc_strong_db_parsubst.fst norm-take2.fst --max_fuel 1 --max_ifuel 1

norm-take3:
	$(FSTAR) ../../lib/constr.fst ../../lib/classical.fst ../../lib/ext.fst stlc_strong_db_parsubst.fst norm-take3.fst --max_fuel 1 --max_ifuel 1

stlc_cbv_db_pntsubst_lists:
	make stlc_cbv_db_pntsubst_lists.fulllib.ver OTHERFLAGS='--z3timeout 20'
