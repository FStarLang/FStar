VERFILES=stlc_cbv_db_pntsubst_nolists.fst stlc_cbv_named.fst db_subst.fst hs.fst
include ../Makefile.include
all: .all.ver pars stlc_cbv_db_parsubst lambda_omega f-omega micro-fstar hoare_wp

_STDLIB_=FStar.Constructive.fst FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst --admit_fsi FStar.Set

pars:
	$(FSTAR) $(_STDLIB_) pars.fst --max_fuel 1 --max_ifuel 1

stlc_strong_db_parsubst:
	$(FSTAR) stlc_strong_db_parsubst.fst --max_fuel 1 --max_ifuel 1

stlc_cbv_db_parsubst:
	$(FSTAR) stlc_cbv_db_parsubst.fst --max_fuel 1 --max_ifuel 1

lambda_omega:
	$(FSTAR) $(_STDLIB_) lambda_omega.fst --max_fuel 1 --max_ifuel 1 --initial_fuel 1

f-omega:
	$(FSTAR) f-omega.fst

micro-fstar:
	$(FSTAR) micro-fstar.fst

hoare_wp:
	$(FSTAR) $(_STDLIB_) hoare_wp.fst --max_fuel 1 --max_ifuel 1

# This takes forever to verify
stlc_cbv_db_pntsubst_lists:
	make stlc_cbv_db_pntsubst_lists.fulllib.ver OTHERFLAGS='--z3timeout 20'
