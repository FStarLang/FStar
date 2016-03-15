VERFILES=stlc_cbv_db_pntsubst_nolists.fst stlc_cbv_named.fst db_subst.fst hs.fst
FSTAR_HOME=../..
include ../Makefile.include
all: .all.ver pars stlc_cbv_db_parsubst lambda_omega f-omega micro-fstar hoare_wp

_STDLIB_=FStar.Constructive.fst FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fst FStar.Heap.fst FStar.ST.fst FStar.All.fst 

pars:
	$(FSTAR) $(_STDLIB_) pars.fst --max_fuel 1 --max_ifuel 1

stlc_strong_db_parsubst:
	$(FSTAR) --explicit_deps FStar.Constructive.fst FStar.Classical.fst FStar.FunctionalExtensionality.fst stlc_strong_db_parsubst.fst --max_fuel 1 --max_ifuel 1

stlc_cbv_db_parsubst:
	$(FSTAR) --explicit_deps FStar.Constructive.fst FStar.Classical.fst FStar.FunctionalExtensionality.fst stlc_strong_db_parsubst.fst stlc_cbv_db_parsubst.fst --max_fuel 1 --max_ifuel 1

lambda_omega:
	$(FSTAR) $(_STDLIB_) lambda_omega.fst --max_fuel 1 --max_ifuel 1 --initial_fuel 1

f-omega:
	$(FSTAR) FOmega.fst

micro-fstar:
	$(FSTAR) MicroFStar.fst

hoare_wp:
	$(FSTAR) $(_STDLIB_) HoareWeakestPrecondition.fst --max_fuel 1 --max_ifuel 1

# This takes forever to verify
stlc_cbv_db_pntsubst_lists:
	make stlc_cbv_db_pntsubst_lists.fulllib.ver OTHERFLAGS='--z3timeout 20'
