VERFILES=StlcCbvNamed.fst DbSubst.fst HereditarySubst.fst
FSTAR_HOME=../..
include ../Makefile.include
all: .all.ver ParSubst.univ.ver StlcCbvDbPntSubstNoLists.univ.ver StlcStrongDbParSubst.univ.ver StlcCbvDbParSubst.univ.ver LambdaOmega FOmega.fst MicroFStar HoareWeakestPrecondition

_STDLIB_=FStar.Constructive.fst FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fst FStar.Heap.fst FStar.ST.fst FStar.All.fst 

%.univ.ver: %.fst
	$(FSTAR) --universes $^

LambdaOmega:
	$(FSTAR) $(_STDLIB_) LambdaOmega.fst --max_fuel 1 --max_ifuel 1 --initial_fuel 1

FOmega:
	$(FSTAR) FOmega.fst

MicroFStar:
	$(FSTAR) MicroFStar.fst

HoareWeakestPrecondition:
	$(FSTAR) $(_STDLIB_) HoareWeakestPrecondition.fst --max_fuel 1 --max_ifuel 1

# This takes forever to verify
StlcCbvDbPntsubstLists:
	make StlcCbvDbPntsubstLists.fulllib.ver OTHERFLAGS='--z3timeout 20'
