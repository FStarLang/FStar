FSTAR_HOME=../..
include ../Makefile.include
all: uall sall

uall: ParSubst.uver StlcCbvDbPntSubstNoLists.uver StlcStrongDbParSubst.uver StlcCbvDbParSubst.uver LambdaOmega StackMachine.uver
sall: StlcCbvNamed.sver DbSubst.sver HereditarySubst.sver FOmega.sver MicroFStar.sver HoareWeakestPrecondition

LambdaOmega:
	$(FSTAR) LambdaOmega.fst --max_fuel 1 --max_ifuel 1 --initial_fuel 1

HoareWeakestPrecondition:
	$(SFSTAR) $(_STDLIB_) HoareWeakestPrecondition.fst --max_fuel 1 --max_ifuel 1

# This takes forever to verify
StlcCbvDbPntSubstLists:
	$(FSTAR) StlcCbvDbPntSubstLists.fst --z3timeout 20
