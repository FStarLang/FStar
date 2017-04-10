FSTAR_HOME=../..
include ../Makefile.include
all: uall

uall: ParSubst.uver StlcCbvDbPntSubstNoLists.uver StlcStrongDbParSubst.uver StlcCbvDbParSubst.uver LambdaOmega StackMachine.uver

LambdaOmega:
	$(FSTAR) LambdaOmega.fst --max_fuel 1 --max_ifuel 1 --initial_fuel 1

# This takes forever to verify
StlcCbvDbPntSubstLists:
	$(FSTAR) StlcCbvDbPntSubstLists.fst --z3rlimit 20
