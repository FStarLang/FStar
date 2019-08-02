FSTAR_HOME=../..
FSTAR_FILES = ParSubst.fst StlcCbvDbPntSubstNoLists.fst		\
	      StlcStrongDbParSubst.fst StlcCbvDbParSubst.fst	\
	      LambdaOmega.fst StackMachine.fst indind.fst

all:
	mkdir -p $(CACHE_DIR)
	$(MAKE) verify-all

include ../Makefile.common

verify-all: $(addsuffix .checked, $(addprefix $(CACHE_DIR)/, $(FSTAR_FILES)))

# This takes forever to verify
StlcCbvDbPntSubstLists:
	$(FSTAR) StlcCbvDbPntSubstLists.fst --z3rlimit 20
