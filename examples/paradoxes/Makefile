FSTAR_HOME=../..
include ../Makefile.include

all: uall

uall: propext propImpredicative

propext:
	$(FSTAR) PropositionalExtensionalityInconsistent.fst

propImpredicative:
	$(FSTAR) --__no_positivity propImpredicativeAndNonStrictlyPositiveinductives.fst

%.fst-in:
	@echo $(OPTIONS) \
	--__temp_no_proj InjectiveTypeFormers \
	--verify_module $(basename $(notdir $@))


CFSTAR=$(subst CURRENT_DIR,examples/paradoxes,$(CVERFSTAR))
all-cver: 
	$(CFSTAR) PropositionalExtensionalityInconsistent.fst
	$(CFSTAR) --__no_positivity propImpredicativeAndNonStrictlyPositiveinductives.fst

