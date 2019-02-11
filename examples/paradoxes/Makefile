FSTAR_HOME=../..
include ../Makefile.include

all: uall

uall: propext propImpredicative ioWpInconsistent

injectiveTypeFormers:
	$(FSTAR) InjectiveTypeFormers.Explicit.fst
	$(FSTAR) InjectiveTypeFormers.SMT.fst

propext:
	$(FSTAR) PropositionalExtensionalityInconsistent.fst

propImpredicative:
	$(FSTAR) --__no_positivity propImpredicativeAndNonStrictlyPositiveinductives.fst

ioWpInconsistent:
	$(FSTAR) IOWPInconsistent.fst

%.fst-in:
	@echo $(OPTIONS)
