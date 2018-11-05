FSTAR_HOME=../..
include ../Makefile.include

all: uall

uall: propext propImpredicative ioWpInconsistent

propext:
	$(FSTAR) PropositionalExtensionalityInconsistent.fst

propImpredicative:
	$(FSTAR) --__no_positivity propImpredicativeAndNonStrictlyPositiveinductives.fst

ioWpInconsistent:
	$(FSTAR) IOWPInconsistent.fst

%.fst-in:
	@echo $(OPTIONS)
