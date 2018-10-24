FSTAR_HOME=../..
include ../Makefile.include
ROOTS=HighComp.fst LowComp.fst sum_and_swap.fst

all: verify-all

.depend:
	$(FSTAR) --dep full $(ROOTS) > .depend

depend: .depend

include .depend

verify-all: $(addsuffix .checked, $(ALL_FST_FILES))

%.checked:
	$(FSTAR) --cache_checked_modules $<

clean:
	rm -f .depend *.checked
