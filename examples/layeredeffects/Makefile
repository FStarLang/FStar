FSTAR_HOME=../..

all: verify-all

include .depend
include ../Makefile.include

verify-all: $(addsuffix .checked, $(ALL_FST_FILES) $(ALL_FSTI_FILES))

.depend:
	$(FSTAR) --dep full $(wildcard *.fst *.fsti) > .depend

%.checked:
	$(FSTAR) --cache_checked_modules $<
	touch -c $@

clean:
	rm -f .depend *.checked

depend: .depend
