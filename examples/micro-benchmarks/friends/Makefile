FSTAR=fstar
DIRS=1 2

all: verify-all

all-dirs: $(addsuffix .ver, $(DIRS))

%.ver:
	$(MAKE) -C $* verify-all

.depend:
	$(FSTAR) --dep full $(wildcard *.fst *.fsti) > .depend

depend: .depend

include .depend

verify-all: $(addsuffix .checked, $(ALL_FST_FILES))

%.checked:
	$(FSTAR) --cache_checked_modules $<

clean:
	rm -f .depend *.checked
