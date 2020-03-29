FSTAR_HOME=../../..
OTHERFLAGS+=--already_cached 'Prims FStar LowStar'

all: verify-all

include .depend
include $(FSTAR_HOME)/examples/Makefile.include

verify-all: $(ALL_CHECKED_FILES)

.depend:
	$(FSTAR) --dep full $(wildcard *.fst *.fsti) > .depend

%.checked:
	$(FSTAR) --cache_checked_modules $<
	touch -c $@

clean:
	rm -f .depend *.checked

depend: .depend
