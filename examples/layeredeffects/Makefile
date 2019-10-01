FSTAR_HOME=../..
OTHERFLAGS+=--already_cached 'Prims FStar LowStar Steel'
include ../Makefile.include
ROOTS=Test.fst RST.Effect.Test.fst Locals.Effect.fst

all: verify-all

.depend:
	$(FSTAR) --dep full $(ROOTS) > .depend

depend: .depend

include .depend

verify-all: $(ALL_CHECKED_FILES)

%.checked:
	$(FSTAR) --cache_checked_modules $<

clean:
	rm -f .depend *.checked
