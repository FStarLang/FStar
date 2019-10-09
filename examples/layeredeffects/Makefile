FSTAR_HOME=../..
OTHERFLAGS+=--already_cached 'Prims FStar LowStar Steel' --include parsing --record_hints
include ../Makefile.include
ROOTS=Test.fst RST.Effect.Test.fst Locals.Effect.fst Buffers.fst Flights.fst FlightsExn.fst FlightsStExn.fst

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
