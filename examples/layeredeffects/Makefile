FSTAR_HOME=../..
OTHERFLAGS+=--already_cached 'Prims FStar LowStar' --include parsing --record_hints
include ../Makefile.include

NO_VERIFY=Buffers.fst

ROOTS=$(wildcard *.fst)

all: verify

.depend:
	$(FSTAR) --dep full $(ROOTS) > .depend

depend: .depend

include .depend

verify: $(filter-out $(addsuffix .checked,$(NO_VERIFY)),$(ALL_CHECKED_FILES))

verify-all: $(ALL_CHECKED_FILES)

%.checked:
	$(FSTAR) --cache_checked_modules $<

clean:
	rm -f .depend *.checked parsing/*.checked
	rm -rf out

extract:
	fstar.exe --codegen OCaml --extract '-* LL' --odir out LL.fst
	krml -skip-compilation -tmpdir out -I parsing Buffers.fst parsing/Flights.fst parsing/FlightsExn.fst parsing/FlightsStExn.fst

.PHONY: all depend verify verify-all clean extract
