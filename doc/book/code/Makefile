include ../../Makefile.include

EXCLUDE_FILES = ContextPollution.fst
FSTAR_FILES := $(filter-out $(EXCLUDE_FILES),$(wildcard *.fst *.fsti))
FSTAR_FLAGS +=--cache_checked_modules $(OTHERFLAGS)

all: $(addsuffix .checked, $(FSTAR_FILES))
	$(MAKE) -C exercises

.depend:
	$(FSTAR) --dep full $(FSTAR_FILES) --already_cached '+Prims +FStar +LowStar' > .depend

.DELETE_ON_ERROR:
include .depend

depend: .depend

%.checked:
	$(FSTAR) $<
	touch -c $@

wc:
	wc -l prims.fst $(ALL)


extract:
	krml -skip-compilation MemCpy.fst -tmpdir out

clean:
	rm -rf *.c *.h *~ *.checked *.checked.lax *.krml .depend
	$(MAKE) -C exercises clean
