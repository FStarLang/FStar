include ../../Makefile.include

EXCLUDE_FILES = ContextPollution.fst
FSTAR_FILES := $(filter-out $(EXCLUDE_FILES),$(wildcard *.fst *.fsti))
OTHERFLAGS  := --cache_checked_modules $(OTHERFLAGS)

all: $(addsuffix .checked, $(FSTAR_FILES))
	$(MAKE) -C exercises

.depend:
	$(FSTAR) --dep full $(FSTAR_FILES) --output_deps_to .depend

.DELETE_ON_ERROR:
include .depend

depend: .depend

%.checked:
	$(FSTAR) --already_cached '+Prims +FStar +LowStar' $<
	touch -c $@

wc:
	# Prims.fst seems to be missing here?
	wc -l Prims.fst $(ALL)


extract:
	krml -skip-compilation MemCpy.fst -tmpdir out

clean:
	rm -rf *.c *.h *~ *.checked *.checked.lax *.krml .depend
	$(MAKE) -C exercises clean
