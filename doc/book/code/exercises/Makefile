include ../../../Makefile.include

FSTAR_FILES := $(wildcard *fst *fsti)
OTHERFLAGS  := --cache_checked_modules $(OTHERFLAGS)

all: $(addsuffix .checked, $(FSTAR_FILES))

.depend:
	$(FSTAR) --dep full $(FSTAR_FILES) --output_deps_to .depend

depend: .depend

-include .depend

%.checked:
	$(FSTAR) --already_cached '+Prims +FStar +LowStar' $<
	touch -c $@

wc:
	wc -l Prims.fst $(ALL)


extract:
	krml -skip-compilation MemCpy.fst -tmpdir out

clean:
	rm -rf *.c *.h *~ *.checked *.checked.lax *.krml .depend
